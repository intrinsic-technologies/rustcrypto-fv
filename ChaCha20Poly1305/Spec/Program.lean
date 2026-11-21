import ChaCha20Poly1305.Spec.Program.Routine
import ChaCha20Poly1305.Spec.Program.Extracted.Image
import Prelude

/-!
# Call contract of the chacha20poly1305 wrappers

The 4 wrappers in `ChaCha20Poly1305/program/src/lib.rs` that have a theorem are System V functions
with one contract. A `Routine` (`Spec/Program/Routine.lean`), one constant per wrapper, holds what
differs: where each input and its length are passed, where the output goes and how its size follows
the message's length, the heap, the in-place buffer's capacity, and whether the crate accepts the
inputs. `ValidCall routine s inputs` is what a call needs; `outputRegion` is the bytes it writes to
its output, and `readOutput` reads them from final memory. EAX holds the status: 0 when the crate
returns `Ok`, `aeadErrorStatus` (1) when it returns `aead::Error`. Arguments (lengths go in the
8-byte stack slots above the return address; "data" is the associated data):

| Wrappers | RDI | RSI | RDX | RCX | R8 | R9 | stack slots 0, 1, 2, 3 |
|---|---|---|---|---|---|---|---|
| `encrypt_in_place` | key | nonce | data | buffer | data length | message length | buffer capacity |
| `decrypt_in_place` | key | nonce | data | buffer | data length | buffer length | |
| `encrypt`, `decrypt` | key | nonce | data | message | heap | output | data, message, heap and output lengths |

`ChaCha20Poly1305/README.md` has the wrappers and the build;
`Spec/Program/Routine.lean` says how each stack budget is derived.
-/

namespace ChaCha20Poly1305.Spec.Program

open Prelude X86

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM holds every byte of the extracted sections at its address -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, Extracted.programSections.fetchByte address = some byte →
    s.external[address]? = some byte

/-- `address` is in an extracted section -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, Extracted.programSections.fetchByte address = some byte

/-- The page-table bytes that `IdentityMappedMemory` requires, from `0x1000` to `0x2020` -/
def pageTables : MemoryRegion := ⟨0x1000, 0x1020⟩

/-- The return address in the slot at RSP is below the user address limit, outside the program -/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

/--
The status for the crate's `aead::Error`: in a decryption, the tag does not match or the input is
shorter than a tag; in `encrypt_in_place`, the buffer has no room for the tag
-/
def aeadErrorStatus : BitVec 32 := 1

/-- The bump allocator's state, two 8-byte words that `program/layout.ld` places at `0x300000` -/
def allocatorStateRegion : MemoryRegion := ⟨0x300000, 16⟩

/-- Stack argument `index` is below 4 GiB and holds `value` -/
def StackArgument (s : Machine.RamState) (index : Nat) (value : BitVec 64) : Prop :=
  let slot := stackArgumentSlot s index
  slot.Bounded ∧
  slot.Word64At s.external value

/--
Argument `argument` holds the number `n`: a register's 64 bits as a number, or a stack slot,
below 4 GiB, holding `n` as a 64-bit word
-/
def ArgumentHolds (s : Machine.RamState) : Argument → Nat → Prop
  | .register register, n => (s.regValue register).toNat = n
  | .stack index, n => StackArgument s index (BitVec.ofNat 64 n)

/-- Argument `argument` holds a number of at least `n` -/
def ArgumentCovers (s : Machine.RamState) : Argument → Nat → Prop
  | .register register, n => n ≤ (s.regValue register).toNat
  | .stack index, n => ∃ length, StackArgument s index length ∧ n ≤ length.toNat

/-- The stack slot an argument occupies, which the call reads; none for a register -/
def argumentRegions (s : Machine.RamState) : Argument → List MemoryRegion
  | .register _ => []
  | .stack index => [stackArgumentSlot s index]

/--
The bytes a call writes to its output buffer, at the address in the routine's output register,
which `readOutput` reads: the output where it fits (`hasRoom`); otherwise the message's own bytes,
which an in-place call overwrites before finding no room
-/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s routine.outputPointer
    (if hasRoom routine s then routine.outputBytes (messageBytes routine s)
    else messageBytes routine s)

/-- The whole output buffer the call may read or write: `bufferBytes` at the output register -/
def bufferRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s routine.outputPointer (bufferBytes routine s)

/--
The heap bytes a call that allocates may write, from the heap's start; empty, at address 0, for a
call that does not allocate
-/
def heapRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  match routine.heap with
  | some heap => registerRegion s heap.pointer (heap.bytes (messageBytes routine s))
  | none => ⟨0, 0⟩

/-- The region of an input, `bytes`, as its layout passes it -/
def inputRegion (routine : Routine) (s : Machine.RamState) (layout : InputLayout)
    (bytes : ByteArray) : MemoryRegion :=
  match layout with
  | .fixed pointer size => registerRegion s pointer size
  | .slice pointer _ => registerRegion s pointer bytes.size
  | .inPlace _ => registerRegion s routine.outputPointer bytes.size

/-- For a slice or an in-place message, its length argument holds its length -/
def LengthArgumentMatches (s : Machine.RamState) (layout : InputLayout) (bytes : ByteArray) :
    Prop :=
  match layout with
  | .fixed _ _ => True
  | .slice _ length => ArgumentHolds s length bytes.size
  | .inPlace length => ArgumentHolds s length bytes.size

/--
`property` holds of each layout and the input in the same position, and there are as many inputs
as layouts
-/
def EachInput (property : InputLayout → ByteArray → Prop) :
    List InputLayout → List ByteArray → Prop
  | [], [] => True
  | layout :: layouts, bytes :: inputs => property layout bytes ∧ EachInput property layouts inputs
  | _, _ => False

/--
Validity conditions on an input in memory: the region ends below 4 GiB and holds `bytes`; its
start may be 0
-/
def ValidInput (s : Machine.RamState) (region : MemoryRegion) (bytes : ByteArray) : Prop :=
  region.Bounded ∧
  region.HasBytes s.external bytes

/--
Validity conditions on an output buffer in memory: the region ends below 4 GiB and every byte of
it is in RAM; its start may be 0
-/
def ValidOutput (s : Machine.RamState) (region : MemoryRegion) : Prop :=
  region.Bounded ∧
  region.Allocated s.external

/--
The regions the call may write: the output buffer where the call needs it, the heap and the
allocator's state where it allocates, and the stack
-/
def writtenRegions (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) :
    List MemoryRegion :=
  (if routine.needsOutput inputs then [bufferRegion routine s] else []) ++
    (if routine.heap.isSome then [heapRegion routine s, allocatorStateRegion] else []) ++
    [Stack.region s routine.minStackBytes]

/--
The regions the call only reads: the inputs apart from an in-place message; the stack slots of the
inputs' lengths, the heap's length and the buffer's capacity; and the stack slot of the output's
length, where the call needs the output
-/
def readRegions (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) :
    List MemoryRegion :=
  (List.zip routine.inputs inputs).flatMap (fun
      | (.inPlace _, _) => []
      | (layout, bytes) => [inputRegion routine s layout bytes]) ++
    routine.inputs.flatMap (fun
      | .fixed _ _ => []
      | .slice _ length => argumentRegions s length
      | .inPlace length => argumentRegions s length) ++
    (routine.heap.toList.flatMap fun heap => argumentRegions s heap.length) ++
    routine.capacity.toList.flatMap (argumentRegions s) ++
    (if routine.needsOutput inputs then routine.outputLength.toList.flatMap (argumentRegions s)
    else [])

/--
The written regions are pairwise disjoint and disjoint from the regions only read, which may
overlap one another; the written regions also avoid the program and the page tables
-/
def MemorySeparation (written read : List MemoryRegion) : Prop :=
  written.Pairwise MemoryRegion.Disjoint ∧
  (∀ region ∈ written, ∀ input ∈ read, region.Disjoint input) ∧
  ∀ region ∈ written, region.Avoids (fun a => InProgram a ∨ pageTables.Contains a.toNat)

/--
Validity conditions for a System V call to `routine` with `inputs`, the byte strings the wrapper
takes in its argument order, each where `routine.inputs` says. This is the one statement of what a
call needs:
- the direction flag is clear, the program is loaded at its link-time addresses, and RIP is at the
  routine's entry;
- each slice's or in-place message's length argument holds its input's length; the heap's length
  argument holds at least what the call allocates (`heapRegion`), the output's length argument at
  least what it writes (`outputRegion`), and the capacity argument at least the message's length;
  each stack slot used ends below `userAddressLimit` (2^32);
- each input ends below `userAddressLimit` and holds its bytes, an in-place message at the start of
  the output buffer;
- the output buffer (`bufferRegion`, the whole capacity where the routine has one) is RAM ending
  below `userAddressLimit`;
- where the call allocates, the heap is RAM ending below `userAddressLimit`, at a nonzero address
  unless it is empty, and the allocator's state is RAM; no other pointer needs to be nonzero;
- `Stack.Valid`: the `minStackBytes` below RSP and the return slot are RAM ending below
  `userAddressLimit`, RSP is at least `minStackBytes`, and RSP is 8 more than a multiple of 16;
- `MemorySeparation`: the regions written (`writtenRegions`: output buffer, heap, allocator state,
  stack) are pairwise disjoint, disjoint from the regions only read (`readRegions`: the inputs and
  stack slots), which may overlap one another, and avoid the program and the page tables;
- `ValidReturnAddress`: the return address at RSP is below `userAddressLimit`, outside the program.

The output buffer and its length are required only where the call needs them
(`Routine.needsOutput`): a rejected `decrypt` neither touches the output nor reads its length.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  lengthArgumentsMatchInputs : EachInput (LengthArgumentMatches s) routine.inputs inputs
  heapLengthArgumentCoversHeap :
    ∀ heap ∈ routine.heap, ArgumentCovers s heap.length (heapRegion routine s).size
  outputLengthArgumentCoversOutput : routine.needsOutput inputs = true →
    ∀ length ∈ routine.outputLength, ArgumentCovers s length (outputRegion routine s).size
  capacityArgumentCoversMessage :
    ∀ capacity ∈ routine.capacity, ArgumentCovers s capacity (messageBytes routine s)
  inputsInMemory :
    EachInput (fun layout bytes => ValidInput s (inputRegion routine s layout bytes) bytes)
      routine.inputs inputs
  outputInMemory : routine.needsOutput inputs = true → ValidOutput s (bufferRegion routine s)
  heapInMemory : routine.heap.isSome = true →
    ValidOutput s (heapRegion routine s) ∧ allocatorStateRegion.Allocated s.external
  heapNonzeroIfAllocating : routine.heap.isSome = true →
    0 < (heapRegion routine s).size → (heapRegion routine s).start ≠ 0
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation (writtenRegions routine s inputs) (readRegions routine s inputs)
  returnAddress : ValidReturnAddress s

/-- Reads the bytes of `region` from final memory in address order; fails at a missing byte -/
def readRegion (final : Machine.RamState) (region : MemoryRegion) :
    Except Machine.Fault ByteArray :=
  (List.range region.size).foldlM (init := ByteArray.empty) fun bytes offset =>
    let address := BitVec.ofNat 64 (region.start + offset)
    match final.external[address]? with
    | some byte => .ok (bytes.push byte)
    | none => .error (.unmappedMemory address)

/-- Reads the output from final memory at the initial output pointer -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault ByteArray :=
  readRegion final (outputRegion routine initial)

end ChaCha20Poly1305.Spec.Program
