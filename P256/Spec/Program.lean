import Prelude
import P256.Spec.Program.Extracted.Image

/-!
# P-256 call semantics

The machine-level contract of the one-function entry points of `P256/program`, in
`P256.Spec.Program.Routines`. `Program/Functions.lean` gives one `Routine` per wrapper: its entry,
its stack budget, what its slices must hold, which inputs its function accepts, its output register,
its result's size and its heap bound. This file defines what the routines share:

- `ValidCall routine initial inputs`, the call premise of every theorem, with `inputs` the call's
  byte arrays in the wrapper's slice order, such as
  `ValidCall signingKeyTrySign initial [signingKey, msg]`; `ValidCallWithSlices` lists its
  conditions;
- `readOutput`, the result read back from the output buffer: its length as eight little-endian
  bytes, then that many bytes;
- the regions a call may write, listed in every frame in one order: the output (`outputRegion`),
  the heap (`heapRegion`), the allocator's state (`allocatorStateRegion`), the random source
  (`randomSourceRegion`) and the stack (`callStack`), leaving out the heap where a routine
  allocates nothing;
- the status each failure returns (`invalidPublicKeyStatus` and the others), all 1.

The wrappers' ABI and the build are in `P256/README.md`.
-/

set_option autoImplicit false

namespace P256.Spec.Program.Routines

open Prelude X86

/-! ## Machine conditions of every entry point -/

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM contains every byte of each extracted section -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, Extracted.programSections.fetchByte address = some byte →
    s.external[address]? = some byte

/-- `address` is in an extracted section -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, Extracted.programSections.fetchByte address = some byte

/-- `address` is in the two page-table pages of Prelude's fixed identity mapping -/
def InPageTables (address : BitVec 64) : Prop :=
  (⟨0x1000, 0x2000⟩ : MemoryRegion).Contains address.toNat

/-- The return address in the slot at RSP is below the user address limit, outside the program -/
def ValidReturnAddress [Machine.Bindings] (s : Machine.RamState) : Prop :=
  ∃ boundary, nearReturn64Boundary s = .ok boundary ∧
    boundary.rip.toNat < userAddressLimit ∧ ¬ InProgram boundary.rip

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

/--
The run never returns: every finite machine-step budget is exhausted before the return boundary,
as when the crate panics, since the wrapper's panic handler loops forever
-/
def NeverReturns [Machine.Bindings] (initial : Machine.RamState) : Prop :=
  ∃ boundary, nearReturn64Boundary initial = .ok boundary ∧ Prelude.Diverges boundary initial []

/--
The bump allocator's state, the first of the wrapper's two writable statics in its `.bss` at
0x300000 (`program/layout.ld`), as the linker lays it out in the extracted image: the caller's heap
address, length and offset (`HEAP`, `src/arena.rs`, 24 bytes at 0x300000). Every entry point sets
it on entry, before reading it; it lies below `userAddressLimit`, above the image
-/
def allocatorStateRegion : MemoryRegion := ⟨0x300000, 0x18⟩

/--
The second writable static, right after the allocator's state: the address and length of the
caller's random bytes that getrandom's custom backend hands out (`RANDOM`, `src/abi.rs`, 16 bytes
at 0x300018). Every entry point empties it on entry; no entry point of this specification reads it
afterwards
-/
def randomSourceRegion : MemoryRegion := ⟨0x300018, 0x10⟩

/-! ## Entry points -/

/--
One wrapper: everything about its call that the one `ValidCall`, `outputRegion` and `readOutput`
read. All of it differs between the entry points but the output register, which every wrapper's
signature puts in RCX
-/
structure Routine where
  /-- Address of the routine's first instruction -/
  entryAddress : BitVec 64
  /-- Stack budget in bytes below entry RSP that a valid call provides; it may exceed the use -/
  minStackBytes : Nat
  /--
  What the slices must hold to be the bytes of values of the Rust arguments, a premise of
  `ValidCall` the wrapper does not check
  -/
  arguments : Array ByteArray → Bool
  /--
  Whether the function succeeds on the slices' contents, so that the call writes its output: its
  specification's success; `true` everywhere for a function that cannot fail
  -/
  accepts : Array ByteArray → Bool
  /--
  The register holding the output buffer's address, where `outputRegion` and `readOutput` find
  it: RCX, the fourth System V argument, in every wrapper's signature (`program/src/abi.rs`)
  -/
  outputPointer : Syntax.Reg
  /-- The bytes of the result its specification gives on the slices' contents, 0 for a failure -/
  outputBytes : Array ByteArray → Nat
  /--
  The heap bytes a call with this many slices needs: a bound on what it allocates, 0 for a function
  that allocates nothing; only the number of slices, not their contents, changes it
  -/
  heapBytes : Nat → Nat

/-- The status `PublicKey::from_sec1_bytes` returns for its `elliptic_curve::Error`: 1 -/
def invalidPublicKeyStatus : BitVec 32 := 1

/-- The status `Verifier::verify` returns for its `signature::Error`, a signature that fails: 1 -/
def invalidSignatureStatus : BitVec 32 := 1

/-- The status `Signature::from_slice` returns for its `signature::Error`: 1 -/
def invalidSignatureBytesStatus : BitVec 32 := 1

/--
The bytes of a specification's result, 0 for its failure: `outputBytes` of a routine that can fail
-/
def resultBytes : Option ByteArray → Nat
  | some bytes => bytes.size
  | none => 0

/-- One input slice in memory -/
structure Input where
  /-- Address of the slice's first byte, the word in its pointer-table entry -/
  address : BitVec 64
  /-- The slice's bytes in address order; their number is the word in its length-table entry -/
  bytes : ByteArray

/-- The bytes of the slice `input` -/
def Input.region (input : Input) : MemoryRegion := ⟨input.address.toNat, input.bytes.size⟩

/-- The slices' contents, in order -/
def inputBytes (slices : Array Input) : Array ByteArray := slices.map Input.bytes

/-- Table of `count` eight-byte slice addresses supplied through the System V RDI argument -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- Table of `count` eight-byte slice lengths supplied through the System V RDX argument -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The eight-byte entry `i` of a table, counting from zero at the table's start -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion := ⟨table.start + 8 * i, 8⟩

/-- Validity conditions on a table in memory, at a non-null address -/
def ValidTable (table : MemoryRegion) : Prop :=
  table.start ≠ 0 ∧
  table.Bounded

/--
Validity conditions on input slice `i`: entry `i` of the pointer table holds its address, entry
`i` of the length table holds its length, and its bytes are in memory at that non-null address
-/
def ValidInput (s : Machine.RamState) (slices : Array Input) (i : Fin slices.size) : Prop :=
  let slice := slices[i]
  (tableEntry (pointerTable s slices.size) i).Word64At s.external slice.address ∧
  (tableEntry (lengthTable s slices.size) i).Word64At s.external
    (BitVec.ofNat 64 slice.bytes.size) ∧
  slice.address ≠ 0 ∧
  slice.region.Bounded ∧
  slice.region.HasBytes s.external slice.bytes

/--
Validity conditions on the slices in memory: the pointer table, the length table, and every slice
are valid
-/
structure ValidInputs (s : Machine.RamState) (slices : Array Input) : Prop where
  pointerTableValid : ValidTable (pointerTable s slices.size)
  lengthTableValid : ValidTable (lengthTable s slices.size)
  slicesValid : ∀ i, ValidInput s slices i

/-- The regions a call only reads: the pointer table, the length table, and every slice -/
def readRegions (s : Machine.RamState) (slices : Array Input) : List MemoryRegion :=
  pointerTable s slices.size :: lengthTable s slices.size :: (slices.map Input.region).toList

/--
The bytes a call on `inputs` writes to the output buffer at the routine's output register: the
result's length, then the result, `8 + routine.outputBytes` bytes
-/
def outputRegion (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) :
    MemoryRegion :=
  registerRegion s routine.outputPointer (8 + routine.outputBytes inputs.toArray)

/-- Validity conditions on the bytes of the output buffer the call writes: at a nonzero address -/
def ValidOutput (routine : Routine) (s : Machine.RamState) (inputs : List ByteArray) : Prop :=
  let region := outputRegion routine s inputs
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
The seventh System V argument, the heap's length: the eight bytes above the return address, the
first stack argument
-/
def heapLengthSlot (s : Machine.RamState) : MemoryRegion :=
  ⟨(s.regValue .rsp).toNat + Stack.returnAddressBytes, 8⟩

/--
The stack a call may use: `routine.minStackBytes` below entry RSP, the return address at RSP and
the heap-length slot above it, the seventh argument, which the callee owns under System V
(`Stack.region s routine.minStackBytes (Stack.returnAddressBytes + 8)`); it stands last in every
frame
-/
def callStack (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  Stack.region s routine.minStackBytes (Stack.returnAddressBytes + 8)

/--
The caller's heap, given by its address in R9: the `routine.heapBytes` bytes the call may allocate
from its start, for the slice count in RSI, which `ValidCall` requires to be the number of inputs
-/
def heapRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .r9 (routine.heapBytes (s.regValue .rsi).toNat)

/--
The alignment the caller gives the heap's start when a call allocates: 8 bytes, a multiple of the
alignment of every block a wrapper requests, read from the image, where the bump allocator
(`src/arena.rs`) is inlined at each allocation. The allocator rounds each block's address, not its
offset, up to the block's alignment, so from a start that is a multiple of 8 no block gains
padding. No routine here allocates: every `heapBytes` is 0.
-/
def heapAlignment : Nat := 8

/--
Validity conditions on the caller's heap of `length` bytes, the heap length argument: it is at least
what the call allocates (`heapRegion`, `routine.heapBytes` bytes); when the call allocates, the
heap's start in R9 is nonzero (the allocator's first block is the heap's start, and Rust takes a
null block for an allocation failure) and a multiple of `heapAlignment`, and the whole heap,
`length` bytes from R9, ends below `userAddressLimit` (so the allocator's end address does not
overflow); and the bytes the call needs are RAM. A call that allocates nothing needs nothing of R9
or of `length`.
-/
def ValidHeap (routine : Routine) (s : Machine.RamState) (length : Nat) : Prop :=
  (heapRegion routine s).size ≤ length ∧
  (0 < (heapRegion routine s).size →
    (s.regValue .r9).toNat ≠ 0 ∧ (s.regValue .r9).toNat % heapAlignment = 0 ∧
      (registerRegion s .r9 length).Bounded) ∧
  (heapRegion routine s).Allocated s.external

/--
The written regions are pairwise disjoint, and each avoids every region the call only reads, the
program, and the page tables. The regions the call only reads may overlap one another.
-/
def MemorySeparation {n : Nat} (written : Vector MemoryRegion n) (read : List MemoryRegion) :
    Prop :=
  MemoryRegion.PairwiseDisjoint written ∧
  ∀ region ∈ written,
    (∀ other ∈ read, other.Disjoint region) ∧
    region.Avoids fun address => InProgram address ∨ InPageTables address

/--
Validity conditions for a System V call to the wrapper `routine` on the byte arrays `inputs`, in
the wrapper's slice order, held by the slices `slices` at the addresses the pointer table gives.
The wrapper checks none of them, so on other calls its behaviour is not specified.

- entry: the program is loaded at its link-time addresses (`ProgramLoaded`), RIP is at
  `routine.entryAddress`, and the direction flag is clear;
- inputs: RSI is the number of inputs; the pointer table at RDI and the length table at RDX, each
  at a nonzero address, give each slice's address and length, and each slice's bytes are in memory
  there, at a nonzero address (`ValidInputs`); the slices hold `inputs`;
- arguments: the slices are as many as the Rust function's arguments and each holds the bytes of a
  value of its argument's Rust type (`routine.arguments`, which for
  `SigningKey::generate_from_rng` also asks for enough random bytes);
- output: RCX is nonzero (`outputNonzero`). On a call the function accepts (`routine.accepts`), the
  capacity in R8 is at least `8 + routine.outputBytes` and those bytes at RCX are RAM
  (`ValidOutput`); a rejected call writes nothing to the output (`program/src/abi.rs`, `call`), so
  it needs only the nonzero pointer;
- heap: the heap length slot, the first stack argument, 8 bytes above the return address, holds a
  length of at least `routine.heapBytes`, and the `routine.heapBytes` bytes from R9 are RAM
  (`ValidHeap`); when the call allocates, R9 is nonzero and a multiple of `heapAlignment` and the
  whole heap ends below `userAddressLimit`. A call that allocates nothing needs nothing of R9 or of
  the length;
- statics: the allocator's state and the random source are RAM;
- stack: RSP is at least `routine.minStackBytes`, those bytes below RSP and the return address at
  RSP are RAM, and RSP is 8 more than a multiple of 16 (`Stack.Valid`); the stack the call may
  write (`callStack`) runs through the heap length slot;
- separation: the heap, the two statics and the stack are pairwise disjoint, each avoiding the
  tables, every slice, the program and the page tables (`separation`); on an accepted call the
  output too (`outputSeparationIfAccepted`). The regions the call only reads may overlap one
  another;
- return address: below `userAddressLimit` and outside the program (`ValidReturnAddress`).

The tables, the slices, the output of an accepted call and the stack through the heap length slot
each end strictly below `userAddressLimit` (2^32; `MemoryRegion.Bounded` is strict on the end).
-/
structure ValidCallWithSlices [Machine.Bindings] (routine : Routine) (s : Machine.RamState)
    (inputs : List ByteArray) (slices : Array Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  countArgumentMatchesInputs : (s.regValue .rsi).toNat = inputs.length
  argumentsValid : routine.arguments inputs.toArray = true
  slicesHoldInputs : inputBytes slices = inputs.toArray
  inputsInMemory : ValidInputs s slices
  outputNonzero : (outputRegion routine s inputs).start ≠ 0
  outputSufficesIfAccepted : routine.accepts inputs.toArray = true →
    8 + routine.outputBytes inputs.toArray ≤ (s.regValue .r8).toNat
  outputInMemoryIfAccepted : routine.accepts inputs.toArray = true →
    ValidOutput routine s inputs
  heapInMemory :
    ∃ length, (heapLengthSlot s).Word64At s.external length ∧ ValidHeap routine s length.toNat
  allocatorStateInMemory : allocatorStateRegion.Allocated s.external
  randomSourceInMemory : randomSourceRegion.Allocated s.external
  stackAvailable : Stack.Valid s routine.minStackBytes ∧ (callStack routine s).Bounded
  separation :
    MemorySeparation
      #v[heapRegion routine s, allocatorStateRegion, randomSourceRegion, callStack routine s]
      (readRegions s slices)
  outputSeparationIfAccepted : routine.accepts inputs.toArray = true →
    MemorySeparation
      #v[outputRegion routine s inputs, heapRegion routine s, allocatorStateRegion,
        randomSourceRegion, callStack routine s]
      (readRegions s slices)
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to the wrapper `routine` on the byte arrays `inputs`, in
the wrapper's slice order: some slices holding them, at the addresses the pointer table at RDI
gives, meet `ValidCallWithSlices`. The slices' addresses are data in memory, not arguments of the
theorems, so they are named here; the table's words determine them.
-/
def ValidCall [Machine.Bindings] (routine : Routine) (s : Machine.RamState)
    (inputs : List ByteArray) : Prop :=
  ∃ slices : Array Input, ValidCallWithSlices routine s inputs slices

/-- The byte at `address` of final memory, or the fault for a missing byte -/
def readByte (final : Machine.RamState) (address : Nat) : Except Machine.Fault UInt8 :=
  let word := BitVec.ofNat 64 address
  match final.external[word]? with
  | some byte => .ok byte
  | none => .error (.unmappedMemory word)

/--
Reads the result from final memory at the initial output pointer, in the routine's output register:
its length from the first eight bytes, little-endian, then that many bytes. Returns
`.error (.unmappedMemory address)` for the first missing byte.
-/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault ByteArray := do
  let start := (initial.regValue routine.outputPointer).toNat
  let length ← (List.range 8).foldrM
    (fun i value => do return value * 256 + (← readByte final (start + i)).toNat) 0
  let bytes ← (List.range length).mapM fun i => readByte final (start + 8 + i)
  return ⟨bytes.toArray⟩

end P256.Spec.Program.Routines
