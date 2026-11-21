import Prelude
import Standards.NIST.SHA1
import Sha1.Spec.Hasher
import Sha1.Spec.Program.Extracted.Image

/-!
# Call semantics of the extracted entry points

Three of the System V entry points of `Sha1/program/src/lib.rs`, which wraps `sha1` 0.11.0. Each
hashes from a fresh hasher, or compresses a state the caller supplies, within one call. One
namespace per argument shape (registers in System V order RDI, RSI, RDX, RCX, R8), each with its
call predicate `ValidCall` and its `readOutput`, the output bytes in final memory:

* `Digest`: `sha1_digest(input, input_len, output)`, 20 bytes out at RDX;
* `Compress`: `sha1_compress(state, blocks, num_blocks)`, a five-word state at RDI read and
  overwritten in place;
* `SliceHash`: `sha1_update_finalize(input, num_inputs, input_lens, output)`, slice `i` being the
  `input_lens[i]` bytes at `input[i]`, 20 bytes out at RCX.

No call can fail, so none returns a status. Definitions shared by all entry points come first, then
the slice tables (`Slices`), then the shapes. The wrappers' ABI, the conditions in short and the
build are in `Sha1/README.md`.
-/

namespace Sha1.Spec.Program

open Prelude X86

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM contains every extracted byte -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- `address` is contained by an extracted section -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, (address, byte) ∈ Extracted.programImage

/-- `address` holds one of the page-table bytes that `Prelude.IdentityMappedMemory` fixes -/
def InPageTables (address : BitVec 64) : Prop :=
  ∃ region ∈ #v[(⟨0x1000, 8⟩ : MemoryRegion), ⟨0x2000, 32⟩], region.Contains address.toNat

/-- The return address is below the user address limit and outside the program image -/
def ValidReturnAddress (bindings : Machine.Bindings) (s : Machine.RamState) : Prop :=
  letI := bindings
  ∃ boundary, nearReturn64Boundary s = .ok boundary ∧
    boundary.rip.toNat < userAddressLimit ∧
    ¬ InProgram boundary.rip

/--
The System V callee-saved general-purpose registers other than RSP, namely RBX, RBP and R12–R15,
retain their entry values. RSP is fixed by the return boundary of `Prelude.UniqueExecution`; the
x87 control word and the MXCSR control bits, also callee-saved, are not covered.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

/--
Validity conditions on bytes the call only reads: at a nonzero address, ending below 4 GiB, and
holding `bytes`
-/
def ValidInput (s : Machine.RamState) (region : MemoryRegion) (bytes : ByteArray) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external bytes

/-- Validity conditions on an output buffer: at a nonzero address, ending below 4 GiB, in RAM -/
def ValidOutput (s : Machine.RamState) (output : MemoryRegion) : Prop :=
  output.start ≠ 0 ∧
  output.Bounded ∧
  output.Allocated s.external

/--
The output and stack regions are disjoint, and each avoids every region in `reads`, which the call
only reads, the program, and the page tables. The regions in `reads` may overlap one another and
the program.
-/
def MemorySeparation (reads : List MemoryRegion) (output stack : MemoryRegion) : Prop :=
  output.Disjoint stack ∧
  ∀ region ∈ #v[output, stack],
    (∀ read ∈ reads, read.Disjoint region) ∧
    region.Avoids fun address => InProgram address ∨ InPageTables address

/--
Reads the bytes of `region` from `memory`, in address order. Returns `.ok` on success or
`.error (.unmappedMemory address)` for the first missing byte.
-/
def readBytes (region : MemoryRegion) (memory : Machine.Ram) :
    Except Machine.Fault (Vector UInt8 region.size) :=
  Vector.ofFnM fun i : Fin region.size =>
    let address := BitVec.ofNat 64 (region.start + i.val)
    match memory[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

namespace Slices

/-- One input slice of a call: the address in its pointer-table entry, and the bytes there -/
structure Input where
  /-- Address of the slice's first byte, the word in its pointer-table entry -/
  address : BitVec 64
  /-- The slice's bytes in address order; their number is the word in its length-table entry -/
  bytes : ByteArray

/-- Memory region of the slice's bytes -/
def Input.region (input : Input) : MemoryRegion :=
  ⟨input.address.toNat, input.bytes.size⟩

/-- The bytes of the slices, concatenated in order -/
def message (inputs : Array Input) : ByteArray :=
  inputs.foldl (fun message input => message ++ input.bytes) ByteArray.empty

/-- Table of `count` eight-byte slice addresses supplied through the System V RDI argument -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- Table of `count` eight-byte slice lengths supplied through the System V RDX argument -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The eight-byte entry `i` of a table, counting from zero at the table's start -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion :=
  ⟨table.start + 8 * i, 8⟩

/-- A table is at a nonzero address, even when empty, and ends below 4 GiB -/
def ValidTable (table : MemoryRegion) : Prop :=
  table.start ≠ 0 ∧ table.Bounded

/--
Validity conditions on the two tables in memory: both are valid, entry `i` of the pointer table
holds slice `i`'s address and entry `i` of the length table its length
-/
structure ValidTables (s : Machine.RamState) (inputs : Array Input) : Prop where
  pointerTableValid : ValidTable (pointerTable s inputs.size)
  lengthTableValid : ValidTable (lengthTable s inputs.size)
  pointerEntriesMatchInputs : ∀ i : Fin inputs.size,
    (tableEntry (pointerTable s inputs.size) i).Word64At s.external inputs[i].address
  lengthEntriesMatchInputs : ∀ i : Fin inputs.size,
    (tableEntry (lengthTable s inputs.size) i).Word64At s.external
      (BitVec.ofNat 64 inputs[i].bytes.size)

/--
Validity conditions on the slices in memory: both tables are valid and hold the slices' addresses
and lengths (`ValidTables`), and each slice is a valid input at its address
-/
structure ValidInputs (s : Machine.RamState) (inputs : Array Input) : Prop
    extends ValidTables s inputs where
  inputsInMemory : ∀ i : Fin inputs.size, ValidInput s inputs[i].region inputs[i].bytes

/-- The regions a call only reads: the pointer table, the length table, and every slice -/
def readRegions (s : Machine.RamState) (inputs : Array Input) : List MemoryRegion :=
  pointerTable s inputs.size :: lengthTable s inputs.size :: (inputs.map Input.region).toList

end Slices

namespace Digest

/--
Stack budget, in bytes below entry RSP; a caller may provide more. The extractor's estimate for
`sha1_digest`, read from the same extraction as the program bytes: 656 bytes, 528 of them the
deepest use in the disassembly (four pushes, `sub rsp,0x118`, one `call`, and the 208 bytes of
`compress`) and 128 of slack (the target disables the red zone).
-/
def minStackBytes : Nat := Extracted.sha1DigestStackBytes.get (by decide)

/-- Input bytes supplied through the System V RDI argument -/
def inputRegion (s : Machine.RamState) (input : ByteArray) : MemoryRegion :=
  registerRegion s .rdi input.size

/-- 20-byte digest output buffer supplied through the System V RDX argument -/
def outputRegion (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx 20

/-- The 20 bytes of the output buffer in final memory -/
def readOutput (initial final : Machine.RamState) : Except Machine.Fault (Vector UInt8 20) :=
  readBytes (outputRegion initial) final.external

/--
Validity conditions for a System V call to `sha1_digest` with input `input`; the input, its length,
and the output buffer are supplied through RDI, RSI, and RDX. A valid call has:

* the direction flag clear, the program loaded at its link-time addresses, and RIP at
  `sha1_digest`;
* RSI equal to the input's length, and the input's bytes at RDI, at a nonzero address even when
  empty (`ValidInput`);
* 20 bytes of RAM at RDX, at a nonzero address (`ValidOutput`);
* `minStackBytes` bytes below RSP and the 8-byte return slot at RSP, all in RAM, with RSP at least
  `minStackBytes` and 8 more than a multiple of 16 (`Stack.Valid`);
* the input, the output and the stack region each ending strictly below `userAddressLimit` (2³²),
  so the input has fewer than 2³² bytes;
* the output and the stack disjoint from each other and from the input, and avoiding the program
  and the page tables; the input may overlap the program (`MemorySeparation`);
* a return address below `userAddressLimit` and outside the program image (`ValidReturnAddress`).

No alignment is required of the input or the output.
-/
structure ValidCall (bindings : Machine.Bindings) (s : Machine.RamState) (input : ByteArray) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = Extracted.sha1DigestAddress
  inputLengthArgumentMatchesInput : (s.regValue .rsi).toNat = input.size
  inputInMemory : ValidInput s (inputRegion s input) input
  outputInMemory : ValidOutput s (outputRegion s)
  stackAvailable : Stack.Valid s minStackBytes
  separation :
    MemorySeparation [inputRegion s input] (outputRegion s) (Stack.region s minStackBytes)
  returnAddress : ValidReturnAddress bindings s

end Digest

namespace Compress

/--
Stack budget, in bytes below entry RSP; a caller may provide more. The extractor's estimate for
`sha1_compress`, read from the same extraction as the program bytes: 336 bytes, 208 of them the
deepest use in the disassembly (six pushes and `sub rsp,0xa0` in `compress`, which the entry point
jumps to) and 128 of slack (the target disables the red zone).
-/
def minStackBytes : Nat := Extracted.sha1CompressStackBytes.get (by decide)

/-- Block bytes supplied through the System V RSI argument -/
def inputRegion (s : Machine.RamState) (blocks : ByteArray) : MemoryRegion :=
  registerRegion s .rsi blocks.size

/-- 20-byte state, read and overwritten in place, supplied through the System V RDI argument -/
def outputRegion (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdi 20

/-- The 20 bytes of the state in final memory -/
def readOutput (initial final : Machine.RamState) : Except Machine.Fault (Vector UInt8 20) :=
  readBytes (outputRegion initial) final.external

/--
Validity conditions on the state in memory, which the call reads and overwrites in place: at a
nonzero address, ending below 4 GiB, and holding `stateBytes H`
-/
def ValidOutput (s : Machine.RamState) (H : Vector (BitVec 32) 5) : Prop :=
  let region := outputRegion s
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external ⟨(Hasher.stateBytes H).toArray⟩

/--
Validity conditions for a System V call to `sha1_compress` with state `H` and block bytes `blocks`;
the state, the blocks, and the number of blocks are supplied through RDI, RSI, and RDX
-/
structure ValidCall (bindings : Machine.Bindings) (s : Machine.RamState)
    (H : Vector (BitVec 32) 5) (blocks : ByteArray) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = Extracted.sha1CompressAddress
  blockCountArgumentMatchesBlocks : 64 * (s.regValue .rdx).toNat = blocks.size
  inputInMemory : ValidInput s (inputRegion s blocks) blocks
  outputInMemory : ValidOutput s H
  stackAvailable : Stack.Valid s minStackBytes
  separation :
    MemorySeparation [inputRegion s blocks] (outputRegion s) (Stack.region s minStackBytes)
  returnAddress : ValidReturnAddress bindings s

end Compress

namespace SliceHash

/--
The entry point taking `(input, num_inputs, input_lens, output)`, `sha1_update_finalize`: the
slices are hashed from a new hasher and one result of `outputBytes` bytes is written at RCX
-/
structure Routine where
  /-- The entry point's address in the extracted image -/
  entryAddress : BitVec 64
  /-- Stack budget, in bytes below entry RSP; a caller may provide more -/
  minStackBytes : Nat
  /-- Size of the output buffer in bytes -/
  outputBytes : Nat

/--
`sha1_update_finalize`, writing a 20-byte digest. Stack budget: the extractor's estimate, 704
bytes, 576 of them the deepest use in the disassembly (six pushes, `sub rsp,0x138`, one `call`, and
the 208 bytes of `compress`) and 128 of slack (the target disables the red zone).
-/
def updateFinalize : Routine where
  entryAddress := Extracted.sha1UpdateFinalizeAddress
  minStackBytes := Extracted.sha1UpdateFinalizeStackBytes.get (by decide)
  outputBytes := 20

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V RCX argument -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rcx routine.outputBytes

/-- The bytes of the output buffer in final memory -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (outputRegion routine initial) final.external

/--
Validity conditions for a System V call to `routine` with input slices `inputs`; the pointer table,
the slice count, the length table, and the output buffer are supplied through RDI, RSI, RDX, and
RCX. A valid call has:

* the direction flag clear, the program loaded at its link-time addresses, and RIP at the
  routine's entry;
* RSI equal to the number of slices; the pointer table at RDI and the length table at RDX, 8 bytes
  per slice each, at nonzero addresses even when empty, entry `i` of each holding slice `i`'s
  address and length; each slice's bytes in memory at its nonzero address (`Slices.ValidInputs`);
* `routine.outputBytes` bytes of RAM at RCX, at a nonzero address (`ValidOutput`);
* `routine.minStackBytes` bytes below RSP and the 8-byte return slot at RSP, all in RAM, with RSP
  at least `routine.minStackBytes` and 8 more than a multiple of 16 (`Stack.Valid`);
* the two tables, every slice, the output and the stack region each ending strictly below
  `userAddressLimit` (2³²), so the message is shorter than 2⁶¹ bytes;
* the output and the stack disjoint from each other, from the tables and from every slice, and
  avoiding the program and the page tables; the tables and the slices may overlap one another and
  the program (`MemorySeparation`);
* a return address below `userAddressLimit` and outside the program image (`ValidReturnAddress`).

No alignment is required of the tables, the slices or the output.
-/
structure ValidCall (routine : Routine) (bindings : Machine.Bindings) (s : Machine.RamState)
    (inputs : Array Slices.Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  sliceCountArgumentMatchesInputs : (s.regValue .rsi).toNat = inputs.size
  inputInMemory : Slices.ValidInputs s inputs
  outputInMemory : ValidOutput s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation (Slices.readRegions s inputs) (outputRegion routine s)
      (Stack.region s routine.minStackBytes)
  returnAddress : ValidReturnAddress bindings s

end SliceHash

end Sha1.Spec.Program
