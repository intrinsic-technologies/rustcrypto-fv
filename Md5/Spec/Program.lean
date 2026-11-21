import Prelude
import Standards.RFC.MD5
import Md5.Spec.Program.Extracted.Image

/-!
# Call semantics of the extracted entry points

The 10 System V entry points of `Md5/program/src/lib.rs`, which wraps `md-5` 0.11.0. Each calls
the crate's public methods in a fixed order and writes the results out as bytes; none returns a
value or an error:

| Entry point | Arguments, in RDI, RSI, RDX, RCX, R8, R9 | Contract |
| --- | --- | --- |
| `md5_digest` | input, length, output | `Digest` |
| `md5_digest_slices` | slice tables, output | `OneMessage.digestSlices` |
| `md5_update_finalize_into` | slice tables, output | `OneMessage.updateFinalizeInto` |
| `md5_digest_slices_reset` | slice tables, first count, output | `TwoMessages.digestSlicesReset` |
| `md5_finalize_into_reset_slices` | the same | `TwoMessages.finalizeIntoResetSlices` |
| `md5_fixed_finalize_into_reset_slices` | the same | `TwoMessages.fixedFinalizeIntoResetSlices` |
| `md5_finalize_fixed_reset_slices` | the same | `TwoMessages.finalizeFixedResetSlices` |
| `md5_reset_slices` | the same | `ResetThenDigest.resetSlices` |
| `md5_update_reset_slices` | the same | `ResetThenDigest.updateResetSlices` |
| `md5_compress` | MD buffer, blocks, block count | `Compress` |

"Slice tables" are three arguments: a table of eight-byte slice addresses (RDI), the number of
slices (RSI), and a table of their eight-byte lengths (RDX), the slices forming one message in
order (`Slices`). A "first count" splits them into a first message, the first that many slices,
all of them if it exceeds their number, and a second message, the rest.

Each contract's `ValidCall` says what a call needs, and `Digest.ValidCall` lists the conditions
they share; the machine environment a call assumes is lean-x86's
`Prelude.SupportedIntegerMachineState` and `Prelude.MachineRamUnitStrideDecodable`. Each
`readOutput` reads the output from final memory at the initial output pointer. The machine
assumptions (Theorem Hypotheses) and how to build the verified binary are in `Md5/README.md`.
-/

namespace Md5.Spec.Program

open Prelude X86 Standards.RFC

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
The bytes of `region` in `final` memory, in address order. Returns `.ok` on success or
`.error (.unmappedMemory address)` at the first missing byte.
-/
def readRegion (final : Machine.RamState) (region : MemoryRegion) :
    Except Machine.Fault (Vector UInt8 region.size) :=
  Vector.ofFnM fun i =>
    let address := BitVec.ofNat 64 (region.start + i.val)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

/--
Validity conditions on a written region in memory: at a nonzero address, even when empty, below
4 GiB, and present, with unrestricted initial contents. Every output buffer is one except
`md5_compress`'s MD buffer, whose initial contents are fixed (`Compress.ValidOutput`).
-/
def ValidWritable (s : Machine.RamState) (region : MemoryRegion) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
The written regions are pairwise disjoint, and each avoids every region the call only reads,
the program, and the page tables. The regions the call only reads may overlap one another.
-/
def MemorySeparation (written : Vector MemoryRegion n) (read : List MemoryRegion) : Prop :=
  MemoryRegion.PairwiseDisjoint written ∧
  ∀ region ∈ written,
    (∀ other ∈ read, other.Disjoint region) ∧
    region.Avoids fun address => InProgram address ∨ InPageTables address

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

/--
The first message of a call given a first count `first`: the first `first` slices concatenated,
all of them if `first` exceeds their number
-/
def firstMessage (inputs : Array Input) (first : Nat) : ByteArray :=
  message (inputs.extract 0 first)

/--
The second message of a call given a first count `first`: the slices after the first `first`
concatenated, none if `first` is at least their number
-/
def secondMessage (inputs : Array Input) (first : Nat) : ByteArray :=
  message (inputs.extract first inputs.size)

/-- Table of `count` eight-byte slice addresses supplied through the System V RDI argument -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- Table of `count` eight-byte slice lengths supplied through the System V RDX argument -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The eight-byte entry `i` of a table, counting from zero at the table's start -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion :=
  ⟨table.start + 8 * i, 8⟩

/-- Validity conditions on a table in memory: at a nonzero address, even when empty, below 4 GiB -/
def ValidTable (table : MemoryRegion) : Prop :=
  table.start ≠ 0 ∧
  table.Bounded

/--
Validity conditions on input slice `i`: entry `i` of the pointer table holds its address, which is
nonzero even for an empty slice, entry `i` of the length table holds its length, and its bytes are
in memory at that address
-/
def ValidInput (s : Machine.RamState) (inputs : Array Input) (i : Fin inputs.size) : Prop :=
  let input := inputs[i]
  input.address ≠ 0 ∧
  (tableEntry (pointerTable s inputs.size) i).Word64At s.external input.address ∧
  (tableEntry (lengthTable s inputs.size) i).Word64At s.external
    (BitVec.ofNat 64 input.bytes.size) ∧
  input.region.Bounded ∧
  input.region.HasBytes s.external input.bytes

/--
Validity conditions on the slices in memory: RSI holds their number, and the pointer table, the
length table, and every slice are valid
-/
structure ValidInputs (s : Machine.RamState) (inputs : Array Input) : Prop where
  countArgument : (s.regValue .rsi).toNat = inputs.size
  pointerTableValid : ValidTable (pointerTable s inputs.size)
  lengthTableValid : ValidTable (lengthTable s inputs.size)
  slicesValid : ∀ i, ValidInput s inputs i

/-- The regions the slices occupy: the pointer table, the length table, and every slice -/
def readRegions (s : Machine.RamState) (inputs : Array Input) : List MemoryRegion :=
  pointerTable s inputs.size :: lengthTable s inputs.size :: (inputs.map Input.region).toList

end Slices

/--
One entry point of a shape that several entry points share: its address, its stack budget, and
the number of output bytes it writes
-/
structure Routine where
  /-- The link-time address of the exported symbol -/
  entryAddress : BitVec 64
  /--
  Stack budget, in bytes below entry RSP. `ValidCall` requires the caller to provide at least
  this much, and a caller may provide more.
  -/
  minStackBytes : Nat
  /-- The number of bytes written at the output pointer -/
  outputBytes : Nat

namespace Digest

/--
Stack budget, in bytes below entry RSP, for `md5_digest`. `ValidCall` requires the caller to provide
at least this much, and a caller may provide more. The budget is the extractor's estimate, read from
the same extraction as the program bytes; it includes 128 bytes of slack (the target disables the
red zone).
-/
def minStackBytes : Nat := Extracted.md5DigestStackBytes.get (by decide)

/-- Input bytes supplied through the System V RDI argument -/
def inputRegion (s : Machine.RamState) (input : ByteArray) : MemoryRegion :=
  registerRegion s .rdi input.size

/-- 16-byte digest output buffer supplied through the System V RDX argument -/
def outputRegion (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx 16

/-- Validity conditions on the input in memory, at a nonzero address even when empty -/
def ValidInput (s : Machine.RamState) (input : ByteArray) : Prop :=
  let region := inputRegion s input
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external input

/--
Validity conditions for a System V call to `md5_digest` with message `input`: the input at RDI
(`ValidInput`), its length `input.size` in RSI, and the 16-byte output buffer at RDX
(`ValidWritable`), with the conditions that every call predicate here shares:
- RIP at the entry point, the program loaded at its link-time addresses, and the direction flag
  clear
- every pointer at a nonzero address, even when its region is empty, and every region ending
  strictly below `userAddressLimit`, 2^32; the regions read hold the given bytes, and the output
  is present in memory
- the stack (`Stack.Valid`): the `minStackBytes` bytes below RSP and the 8-byte return slot at
  RSP present, RSP at least `minStackBytes` and 8 more than a multiple of 16
- the return address, the word at RSP, below `userAddressLimit` and outside the program
- the stack disjoint from every input, which the call reads while it writes its frames, and from
  the output, which it would otherwise overwrite; the output and the stack avoid the program and
  the page tables
- no alignment of any region but the stack: the compiled code makes no aligned access, so the
  slice tables need not be eight-byte aligned and the MD buffer need not be four-byte aligned,
  although the wrappers' Rust safety contracts exclude such calls

The nonzero addresses are Rust's rule for `core::slice::from_raw_parts` and references, which the
wrappers use; no instruction of the compiled code compares a caller-supplied address with zero.
The output may overlap the input: the wrapper writes it through a raw pointer, `*output = …`, only
after `Md5::digest` has read the whole input, so neither Rust's aliasing rules nor any instruction
needs them apart.
-/
structure ValidCall (bindings : Machine.Bindings) (s : Machine.RamState) (input : ByteArray) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = Extracted.md5DigestAddress
  inputLengthArgumentMatchesInput : (s.regValue .rsi).toNat = input.size
  inputInMemory : ValidInput s input
  outputInMemory : ValidWritable s (outputRegion s)
  stackAvailable : Stack.Valid s minStackBytes
  stackSeparation : MemorySeparation #v[Stack.region s minStackBytes] [inputRegion s input]
  outputSeparation : MemorySeparation #v[outputRegion s, Stack.region s minStackBytes] []
  returnAddress : ValidReturnAddress bindings s

/-- Reads the digest from final memory at the initial output pointer -/
def readOutput (initial final : Machine.RamState) : Except Machine.Fault (Vector UInt8 16) :=
  readRegion final (outputRegion initial)

end Digest

namespace OneMessage

/--
`md5_digest_slices`: `Md5::new`, `Digest::update` per slice, `Digest::finalize`. The stack budget
is the extractor's estimate, read from the same extraction as the program bytes; it includes 128
bytes of slack (the target disables the red zone).
-/
def digestSlices : Routine :=
  ⟨Extracted.md5DigestSlicesAddress, Extracted.md5DigestSlicesStackBytes.get (by decide), 16⟩

/--
`md5_update_finalize_into`: `Md5::new`, `Update::update` per slice,
`FixedOutput::finalize_into`. The stack budget is the extractor's estimate, read from the same
extraction as the program bytes; it includes 128 bytes of slack (the target disables the red zone).
-/
def updateFinalizeInto : Routine :=
  ⟨Extracted.md5UpdateFinalizeIntoAddress,
    Extracted.md5UpdateFinalizeIntoStackBytes.get (by decide), 16⟩

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V RCX argument -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rcx routine.outputBytes

/--
Validity conditions for a System V call to `routine` with input slices `inputs`; the slice tables
and the output buffer are supplied through RDI, RSI, RDX, and RCX, with the conditions listed on
`Digest.ValidCall`. The stack is disjoint from the tables and the slices, which the call reads while
it writes its frames, and from the output, which it would otherwise overwrite. The output may
overlap the tables and the slices: the wrapper writes it only after the last slice is read and the
slice iterator is dropped, through a raw pointer (`*output = …`) or, in `md5_update_finalize_into`,
through a reference it makes only then, so neither Rust's aliasing rules nor any instruction needs
them apart.
-/
structure ValidCall (routine : Routine) (bindings : Machine.Bindings) (s : Machine.RamState)
    (inputs : Array Slices.Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  inputsInMemory : Slices.ValidInputs s inputs
  outputInMemory : ValidWritable s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  stackSeparation :
    MemorySeparation #v[Stack.region s routine.minStackBytes] (Slices.readRegions s inputs)
  outputSeparation :
    MemorySeparation #v[outputRegion routine s, Stack.region s routine.minStackBytes] []
  returnAddress : ValidReturnAddress bindings s

/-- Reads the output from final memory at the initial output pointer -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readRegion final (outputRegion routine initial)

end OneMessage

namespace TwoMessages

/--
`md5_digest_slices_reset`: the first message by `Digest::update`, `Digest::finalize_reset`,
the second by `Digest::update`, `Digest::finalize`; two 16-byte digests. The stack budget is the
extractor's estimate, read from the same extraction as the program bytes; it includes 128 bytes of
slack (the target disables the red zone).
-/
def digestSlicesReset : Routine :=
  ⟨Extracted.md5DigestSlicesResetAddress,
    Extracted.md5DigestSlicesResetStackBytes.get (by decide), 32⟩

/--
`md5_finalize_into_reset_slices`: the first message by `Digest::update`,
`Digest::finalize_into_reset`, the second by `Digest::update`, `Digest::finalize`; two 16-byte
digests. The compiler emitted one function for this symbol and
`md5_fixed_finalize_into_reset_slices`, so both have the same address. The stack budget is the
extractor's estimate, read from the same extraction as the program bytes; it includes 128 bytes of
slack (the target disables the red zone).
-/
def finalizeIntoResetSlices : Routine :=
  ⟨Extracted.md5FinalizeIntoResetSlicesAddress,
    Extracted.md5FinalizeIntoResetSlicesStackBytes.get (by decide), 32⟩

/--
`md5_fixed_finalize_into_reset_slices`: the first message by `Update::update`,
`FixedOutputReset::finalize_into_reset`, the second by `Update::update`, `Digest::finalize`; two
16-byte digests. The compiler emitted one function for this symbol and
`md5_finalize_into_reset_slices`, so both have the same address. The stack budget is the
extractor's estimate, read from the same extraction as the program bytes; it includes 128 bytes of
slack (the target disables the red zone).
-/
def fixedFinalizeIntoResetSlices : Routine :=
  ⟨Extracted.md5FixedFinalizeIntoResetSlicesAddress,
    Extracted.md5FixedFinalizeIntoResetSlicesStackBytes.get (by decide), 32⟩

/--
`md5_finalize_fixed_reset_slices`: the first message by `Update::update`,
`FixedOutputReset::finalize_fixed_reset`, the second by `Update::update`, `Digest::finalize`;
two 16-byte digests. The compiler emitted one function for this symbol and
`md5_digest_slices_reset`, so both have the same address. The stack budget is the extractor's
estimate, read from the same extraction as the program bytes; it includes 128 bytes of slack (the
target disables the red zone).
-/
def finalizeFixedResetSlices : Routine :=
  ⟨Extracted.md5FinalizeFixedResetSlicesAddress,
    Extracted.md5FinalizeFixedResetSlicesStackBytes.get (by decide), 32⟩

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V R8 argument -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .r8 routine.outputBytes

/--
Validity conditions for a System V call to `routine` with input slices `inputs`, of which the first
`first` form the first message, all of them if `first` exceeds their number; the slice tables,
`first`, and the output buffer are supplied through RDI, RSI, RDX, RCX, and R8, with the conditions
listed on `Digest.ValidCall`. The output and the stack are disjoint from each other, from the tables
and from the slices. Rust's aliasing rules and the code both need the output apart from the tables
and the slices: the wrapper makes the output a mutable reference before it reads the first slice,
while the tables are borrowed, and writes the first digest while slices of the second message are
still to be read.
-/
structure ValidCall (routine : Routine) (bindings : Machine.Bindings) (s : Machine.RamState)
    (inputs : Array Slices.Input) (first : Nat) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  firstCountArgumentMatchesFirst : (s.regValue .rcx).toNat = first
  inputsInMemory : Slices.ValidInputs s inputs
  outputInMemory : ValidWritable s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  separation :
    MemorySeparation #v[outputRegion routine s, Stack.region s routine.minStackBytes]
      (Slices.readRegions s inputs)
  returnAddress : ValidReturnAddress bindings s

/-- Reads the output from final memory at the initial output pointer -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readRegion final (outputRegion routine initial)

end TwoMessages

namespace ResetThenDigest

/--
`md5_reset_slices`: the first message by `Digest::update`, then `Digest::reset`; the second by
`Digest::update`, `Digest::finalize`; one 16-byte digest. The compiler emitted one function for
`md5_reset_slices` and `md5_update_reset_slices`, so both have the same address. The stack budget
is the extractor's estimate, read from the same extraction as the program bytes; it includes 128
bytes of slack (the target disables the red zone).
-/
def resetSlices : Routine :=
  ⟨Extracted.md5ResetSlicesAddress, Extracted.md5ResetSlicesStackBytes.get (by decide), 16⟩

/--
`md5_update_reset_slices`: the first message by `Update::update`, then `Reset::reset`; the second
by `Update::update`, `Digest::finalize`; one 16-byte digest. The compiler emitted one function for
`md5_reset_slices` and `md5_update_reset_slices`, so both have the same address. The stack budget
is the extractor's estimate, read from the same extraction as the program bytes; it includes 128
bytes of slack (the target disables the red zone).
-/
def updateResetSlices : Routine :=
  ⟨Extracted.md5UpdateResetSlicesAddress,
    Extracted.md5UpdateResetSlicesStackBytes.get (by decide), 16⟩

/--
Digest output buffer of `routine.outputBytes` bytes, 16 for each routine here, supplied through
the System V R8 argument
-/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .r8 routine.outputBytes

/--
Validity conditions for a System V call to `routine` with input slices `inputs`, of which the first
`first` form the first message, all of them if `first` exceeds their number; the slice tables,
`first`, and the output buffer are supplied through RDI, RSI, RDX, RCX, and R8, with the conditions
listed on `Digest.ValidCall`. The stack is disjoint from the tables and the slices, which the call
reads while it writes its frames, and from the output, which it would otherwise overwrite. The
output may overlap the tables and the slices: the wrapper writes it through a raw pointer,
`*output = …`, only after the last slice is read and the slice iterator is dropped, so neither
Rust's aliasing rules nor any instruction needs them apart.
-/
structure ValidCall (routine : Routine) (bindings : Machine.Bindings) (s : Machine.RamState)
    (inputs : Array Slices.Input) (first : Nat) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = routine.entryAddress
  firstCountArgumentMatchesFirst : (s.regValue .rcx).toNat = first
  inputsInMemory : Slices.ValidInputs s inputs
  outputInMemory : ValidWritable s (outputRegion routine s)
  stackAvailable : Stack.Valid s routine.minStackBytes
  stackSeparation :
    MemorySeparation #v[Stack.region s routine.minStackBytes] (Slices.readRegions s inputs)
  outputSeparation :
    MemorySeparation #v[outputRegion routine s, Stack.region s routine.minStackBytes] []
  returnAddress : ValidReturnAddress bindings s

/-- Reads the digest from final memory at the initial output pointer -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readRegion final (outputRegion routine initial)

end ResetThenDigest

namespace Compress

/--
Stack budget, in bytes below entry RSP, for `md5_compress`. `ValidCall` requires the caller to
provide at least this much, and a caller may provide more. The budget is the extractor's estimate,
read from the same extraction as the program bytes; it includes 128 bytes of slack (the target
disables the red zone).
-/
def minStackBytes : Nat := Extracted.md5CompressStackBytes.get (by decide)

/-- Block bytes supplied through the System V RSI argument -/
def inputRegion (s : Machine.RamState) (blocks : ByteArray) : MemoryRegion :=
  registerRegion s .rsi blocks.size

/-- 16-byte MD buffer, read and then overwritten, supplied through the System V RDI argument -/
def outputRegion (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdi 16

/-- Validity conditions on the blocks in memory, at a nonzero address even when empty -/
def ValidInput (s : Machine.RamState) (blocks : ByteArray) : Prop :=
  let region := inputRegion s blocks
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external blocks

/--
Validity conditions on the MD buffer in memory: its words A to D, each low-order byte first, at a
nonzero address below 4 GiB, including the unaligned addresses that the Rust type excludes
-/
def ValidOutput (s : Machine.RamState) (buffer : MD5.Buffer) : Prop :=
  let region := outputRegion s
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external ⟨buffer.toBytes.toArray⟩

/--
Validity conditions for a System V call to `md5_compress` with MD buffer `buffer` and the bytes
`blocks` of whole 64-byte blocks; the buffer, the blocks, and the block count are supplied through
RDI, RSI, and RDX, with the conditions listed on `Digest.ValidCall`. The MD buffer and the stack are
disjoint from each other and from the blocks: the wrapper passes the buffer to `compress` as a
mutable reference while the blocks slice is borrowed.
-/
structure ValidCall (bindings : Machine.Bindings) (s : Machine.RamState)
    (buffer : MD5.Buffer) (blocks : ByteArray) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  atEntryPoint : s.RIP = Extracted.md5CompressAddress
  blockCountArgumentMatchesBlocks : 64 * (s.regValue .rdx).toNat = blocks.size
  inputInMemory : ValidInput s blocks
  outputInMemory : ValidOutput s buffer
  stackAvailable : Stack.Valid s minStackBytes
  separation :
    MemorySeparation #v[outputRegion s, Stack.region s minStackBytes] [inputRegion s blocks]
  returnAddress : ValidReturnAddress bindings s

/-- Reads the MD buffer from final memory at the initial buffer pointer -/
def readOutput (initial final : Machine.RamState) : Except Machine.Fault (Vector UInt8 16) :=
  readRegion final (outputRegion initial)

end Compress

end Md5.Spec.Program
