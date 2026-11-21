import Prelude
import Sha2.Spec.Program.Extracted.Image
import Standards.NIST.SHA2

/-!
# `sha2` 0.11.1 call semantics

Each routine is a wrapper function in `Sha2/program/src/lib.rs`, compiled for x86-64-v1 with the
portable backend and extracted into `Sha2.Spec.Program.Extracted`. A `Routine` gives its entry
address, its stack budget, and the size of what it writes. Each argument shape has a section
below with its regions, separation, call predicate and readers, which read the output bytes from
final memory at the initial output pointer:

* a table, one output (`ValidCall`, `readOutput`): `<hasher>_digest_slices`;
* one slice (`OneShot.ValidCall`, `OneShot.readOutput`): `<hasher>_digest`;
* a table, two outputs (`TwoOutputs`): the `reset` and `finalize_into_reset` forms.

A table call passes a variable number of input slices as a table of addresses in RDI, their count
in RSI, and a table of lengths in RDX, then its other arguments in order. No call can fail, so no
routine returns a status. The wrappers' ABI, the conditions in short and the build are in
`Sha2/README.md`.
-/

namespace Sha2.Spec.Program

open Prelude X86 X86.UserProcess

/--
An extracted wrapper: its entry address, the stack it needs below entry RSP, and the number of
bytes in each buffer it writes.
-/
structure Routine where
  /-- Address of the routine's first instruction. -/
  entryAddress : BitVec 64
  /--
  Stack budget in bytes below entry RSP: the extraction's estimate, which includes 128 bytes of
  slack (the target disables the red zone). A valid call provides it; a caller may provide more.
  -/
  minStackBytes : Nat
  /-- Number of bytes the routine writes to each output buffer, or overwrites in place. -/
  outputBytes : Nat

/-- The wrapper `sha224_digest`, writing 28 bytes. -/
def sha224Digest : Routine where
  entryAddress := Extracted.sha224DigestAddress
  minStackBytes := Extracted.sha224DigestStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha224_digest_slices`, writing 28 bytes. -/
def sha224DigestSlices : Routine where
  entryAddress := Extracted.sha224DigestSlicesAddress
  minStackBytes := Extracted.sha224DigestSlicesStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha224_reset`, writing 28 bytes. -/
def sha224Reset : Routine where
  entryAddress := Extracted.sha224ResetAddress
  minStackBytes := Extracted.sha224ResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha224_finalize_into_reset`, writing 28 bytes. -/
def sha224FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha224FinalizeIntoResetAddress
  minStackBytes := Extracted.sha224FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha224_trait_finalize_into_reset`, writing 28 bytes. -/
def sha224TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha224TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha224TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha256_digest`, writing 32 bytes. -/
def sha256Digest : Routine where
  entryAddress := Extracted.sha256DigestAddress
  minStackBytes := Extracted.sha256DigestStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha256_digest_slices`, writing 32 bytes. -/
def sha256DigestSlices : Routine where
  entryAddress := Extracted.sha256DigestSlicesAddress
  minStackBytes := Extracted.sha256DigestSlicesStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha256_reset`, writing 32 bytes. -/
def sha256Reset : Routine where
  entryAddress := Extracted.sha256ResetAddress
  minStackBytes := Extracted.sha256ResetStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha256_finalize_into_reset`, writing 32 bytes. -/
def sha256FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha256FinalizeIntoResetAddress
  minStackBytes := Extracted.sha256FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha256_trait_finalize_into_reset`, writing 32 bytes. -/
def sha256TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha256TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha256TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha384_digest`, writing 48 bytes. -/
def sha384Digest : Routine where
  entryAddress := Extracted.sha384DigestAddress
  minStackBytes := Extracted.sha384DigestStackBytes.get (by decide)
  outputBytes := 48

/-- The wrapper `sha384_digest_slices`, writing 48 bytes. -/
def sha384DigestSlices : Routine where
  entryAddress := Extracted.sha384DigestSlicesAddress
  minStackBytes := Extracted.sha384DigestSlicesStackBytes.get (by decide)
  outputBytes := 48

/-- The wrapper `sha384_reset`, writing 48 bytes. -/
def sha384Reset : Routine where
  entryAddress := Extracted.sha384ResetAddress
  minStackBytes := Extracted.sha384ResetStackBytes.get (by decide)
  outputBytes := 48

/-- The wrapper `sha384_finalize_into_reset`, writing 48 bytes. -/
def sha384FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha384FinalizeIntoResetAddress
  minStackBytes := Extracted.sha384FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 48

/-- The wrapper `sha384_trait_finalize_into_reset`, writing 48 bytes. -/
def sha384TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha384TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha384TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 48

/-- The wrapper `sha512_digest`, writing 64 bytes. -/
def sha512Digest : Routine where
  entryAddress := Extracted.sha512DigestAddress
  minStackBytes := Extracted.sha512DigestStackBytes.get (by decide)
  outputBytes := 64

/-- The wrapper `sha512_digest_slices`, writing 64 bytes. -/
def sha512DigestSlices : Routine where
  entryAddress := Extracted.sha512DigestSlicesAddress
  minStackBytes := Extracted.sha512DigestSlicesStackBytes.get (by decide)
  outputBytes := 64

/-- The wrapper `sha512_reset`, writing 64 bytes. -/
def sha512Reset : Routine where
  entryAddress := Extracted.sha512ResetAddress
  minStackBytes := Extracted.sha512ResetStackBytes.get (by decide)
  outputBytes := 64

/-- The wrapper `sha512_finalize_into_reset`, writing 64 bytes. -/
def sha512FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512FinalizeIntoResetAddress
  minStackBytes := Extracted.sha512FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 64

/-- The wrapper `sha512_trait_finalize_into_reset`, writing 64 bytes. -/
def sha512TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha512TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 64

/-- The wrapper `sha512_224_digest`, writing 28 bytes. -/
def sha512_224Digest : Routine where
  entryAddress := Extracted.sha512_224DigestAddress
  minStackBytes := Extracted.sha512_224DigestStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha512_224_digest_slices`, writing 28 bytes. -/
def sha512_224DigestSlices : Routine where
  entryAddress := Extracted.sha512_224DigestSlicesAddress
  minStackBytes := Extracted.sha512_224DigestSlicesStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha512_224_reset`, writing 28 bytes. -/
def sha512_224Reset : Routine where
  entryAddress := Extracted.sha512_224ResetAddress
  minStackBytes := Extracted.sha512_224ResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha512_224_finalize_into_reset`, writing 28 bytes. -/
def sha512_224FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512_224FinalizeIntoResetAddress
  minStackBytes := Extracted.sha512_224FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha512_224_trait_finalize_into_reset`, writing 28 bytes. -/
def sha512_224TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512_224TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha512_224TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 28

/-- The wrapper `sha512_256_digest`, writing 32 bytes. -/
def sha512_256Digest : Routine where
  entryAddress := Extracted.sha512_256DigestAddress
  minStackBytes := Extracted.sha512_256DigestStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha512_256_digest_slices`, writing 32 bytes. -/
def sha512_256DigestSlices : Routine where
  entryAddress := Extracted.sha512_256DigestSlicesAddress
  minStackBytes := Extracted.sha512_256DigestSlicesStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha512_256_reset`, writing 32 bytes. -/
def sha512_256Reset : Routine where
  entryAddress := Extracted.sha512_256ResetAddress
  minStackBytes := Extracted.sha512_256ResetStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha512_256_finalize_into_reset`, writing 32 bytes. -/
def sha512_256FinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512_256FinalizeIntoResetAddress
  minStackBytes := Extracted.sha512_256FinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 32

/-- The wrapper `sha512_256_trait_finalize_into_reset`, writing 32 bytes. -/
def sha512_256TraitFinalizeIntoReset : Routine where
  entryAddress := Extracted.sha512_256TraitFinalizeIntoResetAddress
  minStackBytes := Extracted.sha512_256TraitFinalizeIntoResetStackBytes.get (by decide)
  outputBytes := 32

/-- One input slice of a table call: the address in its pointer-table entry, and the bytes there. -/
structure Input where
  /-- Address of the slice's first byte, the word in its pointer-table entry. -/
  address : BitVec 64
  /-- The slice's bytes in address order; their number is the word in its length-table entry. -/
  bytes : ByteArray

/-- Memory region of the slice's bytes. -/
def Input.region (input : Input) : MemoryRegion :=
  ⟨input.address.toNat, input.bytes.size⟩

/-- The message a table call hashes: the bytes of its input slices, concatenated in order. -/
def message (inputs : Array Input) : ByteArray :=
  inputs.foldl (fun message input => message ++ input.bytes) ByteArray.empty

/-- Physical RAM contains every extracted code and read-only data byte of the program. -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- The address belongs to an extracted code or read-only data section of the program. -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, (address, byte) ∈ Extracted.programImage

/--
The page-table frames `[0x1000, 0x3000)` holding the PML4 and PDPT entries that
`Prelude.IdentityMappedMemory` requires.
-/
def pageTables : MemoryRegion :=
  ⟨0x1000, 0x2000⟩

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  RFLAGS.DirectionFlagClear s.RFLAGS

/-- Table of `count` eight-byte slice addresses supplied through the System V RDI argument. -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- Table of `count` eight-byte slice lengths supplied through the System V RDX argument. -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The eight-byte entry `i` of a table, counting from zero at the table's start. -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion :=
  ⟨table.start + 8 * i, 8⟩

/-- Validity conditions on a table in memory: at a nonzero address, even when empty. -/
def ValidTable (table : MemoryRegion) : Prop :=
  table.start ≠ 0 ∧
  table.Bounded

/--
Validity conditions on input slice `i`: entry `i` of the pointer table holds its address, which is
nonzero even for an empty slice, entry `i` of the length table holds its length, and its bytes are
in memory at that address.
-/
def ValidInput (s : Machine.RamState) (inputs : Array Input) (i : Fin inputs.size) : Prop :=
  let input := inputs[i]
  input.address ≠ 0 ∧
  (tableEntry (pointerTable s inputs.size) i).Word64At s.external input.address ∧
  (tableEntry (lengthTable s inputs.size) i).Word64At s.external
    (BitVec.ofNat 64 input.bytes.size) ∧
  input.region.Bounded ∧
  input.region.HasBytes s.external input.bytes

/-- The regions a table call reads: the pointer table, the length table, and every slice. -/
def readRegions (s : Machine.RamState) (inputs : Array Input) : List MemoryRegion :=
  pointerTable s inputs.size :: lengthTable s inputs.size :: (inputs.map Input.region).toList

/--
The writable regions are pairwise disjoint, and each avoids every region the call only reads,
the extracted program, and the page tables. Regions the call only reads may overlap one another.
-/
def WritableRegionsSeparated (writable read : List MemoryRegion) : Prop :=
  writable.Pairwise MemoryRegion.Disjoint ∧
  ∀ region ∈ writable,
    (∀ other ∈ read, other.Disjoint region) ∧
    region.Avoids (fun address => InProgram address ∨ pageTables.Contains address.toNat)

/--
The return address in the slot at RSP is below the user address limit and outside the program
image.
-/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
Reads a region's bytes from final memory in address order. Returns an unmapped-memory fault at
the first missing byte.
-/
def readBytes (region : MemoryRegion) (final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 region.size) :=
  Vector.ofFnM fun j : Fin region.size =>
    let address := BitVec.ofNat 64 (region.start + j.val)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`; the x87 control word and the
MXCSR control bits, also callee-saved, are not covered.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

/-! ## A table, one output: `<hasher>_digest_slices` -/

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V RCX argument. -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rcx routine.outputBytes

/-- Validity conditions on the output buffer in memory: at a nonzero address. -/
def ValidOutput (routine : Routine) (s : Machine.RamState) : Prop :=
  let region := outputRegion routine s
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
The output buffer and the stack are disjoint, and each avoids the tables, the slices, the
program, and the page tables; the tables and slices may overlap one another.
-/
def MemorySeparation (routine : Routine) (s : Machine.RamState) (inputs : Array Input) : Prop :=
  WritableRegionsSeparated [outputRegion routine s, Stack.region s routine.minStackBytes]
    (readRegions s inputs)

/--
Validity conditions for a System V call `f(table, count, lengths, out)` to a table routine with
one output: RDI holds the pointer table, RSI the count, RDX the length table, RCX the output.
Each call starts from a new hasher. A valid call has:

* the direction flag clear, the program loaded at its link-time addresses, and RIP at the
  routine's entry;
* RSI equal to the number of slices; the pointer table at RDI and the length table at RDX, eight
  bytes per slice each, at nonzero addresses even when empty (`ValidTable`);
* for each slice `i`, entry `i` of the pointer table holding its address, which is nonzero even
  for an empty slice, entry `i` of the length table holding its length, both little-endian
  eight-byte words, and its bytes in memory at that address (`ValidInput`);
* `routine.outputBytes` bytes of RAM at RCX, at a nonzero address (`ValidOutput`);
* `routine.minStackBytes` bytes of RAM below RSP, with RSP 8 more than a multiple of 16
  (`Stack.Valid`);
* the tables, the slices, the output and the stack region each ending strictly below
  `userAddressLimit` (2^32);
* the output and the stack region disjoint, each avoiding the tables, the slices, the program and
  the page tables; the tables and slices may overlap one another (`MemorySeparation`);
* in the slot at RSP, a return address below `userAddressLimit` and outside the program image
  (`ValidReturnAddress`).

No region need be aligned. Stack contents may hold message bytes afterwards.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (inputs : Array Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  countArgumentMatchesInputs : (s.regValue .rsi).toNat = inputs.size
  pointerTableValid : ValidTable (pointerTable s inputs.size)
  lengthTableValid : ValidTable (lengthTable s inputs.size)
  inputsInMemory : ∀ i, ValidInput s inputs i
  outputInMemory : ValidOutput routine s
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation routine s inputs
  returnAddress : ValidReturnAddress s

/-- Reads the output bytes from final memory at the initial RCX, in address order. -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (outputRegion routine initial) final

namespace OneShot

/-! ## One slice: `<hasher>_digest(data, length, out)` -/

/-- The message bytes supplied through the System V RDI argument. -/
def inputRegion (s : Machine.RamState) (data : ByteArray) : MemoryRegion :=
  registerRegion s .rdi data.size

/-- Validity conditions on the message in memory: at a nonzero address, even when empty. -/
def ValidInput (s : Machine.RamState) (data : ByteArray) : Prop :=
  let region := inputRegion s data
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external data

/-- Output buffer of `routine.outputBytes` bytes supplied through the System V RDX argument. -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx routine.outputBytes

/-- Validity conditions on the output buffer in memory: at a nonzero address. -/
def ValidOutput (routine : Routine) (s : Machine.RamState) : Prop :=
  let region := outputRegion routine s
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
The output buffer and the stack are disjoint, and each avoids the message, the program, and the
page tables.
-/
def MemorySeparation (routine : Routine) (s : Machine.RamState) (data : ByteArray) : Prop :=
  WritableRegionsSeparated [outputRegion routine s, Stack.region s routine.minStackBytes]
    [inputRegion s data]

/--
Validity conditions for a System V call `f(data, length, out)`: RDI holds the message, RSI its
length, RDX the output. Each call starts from a new hasher. A valid call has:

* the direction flag clear, the program loaded at its link-time addresses, and RIP at the
  routine's entry;
* RSI equal to the message's length, and the message's bytes in memory at RDI, at a nonzero
  address even when empty (`ValidInput`);
* `routine.outputBytes` bytes of RAM at RDX, at a nonzero address (`ValidOutput`);
* `routine.minStackBytes` bytes of RAM below RSP, with RSP 8 more than a multiple of 16
  (`Stack.Valid`);
* the message, the output and the stack region each ending strictly below `userAddressLimit`
  (2^32);
* the output and the stack region disjoint, each avoiding the message, the program and the page
  tables (`MemorySeparation`);
* in the slot at RSP, a return address below `userAddressLimit` and outside the program image
  (`ValidReturnAddress`).

No region need be aligned. Stack contents may hold message bytes afterwards.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (data : ByteArray) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  lengthArgumentMatchesData : (s.regValue .rsi).toNat = data.size
  inputInMemory : ValidInput s data
  outputInMemory : ValidOutput routine s
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation routine s data
  returnAddress : ValidReturnAddress s

/-- Reads the output bytes from final memory at the initial RDX, in address order. -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (outputRegion routine initial) final

end OneShot

namespace TwoOutputs

/-! ## A table, two outputs: the four reset wrappers of each hasher -/

/-- First output buffer of `routine.outputBytes` bytes, through the System V RCX argument. -/
def outputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rcx routine.outputBytes

/-- Second output buffer of `routine.outputBytes` bytes, through the System V R8 argument. -/
def secondOutputRegion (routine : Routine) (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .r8 routine.outputBytes

/-- Validity conditions on the two output buffers in memory: each at a nonzero address. -/
def ValidOutput (routine : Routine) (s : Machine.RamState) : Prop :=
  ∀ region ∈ [outputRegion routine s, secondOutputRegion routine s],
    region.start ≠ 0 ∧ region.Bounded ∧ region.Allocated s.external

/--
The two output buffers and the stack are pairwise disjoint, and each avoids the tables, the
slices, the program, and the page tables; the tables and slices may overlap one another.
-/
def MemorySeparation (routine : Routine) (s : Machine.RamState) (inputs : Array Input) : Prop :=
  WritableRegionsSeparated
    [outputRegion routine s, secondOutputRegion routine s, Stack.region s routine.minStackBytes]
    (readRegions s inputs)

/--
Validity conditions for a System V call `f(table, count, lengths, out, second)`: RDI, RSI, and
RDX hold the table call's arguments, RCX and R8 the two outputs.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (inputs : Array Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  countArgumentMatchesInputs : (s.regValue .rsi).toNat = inputs.size
  pointerTableValid : ValidTable (pointerTable s inputs.size)
  lengthTableValid : ValidTable (lengthTable s inputs.size)
  inputsInMemory : ∀ i, Program.ValidInput s inputs i
  outputInMemory : ValidOutput routine s
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation routine s inputs
  returnAddress : ValidReturnAddress s

/-- Reads the first output from final memory at the initial RCX, in address order. -/
def readOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (outputRegion routine initial) final

/-- Reads the second output from final memory at the initial R8, in address order. -/
def readSecondOutput (routine : Routine) (initial final : Machine.RamState) :
    Except Machine.Fault (Vector UInt8 routine.outputBytes) :=
  readBytes (secondOutputRegion routine initial) final

end TwoOutputs

end Sha2.Spec.Program
