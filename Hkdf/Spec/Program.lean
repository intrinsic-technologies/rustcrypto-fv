import Prelude
import Hkdf.Spec.RFC5869
import Hkdf.Spec.Program.Extracted.Image

/-!
# Call semantics of the extracted entry points

`Hkdf/program/src/lib.rs` wraps `hkdf` 0.13.0 in System V entry points. The theorems use two:
`hkdf_sha256_extract`, a `Routine` (`hkdfSha256Extract`), and `hkdf_sha256_new_expand`, an entry
address and a stack budget `def` (`hkdfSha256NewExpandMinStackBytes`), which returns a status in EAX
(`invalidLengthStatus` for its one error). Every stack budget is the extraction's estimate; for
`new_expand`, which calls `expand_multi_info`, it follows a path that cannot run, past
`core::result::unwrap_failed` into the next function in `.text`.

Each call's predicate states what it needs: `ValidExtractCall` for `extract` and
`ValidDeriveKeyCall` for `new_expand`. `readOutput` reads an output region back from final memory in
address order.

The arguments of `hkdf_sha256_extract` and `hkdf_sha256_new_expand`, the machine assumptions and the
build are in `Hkdf/README.md`.
-/

namespace Hkdf.Spec.Program

open Prelude X86

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop := RFLAGS.DirectionFlagClear s.RFLAGS

/-- Physical RAM contains every extracted code and read-only data byte of the program -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- The address belongs to an extracted code or read-only data section of the program -/
def InProgram (address : BitVec 64) : Prop := ∃ byte, (address, byte) ∈ Extracted.programImage

/--
The page-table frames `[0x1000, 0x3000)` holding the PML4 and PDPT entries that
`Prelude.IdentityMappedMemory` requires
-/
def pageTables : MemoryRegion := ⟨0x1000, 0x2000⟩

/--
An entry point that takes a variable number of input slices through pointer and length tables and
returns no status: an `extract` entry point, such as `hkdf_sha256_extract`. The other entry points
return a status and write a caller-chosen number of bytes, so they are not `Routine`s; each has its
own entry address and stack budget.
-/
structure Routine where
  /-- The link-time address of the entry point -/
  entryAddress : BitVec 64
  /-- Stack budget in bytes below entry RSP; a caller may provide more -/
  minStackBytes : Nat
  /-- Size of the output, the PRK, in bytes -/
  outputBytes : Nat

/--
`hkdf_sha256_extract`, over `HkdfExtract<Sha256>`. Its stack budget is the extraction's estimate.
The PRK has 32 bytes, SHA-256's `HashLen`.
-/
def hkdfSha256Extract : Routine where
  entryAddress := Extracted.hkdfSha256ExtractAddress
  minStackBytes := Extracted.hkdfSha256ExtractStackBytes.get (by decide)
  outputBytes := 32

/--
`simple_hkdf_sha256_extract`, over `SimpleHkdfExtract<Sha256>`. Its stack budget is the extraction's
estimate. The PRK has 32 bytes, SHA-256's `HashLen`.
-/
def simpleHkdfSha256Extract : Routine where
  entryAddress := Extracted.simpleHkdfSha256ExtractAddress
  minStackBytes := Extracted.simpleHkdfSha256ExtractStackBytes.get (by decide)
  outputBytes := 32

/-- Stack budget of `hkdf_sha256_new_expand`, in bytes below entry RSP -/
def hkdfSha256NewExpandMinStackBytes : Nat :=
  Extracted.hkdfSha256NewExpandStackBytes.get (by decide)

/-- The status `expand` returns in EAX for `InvalidLength`, the error of `expand_multi_info` -/
def invalidLengthStatus : BitVec 32 := 2

/-- One input slice: its address, and the bytes there -/
structure Input where
  /-- Address of the slice's first byte -/
  address : BitVec 64
  /-- The slice's bytes in address order -/
  bytes : ByteArray

/-- Memory region of the slice's bytes -/
def Input.region (input : Input) : MemoryRegion := ⟨input.address.toNat, input.bytes.size⟩

/-- The bytes of the slices, concatenated in order -/
def concatenation (inputs : Array Input) : ByteArray :=
  inputs.foldl (fun bytes input => bytes ++ input.bytes) ByteArray.empty

/-- The table of `count` 8-byte slice addresses of `extract`, supplied through RDI -/
def pointerTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdi (8 * count)

/-- The table of `count` 8-byte slice lengths of `extract`, supplied through RDX -/
def lengthTable (s : Machine.RamState) (count : Nat) : MemoryRegion :=
  registerRegion s .rdx (8 * count)

/-- The 8 bytes of a table's word `i`, at `table.start + 8 * i` -/
def tableEntry (table : MemoryRegion) (i : Nat) : MemoryRegion := ⟨table.start + 8 * i, 8⟩

/--
Validity conditions on a table in memory: it ends below 4 GiB. No nonzero start is required: the
extracted code tests no table address for null. A valid call requires this only of a table with at
least one entry, since the code reads no table when the count is 0.
-/
def ValidTable (table : MemoryRegion) : Prop := table.Bounded

instance (table : MemoryRegion) : Decidable (ValidTable table) :=
  inferInstanceAs (Decidable (table.start + table.size < userAddressLimit))

/--
The salt of `derive_key` and `new_expand`, supplied through RDI
-/
def inputRegion (s : Machine.RamState) (bytes : ByteArray) : MemoryRegion :=
  registerRegion s .rdi bytes.size

/--
The salt of `extract`, supplied through the System V RCX argument
-/
def extractSaltRegion (s : Machine.RamState) (salt : ByteArray) : MemoryRegion :=
  registerRegion s .rcx salt.size

/--
The secret of `derive_key`, or the IKM of `new_expand`, supplied through the System V RDX
argument
-/
def secretRegion (s : Machine.RamState) (secret : ByteArray) : MemoryRegion :=
  registerRegion s .rdx secret.size

/--
The info of `derive_key` and `new_expand`, supplied through the System V R8 argument
-/
def infoRegion (s : Machine.RamState) (info : ByteArray) : MemoryRegion :=
  registerRegion s .r8 info.size

/--
The eight bytes of stack argument `index`, counted from 1: under System V, on entry, the seventh
and later integer arguments are at RSP + 8, RSP + 16 and so on, above the return slot
-/
def stackArgumentSlot (s : Machine.RamState) (index : Nat) : MemoryRegion :=
  ⟨(s.regValue .rsp).toNat + 8 * index, 8⟩

/--
The little-endian word in stack argument `index`. It is 0 when the slot is not in physical memory,
which a valid call excludes (`ValidStackArguments`).
-/
def stackArgument (s : Machine.RamState) (index : Nat) : BitVec 64 :=
  match Machine.loadBytes s.external (BitVec.ofNat 64 (stackArgumentSlot s index).start) 8 with
  | .ok value => value
  | .error _ => 0

/-- The PRK buffer of an `extract` routine, `routine.outputBytes` bytes supplied through R9 -/
def outputRegion (s : Machine.RamState) (routine : Routine) : MemoryRegion :=
  registerRegion s .r9 routine.outputBytes

/--
The `out` buffer of `derive_key`, or the `okm` buffer of `new_expand`, `size` bytes at the address
in stack argument 1
-/
def deriveKeyOutputRegion (s : Machine.RamState) (size : Nat) : MemoryRegion :=
  ⟨(stackArgument s 1).toNat, size⟩

/-- Validity conditions on bytes a call reads, in memory -/
def ValidInput (memory : Machine.Ram) (region : MemoryRegion) (bytes : ByteArray) : Prop :=
  region.Bounded ∧
  region.HasBytes memory bytes

/-- Validity conditions on an output buffer in memory -/
def ValidOutput (memory : Machine.Ram) (region : MemoryRegion) : Prop :=
  region.Bounded ∧
  region.Allocated memory

/--
Validity conditions on stack arguments 1 to `count` in memory: 2 for `derive_key` and
`new_expand`
-/
def ValidStackArguments (s : Machine.RamState) (count : Nat) : Prop :=
  ∀ index ∈ List.range' 1 count,
    (stackArgumentSlot s index).Bounded ∧
    (stackArgumentSlot s index).Allocated s.external

/--
The writable regions are pairwise disjoint, and each avoids every region in `reads`, the extracted
program, and the page tables. The regions a call only reads may overlap one another.
-/
def MemorySeparation {n : Nat} (writable : Vector MemoryRegion n) (reads : List MemoryRegion) :
    Prop :=
  MemoryRegion.PairwiseDisjoint writable ∧
  ∀ region ∈ writable,
    (∀ read ∈ reads, read.Disjoint region) ∧
    region.Avoids (fun address => InProgram address ∨ pageTables.Contains address.toNat)

/--
The return address in the slot at RSP is below the user address limit and outside the program
image
-/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
Validity conditions for a System V call to the `extract` routine `routine`, with salt `salt` and
IKM slices `ikm`:
- inputs: the slice count in RSI, as a 64-bit word; when it is not 0, at RDI a table of that many
  8-byte little-endian slice addresses and at RDX one of their lengths (`ValidTable`), each slice's
  bytes at its address; with no slices the code reads neither table. RCX null exactly when `salt`
  is `none`, and otherwise the salt's bytes at RCX and its length in R8.
- output: the `routine.outputBytes`-byte PRK buffer at R9, in RAM
- stack (`Stack.Valid`): the `routine.minStackBytes` bytes below RSP and the 8-byte return slot in
  RAM; RSP is 8 more than a multiple of 16, and at least `routine.minStackBytes`
- low 4 GiB: the tables when there is a slice, the slices, the salt, the PRK buffer and the stack
  region each end strictly below `userAddressLimit`, 2^32
- return address: below 2^32, outside the program image
- program: loaded at its link-time addresses, RIP at `routine.entryAddress`, the direction flag
  clear
- separation: the PRK buffer and the stack region are disjoint and outside the program and the page
  tables; the stack region avoids the tables, the slices and the salt
- overlap: the PRK buffer may overlap the tables, the slices and the salt, since the code writes it
  only after reading them; those may overlap one another
-/
structure ValidExtractCall (routine : Routine) (s : Machine.RamState)
    (salt : Option ByteArray) (ikm : Array Input) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  countArgumentMatchesInputs : (s.regValue .rsi).toNat = ikm.size
  saltPointerArgumentIsNullIffNoSalt : s.regValue .rcx = 0 ↔ salt = none
  saltLengthArgumentMatchesSalt : ∀ bytes ∈ salt, (s.regValue .r8).toNat = bytes.size
  pointerTableValid : 0 < ikm.size → ValidTable (pointerTable s ikm.size)
  lengthTableValid : 0 < ikm.size → ValidTable (lengthTable s ikm.size)
  ikmInMemory :
    ∀ i : Fin ikm.size,
      (tableEntry (pointerTable s ikm.size) i).Word64At s.external ikm[i].address ∧
      (tableEntry (lengthTable s ikm.size) i).Word64At s.external
        (BitVec.ofNat 64 ikm[i].bytes.size) ∧
      ValidInput s.external ikm[i].region ikm[i].bytes
  saltInMemory : ∀ bytes ∈ salt, ValidInput s.external (extractSaltRegion s bytes) bytes
  outputInMemory : ValidOutput s.external (outputRegion s routine)
  stack : Stack.Valid s routine.minStackBytes
  stackSeparation :
    MemorySeparation #v[Stack.region s routine.minStackBytes]
      (pointerTable s ikm.size :: lengthTable s ikm.size :: (ikm.map Input.region).toList ++
        salt.toList.map (extractSaltRegion s))
  outputSeparation :
    MemorySeparation #v[outputRegion s routine, Stack.region s routine.minStackBytes] []
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to `hkdf_sha256_derive_key` or
`simple_hkdf_sha256_derive_key` at `entryAddress`, with a stack budget of `minStackBytes`, salt
`salt`, secret `secret`, info `info`, and an output of `okmLength` bytes, and equally for a call to
`hkdf_sha256_new_expand` or `simple_hkdf_sha256_new_expand`, whose IKM is `secret`:
- inputs: RDI null exactly when `salt` is `none`, and otherwise the salt's bytes at RDI and its
  length in RSI; the secret's bytes at RDX and its length in RCX; the info's length in R9, and when
  `okmLength` is 1 to 8160 (`255 * HashLen` for SHA-256), the info's bytes at R8
- output: its address and its length, as 64-bit words, in stack arguments 1 and 2 (RSP + 8 and
  RSP + 16), both slots in RAM; when `okmLength` is 1 to 8160, a buffer of that length at that
  address, in RAM. Otherwise the code reads neither the info nor the output buffer.
- stack (`Stack.Valid`): the `minStackBytes` bytes below RSP and the 8-byte return slot in RAM; RSP
  is 8 more than a multiple of 16, and at least `minStackBytes`
- low 4 GiB: the salt, the secret, the two stack-argument slots, the stack region, and the info and
  the output buffer when required, each end strictly below `userAddressLimit`, 2^32
- return address: below 2^32, outside the program image
- program: loaded at its link-time addresses, RIP at `entryAddress`, the direction flag clear
- separation: the stack region avoids the salt and the secret and is outside the program and the
  page tables; when the output is written, the output buffer and the stack region are disjoint,
  avoid the info, and are outside the program and the page tables
- overlap: the output buffer may overlap the salt and the secret, which the code reads only before
  writing any output, but not the info; the salt, the secret and the info may overlap one another;
  each of the four may lie over the two stack-argument slots, which the code reads before writing
  any output and never writes
-/
structure ValidDeriveKeyCall (entryAddress : BitVec 64) (minStackBytes : Nat)
    (s : Machine.RamState) (salt : Option ByteArray) (secret info : ByteArray) (okmLength : Nat) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = entryAddress
  saltPointerArgumentIsNullIffNoSalt : s.regValue .rdi = 0 ↔ salt = none
  saltLengthArgumentMatchesSalt : ∀ bytes ∈ salt, (s.regValue .rsi).toNat = bytes.size
  secretLengthArgumentMatchesSecret : (s.regValue .rcx).toNat = secret.size
  infoLengthArgumentMatchesInfo : (s.regValue .r9).toNat = info.size
  outputLengthArgumentMatchesLength : (stackArgument s 2).toNat = okmLength
  stackArgumentsInMemory : ValidStackArguments s 2
  saltInMemory : ∀ bytes ∈ salt, ValidInput s.external (inputRegion s bytes) bytes
  secretInMemory : ValidInput s.external (secretRegion s secret) secret
  infoInMemoryIfWritten :
    0 < okmLength → okmLength ≤ 8160 → ValidInput s.external (infoRegion s info) info
  outputInMemoryIfWritten :
    0 < okmLength → okmLength ≤ 8160 →
      ValidOutput s.external (deriveKeyOutputRegion s okmLength)
  stack : Stack.Valid s minStackBytes
  stackSeparation :
    MemorySeparation #v[Stack.region s minStackBytes]
      (secretRegion s secret :: salt.toList.map (inputRegion s))
  separationIfWritten :
    0 < okmLength → okmLength ≤ 8160 →
      MemorySeparation #v[deriveKeyOutputRegion s okmLength, Stack.region s minStackBytes]
        [infoRegion s info]
  returnAddress : ValidReturnAddress s

/--
Reads the bytes of `output` from `memory` in address order. Returns an unmapped-memory fault at
the first missing byte.
-/
def readOutput (output : MemoryRegion) (memory : Machine.Ram) : Except Machine.Fault ByteArray :=
  ByteArray.mk <$> (Array.range output.size).mapM fun i =>
    let address := BitVec.ofNat 64 (output.start + i)
    match memory[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)

/--
The System V callee-saved general-purpose registers other than RSP, namely RBX, RBP and R12–R15,
retain their entry values. RSP is fixed by the return boundary of `Prelude.UniqueExecution`; the
x87 control word and the MXCSR control bits, also callee-saved, are not covered.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

end Hkdf.Spec.Program
