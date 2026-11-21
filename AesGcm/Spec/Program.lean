import AesGcm.Spec.GCM
import AesGcm.Spec.Program.Extracted.Image
import Prelude.Memory
import Prelude.Execution
import Prelude.Invariant

/-!
# Calls to the extracted `aes-gcm` entry points

The machine contract of the four System V x86-64 C-ABI wrappers in `AesGcm/program/src/lib.rs` that
the theorems use: `*_encrypt_in_place` and `*_decrypt_in_place`, for `Aes128Gcm` and for
`Aes256Gcm`. Every wrapper returns a status in EAX: 0 for `Ok`, 1 for `Err`. Each takes the 16- or
32-byte key at RDI, the 12-byte nonce at RSI, and the associated data at RDX with its length in RCX,
then one buffer at R8 that is read and overwritten, with the length of its contents in R9
(`InPlace`). `*_encrypt_in_place` also takes the buffer's capacity, the bytes it may grow to, as the
first stack argument.

What a call needs is `InPlace.ValidCall` or, for `*_encrypt_in_place`, `InPlace.ValidCapacityCall`;
`InPlace.readOutput` reads the output back from final memory at the initial pointer. The wrappers'
ABI and the build are in `AesGcm/README.md`.
-/

namespace AesGcm.Spec.Program

open Prelude X86

/-- Physical RAM contains every extracted byte -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- `address` is contained by an extracted section -/
def InProgram (address : BitVec 64) : Prop := ∃ byte, (address, byte) ∈ Extracted.programImage

/-- The page-table frames at 0x1000 and 0x2000 that `IdentityMappedMemory` requires -/
def pageTables : MemoryRegion := ⟨0x1000, 0x2000⟩

/-- The direction flag is clear, so string instructions advance their pointers. -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  Prelude.RFLAGS.DirectionFlagClear s.RFLAGS

/-- An entry point: its link-time address and its stack budget in bytes below entry RSP -/
structure Routine where
  entryAddress : BitVec 64
  minStackBytes : Nat

/-- `aes128gcm_encrypt_in_place`, with the extraction's stack estimate (2976 bytes) -/
def aes128gcmEncryptInPlace : Routine :=
  ⟨Extracted.aes128gcmEncryptInPlaceAddress,
    Extracted.aes128gcmEncryptInPlaceStackBytes.get (by decide)⟩

/-- `aes128gcm_decrypt_in_place`, with the extraction's stack estimate (2976 bytes) -/
def aes128gcmDecryptInPlace : Routine :=
  ⟨Extracted.aes128gcmDecryptInPlaceAddress,
    Extracted.aes128gcmDecryptInPlaceStackBytes.get (by decide)⟩

/-- `aes256gcm_encrypt_in_place`, with the extraction's stack estimate (3632 bytes) -/
def aes256gcmEncryptInPlace : Routine :=
  ⟨Extracted.aes256gcmEncryptInPlaceAddress,
    Extracted.aes256gcmEncryptInPlaceStackBytes.get (by decide)⟩

/-- `aes256gcm_decrypt_in_place`, with the extraction's stack estimate (3632 bytes) -/
def aes256gcmDecryptInPlace : Routine :=
  ⟨Extracted.aes256gcmDecryptInPlaceAddress,
    Extracted.aes256gcmDecryptInPlaceStackBytes.get (by decide)⟩

/-- Key bytes supplied through the System V RDI argument -/
def keyRegion (s : Machine.RamState) (size : Nat) : MemoryRegion := registerRegion s .rdi size

/-- Nonce bytes supplied through the System V RSI argument -/
def nonceRegion (s : Machine.RamState) : MemoryRegion := registerRegion s .rsi 12

/-- Associated data supplied through the System V RDX argument -/
def associatedDataRegion (s : Machine.RamState) (associatedData : ByteArray) : MemoryRegion :=
  registerRegion s .rdx associatedData.size

/-- The first stack argument, the 8 bytes above the return address at RSP -/
def stackArgumentRegion (s : Machine.RamState) : MemoryRegion :=
  ⟨(s.regValue .rsp).toNat + 8, 8⟩

/--
Validity conditions on a read-only input in memory: a non-null address, ending below
`userAddressLimit`, holding its bytes
-/
def ValidInput (region : MemoryRegion) (memory : Machine.Ram) (bytes : ByteArray) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes memory bytes

/--
Validity conditions on a written region in memory: a non-null address, ending below
`userAddressLimit`, and RAM to write
-/
def ValidOutput (region : MemoryRegion) (memory : Machine.Ram) : Prop :=
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated memory

/--
The first stack argument is below `userAddressLimit` and holds `value` as a little-endian 8-byte
word
-/
def ValidStackArgument (s : Machine.RamState) (value : Nat) : Prop :=
  let region := stackArgumentRegion s
  region.Bounded ∧
  region.Word64At s.external (BitVec.ofNat 64 value)

/-- The return address in the slot at RSP is below the user address limit, outside the program -/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
The stack region, with `returnBytes` above RSP, is disjoint from every region the call reads or
writes; the written regions are disjoint from every read region and from one another; the stack
and the written regions avoid the program and the page tables. Read regions may overlap one
another.
-/
def MemorySeparation (s : Machine.RamState) (readRegions writtenRegions : List MemoryRegion)
    (stackBytes returnBytes : Nat) : Prop :=
  let stack := Stack.region s stackBytes returnBytes
  (∀ region ∈ readRegions ++ writtenRegions, region.Disjoint stack) ∧
  (∀ written ∈ writtenRegions, ∀ read ∈ readRegions, written.Disjoint read) ∧
  writtenRegions.Pairwise MemoryRegion.Disjoint ∧
  ∀ region ∈ stack :: writtenRegions,
    region.Avoids (fun address => InProgram address ∨ pageTables.Contains address.toNat)

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

namespace InPlace

/-- The buffer supplied through the System V R8 argument, read and overwritten -/
def outputRegion (s : Machine.RamState) (size : Nat) : MemoryRegion := registerRegion s .r8 size

/--
Reads `size` bytes from final memory at the initial buffer pointer. Returns `.ok` on success or
`.error (.unmappedMemory address)` for the first missing byte.
-/
def readOutput (initial final : Machine.RamState) (size : Nat) :
    Except Machine.Fault ByteArray :=
  let region := outputRegion initial size
  (List.range region.size).foldlM (fun bytes i =>
    let address := BitVec.ofNat 64 (region.start + i)
    match final.external[address]? with
    | some byte => .ok (bytes.push byte)
    | none => .error (.unmappedMemory address)) ByteArray.empty

/--
Validity conditions on the buffer in memory: a non-null address and `size` bytes of RAM, whose
first bytes hold `contents`
-/
def ValidBuffer (s : Machine.RamState) (contents : ByteArray) (size : Nat) : Prop :=
  let region := outputRegion s size
  ValidOutput region s.external ∧
  contents.size ≤ size ∧
  (outputRegion s contents.size).HasBytes s.external contents

/--
Validity conditions for a System V call of the `InPlace` shape to `routine` with the key, the
nonce, the associated data, and a buffer of `bufferSize` bytes that begins with `contents`, whose
length argument in R9 is `length`. This is what a call needs:
- the program is loaded (`ProgramLoaded`), RIP is at the routine's entry, and the direction flag
  is clear;
- RCX holds the associated data's length and R9 holds `length`;
- the key (RDI), the nonce (RSI) and the associated data (RDX) are at nonzero addresses, even when
  empty, end below `userAddressLimit` (2³²) and hold their bytes (`ValidInput`);
- the buffer at R8 is `bufferSize` bytes of RAM at a nonzero address, ending below
  `userAddressLimit`, whose first bytes hold `contents` (`ValidBuffer`);
- `Stack.Valid`: the `routine.minStackBytes` bytes below RSP and the 8-byte return slot are RAM
  ending below `userAddressLimit`, RSP is at least `routine.minStackBytes`, and RSP is 8 more than a
  multiple of 16;
- `MemorySeparation`: the stack region is disjoint from the key, nonce, associated data and
  buffer; the buffer is disjoint from the key, nonce and associated data; the buffer and the stack
  region avoid the program and the page tables; the key, nonce and associated data may overlap one
  another;
- `ValidReturnAddress`: the return address at RSP is below `userAddressLimit`, outside the program.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (key : Vector UInt8 n)
    (nonce : Vector UInt8 12) (associatedData contents : ByteArray) (length bufferSize : Nat) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  associatedDataLengthArgumentMatchesData : (s.regValue .rcx).toNat = associatedData.size
  lengthArgumentMatchesBuffer : (s.regValue .r9).toNat = length
  keyInMemory : ValidInput (keyRegion s n) s.external ⟨key.toArray⟩
  nonceInMemory : ValidInput (nonceRegion s) s.external ⟨nonce.toArray⟩
  associatedDataInMemory : ValidInput (associatedDataRegion s associatedData) s.external
    associatedData
  outputInMemory : ValidBuffer s contents bufferSize
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation s
    [keyRegion s n, nonceRegion s, associatedDataRegion s associatedData]
    [outputRegion s bufferSize] routine.minStackBytes 8
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to `*_encrypt_in_place` with the key, the nonce, the
associated data, and a buffer of `capacity` bytes that begins with the `plaintext`: those of
`ValidCall` with `contents := plaintext`, `length := plaintext.size` and `bufferSize := capacity`,
and also `capacity` in the first stack argument, the 8 bytes at RSP + 8, which end below
`userAddressLimit` (`ValidStackArgument`); the stack region of `MemorySeparation` covers that
argument too. The plaintext lies within the buffer, so `plaintext.size ≤ capacity`, the wrapper's
documented contract (`len <= capacity`). `ValidOverCapacityCall` covers `len > capacity`.
-/
structure ValidCapacityCall (routine : Routine) (s : Machine.RamState) (key : Vector UInt8 n)
    (nonce : Vector UInt8 12) (associatedData plaintext : ByteArray) (capacity : Nat) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  associatedDataLengthArgumentMatchesData : (s.regValue .rcx).toNat = associatedData.size
  lengthArgumentMatchesBuffer : (s.regValue .r9).toNat = plaintext.size
  capacityArgumentOnStack : ValidStackArgument s capacity
  keyInMemory : ValidInput (keyRegion s n) s.external ⟨key.toArray⟩
  nonceInMemory : ValidInput (nonceRegion s) s.external ⟨nonce.toArray⟩
  associatedDataInMemory : ValidInput (associatedDataRegion s associatedData) s.external
    associatedData
  outputInMemory : ValidBuffer s plaintext capacity
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation s
    [keyRegion s n, nonceRegion s, associatedDataRegion s associatedData]
    [outputRegion s capacity] routine.minStackBytes 16
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call to `*_encrypt_in_place` whose length argument in R9 is
any value larger than the `capacity` in the first stack argument, up to 2⁶⁴ − 1. The wrapper's
doc asks for `len <= capacity`, but nothing in Rust restricts the value, so this call is defined:
`encrypt_in_place` encrypts `SliceBuffer::as_mut`, which is then empty, and `extend_from_slice`
fails because `len..len + 16` is not within the `capacity` bytes (or `len + 16` overflows), so
the call returns status 1 and writes nothing outside the stack region. The buffer is `capacity`
bytes of RAM, the slice the wrapper makes; no plaintext is read. The key, nonce, associated data
and buffer are supplied through RDI, RSI, RDX and R8. The stack region includes the stack argument.
No theorem states such a call.
-/
structure ValidOverCapacityCall (routine : Routine) (s : Machine.RamState) (key : Vector UInt8 n)
    (nonce : Vector UInt8 12) (associatedData : ByteArray) (capacity : Nat) :
    Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  associatedDataLengthArgumentMatchesData : (s.regValue .rcx).toNat = associatedData.size
  lengthArgumentExceedsCapacity : capacity < (s.regValue .r9).toNat
  capacityArgumentOnStack : ValidStackArgument s capacity
  keyInMemory : ValidInput (keyRegion s n) s.external ⟨key.toArray⟩
  nonceInMemory : ValidInput (nonceRegion s) s.external ⟨nonce.toArray⟩
  associatedDataInMemory : ValidInput (associatedDataRegion s associatedData) s.external
    associatedData
  outputInMemory : ValidOutput (outputRegion s capacity) s.external
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation s
    [keyRegion s n, nonceRegion s, associatedDataRegion s associatedData]
    [outputRegion s capacity] routine.minStackBytes 16
  returnAddress : ValidReturnAddress s

end InPlace

end AesGcm.Spec.Program
