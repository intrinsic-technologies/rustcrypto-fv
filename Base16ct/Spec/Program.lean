import Prelude
import Base16ct.Spec.Program.Extracted.Image

/-!
# Call semantics

Each routine is a wrapper function in `Base16ct/program/src/lib.rs` that calls one `base16ct`
1.0.0 function. The System V arguments come in one order, each wrapper taking the ones it needs:
`src` (RDI) and `src_len` (RSI) the input, `out_len` (RDX) an 8-byte word that receives the
length of the result, `dst` (RCX) the output buffer, and `dst_len` (R8) its capacity. The 32-bit
status in EAX is 0 on success, `invalidLengthStatus` for `base16ct::Error::InvalidLength`, and
`invalidEncodingStatus` for `base16ct::Error::InvalidEncoding`. Two call shapes, each with its own
call predicate:

* `ValidCall`: `f(src, src_len, out_len, dst, dst_len) -> u32`, for `encode`, `encode_str` and
  `decode`, which write into a caller's buffer of any capacity;
* `ValidLengthCall`: `f(src, src_len, out_len)`, for `decoded_len` (status) and `encoded_len`
  (no status), which read no input byte but still require the input's memory.

`readOutput` reads the output bytes, and `readLengthOutput` the length word, from final memory at
the initial pointers. The machine environment (Theorem Hypotheses) and how to build the verified
binary are in `Base16ct/README.md`.
-/

namespace Base16ct.Spec.Program

open Prelude X86

/-- A wrapper routine: its entry address and the stack budget its calls require -/
structure Routine where
  /-- Address of the routine's first instruction -/
  entryAddress : BitVec 64
  /--
  Bytes below entry RSP that the call may use. The call predicates require them, with the return
  slot at RSP, to be allocated, and the theorems' frames allow them to change: both use
  `Stack.region s minStackBytes`, `[RSP - minStackBytes, RSP + 8)`.

  Every budget is the extraction's estimate, which includes 128 bytes of slack: the tool adds them
  for the System V red zone, which the `x86_64-unknown-none` target disables, so the compiled code
  never touches memory below its current RSP, and the 128 bytes lie below the deepest RSP a call
  reaches.
  -/
  minStackBytes : Nat

/-- `base16ct_lower_encode`, calling `base16ct::lower::encode` -/
def base16ctLowerEncode : Routine where
  entryAddress := Extracted.lower_encodeAddress
  minStackBytes := Extracted.lower_encodeStackBytes.get (by decide)

/-- `base16ct_upper_encode`, calling `base16ct::upper::encode` -/
def base16ctUpperEncode : Routine where
  entryAddress := Extracted.upper_encodeAddress
  minStackBytes := Extracted.upper_encodeStackBytes.get (by decide)

/-- `base16ct_lower_encode_str`, calling `base16ct::lower::encode_str` -/
def base16ctLowerEncodeStr : Routine where
  entryAddress := Extracted.lower_encode_strAddress
  minStackBytes := Extracted.lower_encode_strStackBytes.get (by decide)

/-- `base16ct_upper_encode_str`, calling `base16ct::upper::encode_str` -/
def base16ctUpperEncodeStr : Routine where
  entryAddress := Extracted.upper_encode_strAddress
  minStackBytes := Extracted.upper_encode_strStackBytes.get (by decide)

/-- `base16ct_lower_decode`, calling `base16ct::lower::decode` -/
def base16ctLowerDecode : Routine where
  entryAddress := Extracted.lower_decodeAddress
  minStackBytes := Extracted.lower_decodeStackBytes.get (by decide)

/-- `base16ct_upper_decode`, calling `base16ct::upper::decode` -/
def base16ctUpperDecode : Routine where
  entryAddress := Extracted.upper_decodeAddress
  minStackBytes := Extracted.upper_decodeStackBytes.get (by decide)

/-- `base16ct_mixed_decode`, calling `base16ct::mixed::decode` -/
def base16ctMixedDecode : Routine where
  entryAddress := Extracted.mixed_decodeAddress
  minStackBytes := Extracted.mixed_decodeStackBytes.get (by decide)

/-- `base16ct_decoded_len`, calling `base16ct::decoded_len` -/
def base16ctDecodedLen : Routine where
  entryAddress := Extracted.decoded_lenAddress
  minStackBytes := Extracted.decoded_lenStackBytes.get (by decide)

/-- `base16ct_encoded_len`, calling `base16ct::encoded_len` -/
def base16ctEncodedLen : Routine where
  entryAddress := Extracted.encoded_lenAddress
  minStackBytes := Extracted.encoded_lenStackBytes.get (by decide)

/-- Status for `base16ct::Error::InvalidLength` (`error_status` in the wrapper) -/
def invalidLengthStatus : BitVec 32 := 1

/-- Status for `base16ct::Error::InvalidEncoding` (`error_status` in the wrapper) -/
def invalidEncodingStatus : BitVec 32 := 2

/-- Physical RAM contains every extracted code and read-only data byte of the program -/
def ProgramLoaded (s : Machine.RamState) : Prop :=
  ∀ address byte, (address, byte) ∈ Extracted.programImage → s.external[address]? = some byte

/-- The address belongs to an extracted code or read-only data section of the program -/
def InProgram (address : BitVec 64) : Prop :=
  ∃ byte, (address, byte) ∈ Extracted.programImage

/--
The page-table frames `[0x1000, 0x3000)` holding the entries that `Prelude.IdentityMappedMemory`
requires
-/
def pageTables : MemoryRegion :=
  ⟨0x1000, 0x2000⟩

/-- The direction flag is clear, as the System V ABI requires on function entry and return -/
abbrev DirectionFlagUnset (s : Machine.RamState) : Prop :=
  RFLAGS.DirectionFlagClear s.RFLAGS

/-- Input bytes `src[..src_len]` supplied through the System V RDI argument -/
def inputRegion (s : Machine.RamState) (input : ByteArray) : MemoryRegion :=
  registerRegion s .rdi input.size

/-- The 8-byte word `*out_len` supplied through the System V RDX argument -/
def lengthOutputRegion (s : Machine.RamState) : MemoryRegion :=
  registerRegion s .rdx 8

/-- Output buffer `dst[..length]` supplied through the System V RCX argument -/
def outputRegion (s : Machine.RamState) (length : Nat) : MemoryRegion :=
  registerRegion s .rcx length

/--
The input bytes are in memory at a non-null address, as `core::slice::from_raw_parts` requires
even for an empty input, and end below `userAddressLimit`
-/
def ValidInput (s : Machine.RamState) (input : ByteArray) : Prop :=
  let region := inputRegion s input
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.HasBytes s.external input

/--
Bytes `src[..src_len]` of a length call (`ValidLengthCall`), which reads only their length,
supplied through the System V RDI argument
-/
def lengthInputRegion (s : Machine.RamState) (byteLength : Nat) : MemoryRegion :=
  registerRegion s .rdi byteLength

/--
The `byteLength` bytes at `src` are at a non-null address, allocated, and end below
`userAddressLimit`. This is the Rust contract, not an extra premise: both length wrappers build
a `&[u8]` with `core::slice::from_raw_parts(src, src_len)`, which requires a non-null pointer,
even for an empty slice, and memory valid for the slice's whole length, although neither
wrapper reads a byte of it. The bound keeps `byteLength` below `2 ^ 32`.
-/
def ValidLengthInput (s : Machine.RamState) (byteLength : Nat) : Prop :=
  let region := lengthInputRegion s byteLength
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
The 8-byte word at `out_len` is allocated and ends below `userAddressLimit`. Neither a non-null
nor an 8-byte-aligned address is required, although Rust's `*out_len = …` needs both: the
wrappers write through the raw pointer without forming a reference, and the claim holds without
them, so the theorems are the more general.
-/
def ValidLengthOutput (s : Machine.RamState) : Prop :=
  let region := lengthOutputRegion s
  region.Bounded ∧
  region.Allocated s.external

/--
The output buffer of `length` bytes is at a non-null address, as
`core::slice::from_raw_parts_mut` requires even for an empty buffer, is allocated, and ends below
`userAddressLimit`. The `ValidCall` wrappers rely on the non-null address: the crate's result
`Result<&[u8], Error>` is `Err` exactly when its pointer is null.
-/
def ValidOutput (s : Machine.RamState) (length : Nat) : Prop :=
  let region := outputRegion s length
  region.start ≠ 0 ∧
  region.Bounded ∧
  region.Allocated s.external

/--
Separation for a call to `routine` with `outputCapacity` bytes of output buffer:

* always, the input, the output buffer and the stack region are pairwise disjoint, as the
  `&[u8]` and `&mut [u8]` the wrapper builds from them require, and the output buffer and the
  stack region avoid the extracted program and the page tables;
* when `lengthWritten`, the length word is also disjoint from the first `writtenLength` bytes
  of the output buffer, the bytes the call writes, and from the stack region, and avoids the
  extracted program and the page tables. The wrapper writes through `out_len` as a raw pointer
  only on success, so a call that does not write it needs nothing of it.

The length word may overlap the input and the rest of the output buffer, past `writtenLength`:
`out_len` is a raw `*mut usize`, not a reference, and the wrapper stores through it only after
the crate has returned, so after the crate's last read of the input and last write to `dst`.
-/
def MemorySeparation (routine : Routine) (s : Machine.RamState) (input : ByteArray)
    (outputCapacity writtenLength : Nat) (lengthWritten : Prop) : Prop :=
  MemoryRegion.PairwiseDisjoint #v[inputRegion s input, outputRegion s outputCapacity,
    Stack.region s routine.minStackBytes] ∧
  (∀ region ∈ #v[outputRegion s outputCapacity, Stack.region s routine.minStackBytes],
    region.Avoids (fun address => InProgram address ∨ pageTables.Contains address.toNat)) ∧
  (lengthWritten →
    MemoryRegion.PairwiseDisjoint #v[lengthOutputRegion s, outputRegion s writtenLength,
      Stack.region s routine.minStackBytes] ∧
    (lengthOutputRegion s).Avoids
      (fun address => InProgram address ∨ pageTables.Contains address.toNat))

/--
Separation for a length call to `routine`:

* always, the stack region avoids the extracted program and the page tables;
* when `lengthWritten`, the length word and the stack region are disjoint, and the length word
  avoids the extracted program and the page tables.

The input bytes may overlap the stack region and the length word. Neither wrapper reads an input
byte or writes a stack byte: both are leaf code that pushes nothing. The `&[u8]` they build from
`src` is a shared reference, which Rust's aliasing rules let overlap memory that nothing writes
while it is live, and `out_len` is a raw `*mut usize`, written only after the crate's
`decoded_len` or `encoded_len` has returned.
-/
def LengthMemorySeparation (routine : Routine) (s : Machine.RamState) (lengthWritten : Prop) :
    Prop :=
  (Stack.region s routine.minStackBytes).Avoids
    (fun address => InProgram address ∨ pageTables.Contains address.toNat) ∧
  (lengthWritten →
    (lengthOutputRegion s).Disjoint (Stack.region s routine.minStackBytes) ∧
    (lengthOutputRegion s).Avoids
      (fun address => InProgram address ∨ pageTables.Contains address.toNat))

/--
The return address in the slot at RSP is below the user address limit and outside the program
image
-/
def ValidReturnAddress (s : Machine.RamState) : Prop :=
  ∃ address, (Stack.returnSlot s).Word64At s.external address ∧
    address.toNat < userAddressLimit ∧
    ¬ InProgram address

/--
Validity conditions for a System V call `routine(src, src_len, out_len, dst, dst_len)` with
`src[..src_len]` holding `input` and `dst_len = outputCapacity`, for the wrappers of `encode`,
`encode_str` and `decode`:
- RIP at `routine.entryAddress`, the program loaded at its link-time addresses, and the direction
  flag clear
- `input` at RDI, non-null even when empty and ending below `userAddressLimit` (`ValidInput`), its
  length in RSI, and `outputCapacity` in R8
- the whole `outputCapacity`-byte output buffer at RCX non-null, allocated and ending below
  `userAddressLimit` (`ValidOutput`)
- when `lengthWritten`, the 8-byte length word at RDX allocated and ending below
  `userAddressLimit` (`ValidLengthOutput`)
- the stack (`Stack.Valid`): the `routine.minStackBytes` bytes below RSP and the 8-byte return
  slot at RSP allocated and ending below `userAddressLimit`, RSP at least `routine.minStackBytes`
  and 8 more than a multiple of 16
- the return address in the slot at RSP below `userAddressLimit` and outside the program
- the separation of `MemorySeparation`

The input, the output buffer and their separation are required on every call, rejected ones
included, although a call rejected by a length check reads no input byte and writes no output
byte. This is the Rust contract, not an extra premise: the wrapper builds `&[u8]` from `src` and
`&mut [u8]` from `dst` with `core::slice::from_raw_parts` and `from_raw_parts_mut` before
calling the crate, which requires both pointers to be non-null, even for an empty slice, both
to be valid for their whole length, and the two not to overlap. The input's bound below
`userAddressLimit` also keeps `src_len` below `2 ^ 32`, well under the `2 ^ 63` the compiled code
relies on, since `encoded_len` computes `src_len * 2` with wrapping arithmetic in Cargo's release
profile, and a wrapped length could pass the capacity check.

`lengthWritten` is the condition under which the wrapper stores the result's length through the
raw pointer `out_len`, which it does only on success; each theorem supplies its own:
`2 * input.size ≤ outputCapacity` for `encode` and `encode_str`, and a
successful decoding for `decode`. Only then are the length word and its separation required.
`writtenLength` is the number of output bytes such a call writes, which the length word must
avoid: `2 * input.size` for `encode` and `encode_str`, and `input.size / 2` for `decode`.
-/
structure ValidCall (routine : Routine) (s : Machine.RamState) (input : ByteArray)
    (outputCapacity writtenLength : Nat) (lengthWritten : Prop) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  lengthArgumentMatchesInput : (s.regValue .rsi).toNat = input.size
  capacityArgumentMatchesOutput : (s.regValue .r8).toNat = outputCapacity
  inputInMemory : ValidInput s input
  outputInMemory : ValidOutput s outputCapacity
  lengthOutputInMemoryIfLengthWritten : lengthWritten → ValidLengthOutput s
  stack : Stack.Valid s routine.minStackBytes
  separation : MemorySeparation routine s input outputCapacity writtenLength lengthWritten
  returnAddress : ValidReturnAddress s

/--
Validity conditions for a System V call `routine(src, src_len, out_len)` with
`src_len = byteLength`, for the wrappers of `decoded_len` and `encoded_len`:
- RIP at `routine.entryAddress`, the program loaded at its link-time addresses, and the direction
  flag clear
- `byteLength` in RSI, and the `byteLength` bytes at RDI non-null, allocated and ending below
  `userAddressLimit` (`ValidLengthInput`); nothing is assumed of their values
- when `lengthWritten`, the 8-byte length word at RDX allocated and ending below
  `userAddressLimit` (`ValidLengthOutput`)
- the stack and the return address as in `ValidCall`
- the separation of `LengthMemorySeparation`: the input bytes may overlap the stack region and
  the length word

These wrappers read only the length of the input, but both build
`core::slice::from_raw_parts(src, src_len)`, so the Rust contract requires `src` to be non-null
and the `byteLength` bytes there to be valid. `lengthWritten` is the condition under which the
wrapper stores a length in the length word; each theorem supplies it: an even `byteLength` for
`decoded_len`, which returns status 1 for an odd length without a store, and `True` for
`encoded_len`. Only then are the length word and its separation required.
-/
structure ValidLengthCall (routine : Routine) (s : Machine.RamState) (byteLength : Nat)
    (lengthWritten : Prop) : Prop where
  directionFlagUnset : DirectionFlagUnset s
  programLoaded : ProgramLoaded s
  entry : s.RIP = routine.entryAddress
  lengthArgumentMatchesInput : (s.regValue .rsi).toNat = byteLength
  inputInMemory : ValidLengthInput s byteLength
  lengthOutputInMemoryIfLengthWritten : lengthWritten → ValidLengthOutput s
  stack : Stack.Valid s routine.minStackBytes
  separation : LengthMemorySeparation routine s lengthWritten
  returnAddress : ValidReturnAddress s

/--
Reads `length` bytes from final memory at the initial output pointer, in address order. Returns
an unmapped-memory fault at the first missing byte.
-/
def readOutput (initial final : Machine.RamState) (length : Nat) :
    Except Machine.Fault ByteArray := do
  let region := outputRegion initial length
  let bytes ← (List.range length).mapM fun j =>
    let address := BitVec.ofNat 64 (region.start + j)
    match final.external[address]? with
    | some byte => .ok byte
    | none => .error (.unmappedMemory address)
  pure ⟨bytes.toArray⟩

/--
Reads the little-endian 8-byte word `*out_len` from final memory at the initial length pointer,
or the unmapped-memory fault of its first missing byte
-/
def readLengthOutput (initial final : Machine.RamState) : Except Machine.Fault (BitVec 64) :=
  Machine.loadBytes final.external (BitVec.ofNat 64 (lengthOutputRegion initial).start) 8

/--
The System V callee-saved general-purpose registers other than RSP retain their entry values.
RSP is fixed by the return boundary of `Prelude.UniqueExecution`.
-/
def CalleeSavedRegistersUnchanged (initial final : Machine.RamState) : Prop :=
  ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
    final.regValue register = initial.regValue register

end Base16ct.Spec.Program
