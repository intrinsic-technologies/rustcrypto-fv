import Sha1.Spec
import Standards.NIST.SHA2.Tests
import Standards.Tests.Utilities

/-!
# `sha1` tests

Executable checks of the specification, run by `cd Sha1 && lake test` (`Sha1` is its own Lake
package). The FIPS 180-4 definitions are tested against the bit- and byte-oriented NIST CAVP
vectors in `Standards/NIST/SHA1/Tests.lean`; this file tests the crate's definitions in
`Sha1/Spec/Hasher.lean` and `Sha1/Spec/Program.lean`, and the expressions of the two theorems, for
`sha1_digest` and `sha1_update_finalize`. The checks below for `compress`, `sha1_reset`,
`sha1_finalize_reset`, `sha1_update_reset`, `sha1_finalize_into_reset` and
`sha1_finalize_fixed_reset` test expressions that no theorem states.

Vector files:

* `Sha1/Tests/Vectors/sha1_kat.blb` is unmodified: the known-answer tests of `sha1` 0.11.0,
  `tests/data/sha1_kat.blb`, in the `blobby` 0.4 format (pairs of input and digest);
* `Sha1/Tests/Generated/crate_generated.txt` holds crate-generated answers, not published vectors:
  `Sha1/Tests/Generated/generator/` prints it, byte for byte, by running the real `sha1` 0.11.0
  with the backend and features the wrappers pin.

Two vectors have no file. `millionA` below and its digest are the third test of the driver in RFC
3174, §7.3, which repeats `"a"` 1,000,000 times. RFC 3174 is a secondary source, not the defining
standard:
https://www.rfc-editor.org/rfc/rfc3174.txt
The hash value after one block of 64 bytes `0x13` from the initial hash value, the `compress`
example, is bytes 0 to 19 of the crate's `tests/data/sha1_serialization.bin`, copied here as hex:
the `h` field of the state that file holds after 65 such bytes, one block compressed.

Checks, with `SHA1 (bytesToBits input)` as the digest of a byte string, as in the statements:

* the 4 crate known-answer tests and the digest of "hello world" in the crate's README, each in
  these forms: as one input, the form of `sha1_digest`; as three slices joined by `Slices.message`;
  as the slices after a split, with another slice before it; as the two messages of a split, of
  which the first is empty; and through `SHA1.compress` from the initial hash value on the message
  padded by hand as FIPS 180-4 §5.1.1 pads, read through `stateBytes` with each word's bytes
  reversed;
* the 1,000,000-byte RFC 3174 message, as one input and through `SHA1.compress` on the message
  padded by hand; the other forms are identities on the same definitions and would only add time;
* the `compress` example: one block of 64 bytes `0x13` from the initial hash value, against the
  crate's hash value above;
* the 14 `Compress`, 7 `UpdateFinalize`, 42 `Reset`, 42 `FinalizeReset`, 42 `UpdateReset`,
  42 `FinalizeIntoReset`, and 42 `FinalizeFixedReset` records of `crate_generated.txt`, each
  against the expression of its entry point; 35 of each 42 are distinct, because the generator's
  split list repeats values for short slice lists. The `Compress` records start from the all-zero,
  all-one, and initial hash values and two pseudo-random ones, with 0 to 3 and 5 blocks; the slice
  records include zero slices, empty slices, slices ending on and across block boundaries, and
  splits of 0, 1, half, all, one more than the number of slices, and `usize::MAX`;
* the byte layout: `stateBytes` of the initial hash value as literal bytes, which are also the bytes
  of the two `movabs` immediates and the `mov` immediate that the extracted wrappers load;
* the slice helpers: no slices form the empty message, an empty slice adds nothing, slices
  concatenate in order, `Array.extract` at a split above the number of slices leaves the second
  message empty, and `tableEntry` steps by eight bytes;
* `readBytes`, which every `readOutput` uses, on a map holding known bytes, and its error naming
  the first of two missing bytes;
* each `minStackBytes` and each `Routine`'s `minStackBytes` and `outputBytes` equal the figures in
  their doc comments;
* at compile time, the call layer's definitions against the wrappers' System V signatures in
  `Sha1/program/src/lib.rs`: the argument registers and sizes of each region, the count arguments,
  the nonzero-address conditions, the registers of `CalleeSavedRegistersUnchanged`, the parts of
  `MemorySeparation`, the bytes of `InPageTables`, the regions of `Slices.readRegions`, and each
  `ValidCall`'s entry symbol and separation regions, the symbol by its name in `Symbols.lean`, not
  by its address. These restate the definitions, so they catch a later change to one, not a
  misreading shared with this file.

The slices, after-a-split, and two-messages forms of a crate known-answer test reduce to
`ByteArray` and `Array` identities on the same definitions. They check the expressions' shapes and
add no evidence about `reset` or `finalize_reset`; that comes only from `crate_generated.txt`.

Coverage of the range the theorems state, and where it rests on the crate rather than on a published
vector: `Standards/NIST/SHA1/Tests.lean` runs NIST's short file, with every byte length from 0 to
64, and so the empty message, the padding boundaries at 55 and 56 bytes, and whole blocks, and its
long file, with lengths from 163 to 6400 bytes, through `SHA1.SHA1`. Above that, this file has only
the 1,000,000-byte RFC 3174 message, and no test reaches the 2³² − 1 bytes of the largest input or
the near 2⁶¹ bytes of the largest message from slices. Apart from the one example above, no
published vector calls `compress` on a state the caller chooses: none from a state other than an
intermediate hash value of SHA-1, with zero blocks, or from the all-zero or all-one state. None
exercises `Digest::reset`, `finalize_reset`, a split beyond the number of slices, zero slices, empty
slices, or any of the trait methods the entry points from `sha1_update_reset` to
`sha1_finalize_fixed_reset` call; those checks rest only on `crate_generated.txt` and so on the
crate itself. The crate's own `sha1_rand` test is not run. `feed_rand_16mib` in `digest` feeds it
16,793,600 bytes, 16,384 rounds of 1,024 pseudo-random bytes and one byte 42, so evaluating
`SHA1.SHA1` on it would build a bit array of 134,348,800 `Bool`s, which costs minutes on every run
of this suite.

No test runs the extracted code or constructs a `ValidCall`; the generator repeats the wrappers'
call sequences on the crate instead of calling them. Each check also retypes its theorem's
expression rather than referring to it, so a changed expression in `Statements.lean` is seen by no
test.

The padding's length word is not tested above 8,000,000 bits, the length of the RFC 3174 message;
the next longest message any test hashes, in this file or in `Standards/NIST/SHA1/Tests.lean`, has
51,200 bits. So bits 23 and above of the length word that `SHA256.pad` builds are zero in every
test, and an error in `SHA256.pad` that only shows there, such as encoding the length mod 2²³ or
mod 2³², passes every test.
-/

namespace Sha1.Tests

open Standards.Tests Standards.NIST Standards.NIST.SHA1 Sha1.Spec Sha1.Spec.Program

private def vectors : System.FilePath := "Sha1/Tests/Vectors"

private def digestBytes (input : ByteArray) : ByteArray :=
  ⟨(SHA1 (SHA2.bytesToBits input)).bytes.toArray⟩

/-- Reads a `blobby` variable-length quantity: big-endian 7-bit groups, continuations adding one -/
private def readVlq (data : ByteArray) (position : Nat) : Nat × Nat := Id.run do
  let mut position := position
  let mut byte := data.get! position
  let mut value := (byte &&& 0x7f).toNat
  position := position + 1
  for _ in [0:3] do
    if byte &&& 0x80 == 0 then break
    byte := data.get! position
    value := ((value + 1) <<< 7) + (byte &&& 0x7f).toNat
    position := position + 1
  return (value, position)

/--
The blobs of a `blobby` 0.4 file: a header of blob and dedup counts, the dedup table, the blobs
-/
private def blobs (data : ByteArray) : Array ByteArray := Id.run do
  let (count, position) := readVlq data 0
  let (dedupCount, position) := readVlq data position
  let mut position := position
  let mut dedup := #[]
  for _ in [0:dedupCount] do
    let (length, next) := readVlq data position
    dedup := dedup.push (data.extract next (next + length))
    position := next + length
  let mut result := #[]
  for _ in [0:count] do
    let (value, next) := readVlq data position
    if value % 2 == 1 then
      result := result.push (dedup.getD (value / 2) .empty)
      position := next
    else
      result := result.push (data.extract next (next + value / 2))
      position := next + value / 2
  return result

/-- `bytes` split at one third and two thirds of its length, as the slices of a call -/
private def threeSlices (bytes : ByteArray) : Array Slices.Input :=
  let first := bytes.size / 3
  let second := 2 * bytes.size / 3
  #[⟨1, bytes.extract 0 first⟩, ⟨2, bytes.extract first second⟩,
    ⟨3, bytes.extract second bytes.size⟩]

/-- The bytes of `Hasher.stateBytes` for a state, with each word's four bytes reversed -/
private def swappedStateBytes (H : Vector (BitVec 32) 5) : ByteArray :=
  let bytes := (Hasher.stateBytes H).toArray
  ⟨Array.ofFn (n := 20) fun i => bytes[4 * (i.val / 4) + 3 - i.val % 4]!⟩

/--
The message followed by a one bit, zero bytes, and its bit length as a big-endian 64-bit word,
written in bytes as FIPS 180-4 §5.1.1 pads it
-/
private def paddedBytes (input : ByteArray) : ByteArray := Id.run do
  let zeros := (64 + 55 - input.size % 64) % 64
  let mut padded := input.push 0x80
  for _ in [0:zeros] do
    padded := padded.push 0
  let bits := 8 * input.size
  for i in [0:8] do
    padded := padded.push (UInt8.ofNat (bits / 2 ^ (8 * (7 - i)) % 256))
  return padded

/-- The digest through the compression function, as `SHA1.compress` computes it -/
private def digestThroughCompress (input : ByteArray) : ByteArray :=
  swappedStateBytes
    ((SHA2.SHA256.parse (SHA2.bytesToBits (paddedBytes input))).foldl compress initialHashValue)

/-- The message of the third test of RFC 3174, §7.3: `"a"` repeated 1,000,000 times -/
private def millionA : ByteArray := ⟨Array.replicate 1000000 0x61⟩

/-- Checks one message, with its digest, in every form the theorems state -/
private def checkMessage (label : String) (message expected : ByteArray) : IO Unit := do
  let digest := digestBytes message
  expect s!"{label}: one input" digest expected
  let slices := threeSlices message
  expect s!"{label}: slices" (digestBytes (Slices.message slices)) expected
  let afterSplit := #[(⟨9, "before".toUTF8⟩ : Slices.Input)] ++ slices
  expect s!"{label}: slices after a split"
    (digestBytes (Slices.message (afterSplit.extract 1 afterSplit.size))) expected
  expect s!"{label}: two messages, the first empty"
    (digestBytes (Slices.message (slices.extract 0 0)) ++
      digestBytes (Slices.message (slices.extract 0 slices.size)))
    (digestBytes ByteArray.empty ++ expected)
  expect s!"{label}: compress on the padded message" (digestThroughCompress message) expected

/-- The slices in a `Slices = ` field: hex separated by `,`, with `-` for an empty slice -/
private def parseSlices (field : String) : IO (Array Slices.Input) := do
  if field.isEmpty then return #[]
  let mut slices := #[]
  for part in field.splitOn "," do
    let bytes ← if part == "-" then pure ByteArray.empty else hex part
    slices := slices.push (⟨1, bytes⟩ : Slices.Input)
  return slices

/-- The value of `key` in a record of `key = value` lines; the value may be empty -/
private def recordField (lines : List String) (key : String) : IO String := do
  let some line := lines.find? (·.startsWith s!"{key} =")
    | throw (IO.userError s!"crate_generated.txt: missing {key}")
  return ((line.drop (key.length + 2)).trimAscii).toString

/-- Five big-endian words from 20 bytes of hex -/
private def parseState (bytes : ByteArray) : Vector (BitVec 32) 5 :=
  Vector.ofFn fun i : Fin 5 =>
    (List.range 4).foldl (init := (0 : BitVec 32)) fun word j =>
      (word <<< 8) ||| BitVec.ofNat 32 (bytes.get! (4 * i.val + j)).toNat

/-- The record kinds of `crate_generated.txt`, in the order of their pinned counts -/
private def recordKinds : List String :=
  ["Compress", "UpdateFinalize", "Reset", "FinalizeReset", "UpdateReset", "FinalizeIntoReset",
    "FinalizeFixedReset"]

/-- Checks every crate-generated record against its entry point's expression; pins the counts -/
private def crateGenerated : IO Unit := do
  let text ← IO.FS.readFile "Sha1/Tests/Generated/crate_generated.txt"
  let mut counts : Array Nat := recordKinds.toArray.map fun _ => 0
  for record in (text.splitOn "\n\n").drop 1 do
    let lines := record.splitOn "\n" |>.filter (!·.isEmpty)
    let some kind := lines.head? | continue
    let some index := recordKinds.idxOf? kind
      | throw (IO.userError s!"crate_generated.txt: unknown record {kind}")
    let label := s!"crate_generated.txt, {kind} {counts[index]!}"
    counts := counts.modify index (· + 1)
    match kind with
    | "Compress" =>
      let state := parseState (← hex (← recordField lines "State"))
      let blocks ← hex (← recordField lines "Blocks")
      let result := (SHA2.SHA256.parse (SHA2.bytesToBits blocks)).foldl compress state
      expect label ⟨(Hasher.stateBytes result).toArray⟩ (← hex (← recordField lines "Out"))
    | "UpdateFinalize" =>
      let slices ← parseSlices (← recordField lines "Slices")
      expect label (digestBytes (Slices.message slices)) (← hex (← recordField lines "Out"))
    | "Reset" | "UpdateReset" =>
      let slices ← parseSlices (← recordField lines "Slices")
      let split ← SHA2.Tests.number (← recordField lines "Split")
      expect label (digestBytes (Slices.message (slices.extract split slices.size)))
        (← hex (← recordField lines "Out"))
    | "FinalizeReset" | "FinalizeIntoReset" | "FinalizeFixedReset" =>
      let slices ← parseSlices (← recordField lines "Slices")
      let split ← SHA2.Tests.number (← recordField lines "Split")
      expect label
        (digestBytes (Slices.message (slices.extract 0 split)) ++
          digestBytes (Slices.message (slices.extract split slices.size)))
        (← hex (← recordField lines "Out"))
    | _ => pure ()
  check "crate_generated.txt: record counts"
    (counts == #[14, 7, 42, 42, 42, 42, 42])

/-- Checks `readBytes`, which every `readOutput` uses, on memory holding known bytes at 0x1000 -/
private def readOutputChecks : IO Unit := do
  let region : Prelude.MemoryRegion := ⟨0x1000, 20⟩
  let memory : X86.Machine.Ram := (List.range 20).foldl (init := ∅) fun memory i =>
    memory.insert (BitVec.ofNat 64 (0x1000 + i)) (UInt8.ofNat (i + 1))
  check "readBytes reads the bytes in address order"
    (match readBytes region memory with
     | .ok read => read.toArray == (Array.range 20).map fun i => UInt8.ofNat (i + 1)
     | .error _ => false)
  let missing := BitVec.ofNat 64 (0x1000 + 3)
  let alsoMissing := BitVec.ofNat 64 (0x1000 + 19)
  check "readBytes reports the first of two missing bytes"
    (match readBytes region ((memory.erase alsoMissing).erase missing) with
     | .error (.unmappedMemory address) => address == missing
     | _ => false)

/-- Checks the slice helpers on small literal slices -/
private def sliceChecks : IO Unit := do
  let slices : Array Slices.Input :=
    #[⟨1, "ab".toUTF8⟩, ⟨2, ByteArray.empty⟩, ⟨3, "c".toUTF8⟩, ⟨4, "d".toUTF8⟩]
  check "no slices form the empty message" (Slices.message #[]).isEmpty
  check "an empty slice adds nothing" (Slices.message #[⟨1, ByteArray.empty⟩]).isEmpty
  check "slices concatenate in order" ((Slices.message slices).data == "abcd".toUTF8.data)
  check "a split takes the first slices"
    ((Slices.message (slices.extract 0 3)).data == "abc".toUTF8.data &&
      (Slices.message (slices.extract 3 slices.size)).data == "d".toUTF8.data)
  check "a split above the number of slices leaves the second message empty"
    ((Slices.message (slices.extract 0 9)).data == "abcd".toUTF8.data &&
      (Slices.message (slices.extract 9 slices.size)).isEmpty)
  check "tableEntry steps by eight bytes"
    (Slices.tableEntry ⟨0x1000, 32⟩ 2 == ⟨0x1010, 8⟩)
  check "Input.region is the slice's address and length"
    ((⟨0x2000, "ab".toUTF8⟩ : Slices.Input).region == ⟨0x2000, 2⟩)

section CallLayer

open Prelude X86

variable {bindings : Machine.Bindings} {s initial final : Machine.RamState}

example (region : MemoryRegion) (bytes : ByteArray) :
    ValidInput s region bytes ↔
      region.start ≠ 0 ∧ region.Bounded ∧ region.HasBytes s.external bytes := Iff.rfl
example (output : MemoryRegion) :
    ValidOutput s output ↔ output.start ≠ 0 ∧ output.Bounded ∧ output.Allocated s.external :=
  Iff.rfl
example (table : MemoryRegion) : Slices.ValidTable table ↔ table.start ≠ 0 ∧ table.Bounded :=
  Iff.rfl

example (input : ByteArray) : Digest.inputRegion s input = registerRegion s .rdi input.size := rfl
example : Digest.outputRegion s = registerRegion s .rdx 20 := rfl
example {input : ByteArray} (h : Digest.ValidCall bindings s input) :
    s.RIP = Extracted.sha1DigestAddress ∧ (s.regValue .rsi).toNat = input.size ∧
      ValidInput s (Digest.inputRegion s input) input ∧
      MemorySeparation [Digest.inputRegion s input] (Digest.outputRegion s)
        (Stack.region s Digest.minStackBytes) :=
  ⟨h.atEntryPoint, h.inputLengthArgumentMatchesInput, h.inputInMemory, h.separation⟩

example (blocks : ByteArray) : Compress.inputRegion s blocks = registerRegion s .rsi blocks.size :=
  rfl
example : Compress.outputRegion s = registerRegion s .rdi 20 := rfl
example {H : Vector (BitVec 32) 5} {blocks : ByteArray}
    (h : Compress.ValidCall bindings s H blocks) :
    s.RIP = Extracted.sha1CompressAddress ∧ 64 * (s.regValue .rdx).toNat = blocks.size ∧
      (Compress.outputRegion s).start ≠ 0 ∧
      MemorySeparation [Compress.inputRegion s blocks] (Compress.outputRegion s)
        (Stack.region s Compress.minStackBytes) :=
  ⟨h.atEntryPoint, h.blockCountArgumentMatchesBlocks, h.outputInMemory.1, h.separation⟩

example (count : Nat) : Slices.pointerTable s count = registerRegion s .rdi (8 * count) := rfl
example (count : Nat) : Slices.lengthTable s count = registerRegion s .rdx (8 * count) := rfl
example {inputs : Array Slices.Input} :
    Slices.readRegions s inputs =
      Slices.pointerTable s inputs.size :: Slices.lengthTable s inputs.size ::
        (inputs.map Slices.Input.region).toList := rfl
example {inputs : Array Slices.Input} (h : Slices.ValidInputs s inputs) (i : Fin inputs.size) :
    (Slices.pointerTable s inputs.size).start ≠ 0 ∧ (Slices.lengthTable s inputs.size).start ≠ 0 ∧
      inputs[i].region.start ≠ 0 :=
  ⟨h.pointerTableValid.1, h.lengthTableValid.1, (h.inputsInMemory i).1⟩

example (routine : SliceHash.Routine) :
    SliceHash.outputRegion routine s = registerRegion s .rcx routine.outputBytes := rfl
example {inputs : Array Slices.Input} (routine : SliceHash.Routine)
    (h : SliceHash.ValidCall routine bindings s inputs) :
    s.RIP = routine.entryAddress ∧ (s.regValue .rsi).toNat = inputs.size ∧
      MemorySeparation (Slices.readRegions s inputs) (SliceHash.outputRegion routine s)
        (Stack.region s routine.minStackBytes) :=
  ⟨h.atEntryPoint, h.sliceCountArgumentMatchesInputs, h.separation⟩
example : SliceHash.updateFinalize.entryAddress = Extracted.sha1UpdateFinalizeAddress := rfl

example (h : CalleeSavedRegistersUnchanged initial final) :
    final.regValue .rbx = initial.regValue .rbx ∧ final.regValue .rbp = initial.regValue .rbp ∧
      final.regValue .r12 = initial.regValue .r12 ∧ final.regValue .r13 = initial.regValue .r13 ∧
      final.regValue .r14 = initial.regValue .r14 ∧ final.regValue .r15 = initial.regValue .r15 :=
  ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩

example {reads : List MemoryRegion} {output stack : MemoryRegion}
    (h : MemorySeparation reads output stack) :
    output.Disjoint stack ∧ (∀ read ∈ reads, read.Disjoint output ∧ read.Disjoint stack) ∧
      output.Avoids (fun address => InProgram address ∨ InPageTables address) ∧
      stack.Avoids (fun address => InProgram address ∨ InPageTables address) :=
  ⟨h.1, fun read hRead => ⟨(h.2 output (by simp)).1 read hRead, (h.2 stack (by simp)).1 read hRead⟩,
    (h.2 output (by simp)).2, (h.2 stack (by simp)).2⟩

/-- `InPageTables` holds exactly on the bytes `[0x1000, 0x1008)` and `[0x2000, 0x2020)` -/
example (address : BitVec 64) : InPageTables address ↔
    (0x1000 ≤ address.toNat ∧ address.toNat < 0x1008) ∨
      (0x2000 ≤ address.toNat ∧ address.toNat < 0x2020) := by
  simp [InPageTables, MemoryRegion.Contains]

example (h : ValidReturnAddress bindings s) :
    letI := bindings
    ∃ boundary, nearReturn64Boundary s = .ok boundary ∧ boundary.rip.toNat < userAddressLimit ∧
      ¬ InProgram boundary.rip := h

end CallLayer

/-- Runs every `sha1` test, throwing on the first failure -/
def run : IO Unit := do
  let kat := blobs (← IO.FS.readBinFile (vectors / "sha1_kat.blb"))
  check "sha1_kat.blb has 4 input and digest pairs" (kat.size == 8)
  for i in [0:kat.size / 2] do
    checkMessage s!"sha1_kat.blb vector {i}" kat[2 * i]! kat[2 * i + 1]!
  checkMessage "the crate's README" "hello world".toUTF8
    (← hex "2aae6c35c94fcfb415dbe95f408b9ce91ee846ed")
  let millionADigest ← hex "34aa973cd4c4daa4f61eeb2bdbad27316534016f"
  expect "RFC 3174 §7.3, a million a: one input" (digestBytes millionA) millionADigest
  expect "RFC 3174 §7.3, a million a: compress on the padded message"
    (digestThroughCompress millionA) millionADigest
  expect "the compress theorem's example: one block of 64 bytes 0x13 from the initial hash value"
    ⟨(Hasher.stateBytes ((SHA2.SHA256.parse (SHA2.bytesToBits ⟨Array.replicate 64 0x13⟩)).foldl
      compress initialHashValue)).toArray⟩
    (← hex "ad0eca12d0aaa48af970c03f1420a28d260b50df")
  crateGenerated
  expect "stateBytes of the initial hash value" ⟨(Hasher.stateBytes initialHashValue).toArray⟩
    (← hex "0123456789abcdeffedcba9876543210f0e1d2c3")
  sliceChecks
  readOutputChecks
  check "the stack budgets are those in the doc comments"
    (Digest.minStackBytes == 656 && Compress.minStackBytes == 336 &&
      SliceHash.updateFinalize.minStackBytes == 704)
  check "the output size is the one in the doc comment" (SliceHash.updateFinalize.outputBytes == 20)
  IO.println "sha1: 5 crate digests, the RFC 3174 million-byte message, the compress example, \
    231 crate-generated records, and the layout, slice, reader, and budget checks passed"

end Sha1.Tests
