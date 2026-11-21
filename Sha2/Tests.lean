import Sha2.Spec
import Standards.Tests.Utilities

/-!
# `sha2` tests

Checks of the wrappers' input concatenation and of the FIPS 180-4 functions the theorems state
against the crate's own known-answer files and outside digests, run by `cd Sha2 && lake test`. The
FIPS 180-4 definitions, including SHA-224, SHA-512/224 and SHA-512/256, are tested against the NIST
vectors in `Standards/NIST/SHA2/Tests.lean`, which these tests do not repeat.

Sources of expected values:
- `Sha2/Tests/Vectors/*_kat.blb`: the crate's own known-answer files at 0.11.1, unmodified,
  three vectors each, in the crate's `blobby` format;
- `Sha2/Tests/Generated/digests.txt`: digests computed by Python's `hashlib`, not by the crate,
  written by `Sha2/Tests/Generated/generate.py`, 26 per hasher, for messages of 0 to 1000 bytes
  around the one- and two-block boundaries of the 64- and 128-byte blocks.

The crate's `sha256_rand` and `sha512_rand` tests (`tests/mod.rs:22-43`), which hash 16 MiB of
generated input, are not run: the theorems state the bit-level FIPS 180-4 functions directly,
and evaluating them on that input would build a bit array of 2^27 entries. No test evaluates a
message that long: the standard's own tests use NIST's long-message and Monte Carlo vectors,
which are much shorter, and the crate's 16 MiB vectors are left to a proof of the theorems.
-/

namespace Sha2.Tests

open Standards.Tests Standards.NIST.SHA2 Sha2.Spec Sha2.Spec.Program

/-- A test hasher: its file name, its digest size, and the standard function it computes. -/
structure Case where
  /-- The file and generated-vector name, as in `sha512_224`. -/
  name : String
  /-- The digest size in bytes. -/
  outputBytes : Nat
  /-- The FIPS 180-4 function the hasher computes. -/
  standard : Array Bool → Digest outputBytes

/-- The six hashers and the functions the specification's theorems state. -/
def cases : List Case :=
  [⟨"sha224", 28, SHA224⟩, ⟨"sha256", 32, SHA256⟩, ⟨"sha384", 48, SHA384⟩,
    ⟨"sha512", 64, SHA512⟩, ⟨"sha512_224", 28, SHA512_224⟩, ⟨"sha512_256", 32, SHA512_256⟩]

/-- The message of the generated vectors: `length` bytes `i % 251`. -/
def pattern (length : Nat) : ByteArray :=
  ⟨(Array.range length).map fun i => UInt8.ofNat (i % 251)⟩

/-- Reads one variable-length number of the `blobby` format (blobby 0.4.0, `decode.rs:3-41`). -/
partial def readVlq (data : ByteArray) (i : Nat) : IO (Nat × Nat) := do
  let some b := data[i]? | throw (IO.userError "blobby: unexpected end")
  let rec go (value i : Nat) (next : Bool) : IO (Nat × Nat) := do
    if !next then return (value, i)
    let some b := data[i]? | throw (IO.userError "blobby: unexpected end")
    go (((value + 1) <<< 7) + (b &&& 0x7f).toNat) (i + 1) (b &&& 0x80 != 0)
  go (b &&& 0x7f).toNat (i + 1) (b &&& 0x80 != 0)

/-- The blobs of a `blobby` file, in order, resolving de-duplicated ones. -/
def blobs (data : ByteArray) : IO (Array ByteArray) := do
  let (count, i) ← readVlq data 0
  let (dedupCount, i) ← readVlq data i
  let mut i := i
  let mut dedup := #[]
  for _ in [:dedupCount] do
    let (length, j) ← readVlq data i
    dedup := dedup.push (data.extract j (j + length))
    i := j + length
  let mut result := #[]
  for _ in [:count] do
    let (value, j) ← readVlq data i
    if value % 2 == 1 then
      let some blob := dedup[value / 2]? | throw (IO.userError "blobby: invalid index")
      result := result.push blob
      i := j
    else
      result := result.push (data.extract j (j + value / 2))
      i := j + value / 2
  unless i == data.size do throw (IO.userError "blobby: trailing bytes")
  return result

/--
Checks one message and its digest from an outside source: the standard function of the
message, and of the message given as four slices, one of them empty, joined by `message` as the
table wrappers' theorems join them.
-/
def checkMessage (case : Case) (label : String) (bytes expected : ByteArray) : IO Unit := do
  let digest (m : ByteArray) := (case.standard (bytesToBits m)).bytes.toArray
  check s!"{label}: standard" (digest bytes == expected.data)
  let third := bytes.size / 3
  let inputs : Array Input := #[⟨1, bytes.extract 0 third⟩, ⟨2, ByteArray.empty⟩,
    ⟨3, bytes.extract third (2 * third)⟩, ⟨4, bytes.extract (2 * third) bytes.size⟩]
  check s!"{label}: four slices" (digest (message inputs) == expected.data)

/-- The crate's known-answer files: three vectors each. -/
def checkKnownAnswers (case : Case) : IO Unit := do
  let path := s!"Sha2/Tests/Vectors/{case.name}_kat.blb"
  let items ← blobs (← IO.FS.readBinFile path)
  check s!"{path}: vector count" (items.size == 6)
  for i in [:items.size / 2] do
    checkMessage case s!"{path}, vector {i}" items[2 * i]! items[2 * i + 1]!
  IO.println s!"{path}: 3 vectors passed"

/-- The generated digests: 26 pattern messages per hasher. -/
def checkGenerated (lines : List String) (case : Case) : IO Unit := do
  let mut count := 0
  for line in lines do
    match line.splitOn " " with
    | [name, "pattern", length, digest] =>
      if name != case.name then continue
      let some length := length.toNat? | throw (IO.userError s!"bad length: {line}")
      checkMessage case s!"{name} pattern {length}" (pattern length) (← hex digest)
      count := count + 1
    | _ => throw (IO.userError s!"bad line: {line}")
  check s!"{case.name}: generated count" (count == 26)
  IO.println s!"{case.name}: 26 generated digests passed"

/-- The wrappers hash the concatenation of their input slices, in table order. -/
def checkMessageConcatenation : IO Unit := do
  check "no slices" ((message #[]).size == 0)
  check "one empty slice" ((message #[⟨0, ByteArray.empty⟩]).size == 0)
  check "three slices"
    ((message #[⟨1, "ab".toUTF8⟩, ⟨1, ByteArray.empty⟩, ⟨2, "c".toUTF8⟩]).data == "abc".toUTF8.data)
  IO.println "Input slices concatenate in table order"

/-- The lines of a generated file, without its `#` label line and blank lines. -/
def generatedLines (path : String) : IO (List String) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  check s!"{path}: label" ((lines.headD "").startsWith "# generated by ")
  return (lines.drop 1).filter (· != "")

/-- Runs every `sha2` test, throwing on the first failure. -/
def run : IO Unit := do
  checkMessageConcatenation
  let lines ← generatedLines "Sha2/Tests/Generated/digests.txt"
  check "generated line count" (lines.length == 156)
  for case in cases do
    checkKnownAnswers case
    checkGenerated lines case
  IO.println "Passed every sha2 test"

end Sha2.Tests
