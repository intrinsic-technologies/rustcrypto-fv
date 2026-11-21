import Sha3.Spec
import Standards.Tests.Utilities

/-!
# `sha3` tests

Checks of the `sha3` 0.12.0 specification, run by `cd Sha3 && lake test` (`Sha3` is its
own Lake package). FIPS 202 itself (`Standards.NIST.SHA3`, the SHA-3 functions the
theorems name) is tested against NIST's vectors in `Standards/NIST/SHA3/Tests.lean`; these tests
cover what this crate adds: the Keccak instances, and the parts of the theorem statements and call
semantics this crate defines (`message`, `Array.extract` for the split-output forms, the routines'
output sizes).

The theorems in `Sha3.Statements` are the `digest` and `digest_slices` theorems of `Sha3_224`,
`Sha3_256`, `Sha3_384`, `Sha3_512`, `Keccak224`, `Keccak256`, `Keccak384` and `Keccak512`. The
checks below also cover an expression that no theorem states: the first output of the two-output
forms.

Vectors, all unmodified, in `Sha3/Tests/Vectors/`:

- `sha3_224_kat.blb` and `sha3_256_kat.blb` (256 vectors each), `sha3_384_kat.blb` and
  `sha3_512_kat.blb` (255 each), `keccak_224_kat.blb`, `keccak_384_kat.blb` and
  `keccak_512_kat.blb` (1 each) and `keccak_256_kat.blb` (3): the crate's own `tests/data/` at
  0.12.0;
- `ShortMsgKAT_224.txt` through `ShortMsgKAT_512.txt` (2048 entries each, of which the 256 whose
  length is a whole number of bytes are used), `LongMsgKAT_224.txt` through `LongMsgKAT_512.txt`
  (513 entries each, from 2048 to 34304 bits, of which the 65 whose length is a whole number of
  bytes, 256 to 4288 bytes, are used): the Keccak team's `KeccakKAT-3.zip`,
  https://keccak.team/obsolete/KeccakKAT-3.zip
  (SHA-256 `af92d22d23527a0d168a6bbe70b28c840a43bba5bcea828a6d9a5e7ad79378ce`).

Checks, with the source of each expected value:

- the crate's `.blb` files (the crate's own data): each digest through the function the theorems
  state (`Digest.ofBits (SHA3_256 (bytesToBits m))` and its siblings); and each message cut at a
  third into two parts, through `message`, whole and through `Array.extract` with a split past the
  end, as the `digest_slices` theorems' output of all the parts and the two-output entry points'
  first output of the parts before the split read them;
- the Keccak team's short and long messages (the standard's data): `Keccak.keccak224` and its
  siblings against the published digest;
- each routine's output size against its type's `OutputSize`, from the crate's
  `impl_sha3_variants!` invocation.

Boundaries: the crate's SHA-3 `.blb` files hold every byte length from 0 to 255 (1 to 255 for
`sha3_384_kat.blb` and `sha3_512_kat.blb`, which have no empty message), and the Keccak team's
files every length from 0 to 255: so the empty message, one byte short of a block (where one byte
gets both padding bytes), exactly one block, and one block and one byte, for every rate.
Multi-block messages come from those files, up to 255 bytes, and for the four Keccak variants from
the long-message files, 256 to 4288 bytes. No SHA-3 type has a vector above 255 bytes here; their
longer messages rest on the FIPS 202 tests. The archive's `ExtremelyLongMsgKAT_*` files (a 64-byte
text repeated 2^24 times, 1 GiB) are not used: the Lean definitions would take too long on them.
-/

namespace Sha3.Tests

open Sha3.Spec Sha3.Spec.Program Standards.NIST.SHA3 Standards.Tests

/-- One hasher type under test: its vector file name and its digest under test -/
private structure Algorithm where
  name : String
  standard : ByteArray → ByteArray

private def algorithms : Array Algorithm := #[
  ⟨"sha3_224",
    fun m => (Digest.ofBits (byteCount := 28) (SHA3_224 (bytesToBits m))).toBytes⟩,
  ⟨"sha3_256",
    fun m => (Digest.ofBits (byteCount := 32) (SHA3_256 (bytesToBits m))).toBytes⟩,
  ⟨"sha3_384",
    fun m => (Digest.ofBits (byteCount := 48) (SHA3_384 (bytesToBits m))).toBytes⟩,
  ⟨"sha3_512",
    fun m => (Digest.ofBits (byteCount := 64) (SHA3_512 (bytesToBits m))).toBytes⟩,
  ⟨"keccak_224",
    fun m => (Digest.ofBits (byteCount := 28) (Keccak.keccak224 (bytesToBits m))).toBytes⟩,
  ⟨"keccak_256",
    fun m => (Digest.ofBits (byteCount := 32) (Keccak.keccak256 (bytesToBits m))).toBytes⟩,
  ⟨"keccak_384",
    fun m => (Digest.ofBits (byteCount := 48) (Keccak.keccak384 (bytesToBits m))).toBytes⟩,
  ⟨"keccak_512",
    fun m => (Digest.ofBits (byteCount := 64) (Keccak.keccak512 (bytesToBits m))).toBytes⟩]

private def directory : System.FilePath := "Sha3/Tests/Vectors"

/-- A blobby variable-length quantity at `i` (blobby 0.4, `read_vlq`), and the index after it -/
private def vlq (data : ByteArray) (i : Nat) : IO (Nat × Nat) := do
  let some b := data[i]? | throw (IO.userError "blobby: unexpected end")
  let mut value := (b &&& 0x7f).toNat
  let mut more := b &&& 0x80 != 0
  let mut j := i + 1
  for _ in [:3] do
    if !more then break
    let some b := data[j]? | throw (IO.userError "blobby: unexpected end")
    j := j + 1
    more := b &&& 0x80 != 0
    value := ((value + 1) <<< 7) + (b &&& 0x7f).toNat
  if more then throw (IO.userError "blobby: invalid length")
  return (value, j)

/-- The blobs of a blobby 0.4 file, in order, resolving deduplicated references -/
private def blobs (path : System.FilePath) : IO (Array ByteArray) := do
  let data ← IO.FS.readBinFile path
  let (count, i) ← vlq data 0
  let (dedupCount, i) ← vlq data i
  let mut i := i
  let mut dedup := #[]
  for _ in [:dedupCount] do
    let (length, j) ← vlq data i
    dedup := dedup.push (data.extract j (j + length))
    i := j + length
  let mut items := #[]
  for _ in [:count] do
    let (value, j) ← vlq data i
    i := j
    if value % 2 == 1 then
      let some blob := dedup[value / 2]? | throw (IO.userError s!"{path}: invalid reference")
      items := items.push blob
    else
      unless i + value / 2 ≤ data.size do throw (IO.userError s!"{path}: unexpected end")
      items := items.push (data.extract i (i + value / 2))
      i := i + value / 2
  unless i == data.size do throw (IO.userError s!"{path}: trailing bytes")
  return items

/-- The crate's own known-answer vectors, through the digest under test -/
private def crateVectors (alg : Algorithm) (count : Nat) : IO Unit := do
  let path := directory / s!"{alg.name}_kat.blb"
  let items ← blobs path
  check s!"{path}: incorrect vector count" (items.size == 2 * count)
  for i in [:count] do
    let input := items[2 * i]!
    let expected := items[2 * i + 1]!
    let label := s!"{path}, vector {i}"
    expect s!"{label}, theorem digest" (alg.standard input) expected
    let first := input.extract 0 (input.size / 3)
    let rest := input.extract (input.size / 3) input.size
    let parts : Array Input := #[⟨0, first⟩, ⟨0, rest⟩]
    expect s!"{label}, digest of all parts, as the digest_slices theorems' output"
      (alg.standard (message parts)) expected
    expect s!"{label}, digest of the parts before a split past the end, as a first output"
      (alg.standard (message (parts.extract 0 5))) expected
  IO.println s!"{path}: {count} passed"

/-- Key-value lines of a short- or long-message file, without comments or bracketed headers -/
private def fields (path : System.FilePath) : IO (Array (String × String)) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" || line.startsWith "[" then continue
    match line.splitOn " = " with
    | [key, value] => result := result.push (key, value)
    | _ => throw (IO.userError s!"{path}: invalid line: {line}")
  return result

/--
The byte-length messages of a short- or long-message file and their digests: the entries whose
`Len`, in bits, is a multiple of 8; `Msg` is `00` for the empty message
-/
private def byteMessages (path : System.FilePath) (entries : Nat) :
    IO (Array (ByteArray × ByteArray)) := do
  let data ← fields path
  check s!"{path}: incorrect entry count" (data.size == 3 * entries)
  let mut result := #[]
  for i in [:entries] do
    let (lenKey, len) := data[3 * i]!
    let (msgKey, msg) := data[3 * i + 1]!
    let (mdKey, md) := data[3 * i + 2]!
    check s!"{path}: unexpected keys" (lenKey == "Len" && msgKey == "Msg" && mdKey == "MD")
    let some bits := len.toNat? | throw (IO.userError s!"{path}: invalid length {len}")
    if bits % 8 != 0 then continue
    let message ← hex msg
    check s!"{path}: invalid message length" (message.size == max 1 (bits / 8))
    result := result.push (message.extract 0 (bits / 8), ← hex md)
  return result

/--
The Keccak team's short or long messages (`kind` `"Short"` or `"Long"`), through
`Keccak.keccak224` and its siblings: `entries` entries in the file, `used` of them whole bytes
-/
private def keccakMessages (alg : Algorithm) (bits : Nat) (kind : String) (entries used : Nat) :
    IO Unit := do
  let path := directory / s!"{kind}MsgKAT_{bits}.txt"
  let vectors ← byteMessages path entries
  check s!"{path}: incorrect vector count" (vectors.size == used)
  for (message, expected) in vectors do
    let label := s!"{path}, {message.size} bytes"
    expect s!"{label}: Keccak function" (alg.standard message) expected
  IO.println s!"{path}: {vectors.size} passed"

#guard (message #[]).size == 0
#guard (message #[⟨0, ByteArray.empty⟩]).size == 0
#guard (message #[⟨1, "ab".toUTF8⟩, ⟨1, ByteArray.empty⟩, ⟨2, "c".toUTF8⟩]).data ==
  "abc".toUTF8.data
#guard (message (#[⟨1, "ab".toUTF8⟩, ⟨2, "c".toUTF8⟩, ⟨3, "d".toUTF8⟩].extract 0 2)).data ==
  "abc".toUTF8.data
#guard (message (#[⟨1, "ab".toUTF8⟩, ⟨2, "c".toUTF8⟩, ⟨3, "d".toUTF8⟩].extract 2 3)).data ==
  "d".toUTF8.data
#guard (message (#[⟨1, "ab".toUTF8⟩, ⟨2, "c".toUTF8⟩].extract 0 5)).data == "abc".toUTF8.data
#guard (message (#[⟨1, "ab".toUTF8⟩, ⟨2, "c".toUTF8⟩].extract 5 2)).size == 0

/--
Every routine, with its type's `OutputSize` from the crate's `impl_sha3_variants!` invocation
(`U28`, `U32`, `U48`, `U64`, `U200`)
-/
private def routines : List (String × Nat × List (String × Routine)) := [
  ("sha3_224", 28, [
    ("digest", sha3_224_digest), ("digest_slices", sha3_224_digest_slices),
    ("reset", sha3_224_reset),
    ("fixed_finalize_into_reset", sha3_224_fixed_finalize_into_reset),
    ("finalize_fixed_reset", sha3_224_finalize_fixed_reset),
    ("digest_finalize_into_reset", sha3_224_digest_finalize_into_reset),
    ("digest_finalize_reset", sha3_224_digest_finalize_reset)]),
  ("sha3_256", 32, [
    ("digest", sha3_256_digest), ("digest_slices", sha3_256_digest_slices),
    ("reset", sha3_256_reset),
    ("fixed_finalize_into_reset", sha3_256_fixed_finalize_into_reset),
    ("finalize_fixed_reset", sha3_256_finalize_fixed_reset),
    ("digest_finalize_into_reset", sha3_256_digest_finalize_into_reset),
    ("digest_finalize_reset", sha3_256_digest_finalize_reset)]),
  ("sha3_384", 48, [
    ("digest", sha3_384_digest), ("digest_slices", sha3_384_digest_slices),
    ("reset", sha3_384_reset),
    ("fixed_finalize_into_reset", sha3_384_fixed_finalize_into_reset),
    ("finalize_fixed_reset", sha3_384_finalize_fixed_reset),
    ("digest_finalize_into_reset", sha3_384_digest_finalize_into_reset),
    ("digest_finalize_reset", sha3_384_digest_finalize_reset)]),
  ("sha3_512", 64, [
    ("digest", sha3_512_digest), ("digest_slices", sha3_512_digest_slices),
    ("reset", sha3_512_reset),
    ("fixed_finalize_into_reset", sha3_512_fixed_finalize_into_reset),
    ("finalize_fixed_reset", sha3_512_finalize_fixed_reset),
    ("digest_finalize_into_reset", sha3_512_digest_finalize_into_reset),
    ("digest_finalize_reset", sha3_512_digest_finalize_reset)]),
  ("keccak224", 28, [
    ("digest", keccak224_digest), ("digest_slices", keccak224_digest_slices),
    ("reset", keccak224_reset),
    ("fixed_finalize_into_reset", keccak224_fixed_finalize_into_reset),
    ("finalize_fixed_reset", keccak224_finalize_fixed_reset),
    ("digest_finalize_into_reset", keccak224_digest_finalize_into_reset),
    ("digest_finalize_reset", keccak224_digest_finalize_reset)]),
  ("keccak256", 32, [
    ("digest", keccak256_digest), ("digest_slices", keccak256_digest_slices),
    ("reset", keccak256_reset),
    ("fixed_finalize_into_reset", keccak256_fixed_finalize_into_reset),
    ("finalize_fixed_reset", keccak256_finalize_fixed_reset),
    ("digest_finalize_into_reset", keccak256_digest_finalize_into_reset),
    ("digest_finalize_reset", keccak256_digest_finalize_reset)]),
  ("keccak384", 48, [
    ("digest", keccak384_digest), ("digest_slices", keccak384_digest_slices),
    ("reset", keccak384_reset),
    ("fixed_finalize_into_reset", keccak384_fixed_finalize_into_reset),
    ("finalize_fixed_reset", keccak384_finalize_fixed_reset),
    ("digest_finalize_into_reset", keccak384_digest_finalize_into_reset),
    ("digest_finalize_reset", keccak384_digest_finalize_reset)]),
  ("keccak512", 64, [
    ("digest", keccak512_digest), ("digest_slices", keccak512_digest_slices),
    ("reset", keccak512_reset),
    ("fixed_finalize_into_reset", keccak512_fixed_finalize_into_reset),
    ("finalize_fixed_reset", keccak512_finalize_fixed_reset),
    ("digest_finalize_into_reset", keccak512_digest_finalize_into_reset),
    ("digest_finalize_reset", keccak512_digest_finalize_reset)]),
  ("keccak256_full", 200, [
    ("digest", keccak256_full_digest), ("digest_slices", keccak256_full_digest_slices),
    ("reset", keccak256_full_reset),
    ("fixed_finalize_into_reset", keccak256_full_fixed_finalize_into_reset),
    ("finalize_fixed_reset", keccak256_full_finalize_fixed_reset),
    ("digest_finalize_into_reset", keccak256_full_digest_finalize_into_reset),
    ("digest_finalize_reset", keccak256_full_digest_finalize_reset)])
]

/-- Each routine's output size: its type's `OutputSize` -/
private def routineSizes : IO Unit := do
  check "63 routines" ((routines.map fun (_, _, forms) => forms.length).sum == 63)
  for (prefix_, size, forms) in routines do
    for (form, routine) in forms do
      check s!"{prefix_}_{form}: output size" (routine.outputBytes == size)
  IO.println "routine output sizes: 63 passed"

/-- Runs every `sha3` test, throwing on the first failure -/
def run : IO Unit := do
  routineSizes
  let counts := [256, 256, 255, 255, 1, 3, 1, 1]
  let mut jobs := #[]
  for (alg, count) in algorithms.toList.zip counts do
    jobs := jobs.push <| ← IO.asTask (crateVectors alg count)
  for (alg, bits) in ((algorithms.toList.drop 4).take 4).zip [224, 256, 384, 512] do
    jobs := jobs.push <| ← IO.asTask (keccakMessages alg bits "Short" 2048 256)
    jobs := jobs.push <| ← IO.asTask (keccakMessages alg bits "Long" 513 65)
  for job in jobs do
    IO.ofExcept job.get

end Sha3.Tests
