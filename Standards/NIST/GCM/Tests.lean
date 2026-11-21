import Standards.NIST.GCM
import Standards.NIST.AES
import Standards.Tests.Utilities

/-!
# SP 800-38D tests

The §6.1 examples, transcribed from SP 800-38D, and four unmodified response files of
`gcmtestvectors.zip` of the NIST CAVP GCM validation suite, saved in `Vectors/`, from
https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/cavp-testing-block-cipher-modes
(zip SHA-256 `f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023`). `CIPH` is
`Standards.NIST.AES.cipher`.

* §6.1: the examples of `0^s`, ⊕, `LSB_s`, `MSB_s`, `>>`, `[x]_s` and `int`.
* GHASH: the tag of every record of `gcmEncryptExtIV128.rsp`, through the steps of Algorithm 4
  that compute it (1, 2, 4, 5 and 6), written in this file; GHASH of zero blocks, which the
  document excludes, is `0^128`, the start `Y_0 = 0^128` of Algorithm 2 (not a published vector).
* GCM-AE: the ciphertext and tag of every record of `gcmEncryptExtIV128.rsp` and
  `gcmEncryptExtIV256.rsp`.
* GCM-AD, with the largest supported lengths of §5.2.1.1: the plaintext, or `FAIL`, of every
  record of `gcmDecrypt128.rsp` and `gcmDecrypt256.rsp` (4011 and 3919 `FAIL` records).
* GCM-AD step 1: on one record of each decryption file, lengths that admit the record give its
  plaintext, and IV, additional data or ciphertext lengths one step outside the supported ones,
  or a tag one byte shorter, give `FAIL`. These are not published vectors: the expected `FAIL`
  follows from step 1 of Algorithm 5.
* The 32-bit counter wrap: `inc` against §6.2, and GCTR against the three cases (AES-128 and
  AES-256, two or three blocks) of `Generated/gctr-wrap.txt`, which `Generated/generate.py`
  computes with OpenSSL's AES and its own `inc_32` (not published values).

Each response file has 7875 records, with IVs of 8, 96 and 1024 bits, plaintexts of 0 to 408 bits,
additional data of 0 to 720 bits and tags of 32 to 128 bits, all whole bytes. The 192-bit key
files are not used. No published vector exercises the 32-bit counter wrapping in GCTR, a
ciphertext over one block of `inc_32` steps, a length outside the supported ones, or a tag length
other than the record lengths. SHA-256 of the files used:

* `gcmEncryptExtIV128.rsp`: `30156236f768b0d81e58a3e5bd3bd79ce294cf9ef0ba0a84cf7b869c89ebd9fd`
* `gcmEncryptExtIV256.rsp`: `4448b4998c3f58cd9f5542ddf7c573189a721ff3d3ac24cd5177bb4910a787f8`
* `gcmDecrypt128.rsp`: `0d1f98d0c9e176ede1f3e85484dd13de92c3436ca97df378ec3481e04c19a732`
* `gcmDecrypt256.rsp`: `ed318735a517d5a85c82d2846c23dcf56e57a352fb0f0a163d9e7617a7bd12ad`
-/

namespace Standards.NIST.GCM.Tests

open Standards.Tests Standards.NIST.GCM

-- §6.1: 0^8 = 00000000
#guard zeros 8 == #v[false, false, false, false, false, false, false, false]
-- §6.1: 10011 ⊕ 10101 = 00110
#guard xor #v[true, false, false, true, true] #v[true, false, true, false, true] ==
  #v[false, false, true, true, false]
-- §6.1: LSB_3(111011010) = 010 and MSB_4(111011010) = 1110
#guard LSB 3 (k := 6) #v[true, true, true, false, true, true, false, true, false] ==
  #v[false, true, false]
#guard MSB 4 (k := 5) #v[true, true, true, false, true, true, false, true, false] ==
  #v[true, true, true, false]
-- §6.1: 0110111 >> 1 = 0011011
#guard rightShift #v[false, true, true, false, true, true, true] ==
  #v[false, false, true, true, false, true, true]
-- FIPS 197-upd1 §3.2: the byte {a3} is the bit sequence 10100011
#guard bitsOfBytes #v[(0xa3 : UInt8)] == #v[true, false, true, false, false, false, true, true]
#guard bytesOfBits (k := 1) #v[true, false, true, false, false, false, true, true] == #v[0xa3]

private def toVector (bytes : ByteArray) (n : Nat) (label : String) : IO (Vector UInt8 n) := do
  if h : bytes.data.size = n then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: expected {n} bytes, got {bytes.size}")

/-- The 16-byte blocks of `bytes` followed by zero bytes to a multiple of 16, as bit strings -/
private def paddedBlocks (bytes : ByteArray) : Array (Vector Bool 128) :=
  let padded := bytes ++ ByteArray.mk (Array.replicate ((16 - bytes.size % 16) % 16) 0)
  (Array.range (padded.size / 16)).map fun i =>
    bitsOfBytes (Vector.ofFn fun j : Fin 16 => padded[16 * i + j.val]!)

/-- `[x]_64`, as 8 bytes, most significant first -/
private def word64 (x : Nat) : ByteArray :=
  ByteArray.mk ((Array.range 8).map fun i => (x / 2 ^ (8 * (7 - i)) % 256).toUInt8)

/-- The block `[len(A)]_64 || [len(C)]_64` of two byte strings' bit lengths -/
private def lengthBlock (A C : ByteArray) : Vector Bool 128 :=
  (paddedBlocks (word64 (8 * A.size) ++ word64 (8 * C.size)))[0]!

/-- The field `name =` of a record, as bytes; an empty value is no bytes -/
private def field (record : List String) (name : String) : IO ByteArray := do
  match record.find? (·.startsWith s!"{name} =") with
  | some line => hex ((line.drop (name.length + 2)).toString)
  | none => throw (IO.userError s!"Missing field {name}")

/-- Checks one record's tag; `label` names it in a failure -/
private def checkRecord (record : List String) (label : String) : IO Unit := do
  let key ← toVector (← field record "Key") 16 label
  let IV ← field record "IV"
  let A ← field record "AAD"
  let C ← field record "CT"
  let tag ← field record "Tag"
  let cipher := fun block => bitsOfBytes (Standards.NIST.AES.cipher .aes128 key block)
  let H := cipher (Vector.replicate 16 0)
  let J0 :=
    if IV.size = 12 then bytesOfBits (k := 16) ((paddedBlocks (IV ++ ⟨#[0, 0, 0, 1]⟩))[0]!)
    else bytesOfBits (GHASH H (paddedBlocks IV ++ paddedBlocks (word64 0 ++ word64 (8 * IV.size))))
  let S := GHASH H (paddedBlocks A ++ paddedBlocks C ++ #[lengthBlock A C])
  let T := (bytesOfBits (k := 16) (xor (cipher J0) S)).toArray.extract 0 tag.size
  check s!"{label}: tag" (ByteArray.mk T == tag)

/-- Runs the GHASH tests, throwing on the first failure -/
private def runGHASH : IO Unit := do
  check "GHASH of no blocks is 0^128" (GHASH (zeros 128) #[] == zeros 128)
  let text ← IO.FS.readFile "Standards/NIST/GCM/Vectors/gcmEncryptExtIV128.rsp"
  let lines := (text.splitOn "\n").map fun line => line.trimAscii.toString
  let mut count := 0
  let mut record : List String := []
  for line in lines ++ [""] do
    if line.isEmpty then
      if record.any (·.startsWith "Count = ") then
        checkRecord record.reverse s!"gcmEncryptExtIV128.rsp record {count + 1}"
        count := count + 1
      record := []
    else
      record := line :: record
  check s!"gcmEncryptExtIV128.rsp: 7875 records, got {count}" (count == 7875)
  IO.println s!"SP800-38D: §6.1 examples and the {count} CAVP gcmEncryptExtIV128 tags passed"


-- §6.1: [39]_8 = 00100111
#guard integerToString 8 39 == #v[false, false, true, false, false, true, true, true]
-- §6.1: int(00011010) = 26
#guard int #v[false, false, false, true, true, false, true, false] == 26

/-- The bit string of a byte string -/
private def bits (bytes : ByteArray) : Vector Bool (8 * bytes.size) :=
  bitsOfBytes ⟨bytes.data, rfl⟩

/-- The byte string of a bit string of whole bytes -/
private def bytes (bits : Vector Bool (8 * k)) : ByteArray := ⟨(bytesOfBits bits).toArray⟩

/-- The AES forward cipher under a 16- or 32-byte key as a function on blocks -/
private def forwardCipher (key : ByteArray) (label : String) :
    IO (Vector Bool 128 → Vector Bool 128) := do
  if h : key.data.size = 16 then
    return fun X => bitsOfBytes (Standards.NIST.AES.cipher .aes128 ⟨key.data, h⟩ (bytesOfBits X))
  if h : key.data.size = 32 then
    return fun X => bitsOfBytes (Standards.NIST.AES.cipher .aes256 ⟨key.data, h⟩ (bytesOfBits X))
  throw (IO.userError s!"{label}: key of {key.size} bytes")

/-- The tag length in bits of a tag of at most 16 bytes -/
private def tagLength (tag : ByteArray) : Option (Fin 129) :=
  if h : 8 * tag.size < 129 then some ⟨8 * tag.size, h⟩ else none

/-- The records of a response file, each as its lines -/
private def records (path : String) : IO (Array (List String)) := do
  let text ← IO.FS.readFile path
  let mut result := #[]
  let mut record : List String := []
  for line in (text.splitOn "\n").map (·.trimAscii.toString) ++ [""] do
    if line.isEmpty then
      if record.any (·.startsWith "Count = ") then result := result.push record.reverse
      record := []
    else
      record := line :: record
  return result

/-- Checks every record of an encryption response file through GCM-AE -/
private def checkEncryptFile (path : String) : IO Nat := do
  let all ← records path
  for record in all, i in [:all.size] do
    let label := s!"{path} record {i + 1}"
    let CIPH ← forwardCipher (← field record "Key") label
    let tag ← field record "Tag"
    let some t := tagLength tag | throw (IO.userError s!"{label}: tag length")
    let (C, T) := GCM_AE CIPH t (bits (← field record "IV")) (bits (← field record "PT"))
      (bits (← field record "AAD"))
    check s!"{label}: ciphertext" (bytes C == (← field record "CT"))
    check s!"{label}: tag" (T.toList == (bits tag).toList)
  return all.size

/-- Checks every record of a decryption response file through GCM-AD -/
private def checkDecryptFile (path : String) : IO (Nat × Nat) := do
  let all ← records path
  let mut failures := 0
  for record in all, i in [:all.size] do
    let label := s!"{path} record {i + 1}"
    let CIPH ← forwardCipher (← field record "Key") label
    let tag ← field record "Tag"
    let some t := tagLength tag | throw (IO.userError s!"{label}: tag length")
    let P := GCM_AD CIPH t .maximum (bits (← field record "IV")) (bits (← field record "CT"))
      (bits (← field record "AAD")) (bits tag)
    if record.contains "FAIL" then
      failures := failures + 1
      check s!"{label}: FAIL" P.isNone
    else
      check s!"{label}: plaintext" (P.map bytes == some (← field record "PT"))
  return (all.size, failures)

/--
Checks step 1 of GCM-AD, the length check, on the first record of `path` that is not `FAIL` and
has a 96-bit IV, a ciphertext and associated data: with supported lengths that admit exactly the
record's IV, ciphertext and associated data lengths, or with the largest supported lengths, it
gives the record's plaintext; with the IV length, the associated data length or the ciphertext
length one step outside the supported ones, or a tag length one byte shorter than the record's,
it gives `FAIL`. Returns the number of `FAIL` cases checked.
-/
private def checkStepOne (path : String) : IO Nat := do
  let all ← records path
  let some record ← all.findM? fun record => do
      return !record.contains "FAIL" && (← field record "IV").size == 12 &&
        (← field record "CT").size > 0 && (← field record "AAD").size > 0
    | throw (IO.userError s!"{path}: no record for the step-1 checks")
  let label := s!"{path} step 1"
  let CIPH ← forwardCipher (← field record "Key") label
  let IV ← field record "IV"
  let C ← field record "CT"
  let A ← field record "AAD"
  let tag ← field record "Tag"
  let some t := tagLength tag | throw (IO.userError s!"{label}: tag length")
  let PT ← field record "PT"
  let exact : SupportedLengths :=
    { IV := (· == 8 * IV.size), P := (· ≤ 8 * C.size), A := (· ≤ 8 * A.size) }
  let decrypt := fun (supported : SupportedLengths) (t : Fin 129) =>
    (GCM_AD CIPH t supported (bits IV) (bits C) (bits A) (bits tag)).map bytes
  check s!"{label}: largest supported lengths control" (decrypt .maximum t == some PT)
  check s!"{label}: exactly supported lengths control" (decrypt exact t == some PT)
  check s!"{label}: IV length unsupported"
    (decrypt { exact with IV := (· == 8 * IV.size + 8) } t).isNone
  check s!"{label}: ciphertext length unsupported"
    (decrypt { exact with P := (· < 8 * C.size) } t).isNone
  check s!"{label}: associated data length unsupported"
    (decrypt { exact with A := (· < 8 * A.size) } t).isNone
  let some shorter := (if h : t.val - 8 < 129 then some (⟨t.val - 8, h⟩ : Fin 129) else none)
    | throw (IO.userError s!"{label}: tag length")
  check s!"{label}: tag length other than t" (decrypt exact shorter).isNone
  return 4

/-- Checks every case of `Generated/gctr-wrap.txt`: GCTR across the 32-bit counter wrap -/
private def checkGCTRWrap : IO Nat := do
  let path := "Standards/NIST/GCM/Generated/gctr-wrap.txt"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  for line in lines, i in [:lines.length] do
    let label := s!"{path} case {i + 1}"
    let record := line.splitOn " "
    let value := fun name => field (record.map (·.replace "=" " = ")) name
    let CIPH ← forwardCipher (← value "key") label
    let ICB ← value "icb"
    let some ICB := (if h : 8 * ICB.size = 128 then some ((bits ICB).cast h) else none)
      | throw (IO.userError s!"{label}: initial counter block of {ICB.size} bytes")
    let X ← value "x"
    check s!"{label}: GCTR across the wrap" (bytes (GCTR CIPH ICB (bits X)) == (← value "y"))
  return lines.length

/--
Runs every test of this subject, throwing on the first failure: the GHASH tests, then those of
GCTR, GCM-AE and GCM-AD
-/
def run : IO Unit := do
  runGHASH
  -- §6.2 at the wrap, from the definition (not a published vector): the low 32 bits of
  -- 0x00..01 ffffffff become 0, the bits to their left are unchanged
  let wrapped := inc 32 (k := 96) (bits ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0xff, 0xff, 0xff, 0xff]⟩ |>.cast (by decide))
  check "inc_32 wraps the counter" (bytes (k := 16) (wrapped.cast (by decide)) ==
    ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]⟩)
  -- GCTR across the wrap, against values computed outside these definitions (not published)
  let wraps ← checkGCTRWrap
  check s!"gctr-wrap.txt: 3 cases, got {wraps}" (wraps == 3)
  let e128 ← checkEncryptFile "Standards/NIST/GCM/Vectors/gcmEncryptExtIV128.rsp"
  check s!"gcmEncryptExtIV128.rsp: 7875 records, got {e128}" (e128 == 7875)
  let e256 ← checkEncryptFile "Standards/NIST/GCM/Vectors/gcmEncryptExtIV256.rsp"
  check s!"gcmEncryptExtIV256.rsp: 7875 records, got {e256}" (e256 == 7875)
  let (d128, f128) ← checkDecryptFile "Standards/NIST/GCM/Vectors/gcmDecrypt128.rsp"
  check s!"gcmDecrypt128.rsp: 7875 records and 4011 FAIL, got {d128} and {f128}"
    (d128 == 7875 && f128 == 4011)
  let (d256, f256) ← checkDecryptFile "Standards/NIST/GCM/Vectors/gcmDecrypt256.rsp"
  check s!"gcmDecrypt256.rsp: 7875 records and 3919 FAIL, got {d256} and {f256}"
    (d256 == 7875 && f256 == 3919)
  -- step 1 of GCM-AD with small supported lengths, since no record has an unsupported length
  let s128 ← checkStepOne "Standards/NIST/GCM/Vectors/gcmDecrypt128.rsp"
  let s256 ← checkStepOne "Standards/NIST/GCM/Vectors/gcmDecrypt256.rsp"
  check s!"GCM-AD step 1: 4 and 4 FAIL cases, got {s128} and {s256}" (s128 == 4 && s256 == 4)
  IO.println
    ("SP800-38D GCTR, GCM-AE, GCM-AD: §6.1 examples, 3 GCTR wrap cases, 31500 CAVP records "
      ++ "and 8 GCM-AD step-1 cases passed")

end Standards.NIST.GCM.Tests
