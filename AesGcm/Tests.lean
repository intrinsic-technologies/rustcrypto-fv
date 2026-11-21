import AesGcm.Spec.GCM
import Standards.Tests.Utilities

/-!
# `aes-gcm` tests

Executable checks of the crate's AES-GCM specification, `AesGcm.Spec.GCM`, run by
`cd AesGcm && lake test` (`AesGcm` is its own Lake package). The shared SP 800-38D definitions are
tested with the NIST CAVP files in their subject, `Standards.NIST.GCM`; these tests use the crate's
own test data at 0.11.1, kept unmodified in `AesGcm/Tests/Vectors/`:

- `aes128gcm.rs` and `aes256gcm.rs`, the crate's `tests/aes128gcm.rs` and `tests/aes256gcm.rs`
  (SHA-256 `8c1c6361…` and `c474f9b8…`), whose 375 vectors each the crate takes from the CAVP
  files `gcmEncryptExtIV128.rsp` and `gcmEncryptExtIV256.rsp`: encryption gives each vector's
  ciphertext and tag, detached and as ciphertext then tag, and decryption gives its plaintext;
  the crate's `decrypt_modified` and `decrypt_in_place_detached_modified` cases (a changed first
  ciphertext byte; a changed first tag byte together with the associated data replaced by none)
  are rejected, and so are the two changes of the second case made one at a time, each against
  the unchanged vector as its control;
- the four `tests/data/wycheproof-*.blb` files (Wycheproof vectors in the `blobby` format): the
  22 and 21 passing vectors encrypt to their ciphertext, which carries the tag, and decrypt to
  their plaintext; the 27 and 27 failing vectors are rejected. The failing vectors have no
  control: the files do not hold the accepted input each one was changed from.

Every vector has a 12-byte nonce; empty fields, written `b""` in `aes256gcm.rs`, are empty byte
strings. The rejection of a message shorter than the 16-byte tag is checked at 15 bytes, with 16
bytes as the control. No input reaches the crate's limits `P_MAX` (2³⁶ − 32 bytes) and `A_MAX`
(2⁶¹ − 1 bytes), so the `none` branch of `ciphertextAndTag` is not run on a message; no wrapper call
can reach it either, since every region ends below 4 GiB. Instead the specification's two constants
are checked against the crate's `P_MAX` and `A_MAX` and against SP 800-38D, §5.2.1.1's bit bounds,
`supportedLengths` is checked to accept each limit and reject one byte more, and `lengthsSupported`,
the guard of `ciphertextAndTag`, is checked on lengths alone: it accepts each limit, rejects one
byte more of either input, and accepts a plaintext over `P_MAX` but within `A_MAX` as associated
data, which would catch the two limits swapped. The step-1 length check of GCM-AD, which
`authenticPlaintext` uses, is checked in `Standards.NIST.GCM` with small supported lengths. No
message longer than 257 bytes is tested.
-/

namespace AesGcm.Tests

open Standards.Tests AesGcm.Spec.GCM Standards.NIST

/-- A key of `variant`'s length from bytes -/
private def toKey (variant : AES.Variant) (bytes : ByteArray) (label : String) :
    IO (Vector UInt8 variant.keyBytes) := do
  if h : bytes.data.size = variant.keyBytes then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: key of {bytes.size} bytes")

/-- A fixed-size array from bytes -/
private def toVector (bytes : ByteArray) (n : Nat) (label : String) : IO (Vector UInt8 n) := do
  if h : bytes.data.size = n then return ⟨bytes.data, h⟩
  throw (IO.userError s!"{label}: expected {n} bytes, got {bytes.size}")

/-- One authenticated encryption vector -/
private structure TestVector where
  key : ByteArray
  nonce : ByteArray
  aad : ByteArray
  plaintext : ByteArray
  ciphertext : ByteArray
  tag : ByteArray
  deriving Inhabited

/-- Checks encryption and decryption of a vector, detached and with the tag appended -/
private def checkVector (variant : AES.Variant) (v : TestVector) (label : String) : IO Unit := do
  let key ← toKey variant v.key label
  let nonce ← toVector v.nonce 12 label
  let tag ← toVector v.tag 16 label
  let sealed := v.ciphertext ++ v.tag
  check s!"{label}: ciphertext and tag"
    (ciphertextAndTag variant key nonce v.aad v.plaintext == some (v.ciphertext, tag))
  expectSome s!"{label}: plaintext" (authenticPlaintext variant key nonce v.aad v.ciphertext tag)
    v.plaintext
  expectSome s!"{label}: plaintext of ciphertext with tag"
    (authenticPlaintextOfCiphertextWithTag variant key nonce v.aad sealed) v.plaintext

/-- The field `name`, `&hex!("…")` or the empty `b""`, as bytes -/
private def rustField (chunk name : String) : IO ByteArray := do
  if (chunk.splitOn s!"{name}: b\"\"").length > 1 then return .empty
  let tail ← after chunk s!"{name}: &hex!("
  match tail.splitOn "\"" with
  | _ :: value :: _ => hex value
  | _ => throw (IO.userError s!"Missing field {name}")

/-- The `TestVector` literals of one of the crate's test files -/
private def rustVectors (path : String) : IO (Array TestVector) := do
  let text ← IO.FS.readFile path
  let mut result := #[]
  for chunk in (text.splitOn "    TestVector {").drop 1 do
    result := result.push
      { key := ← rustField chunk "key", nonce := ← rustField chunk "nonce",
        aad := ← rustField chunk "aad", plaintext := ← rustField chunk "plaintext",
        ciphertext := ← rustField chunk "ciphertext", tag := ← rustField chunk "tag" }
  return result

/-- `blobby`'s variable-length number at `position`, and the position after it -/
private def readVlq (data : ByteArray) (position : Nat) : IO (Nat × Nat) := do
  let mut position := position
  let mut value := 0
  for step in [:4] do
    let some byte := data[position]? | throw (IO.userError "blobby: unexpected end")
    position := position + 1
    value := if step == 0 then (byte &&& 0x7f).toNat else (value + 1) * 128 + (byte &&& 0x7f).toNat
    if byte &&& 0x80 == 0 then return (value, position)
  throw (IO.userError "blobby: invalid number")

/-- The blobs of a `blobby` 0.4 file, as `blobby::parse_into_vec` reads them -/
private def blobs (data : ByteArray) : IO (Array ByteArray) := do
  let (count, position) ← readVlq data 0
  let (dedupCount, position) ← readVlq data position
  let mut position := position
  let mut dedup := #[]
  for _ in [:dedupCount] do
    let (length, next) ← readVlq data position
    dedup := dedup.push (data.extract next (next + length))
    position := next + length
  let mut result := #[]
  for _ in [:count] do
    let (value, next) ← readVlq data position
    position := next
    if value % 2 == 1 then
      let some blob := dedup[value / 2]? | throw (IO.userError "blobby: invalid index")
      result := result.push blob
    else
      result := result.push (data.extract position (position + value / 2))
      position := position + value / 2
  check "blobby: trailing bytes" (position == data.size)
  return result

/-- The vectors of a Wycheproof file, five blobs each: key, nonce, aad, plaintext, ciphertext -/
private def wycheproof (path : String) : IO (Array (Array ByteArray)) := do
  let all ← blobs (← IO.FS.readBinFile path)
  check s!"{path}: blob count" (all.size % 5 == 0)
  return (Array.range (all.size / 5)).map fun i => all.extract (5 * i) (5 * i + 5)

/-- Checks a passing Wycheproof file: its ciphertext carries the tag -/
private def checkPass (variant : AES.Variant) (path : String) : IO Nat := do
  let all ← wycheproof path
  for v in all, i in [:all.size] do
    let label := s!"{path} vector {i}"
    let key ← toKey variant v[0]! label
    let nonce ← toVector v[1]! 12 label
    expectSome s!"{label}: encrypt"
      ((ciphertextAndTag variant key nonce v[2]! v[3]!).map fun (C, T) => C ++ ⟨T.toArray⟩) v[4]!
    expectSome s!"{label}: decrypt"
      (authenticPlaintextOfCiphertextWithTag variant key nonce v[2]! v[4]!) v[3]!
  return all.size

/-- Checks a failing Wycheproof file: decryption rejects every vector -/
private def checkFail (variant : AES.Variant) (path : String) : IO Nat := do
  let all ← wycheproof path
  for v in all, i in [:all.size] do
    let label := s!"{path} vector {i}"
    let key ← toKey variant v[0]! label
    let nonce ← toVector v[1]! 12 label
    check s!"{label}: rejected"
      (authenticPlaintextOfCiphertextWithTag variant key nonce v[2]! v[4]! == none)
  return all.size

/-- Checks the crate's vectors of one key length, and its two rejection cases -/
private def checkRust (variant : AES.Variant) (path : String) : IO Unit := do
  let all ← rustVectors path
  check s!"{path}: 375 vectors, got {all.size}" (all.size == 375)
  for v in all, i in [:all.size] do
    checkVector variant v s!"{path} vector {i}"
  -- decrypt_modified: the first vector, its first ciphertext byte XORed with 0xaa
  let first := all[0]!
  let key ← toKey variant first.key path
  let nonce ← toVector first.nonce 12 path
  let sealed := first.ciphertext ++ first.tag
  let modified := sealed.set! 0 (sealed[0]! ^^^ 0xaa)
  expectSome s!"{path}: decrypt_modified control"
    (authenticPlaintextOfCiphertextWithTag variant key nonce first.aad sealed) first.plaintext
  check s!"{path}: decrypt_modified"
    (authenticPlaintextOfCiphertextWithTag variant key nonce first.aad modified == none)
  -- decrypt_in_place_detached_modified: the last vector, its associated data replaced by none and
  -- its first tag byte XORed with 0xaa, as the crate's test has it; that changes two fields, so
  -- each change is also checked alone, against the unchanged vector as the control
  let last := all[all.size - 1]!
  let key ← toKey variant last.key path
  let nonce ← toVector last.nonce 12 path
  let tag ← toVector last.tag 16 path
  let modifiedTag := tag.set 0 (tag[0] ^^^ 0xaa)
  check s!"{path}: last vector has associated data" (last.aad.size > 0)
  expectSome s!"{path}: decrypt_in_place_detached_modified control"
    (authenticPlaintext variant key nonce last.aad last.ciphertext tag) last.plaintext
  check s!"{path}: decrypt_in_place_detached_modified"
    (authenticPlaintext variant key nonce ByteArray.empty last.ciphertext modifiedTag == none)
  check s!"{path}: first tag byte changed alone"
    (authenticPlaintext variant key nonce last.aad last.ciphertext modifiedTag == none)
  check s!"{path}: associated data replaced by none alone"
    (authenticPlaintext variant key nonce ByteArray.empty last.ciphertext tag == none)

/-- Runs every `aes-gcm` test, throwing on the first failure -/
def run : IO Unit := do
  -- the length limits, which no input reaches: the specification's constants equal the crate's
  -- `P_MAX = (1 << 36) - 32` and `A_MAX = (1 << 61) - 1` (`aes-gcm` 0.11.1, `src/lib.rs:107-110`),
  -- each is the most whole bytes SP 800-38D, §5.2.1.1 allows (`len(P) ≤ 2^39 − 256` and
  -- `len(A) ≤ 2^64 − 1` bits), and `supportedLengths` accepts exactly the lengths up to them
  check "P_MAX" (maxMessageBytes == (1 <<< 36) - 32)
  check "A_MAX" (maxAssociatedDataBytes == (1 <<< 61) - 1)
  check "P_MAX is the most bytes of SP 800-38D's plaintext bound"
    (8 * maxMessageBytes ≤ 2 ^ 39 - 256 && 8 * (maxMessageBytes + 1) > 2 ^ 39 - 256)
  check "A_MAX is the most bytes of SP 800-38D's associated data bound"
    (8 * maxAssociatedDataBytes ≤ 2 ^ 64 - 1 && 8 * (maxAssociatedDataBytes + 1) > 2 ^ 64 - 1)
  check "supportedLengths.P accepts P_MAX bytes and rejects one more"
    (supportedLengths.P (8 * maxMessageBytes) && !supportedLengths.P (8 * (maxMessageBytes + 1)))
  check "supportedLengths.A accepts A_MAX bytes and rejects one more"
    (supportedLengths.A (8 * maxAssociatedDataBytes)
      && !supportedLengths.A (8 * (maxAssociatedDataBytes + 1)))
  -- the guard of `ciphertextAndTag` on lengths alone: each limit is accepted and one byte more
  -- rejected, for each input separately, and the limits are not swapped
  check "lengthsSupported accepts P_MAX bytes of plaintext and A_MAX bytes of associated data"
    (lengthsSupported maxAssociatedDataBytes maxMessageBytes)
  check "lengthsSupported rejects P_MAX + 1 bytes of plaintext"
    (!lengthsSupported 0 (maxMessageBytes + 1))
  check "lengthsSupported rejects A_MAX + 1 bytes of associated data"
    (!lengthsSupported (maxAssociatedDataBytes + 1) 0)
  check "lengthsSupported accepts P_MAX + 1 bytes of associated data"
    (lengthsSupported (maxMessageBytes + 1) 0)
  -- a message shorter than the tag: 15 bytes are rejected; the control is the 16-byte tag of
  -- the crate's first AES-128 vector, with an empty plaintext, which decrypts
  let first := (← rustVectors "AesGcm/Tests/Vectors/aes128gcm.rs")[0]!
  let key ← toKey .aes128 first.key "short message"
  let nonce ← toVector first.nonce 12 "short message"
  expectSome "16-byte message control"
    (authenticPlaintextOfCiphertextWithTag .aes128 key nonce .empty first.tag) .empty
  check "15-byte message rejected"
    (authenticPlaintextOfCiphertextWithTag .aes128 key nonce .empty (first.tag.extract 0 15)
      == none)
  checkRust .aes128 "AesGcm/Tests/Vectors/aes128gcm.rs"
  checkRust .aes256 "AesGcm/Tests/Vectors/aes256gcm.rs"
  let counts := [← checkPass .aes128 "AesGcm/Tests/Vectors/wycheproof-128_pass.blb",
    ← checkFail .aes128 "AesGcm/Tests/Vectors/wycheproof-128_fail.blb",
    ← checkPass .aes256 "AesGcm/Tests/Vectors/wycheproof-256_pass.blb",
    ← checkFail .aes256 "AesGcm/Tests/Vectors/wycheproof-256_fail.blb"]
  check s!"Wycheproof: 22, 27, 21 and 27 vectors, got {counts}" (counts == [22, 27, 21, 27])
  IO.println "aes-gcm: 750 crate vectors and 97 Wycheproof vectors passed"

end AesGcm.Tests
