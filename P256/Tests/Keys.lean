import Standards.Tests.Utilities
import P256.Spec.Keys
import P256.Tests.Functions
import P256.Tests.Points

/-!
# Tests of the key specifications

The specifications of `Spec/Keys.lean` and `Spec/KeysEncoding.lean`, run by `cd P256 && lake test`,
against:

- the key pair of the crate's own PKCS#8 vectors, the scalar that p256 0.14.0's `tests/pkcs8.rs`
  expects of its private-key file and the point it expects of the public-key file beside it:
  `SecretKey::public_key` derives the point from the scalar;
- p256 0.14.0 `src/test_vectors/group.rs` (`ADD_TEST_VECTORS`, `kG` for `k` = 1 to 20, and
  `MUL_TEST_VECTORS`, 32 pairs `k`, `kG`) and `src/test_vectors/ecdsa.rs` (FIPS 186-4 SigGen, 15
  pairs `d`, `Q`), unmodified: `SecretKey::public_key`;
- SEC 1 v2.0 §2.3.4 and the base point `G` of SP 800-186 §3.2.1.3 (p256 0.14.0 `tests/affine.rs`,
  `UNCOMPRESSED_BASEPOINT`, `COMPRESSED_BASEPOINT`, `COMPACT_BASEPOINT`, `UNCOMPACT_BASEPOINT`):
  `PublicKey::from_sec1_bytes` on every form, the identity, an off-curve point, the hybrid tag, a
  short encoding and `x = p`;
- `Tests/Generated/B-points-small-coordinates.txt`: two points with a small `x` or `y`, from the
  curve equation by `B-points-small-coordinates.py`, independent of the specifications: SEC 1
  §2.3.4's check that each coordinate is below `p` rejects `x + p` and `y + p`;
- the table `Tests/Generated/C-keys-cases.txt`, which
  `Tests/Generated/C-keys-generator/generate.sh` writes byte for byte from the case list
  `C-keys-generator/cases.txt` by running each case natively through the wrappers of
  `P256/program/src/keys.rs` (x86-64 Linux, release), each case by its entry point: its 11 cases of
  `PublicKey::from_sec1_bytes`, the one key function with a theorem, its success and crate failure
  and every SEC 1 form, with the compact tag `05` at 32 and 65 bytes (rejected) beside 33
  (accepted); the table's cases of the other key functions are not checked. Expected values are
  those of the crate, labelled `host`; calls outside an entry's contract (a wrong slice count, or a
  slice that is no value of its Rust argument) are not in the table, and every case checked must
  meet its entry point's argument premise (`Functions.admits`).
-/

namespace P256.Tests.Keys

open Standards.Tests P256.Spec Standards.SECG.ECC

/-- The octets of hexadecimal text -/
def unhex (text : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let rec go : List Char → List UInt8
    | high :: low :: rest => UInt8.ofNat (16 * digit high + digit low) :: go rest
    | _ => []
  ⟨(go text.toList).toArray⟩

/-- Upper-case hexadecimal text of octets -/
def hexText (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map fun byte =>
    let digits := "0123456789ABCDEF".toList
    s!"{digits[byte.toNat / 16]!}{digits[byte.toNat % 16]!}")

/-- The field `text`, or the empty string for `-` -/
def field (text : String) : String := if text == "-" then "" else text

/--
Every case of the table of an entry point with a theorem meets its entry point's argument premise
and gives its status and result; the counts are pinned, and the table's other cases are not checked
-/
def table : IO Unit := do
  let lines := (← IO.FS.readFile "P256/Tests/Generated/C-keys-cases.txt").splitOn "\n" |>.filter
    fun line => !line.startsWith "case " ||
      Functions.all.any fun (entry, _) => line.startsWith s!"case {entry} "
  let mut pool : List (String × ByteArray) := []
  let mut count := 0
  let mut entries : List String := []
  for line in lines do
    match line.splitOn " " with
    | ["input", name, value] => pool := (name, unhex (field value)) :: pool
    | ["case", entry, names, status, label, result] =>
      let inputs ← ((field names).splitOn "+").filter (· != "") |>.mapM fun name =>
        match pool.lookup name with
        | some bytes => pure bytes
        | none => throw (IO.userError s!"unknown input {name}")
      check s!"{entry} on {names}: labelled host" (label == "host")
      check s!"{entry} admits {names}" (Functions.admits entry inputs.toArray)
      let (got, bytes) := match Functions.model entry inputs.toArray with
        | some (some bytes) => ("0", hexText bytes)
        | some none => ("1", "")
        | none => ("?", "")
      check s!"{entry} on {names}" (got == status && bytes == field result)
      count := count + 1
      if !entries.contains entry then entries := entry :: entries
    | [""] => pure ()
    | _ => throw (IO.userError s!"bad line {line}")
  check "the table: 11 cases, 1 entry with a theorem" (count == 11 && entries.length == 1)
  IO.println s!"Key specifications: {count} host cases of PublicKey::from_sec1_bytes passed"

/-- The secret scalar p256's `tests/pkcs8.rs` expects of its private-key vector -/
def vectorSecret : String := "69624171561A63340DE0E7D869F2A05492558E1A04868B6A9F854A866788188D"

/-- The point p256's `tests/pkcs8.rs` expects of its public-key vector, uncompressed -/
def vectorPoint : String :=
  "041CACFFB55F2F2CEFD89D89EB374B2681152452802DEEA09916068137D839CF7F" ++
    "C481A44492304D7EF66AC117BEFE83A8D08F155F2B52F9F618DD447029048E0F"

/-- The key pair of the crate's PKCS#8 vectors through the secret-key functions -/
def vectors : IO Unit := do
  let secret := unhex vectorSecret
  let point := unhex vectorPoint
  check "public_key of the vector's secret is its point" (Keys.publicKeyOfSecret #[secret] == point)
  check "the vector's secret is a secret scalar"
    (Keys.secretOfBytes secret == some (Encoding.octetsToNat secret))
  IO.println "p256 PKCS#8 key pair: public_key and the secret scalar passed"

/-- `SecretKey::public_key` on the crate's group and ECDSA vectors -/
def publicKeys : IO Unit := do
  let kG ← Points.addVectors
  for k in [1:21] do
    check s!"ADD_TEST_VECTORS: public_key({k}) = {k}G"
      (Keys.publicKeyOfSecret #[Encoding.natToOctets 32 k] == kG[k - 1]!)
  let mut multiples := 0
  for (k, expected) in ← Points.mulVectors do
    if Arith.isNonZeroScalar k then
      check "MUL_TEST_VECTORS: public_key(k) = kG" (Keys.publicKeyOfSecret #[k] == expected)
      multiples := multiples + 1
  check "MUL_TEST_VECTORS: 32 scalars in 1..n" (multiples == 32)
  let text ← IO.FS.readFile "P256/Tests/Vectors/p256-0.14.0-test_vectors-ecdsa.rs"
  let blocks := (text.splitOn "TestVector {").drop 1
  check "15 FIPS 186-4 vectors" (blocks.length == 15)
  let field (block name : String) : IO ByteArray := do
    hex (((← after block s!"{name}: &hex!(\"").splitOn "\"").head!)
  for block in blocks do
    let key := ⟨#[4]⟩ ++ (← field block "q_x") ++ (← field block "q_y")
    check "FIPS 186-4: public_key(d) = Q" (Keys.publicKeyOfSecret #[← field block "d"] == key)
  IO.println "public_key: 20 ADD, 32 MUL and 15 FIPS 186-4 vectors passed"

/-- `PublicKey::from_sec1_bytes` and the secret scalar at their edges -/
def encodings : IO Unit := do
  let g ← hex "04 6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
    4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"
  let gc ← hex "03 6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"
  let compact ← hex "05 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c01"
  let uncompact ← hex "04 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c0
    13ca9d8667de0c07aa71d98b3c8065d2e97ab7bb9cb8776bcc0577a7ac58acd4e"
  let p := Operations.domain.p
  let decode (bytes : ByteArray) := Keys.publicKeyFromSec1 #[bytes]
  expectSome "uncompressed G decodes" (decode g) g
  expectSome "compressed G decodes (odd y)" (decode gc) g
  expectSome "the compact form decodes (tests/affine.rs)" (decode compact) uncompact
  let gy := Encoding.octetsToNat (g.extract 33 65)
  expectSome "02 ‖ x(G) decodes to −G = (x, p − y) (SEC 1 §2.3.4)"
    (decode (⟨#[2]⟩ ++ gc.extract 1 33)) (g.extract 0 33 ++ Encoding.natToOctets 32 (p - gy))
  check "the identity 00 is no public key" (decode ⟨#[0]⟩).isNone
  check "an uncompressed point off the curve" (decode (g.set! 64 (g.get! 64 ^^^ 1))).isNone
  check "the hybrid tag 06 is no SEC 1 encoding here" (decode (g.set! 0 6)).isNone
  check "64 bytes of tag 04" (decode (g.extract 0 64)).isNone
  check "compressed x = p is no field element (SEC 1 §2.3.4)"
    (decode (⟨#[2]⟩ ++ Encoding.natToOctets 32 p)).isNone
  check "no bytes" (decode ByteArray.empty).isNone
  -- small coordinates: `x + p` and `y + p` fit in 32 bytes, so the range check rejects them
  let lines := (← IO.FS.readFile "P256/Tests/Generated/B-points-small-coordinates.txt").splitOn "\n"
  let parse (line : String) : IO (ByteArray × ByteArray) := do
    let [x, y] := line.splitOn " " | throw (IO.userError s!"bad line: {line}")
    return (← hex x, ← hex y)
  let plusP (bytes : ByteArray) := Encoding.natToOctets 32 (Encoding.octetsToNat bytes + p)
  let (x₀, y₀) ← parse lines[0]!
  let (x₁, y₁) ← parse lines[1]!
  for (x, y) in [(x₀, y₀), (x₁, y₁)] do
    expectSome "control: from_sec1_bytes of the small-coordinate point" (decode (⟨#[4]⟩ ++ x ++ y))
      (⟨#[4]⟩ ++ x ++ y)
  check "SEC 1 §2.3.4: 04 ‖ x + p ‖ y" (decode (⟨#[4]⟩ ++ plusP x₀ ++ y₀)).isNone
  check "SEC 1 §2.3.4: 04 ‖ x ‖ y + p" (decode (⟨#[4]⟩ ++ x₁ ++ plusP y₁)).isNone
  -- the secret scalar: SEC 1's 1 ≤ d < n on exactly 32 bytes
  let n := Operations.domain.n
  for d in [0, n, 2 ^ 256 - 1] do
    check s!"no secret scalar {d}" (Keys.secretOfBytes (Encoding.natToOctets 32 d) == none)
  for d in [1, n - 1] do
    check s!"control: secret scalar {d}" (Keys.secretOfBytes (Encoding.natToOctets 32 d) == some d)
  check "31 bytes are no secret scalar" (Keys.secretOfBytes (Encoding.natToOctets 31 1) == none)
  IO.println "SEC 1 decoding and secret-key range checks passed"

/-- Runs this module's tests, throwing on the first failure -/
def run : IO Unit := do
  vectors
  publicKeys
  encodings
  table

end P256.Tests.Keys
