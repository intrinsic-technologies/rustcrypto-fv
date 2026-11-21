import Standards.Tests.Utilities
import P256.Spec.Points
import P256.Tests.Functions
import P256.Tests.Points
import P256.Tests.Keys
import P256.Tests.Signatures
import P256.Tests.Extras

/-!
# P-256 tests

`cd P256 && lake test` runs every check of the P-256 specifications, throwing on the first failure.
This module runs the published key, signature and ECDH vectors through the specifications, by entry
name for the 6 entry points with a theorem, then the family modules, each of which states its own
sources and counts:

- here, the secret scalar, `SecretKey::public_key`, `PublicKey::from_sec1_bytes`,
  `Signer::try_sign`, `Verifier::verify` and `ecdh::diffie_hellman`: RFC 6979 §A.2.5 (1 key,
  2 signatures) and RFC 5903 §8.1 (2 keys, 1 secret), unmodified under
  `Standards/RFC/DeterministicSigning/Vectors/` and `Standards/SECG/ECC/Vectors/`; invalid scalars
  and keys, and the compact key form
- `Tests/Points.lean`, `ProjectivePoint::add`: p256 0.14.0 `src/test_vectors/group.rs`; RFC 9380
  points; the group law; `Tests/Generated/B-points.txt`
- `Tests/Keys.lean`, `Keys` and `KeysEncoding`: p256 0.14.0's PKCS#8 key pair, group and FIPS
  186-4 vectors; SEC 1's decoding rules; `Tests/Generated/C-keys-cases.txt` and
  `B-points-small-coordinates.txt`
- `Tests/Signatures.lean`, `Ecdsa`: RFC 6979 §A.2.5; `Tests/Generated/D-ecdsa-cases.txt` and
  `D-ecdsa-native.txt`; the length and range of a raw `r ‖ s` signature (SEC 1 §4.1.4 step 1), and
  Wycheproof's raw-signature (IEEE P1363) vectors
- `Tests/Extras.lean`, `Ecdh` and `Generate`: RFC 5903 §8.1; the native runs of
  `D-ecdsa-native.txt`

Values in `Tests/Generated/` come with the generator that reproduces them. The expected values of
`B-points.txt`, `C-keys-cases.txt` and `D-ecdsa-native.txt` are the crate's own outputs, so they tie
the specifications to p256 0.14.0, not to a standard: a mistake the specification and the crate
share passes them. The published vectors and the independent Python generators of
`B-points-small-coordinates.txt` and `D-ecdsa-cases.txt` check the specifications against outside
sources.
-/

namespace P256.Tests

open Standards.Tests Standards.SECG.ECC P256.Spec

/--
The specification of entry `name` on `args`, which must meet the entry's argument premise:
`some bytes` on success, `none` for the crate's failure
-/
private def call (name : String) (args : Array ByteArray) : IO (Option ByteArray) := do
  check s!"{name}: the arguments meet its premise" (Functions.admits name args)
  match Functions.model name args with
  | some result => pure result
  | none => throw (IO.userError s!"{name}: no specification result")

private def signingVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let vectors :=
    ((← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n").splitOn "\nA.2.6.").head!
  let secret ← value vectors "\n   x = "
  let x ← value vectors "\n   Ux = "
  let y ← value vectors "\n   Uy = "
  let point := Curve.Point.affine (Encoding.octetsToNat x) (Encoding.octetsToNat y)
  let compressed := Points.encodePoint Operations.domain true point
  let uncompressed := ⟨#[4]⟩ ++ x ++ y
  check "RFC6979 secret scalar" (Keys.secretOfBytes secret == some (Encoding.octetsToNat secret))
  check "RFC6979 SecretKey::public_key" (Keys.publicKeyOfSecret #[secret] == uncompressed)
  check "RFC6979 PublicKey::from_sec1_bytes of the compressed key"
    ((← call "publicKeyFromSec1Bytes" #[compressed]) == some uncompressed)
  for message in ["sample", "test"] do
    let vector ← after vectors s!"With SHA-256, message = \"{message}\":"
    let r ← value vector "\n   r = "
    let s ← value vector "\n   s = "
    check "RFC6979 Signer::try_sign"
      ((← call "signingKeyTrySign" #[secret, message.toUTF8]) == some (r ++ s))
    check "RFC6979 Verifier::verify"
      ((← call "verifyingKeyVerify" #[uncompressed, r ++ s, message.toUTF8]).isSome)
    check "Reject modified message"
      ((← call "verifyingKeyVerify" #[uncompressed, r ++ s, "wrong".toUTF8]).isNone)
  IO.println "RFC6979 A.2.5: secret scalar, public_key, from_sec1_bytes, try_sign and verify passed"

private def ecdhVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/SECG/ECC/Vectors/rfc5903.txt"
  let vectors := ((← after document "\n8.1.  256-Bit Random ECP Group\n").splitOn "\n8.2.").head!
  let alice ← value vectors "\ni:\n"
  let bob ← value vectors "\nr:\n"
  let aliceKey := ⟨#[4]⟩ ++ (← value vectors "\ngix:\n") ++ (← value vectors "\ngiy:\n")
  let bobKey := ⟨#[4]⟩ ++ (← value vectors "\ngrx:\n") ++ (← value vectors "\ngry:\n")
  let shared ← value vectors "\ngirx:\n"
  check "RFC5903 Alice public key" (Keys.publicKeyOfSecret #[alice] == aliceKey)
  check "RFC5903 Bob public key" (Keys.publicKeyOfSecret #[bob] == bobKey)
  check "RFC5903 Alice ECDH" ((← call "ecdhDiffieHellman" #[alice, bobKey]) == some shared)
  check "RFC5903 Bob ECDH" ((← call "ecdhDiffieHellman" #[bob, aliceKey]) == some shared)
  IO.println "RFC5903 8.1: both public keys and ECDH directions passed"

private def rejections : IO Unit := do
  let domain := Operations.domain
  let key := Points.encodePoint domain true domain.G
  for scalar in [0, domain.n, 2^256 - 1] do
    let invalid := Encoding.natToOctets 32 scalar
    check "an invalid scalar is no secret scalar" (Keys.secretOfBytes invalid).isNone
  for invalid in [ByteArray.empty, ⟨#[0]⟩, ⟨#[4]⟩ ++ Encoding.natToOctets 32 1,
      ⟨#[2]⟩ ++ Encoding.natToOctets 32 domain.p, ⟨#[2]⟩ ++ Encoding.natToOctets 32 1,
      ⟨#[0]⟩ ++ key.extract 1 33, ⟨#[1]⟩ ++ key.extract 1 33, ⟨#[4]⟩ ++ key.extract 1 33,
      ⟨#[6]⟩ ++ key.extract 1 33, ⟨#[0xFF]⟩ ++ key.extract 1 33] do
    check "PublicKey::from_sec1_bytes rejects an invalid key"
      ((← call "publicKeyFromSec1Bytes" #[invalid]).isNone)
  -- the compact form `05 ‖ x` decodes to the point with that `x` and the smaller of `y` and `p − y`
  let some (.affine gx gy) := some domain.G | throw (IO.userError "G is the identity")
  let compactPoint := Curve.Point.affine gx (min gy (domain.p - gy))
  check "PublicKey::from_sec1_bytes decodes the compact form"
    ((← call "publicKeyFromSec1Bytes" #[⟨#[5]⟩ ++ key.extract 1 33]) ==
      some (Points.encodePoint domain false compactPoint))
  IO.println "Rejection checks passed"

/-- Runs every `p256` test, throwing on the first failure -/
def run : IO Unit := do
  signingVectors
  ecdhVectors
  rejections
  Points.run
  Keys.run
  Signatures.run
  Extras.run

end P256.Tests
