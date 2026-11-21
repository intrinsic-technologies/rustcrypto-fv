import Standards.Tests.Utilities
import P256.Spec.Ecdh
import P256.Spec.Generate
import P256.Tests.Functions

/-!
# Tests of ECDH and random key generation

The specifications of `Spec/Ecdh.lean` and `Generate.lean`, run by `cd P256 && lake test`.

Sources of the expected values:
- RFC 5903 §8.1, unmodified (`Standards/SECG/ECC/Vectors/rfc5903.txt`): 1 exchange, both ways,
  through `ecdh::diffie_hellman`, with the peer's point uncompressed and compressed
- `Tests/Generated/D-ecdsa-native.txt`, native runs of the wrappers on p256 0.14.0, whose cases of
  the entry points with a theorem `Tests/Signatures.lean` checks: here its
  `SigningKey::generate_from_rng` candidates and its ECDH cases with the identity and with a compact
  point, labelled `native run`, are checked against the specifications
- RFC 6979 §A.2.5, unmodified (`Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt`): its key
  `x` and public key `(Ux, Uy)`, the `SigningKey` `SigningKey::generate_from_rng` draws from a zero
  block then `x`; SP 800-186's base point `G`, the verifying key of the scalar 1

`SigningKey::generate_from_rng` has no published vectors: which block it draws rests on the
crate's native runs; the verifying key it computes is checked against RFC 6979's key pair and the
base point.
Where a premise of the contract decides a case (enough random bytes), its check is tested, with a
control.
-/

namespace P256.Tests.Extras

open Standards.Tests Standards.SECG.ECC P256.Spec P256.Spec.Operations

/-- The generator, uncompressed and compressed, from SP 800-186's constants -/
def generator : ByteArray := Points.encodeWith false domain.G
def generatorCompressed : ByteArray := Points.encodeWith true domain.G

/-- The scalar 1, 32 bytes big-endian -/
def one : ByteArray := Encoding.natToOctets 32 1

private def ecdhVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/SECG/ECC/Vectors/rfc5903.txt"
  let vectors := ((← after document "\n8.1.  256-Bit Random ECP Group\n").splitOn "\n8.2.").head!
  let i ← value vectors "\ni:\n"
  let r ← value vectors "\nr:\n"
  let gi := Curve.Point.affine (Encoding.octetsToNat (← value vectors "\ngix:\n"))
    (Encoding.octetsToNat (← value vectors "\ngiy:\n"))
  let gr := Curve.Point.affine (Encoding.octetsToNat (← value vectors "\ngrx:\n"))
    (Encoding.octetsToNat (← value vectors "\ngry:\n"))
  let shared ← value vectors "\ngirx:\n"
  expect "diffie_hellman, initiator" (Ecdh.diffieHellman #[i, Points.encodeWith false gr]) shared
  expect "diffie_hellman, responder" (Ecdh.diffieHellman #[r, Points.encodeWith false gi]) shared
  expect "diffie_hellman, compressed peer point"
    (Ecdh.diffieHellman #[i, Points.encodeWith true gr]) shared
  check "the RFC's arguments meet the premise"
    (Functions.admits "ecdhDiffieHellman" #[i, Points.encodeWith false gr])
  check "the scalar 0 is no NonZeroScalar argument"
    (!Functions.admits "ecdhDiffieHellman" #[Encoding.natToOctets 32 0, generator])
  check "a point off the curve is no AffinePoint argument"
    (!Functions.admits "ecdhDiffieHellman" #[one, generator.set! 64 (generator.get! 64 ^^^ 1)])
  -- native run (`D-ecdsa-native.txt`): the identity gives 32 zero bytes
  check "the identity is an AffinePoint argument"
    (Functions.admits "ecdhDiffieHellman" #[one, ⟨#[0]⟩])
  expect "diffie_hellman with the identity" (Ecdh.diffieHellman #[one, ⟨#[0]⟩])
    (Encoding.natToOctets 32 0)
  expect "control: 1 · G is x(G)" (Ecdh.diffieHellman #[one, generatorCompressed])
    (generator.extract 1 33)
  -- native run (`D-ecdsa-native.txt`): the compact point of p256 0.14.0's `tests/affine.rs`,
  -- which the crate decodes; with the scalar 0xC9, `diffie_hellman` gave status 0 and
  -- `A0CE5E18…41DF`
  let compact ← hex "058e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c01"
  let compactShared ← hex "a0ce5e18834421da231a2de25b75f5887b1178bfd93eea482e32d6baa74841df"
  expect "diffie_hellman decodes the compact form"
    (Ecdh.diffieHellman #[Encoding.natToOctets 32 0xc9, compact]) compactShared
  IO.println "ECDH: RFC 5903 §8.1 both ways, the identity and the compact form passed"

private def generateChecks : IO Unit := do
  let ff : ByteArray := ⟨Array.replicate 32 0xff⟩
  let zero := Encoding.natToOctets 32 0
  let n := Encoding.natToOctets 32 domain.n
  -- native run: `SigningKey::generate_from_rng` reads 32-byte big-endian candidates and keeps the
  -- first in 1..n; the key is that scalar, then its verifying key, here `1·G`, SP 800-186's base
  -- point
  let keyOfOne := one ++ generator
  expect "SigningKey::generate_from_rng of 1" (Generate.generatedSigningKey #[one]) keyOfOne
  expect "SigningKey::generate_from_rng skips zero"
    (Generate.generatedSigningKey #[zero ++ one]) keyOfOne
  expect "SigningKey::generate_from_rng skips n"
    (Generate.generatedSigningKey #[n ++ one]) keyOfOne
  expect "SigningKey::generate_from_rng skips 2^256 − 1"
    (Generate.generatedSigningKey #[ff ++ one]) keyOfOne
  expect "SigningKey::generate_from_rng ignores the bytes after the key"
    (Generate.generatedSigningKey #[one ++ ff]) keyOfOne
  -- RFC 6979 §A.2.5 (unmodified, `Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt`): its
  -- key `x`, drawn after a zero block, then its public key `(Ux, Uy)` uncompressed
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let part ← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n"
  let vectors := (part.splitOn "\nA.2.6.").head!
  let x ← value vectors "\n   x = "
  let ux ← value vectors "\n   Ux = "
  let uy ← value vectors "\n   Uy = "
  check "RFC 6979 A.2.5: a 32-byte key and coordinates" (x.size == 32 && ux.size == 32 &&
    uy.size == 32)
  expect "SigningKey::generate_from_rng of RFC 6979 A.2.5's key writes its public key"
    (Generate.generatedSigningKey #[zero ++ x]) (x ++ ⟨#[4]⟩ ++ ux ++ uy)
  check "the verifying key follows the scalar"
    ((Generate.generatedSigningKey #[zero ++ x]).size == 97)
  -- enough random bytes, the premise
  check "a zero block alone has no nonzero scalar" (!Ecdh.hasRandomNonZeroScalar #[zero])
  check "31 bytes are outside the premise" (!Ecdh.hasRandomNonZeroScalar #[one.extract 0 31])
  check "n then 31 bytes are outside the premise"
    (!Ecdh.hasRandomNonZeroScalar #[n ++ one.extract 0 31])
  check "control: zero then 1" (Ecdh.hasRandomNonZeroScalar #[zero ++ one])
  check "the random bytes are one slice" (Functions.admits "signingKeyGenerateFromRng" #[one] &&
    !Functions.admits "signingKeyGenerateFromRng" #[one, one])
  check "the call's premise needs enough random bytes"
    (!Functions.admits "signingKeyGenerateFromRng" #[zero])
  IO.println "SigningKey::generate_from_rng: candidates and the random premise passed"

/-- Runs this module's tests, throwing on the first failure -/
def run : IO Unit := do
  ecdhVectors
  generateChecks

end P256.Tests.Extras
