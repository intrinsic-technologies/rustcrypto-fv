import Standards.SECG.ECC
import Standards.NIST.EllipticCurves
import Standards.NIST.SHA2
import Standards.Tests.Utilities

/-!
# SEC 1 tests

ECDSA and ECDH on P-256 against the unmodified RFC 6979 and RFC 5903 texts from
https://www.rfc-editor.org/, and curve, encoding, and subgroup checks on small curves.

| Source            | Vectors             | Checks                                                |
| ----------------- | ------------------- | ----------------------------------------------------- |
| RFC 6979 §A.2.5   | 1 key, 2 signatures | key derivation, point decoding, signing, verification |
| RFC 5903 §8.1     | 2 keys, 1 secret    | key derivation, ECDH in both directions               |
| P-256 edge cases  | —                   | zero scalar, identity point, `−P`, `P + (−P) = O`     |
| Curves over `𝔽₁₇` | —                   | ECDH, ECDSA, supplied `G` and hash, cofactor 2        |
-/

namespace Standards.SECG.ECC.Tests

open Standards.Tests Standards.NIST.SHA2 Standards.SECG.ECC

private def domain := Standards.NIST.EllipticCurves.P256.domain

private def sqrtMod := Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4 domain.p

private def ecdsaVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/RFC/DeterministicSigning/Vectors/rfc6979.txt"
  let vectors := ((← after document "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n").splitOn "\nA.2.6.").head!
  let secret ← value vectors "\n   x = "
  let x ← value vectors "\n   Ux = "
  let y ← value vectors "\n   Uy = "
  let point := Curve.Point.affine (Encoding.octetsToNat x) (Encoding.octetsToNat y)
  check "Public key" (Keys.publicKey domain secret == some point)
  check "Decode uncompressed" (Points.decodePoint domain sqrtMod (⟨#[4]⟩ ++ x ++ y) == some point)
  check "Decode compressed"
    (Points.decodePoint domain sqrtMod (Points.encodePoint domain true point) == some point)
  for message in ["sample", "test"] do
    let vector ← after vectors s!"With SHA-256, message = \"{message}\":"
    let signature := (Encoding.octetsToNat (← value vector "\n   r = "),
      Encoding.octetsToNat (← value vector "\n   s = "))
    let nonce := Encoding.octetsToNat (← value vector "\n   k = ")
    check "ECDSA signature" (ECDSA.signWithNonce domain (Encoding.octetsToNat secret) nonce
      (SHA256.hashBytes message.toUTF8) == some signature)
    check "ECDSA verification" (ECDSA.verify domain SHA256.hashBytes point message.toUTF8 signature)
    check "Reject modified message" (!ECDSA.verify domain SHA256.hashBytes point "wrong".toUTF8 signature)
  IO.println "RFC6979 A.2.5: key, point decoding, ECDSA signing and verification passed"

private def ecdhVectors : IO Unit := do
  let document ← IO.FS.readFile "Standards/SECG/ECC/Vectors/rfc5903.txt"
  let vectors := ((← after document "\n8.1.  256-Bit Random ECP Group\n").splitOn "\n8.2.").head!
  let alice ← value vectors "\ni:\n"
  let bob ← value vectors "\nr:\n"
  let alicePoint := Curve.Point.affine (Encoding.octetsToNat (← value vectors "\ngix:\n"))
    (Encoding.octetsToNat (← value vectors "\ngiy:\n"))
  let bobPoint := Curve.Point.affine (Encoding.octetsToNat (← value vectors "\ngrx:\n"))
    (Encoding.octetsToNat (← value vectors "\ngry:\n"))
  let shared ← value vectors "\ngirx:\n"
  check "RFC5903 Alice keygen" (Keys.publicKey domain alice == some alicePoint)
  check "RFC5903 Bob keygen" (Keys.publicKey domain bob == some bobPoint)
  expectSome "RFC5903 Alice ECDH" (Keys.sharedSecret domain alice bobPoint) shared
  expectSome "RFC5903 Bob ECDH" (Keys.sharedSecret domain bob alicePoint) shared
  IO.println "RFC5903 8.1: both key derivations and ECDH directions passed"

private def boundaries : IO Unit := do
  let generator := domain.G
  check "Zero scalar gives infinity" (Curve.scalarMul domain 0 generator == .infinity)
  check "Identity encoding" (Points.decodePoint domain sqrtMod ⟨#[0]⟩ == some .infinity)
  check "Identity is not a public key" ((Points.decodePublicKey domain sqrtMod ⟨#[0]⟩).isNone)
  let .affine x y := generator | throw (IO.userError "Missing generator")
  let opposite := Curve.Point.affine x (Curve.fieldSub domain.p 0 y)
  check "Inverse points add to infinity" (Curve.add domain generator opposite == .infinity)
  check "Negation of an affine point" (Curve.neg domain generator == opposite)
  check "Negation of infinity" (Curve.neg domain .infinity == .infinity)
  check "Modular exponent zero" (Curve.powMod 17 0 0 == 1)
  check "Generic small curve doubling" (Curve.add ⟨17, 2, 2, .affine 5 1, 19, 1⟩ (.affine 5 1) (.affine 5 1) == .affine 6 3)
  IO.println "Boundary checks passed"

/-- Check that the shared APIs use supplied parameters rather than P-256. -/
private def genericCurves : IO Unit := do
  let sqrtMod := fun (value : Nat) => (List.range 17).find? fun y => y * y % 17 == value
  let domain : Curve.Domain := ⟨17, 2, 2, .affine 5 1, 19, 1⟩
  let secret : ByteArray := ⟨#[1]⟩
  let key := Curve.Point.affine 5 1
  let digest : ByteArray := ⟨#[0]⟩
  let signature := (6, 3)
  check "Generic one-octet key derivation" (Keys.publicKey domain secret == some (.affine 5 1))
  expectSome "Generic one-octet ECDH" (Keys.sharedSecret domain secret key) ⟨#[5]⟩
  check "Generic ECDSA supplied nonce"
    (ECDSA.signWithNonce domain 1 2 digest == some signature)
  check "Generic ECDSA supplied hash"
    (ECDSA.verify domain id key digest signature)
  check "Generic ECDSA uses supplied hash"
    (!ECDSA.verify domain (fun _ => ⟨#[8]⟩) key digest signature)
  check "Generic supplied generator"
    (Keys.publicKey { domain with G := .affine 6 3 } secret == some (.affine 6 3))
  let cofactorDomain : Curve.Domain := ⟨17, 1, 4, .infinity, 7, 2⟩
  check "Accept order-seven public key"
    (Points.decodePublicKey cofactorDomain sqrtMod ⟨#[2, 4]⟩ == some (.affine 4 2))
  check "Decode order-two point"
    (Points.decodePoint cofactorDomain sqrtMod ⟨#[2, 3]⟩ == some (.affine 3 0))
  check "Reject public key outside subgroup"
    (Points.decodePublicKey cofactorDomain sqrtMod ⟨#[2, 3]⟩ == none)
  IO.println "Generic curve, subgroup, and hash checks passed"

def run : IO Unit := do
  ecdsaVectors
  ecdhVectors
  boundaries
  genericCurves

end Standards.SECG.ECC.Tests
