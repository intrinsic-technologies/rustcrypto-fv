import P256.Proofs.SignatureFromDer.Model
import P256.Proofs.Projective.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying

open P256.Spec P256.Spec.Operations Standards.SECG.ECC

def verificationPoint (point : Curve.Point) (digest : ByteArray) (r s : Nat) : Curve.Point :=
  let reciprocal := Curve.inverse domain.n s
  Points.add (Points.mul (ECDSA.digestToInt domain.n digest * reciprocal % domain.n) domain.G)
    (Points.mul (r * reciprocal % domain.n) point)

def verificationResult (point : Curve.Point) (r : Nat) : Bool :=
  match point with
  | .infinity => false
  | .affine x _ => x % domain.n == r

theorem verifies_eq (point : Curve.Point) (digest : ByteArray) (r s : Nat)
    (rPositive : 0 < r) (rBound : r < domain.n) (sPositive : 0 < s) (sBound : s < domain.n) :
    Ecdsa.verifies point digest (r, s) = verificationResult (verificationPoint point digest r s) r := by
  simp [Ecdsa.verifies, ECDSA.verifyDigest, Nat.ne_of_gt rPositive,
    Nat.ne_of_gt sPositive, Nat.not_le_of_gt rBound, Nat.not_le_of_gt sBound,
    verificationPoint, verificationResult, Points.add, Points.mul]
  rfl

theorem verificationResult_projective (point : Projective) (r : Nat) (positive : 0 < r) :
    verificationResult point.toAffine r =
      ((if point.z = 0 then 0 else point.x * Curve.inverse domain.p point.z % domain.p) %
        domain.n == r) := by
  by_cases zero : point.z = 0
  · simp [Projective.toAffine, zero, verificationResult, Ne.symm (Nat.ne_of_gt positive)]
  · simp only [Projective.toAffine, zero, ite_false, verificationResult]

theorem decodeSignature_facts {input : ByteArray} {r s : Nat}
    (decoded : Ecdsa.decodeSignature input = some (r, s)) :
    input.size = 64 ∧ 0 < r ∧ r < domain.n ∧ 0 < s ∧ s < domain.n ∧
      r = Arith.uint (input.extract 0 32) ∧ s = Arith.uint (input.extract 32 64) := by
  have size : input.size = 64 := by
    by_cases h : input.size = 64
    · exact h
    · simp [Ecdsa.decodeSignature, h] at decoded
  rw [SignatureFromDer.decodeSignature_eq size] at decoded
  split at decoded
  · rename_i bounds
    cases decoded
    exact ⟨size, bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2, rfl, rfl⟩
  · contradiction

theorem verifyMessage_eq (key signature message : ByteArray) :
    Ecdsa.verifyMessage #[key, signature, message] =
      if Ecdsa.verifies (Ecdsa.keyValue key) (Operations.hash message) (Ecdsa.signatureValue signature)
      then some .empty else none := rfl

theorem verifyMessage_of_decode {key signature message : ByteArray} {point : Curve.Point} {r s : Nat}
    (keyDecoded : Ecdsa.decodePublicKey key = some point)
    (signatureDecoded : Ecdsa.decodeSignature signature = some (r, s)) :
    Ecdsa.verifyMessage #[key, signature, message] =
      if verificationResult (verificationPoint point (Operations.hash message) r s) r
      then some .empty else none := by
  have facts := decodeSignature_facts signatureDecoded
  rw [verifyMessage_eq]
  simp only [Ecdsa.keyValue, keyDecoded, Ecdsa.signatureValue, signatureDecoded, Option.getD_some]
  rw [verifies_eq point _ r s facts.2.1 facts.2.2.1 facts.2.2.2.1 facts.2.2.2.2.1]

theorem verifyMessage_result {key signature message result : ByteArray}
    (verified : Ecdsa.verifyMessage #[key, signature, message] = some result) : result = .empty := by
  rw [verifyMessage_eq] at verified
  split at verified
  · cases verified
    rfl
  · contradiction

theorem verifying_arguments (key signature message : ByteArray) :
    Program.Routines.verifyingKeyVerify.arguments #[key, signature, message] = true ↔
      Ecdsa.isVerifyingKey key = true ∧ Ecdsa.isSignature signature = true := by
  simp [Program.Routines.verifyingKeyVerify, Functions.verifyingKeyVerifyArguments,
    Arith.slices, Arith.anyBytes]

theorem verifying_arguments_decoded {key signature message : ByteArray}
    (arguments : Program.Routines.verifyingKeyVerify.arguments #[key, signature, message] = true) :
    ∃ point r s, Ecdsa.decodePublicKey key = some point ∧
      Ecdsa.decodeSignature signature = some (r, s) ∧ key.size = 65 ∧
      signature.size = 64 ∧ 0 < r ∧ r < domain.n ∧ 0 < s ∧ s < domain.n := by
  obtain ⟨keyValid, signatureValid⟩ := (verifying_arguments key signature message).mp arguments
  cases hk : Ecdsa.decodePublicKey key with
  | none => simp [Ecdsa.isVerifyingKey, hk] at keyValid
  | some point =>
    cases hs : Ecdsa.decodeSignature signature with
    | none => simp [Ecdsa.isSignature, hs] at signatureValid
    | some pair =>
      obtain ⟨r, s⟩ := pair
      have keySize : key.size = 65 := by
        by_cases h : key.size = 65
        · exact h
        · simp [Ecdsa.decodePublicKey, h] at hk
      have facts := decodeSignature_facts hs
      exact ⟨point, r, s, rfl, rfl, keySize, facts.1, facts.2.1, facts.2.2.1,
        facts.2.2.2.1, facts.2.2.2.2.1⟩

end P256.Proofs.Verifying
