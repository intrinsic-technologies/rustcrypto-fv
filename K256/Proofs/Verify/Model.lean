import K256.Spec.Ecdsa

namespace K256.Proofs.Verify

open K256.Spec Standards.SECG.ECC Standards.NIST.SHA2
open Standards.SECG.DomainParameters.Secp256k1

def verificationPoint (key : Curve.Point) (digest : ByteArray) (r s : Nat) : Curve.Point :=
  let inv := Curve.inverse domain.n s
  let u := (Encoding.octetsToNat digest % domain.n) * inv % domain.n
  let v := r * inv % domain.n
  Curve.add domain (Curve.scalarMul domain u domain.G) (Curve.scalarMul domain v key)

def affineX : Curve.Point → Nat
  | .infinity => 0
  | .affine x _ => x

theorem verifies_of_decoded {key message signature : ByteArray} {p : Curve.Point} {r s : Nat}
    (hk : Secp256k1.decodePublicKey key = some p)
    (hs : Ecdsa.signatureScalars signature = some (r, s)) :
    Ecdsa.verifies key message signature =
      (decide (s ≤ domain.n / 2) &&
        (affineX (verificationPoint p (SHA256.hashBytes message) r s) % domain.n == r)) := by
  rw [Ecdsa.verifies, hk, hs]
  have bounds : 0 < r ∧ r < domain.n ∧ 0 < s ∧ s < domain.n := by
    unfold Ecdsa.signatureScalars at hs
    dsimp only at hs
    split at hs
    next h => cases hs; exact h.2
    next => contradiction
  have size : (SHA256.hashBytes message).size = 32 :=
    (SHA256 (bytesToBits message)).bytes.size_toArray
  have bits : domain.n.log2 + 1 = 256 := by decide +kernel
  have digest : ECDSA.digestToInt domain.n (SHA256.hashBytes message) =
      Encoding.octetsToNat (SHA256.hashBytes message) := by
    simp only [ECDSA.digestToInt, size, bits]
    exact Nat.div_one _
  have unit : ¬ (r == 0 || decide (r ≥ domain.n) || s == 0 || decide (s ≥ domain.n)) = true := by
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega
  simp only [ECDSA.verify, ECDSA.verifyDigest, unit, Bool.false_eq_true, ↓reduceIte,
    verificationPoint, digest, Nat.mod_mul_mod]
  cases Curve.add domain _ _ with
  | infinity => simp [affineX, Nat.ne_of_lt bounds.1]
  | affine x y => rfl

end K256.Proofs.Verify
