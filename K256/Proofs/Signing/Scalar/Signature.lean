import K256.Proofs.Generate.Curve
import K256.Spec.Ecdsa

namespace K256.Proofs.Signing.Scalar

open K256.Spec Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem signWithNonce_of_coordinates {secret nonce x y : Nat} {digest : ByteArray}
    (secretRange : 0 < secret ∧ secret < domain.n) (nonceRange : 0 < nonce ∧ nonce < domain.n)
    (point : Generate.Curve.generatorWindow nonce = .affine x y) (length : digest.size = 32) :
    let r := x % domain.n
    let e := Encoding.octetsToNat digest % domain.n
    let product := r * secret % domain.n
    let sum := (e + product) % domain.n
    let s := Curve.inverse domain.n nonce * sum % domain.n
    ECDSA.signWithNonce domain secret nonce digest =
      if r = 0 ∨ s = 0 then none else some (r, s) := by
  dsimp only
  have coord := (Generate.Curve.generatorWindow_eq_scalarMul nonce nonceRange.2).symm.trans point
  have bits : domain.n.log2 + 1 = 256 := by decide +kernel
  have digestValue : ECDSA.digestToInt domain.n digest = Encoding.octetsToNat digest := by
    simp [ECDSA.digestToInt, length, bits]
  have reduced (n e r d inv : Nat) :
      inv * ((e % n + (r * d) % n) % n) % n = inv * (e + r * d) % n := by
    rw [← Nat.add_mod, Nat.mul_mod_mod]
  rw [reduced]
  simp [ECDSA.signWithNonce, Nat.ne_of_gt secretRange.1, Nat.ne_of_gt nonceRange.1,
    Nat.not_le_of_lt secretRange.2, Nat.not_le_of_lt nonceRange.2, coord, digestValue]

end K256.Proofs.Signing.Scalar
