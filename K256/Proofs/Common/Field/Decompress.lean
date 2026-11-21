import K256.Proofs.Common.Arithmetic.CubicNonzero
import K256.Proofs.Common.Field.SqrtChain
import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Common.Field
open Standards.SECG.ECC

private theorem neg_square {r : Nat} (hr : r < modulus) :
    (modulus - r) * (modulus - r) % modulus = r * r % modulus := by
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod, Int.natCast_mul, Int.ofNat_sub (Nat.le_of_lt hr)]
  rw [Int.mul_emod]
  simp only [Int.sub_emod_left]
  rw [← Int.mul_emod, Int.neg_mul_neg]

theorem decompress_eq (tag : UInt8) (x : Nat) :
    K256.Proofs.Sec1.decompress tag x =
      let s := (x * x * x + 7) % modulus
      let r := SqrtChain.result SqrtChain.modSq SqrtChain.modMul s SqrtChain.chain
      if x < modulus ∧ r * r % modulus = s then
        some (Curve.Point.affine x (if r % 2 = tag.toNat % 2 then r else modulus - r))
      else none := by
  let s := (x * x * x + 7) % modulus
  let r := SqrtChain.result SqrtChain.modSq SqrtChain.modMul s SqrtChain.chain
  have hc : s % modulus = s := Nat.mod_mod _ _
  have hs : s ≠ 0 := by
    simpa only [Arithmetic.decompressSquare, show Standards.SECG.DomainParameters.Secp256k1.domain.a = 0 from rfl,
      Nat.zero_mul, Nat.add_zero, show Standards.SECG.DomainParameters.Secp256k1.domain.b = 7 from rfl, s, modulus] using Arithmetic.decompressSquare_ne_zero x
  have hr : r < modulus := by
    dsimp only [r, s]
    rw [SqrtChain.result_modPow]
    exact Nat.mod_lt _ (by decide)
  have hspec : K256.Spec.Secp256k1.sqrtMod s =
      if r * r % modulus = s then some r else none := by
    rw [SqrtChain.sqrtMod_eq, hc]
    rfl
  change (if x ≥ modulus then none else (K256.Spec.Secp256k1.sqrtMod s).bind fun raw =>
      let root := raw % modulus
      let y := if root % 2 == tag.toNat % 2 then root else Curve.fieldSub modulus 0 root
      if y * y % modulus == s && y % 2 == tag.toNat % 2 then some (Curve.Point.affine x y) else none) =
    if x < modulus ∧ r * r % modulus = s then
      some (Curve.Point.affine x (if r % 2 = tag.toNat % 2 then r else modulus - r)) else none
  rw [hspec]
  by_cases hx : x < modulus
  · simp only [Nat.not_le.mpr hx, ite_false, hx, true_and]
    split
    · rename_i hsq
      have hpos : 0 < r := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp only [hz, Nat.zero_mul, Nat.zero_mod] at hsq
        exact hs hsq.symm
      have hneg : Curve.fieldSub modulus 0 r = modulus - r := by
        simp only [Curve.fieldSub, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hr]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [Option.bind_some, Nat.mod_eq_of_lt hr, hneg, beq_iff_eq]
      by_cases he : r % 2 = tag.toNat % 2
      · simp [he, hsq]
      · have hodd : modulus % 2 = 1 := by decide
        have hp : (modulus - r) % 2 = tag.toNat % 2 := by omega
        simp [he, neg_square hr, hsq, hp]
    · rfl
  · simp [hx, Nat.le_of_not_lt hx]

end K256.Proofs.Common.Field
