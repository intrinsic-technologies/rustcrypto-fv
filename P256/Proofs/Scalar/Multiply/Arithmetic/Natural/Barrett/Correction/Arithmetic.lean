import P256.Proofs.Scalar.Multiply.Arithmetic.Support
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Correction.Defs
import P256.Proofs.Field.Add.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett


open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs adc carry addRaw addRaw_toNat)
open P256.Proofs.SecretKeyFromBytes.Scalar (limbs_toNat_lt eq_zero_or_one)
open P256.Proofs.SecretKeyFromBytes.Scalar (orderBorrow orderBorrow_eq)

theorem correctionResult_addRaw (r : Limbs) (q : BitVec 64) :
    correctionResult r q =
      (addRaw ⟨0xf3b9cac2fc632551 &&& -q, 0xbce6faada7179e84 &&& -q,
        -q, 0xffffffff00000000 &&& -q⟩ r).1 := by
  simp only [correctionResult, addRaw, adc, Bool.toNat_false, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, BitVec.sub_eq_add_neg, BitVec.add_comm r.l2 (-q)]

theorem correctionResult_toNat (r : Limbs) (q : BitVec 64) (hq : q = 0 ∨ q = 1) :
    (correctionResult r q).toNat = (r.toNat + P256.Spec.Operations.domain.n*q.toNat) % 2^256 := by
  have hsum := addRaw_toNat
    (Limbs.mk (0xf3b9cac2fc632551 &&& -q) (0xbce6faada7179e84 &&& -q)
      (-q) (0xffffffff00000000 &&& -q)) r
  rw [← correctionResult_addRaw] at hsum
  have hb := limbs_toNat_lt (correctionResult r q)
  have hm : (Limbs.mk (0xf3b9cac2fc632551 &&& -q) (0xbce6faada7179e84 &&& -q)
      (-q) (0xffffffff00000000 &&& -q)).toNat = P256.Spec.Operations.domain.n*q.toNat := by
    rcases hq with rfl | rfl <;> decide +kernel
  rw [hm] at hsum
  omega

theorem correctionBorrow_eq (a : Limbs) (top : BitVec 64)
    (bound : a.toNat + 2^256 * top.toNat < 2 * P256.Spec.Operations.domain.n) :
    correctionBorrow a top = if a.toNat + 2^256 * top.toNat < P256.Spec.Operations.domain.n then 1 else 0 := by
  have htop : top.toNat ≤ 1 := by
    dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at bound
    omega
  rcases eq_zero_or_one htop with rfl | rfl
  · change correctionBorrow a 0 = if a.toNat < P256.Spec.Operations.domain.n then 1 else 0
    rw [correctionBorrow, orderBorrow_eq]
    split <;> decide +kernel
  · have small : a.toNat < P256.Spec.Operations.domain.n := by
      change a.toNat + 2^256 * 1 < 2 * P256.Spec.Operations.domain.n at bound
      dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at bound ⊢
      omega
    have large : ¬ a.toNat + 2^256 * (1 : BitVec 64).toNat < P256.Spec.Operations.domain.n := by
      change ¬ a.toNat + 2^256 * 1 < P256.Spec.Operations.domain.n
      dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
      omega
    rw [ite_eq_right large, correctionBorrow, orderBorrow_eq, ite_eq_left small]
    decide +kernel

theorem correctionResult_subtractOrder (a : Limbs) (top : BitVec 64)
    (bound : a.toNat + 2^256 * top.toNat < 2 * P256.Spec.Operations.domain.n) :
    (correctionResult (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a)
      (correctionBorrow a top)).toNat =
      P256.Proofs.Scalar.Multiply.Arithmetic.Natural.subtractOrder (a.toNat + 2^256 * top.toNat) := by
  have hdiff := P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder_toNat a
  have hrem := limbs_toNat_lt (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a)
  have hab := limbs_toNat_lt a
  have htop : top.toNat ≤ 1 := by
    dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at bound
    omega
  rw [correctionResult_toNat _ _ (by rw [correctionBorrow_eq a top bound]; split <;> simp)]
  rw [correctionBorrow_eq a top bound, orderBorrow_eq] at *
  unfold P256.Proofs.Scalar.Multiply.Arithmetic.Natural.subtractOrder
  split
  · rename_i small
    have aSmall : a.toNat < P256.Spec.Operations.domain.n := by omega
    rw [ite_eq_left aSmall] at hdiff
    change (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat + P256.Spec.Operations.domain.n =
      a.toNat + 2^256 * 1 at hdiff
    change ((P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat + P256.Spec.Operations.domain.n) % 2^256 =
      a.toNat + 2^256 * top.toNat
    dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at small hdiff bound ⊢
    omega
  · rename_i large
    by_cases aSmall : a.toNat < P256.Spec.Operations.domain.n
    · rw [ite_eq_left aSmall] at hdiff
      change (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat + P256.Spec.Operations.domain.n =
        a.toNat + 2^256 * 1 at hdiff
      change (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat % 2^256 =
        a.toNat + 2^256 * top.toNat - P256.Spec.Operations.domain.n
      rw [Nat.mod_eq_of_lt hrem]
      dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at aSmall large bound hdiff ⊢
      omega
    · rw [ite_eq_right aSmall] at hdiff
      change (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat + P256.Spec.Operations.domain.n =
        a.toNat + 2^256 * 0 at hdiff
      change (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a).toNat % 2^256 =
        a.toNat + 2^256 * top.toNat - P256.Spec.Operations.domain.n
      rw [Nat.mod_eq_of_lt hrem]
      dsimp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at aSmall large bound hdiff ⊢
      omega

theorem correctionResult_barrett {x : Nat} (bound : x < 2^512)
    (a : Limbs) (top : BitVec 64)
    (value : a.toNat + 2^256 * top.toNat = barrettRemainder x) :
    (correctionResult (P256.Proofs.Scalar.Multiply.Arithmetic.Reduction.subtractOrder a)
      (correctionBorrow a top)).toNat = x % P256.Spec.Operations.domain.n := by
  rw [correctionResult_subtractOrder a top (value ▸ barrettRemainder_lt bound), value]
  exact barrett_correct bound

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
