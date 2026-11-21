import P256.Proofs.Verifying.Combination.Algebra.Lookup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective P256.Proofs.Projective.Multiply.Group
open Table (oddTable oddTableEntry)
open Lean.Grind

theorem accumulator_valid (p q : Projective) (hp : p.valid) (hq : q.valid)
    (digits : List (Int × Int)) (hd : digitsValid digits) :
    (accumulator (oddTable p) (oddTable q) digits).valid := by
  induction digits with
  | nil => exact Projective.identity_valid
  | cons pair rest ih =>
    have first := hd pair (by simp)
    have tail : digitsValid rest := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    exact addDigit_valid q _ hq
      (addDigit_valid p _ hp (Projective.double_valid _ (ih tail)) pair.1 first.1)
      pair.2 first.2

theorem accumulator_value (p q : Projective) (hp : p.valid) (hq : q.valid)
    (digits : List (Int × Int)) (hd : digitsValid digits) :
    projectiveValue (accumulator (oddTable p) (oddTable q) digits)
      (accumulator_valid p q hp hq digits hd) =
        integerMultiple (projectiveValue p hp) (firstValue digits) +
          integerMultiple (projectiveValue q hq) (secondValue digits) := by
  induction digits with
  | nil =>
    change (0 : CurvePoint) = 0 + 0
    exact (AddCommMonoid.add_zero _).symm
  | cons pair rest ih =>
    have first := hd pair (by simp)
    have tail : digitsValid rest := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have hv := accumulator_valid p q hp hq rest tail
    change projectiveValue
      (addDigit (oddTable q)
        (addDigit (oddTable p) (accumulator (oddTable p) (oddTable q) rest).double pair.1)
        pair.2) _ = _
    rw [addDigit_value q _ hq
      (addDigit_valid p _ hp (Projective.double_valid _ hv) pair.1 first.1) pair.2 first.2,
      addDigit_value p _ hp (Projective.double_valid _ hv) pair.1 first.1,
      projectiveValue_double _ hv, ih tail]
    change _ = integerMultiple (projectiveValue p hp) (pair.1 + 2 * firstValue rest) +
      integerMultiple (projectiveValue q hq) (pair.2 + 2 * secondValue rest)
    rw [integerMultiple_add, integerMultiple_add, integerMultiple_twice, integerMultiple_twice]
    simp only [AddCommMonoid.add_assoc, AddCommMonoid.add_comm, AddCommMonoid.add_left_comm]

theorem accumulator_toAffine (p q : Projective) (hp : p.valid) (hq : q.valid)
    (digits : List (Int × Int)) (hd : digitsValid digits)
    (u v : Nat) (hu : firstValue digits = u) (hv : secondValue digits = v) :
    (accumulator (oddTable p) (oddTable q) digits).toAffine =
      P256.Spec.Points.add (P256.Spec.Points.mul u p.toAffine)
        (P256.Spec.Points.mul v q.toAffine) := by
  have hp' := toAffine_onCurve p hp
  have hq' := toAffine_onCurve q hq
  change _ = Curve.add domain (Curve.scalarMul domain u p.toAffine)
    (Curve.scalarMul domain v q.toAffine)
  rw [scalarMul_eq_multiple domain p256_add_laws p.toAffine hp',
    scalarMul_eq_multiple domain p256_add_laws q.toAffine hq']
  have valid := accumulator_valid p q hp hq digits hd
  apply (projectiveValue_eq_iff _ valid _
    (p256_add_closed _ _ (multiple_onCurve _ p256_add_laws _ hp' u)
      (multiple_onCurve _ p256_add_laws _ hq' v))).mp
  rw [accumulator_value p q hp hq digits hd, hu, hv]
  change naturalMultiple (affineValue p.toAffine hp') u +
    naturalMultiple (affineValue q.toAffine hq') v = _
  rw [naturalMultiple_affineValue, naturalMultiple_affineValue]
  exact (affineValue_add _ _ _ _).symm

end P256.Proofs.Verifying.Combination.Algebra
