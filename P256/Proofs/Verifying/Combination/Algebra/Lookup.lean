import P256.Proofs.Verifying.Combination.Algebra.Table

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective P256.Proofs.Projective.Multiply.Group
open Table (oddTable oddTableEntry)
open Lean.Grind

theorem selectMagnitude_value (point : Projective) (hp : point.valid)
    (magnitude : Nat) (hm : magnitude = 0 ∨ magnitude % 2 = 1 ∧ magnitude ≤ 15) :
    projectiveValue (selectMagnitude (oddTable point) magnitude)
      (selectMagnitude_correct point hp magnitude hm).1 =
        naturalMultiple (projectiveValue point hp) magnitude := by
  change projectiveValue _ _ = naturalMultiple
    (affineValue point.toAffine (Projective.toAffine_onCurve point hp)) magnitude
  rw [naturalMultiple_affineValue]
  exact (projectiveValue_eq_iff _ _ _ _).mpr (selectMagnitude_correct point hp magnitude hm).2

theorem DigitValid.magnitude {digit : Int} (h : DigitValid digit) :
    digit.natAbs = 0 ∨ digit.natAbs % 2 = 1 ∧ digit.natAbs ≤ 15 := by
  rcases h with hz | h
  · exact Or.inl (by rw [hz]; rfl)
  · exact Or.inr h

theorem signedLookup_valid (point : Projective) (hp : point.valid)
    (digit : Int) (hd : DigitValid digit) :
    (signedLookup (oddTable point) digit).valid := by
  have hm := (selectMagnitude_correct point hp digit.natAbs hd.magnitude).1
  unfold signedLookup
  split
  · exact Projective.negate_valid _ hm
  · exact hm

theorem signedLookup_value (point : Projective) (hp : point.valid)
    (digit : Int) (hd : DigitValid digit) :
    projectiveValue (signedLookup (oddTable point) digit)
      (signedLookup_valid point hp digit hd) = integerMultiple (projectiveValue point hp) digit := by
  cases digit with
  | ofNat n =>
    have hn : ¬(Int.ofNat n < 0) := by change ¬((n : Int) < 0); omega
    simp only [signedLookup, hn, ite_false, integerMultiple]
    exact selectMagnitude_value point hp n hd.magnitude
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by omega
    simp only [signedLookup, hn, ite_true, integerMultiple]
    rw [projectiveValue_negate _ (selectMagnitude_correct point hp _ hd.magnitude).1]
    exact congrArg Neg.neg (selectMagnitude_value point hp (n + 1) hd.magnitude)

theorem addDigit_valid (point acc : Projective) (hp : point.valid) (ha : acc.valid)
    (digit : Int) (hd : DigitValid digit) :
    (addDigit (oddTable point) acc digit).valid := by
  unfold addDigit
  split
  · exact ha
  · exact Projective.add_valid _ _ ha (signedLookup_valid point hp digit hd)

theorem addDigit_value (point acc : Projective) (hp : point.valid) (ha : acc.valid)
    (digit : Int) (hd : DigitValid digit) :
    projectiveValue (addDigit (oddTable point) acc digit)
      (addDigit_valid point acc hp ha digit hd) =
        projectiveValue acc ha + integerMultiple (projectiveValue point hp) digit := by
  by_cases hz : digit = 0
  · subst digit
    simp only [addDigit, ite_true, integerMultiple, naturalMultiple, AddCommMonoid.add_zero]
  · simp only [addDigit, hz, ite_false]
    rw [projectiveValue_add _ _ ha (signedLookup_valid point hp digit hd),
      signedLookup_value point hp digit hd]

end P256.Proofs.Verifying.Combination.Algebra
