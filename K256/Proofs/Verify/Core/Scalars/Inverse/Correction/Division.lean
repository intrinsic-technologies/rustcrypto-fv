import K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Parameters
import K256.Proofs.Common.Invert.ModularShift.Division

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Correction

open Common.Invert.LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open Common.Invert.ModularShift (limbs words productWide productWide_value subWide subWide_value wideValue wideValue_lt limbs_toNat_lt)
open Generate.Generator.Affine.Invert
open X86Proofs
open Common.Invert.ModularShift (signed_magnitude_div)
open Common.Invert.ModularShift.AbsoluteShift (negLow negHigh negWide_value)

theorem correctionWord_divisible (params : Parameters) (magnitude shift : Nat) (hs : shift ≤ 62) :
    (2 : Int)^shift ∣ (magnitude : Int) - (limbs params.modulusWords).toNat *
      ((params.correctionWord magnitude shift).toNat : Int) := by
  rw [params.correctionWord_value magnitude shift (by omega)]
  exact SafeGcd.corrected_divisible (params.inverse_mod_two_pow (by omega))

def correctionProduct (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) :=
  productWide (limbs params.modulusWords) (params.correctionWord (wideValue a ah) shift)

def correctedWords (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) :=
  subWide a (correctionProduct params a ah shift).1 ah (correctionProduct params a ah shift).2

def correctedValue (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) : Int :=
  (wideValue a ah : Int) - (limbs params.modulusWords).toNat * (params.correctionWord (wideValue a ah) shift).toNat

theorem signed_quotient_result (params : Parameters) {a result : Limbs} {ah : BitVec 64} {shift : Nat}
    {negative sign : Bool} {value : Int} (hi : shift ≤ 62)
    (input : value = if negative then -(wideValue a ah : Int) else (wideValue a ah : Int))
    (output : (if sign then -(result.toNat : Int) else (result.toNat : Int)) =
      correctedValue params a ah shift / (2 : Int)^shift)
    (bound : value.natAbs < 2^shift*(limbs params.modulusWords).toNat) :
    (if negative != sign then -(result.toNat : Int) else (result.toNat : Int)).natAbs <
        (limbs params.modulusWords).toNat ∧
      ((2 : Int)^shift*(if negative != sign then -(result.toNat : Int) else (result.toNat : Int))) %
        (limbs params.modulusWords).toNat = value % (limbs params.modulusWords).toNat := by
  have hm : value.natAbs = wideValue a ah := by
    rw [input]
    cases negative <;> simp
  have theoremResult := SafeGcd.signed_modular_correction params.positive
    value params.inverseWord.toNat shift (params.inverse_mod_two_pow (by omega)) bound
  have quotient : correctedValue params a ah shift / (2 : Int)^shift =
      ((value.natAbs : Int)-(limbs params.modulusWords).toNat*(((value.natAbs : Int)*params.inverseWord.toNat)%(2 : Int)^shift)) /
        (2 : Int)^shift := by
    rw [hm,correctedValue,params.correctionWord_value _ _ (by omega)]
  dsimp only at theoremResult
  rw [←quotient] at theoremResult
  have signed : (if value < 0 then -(correctedValue params a ah shift / (2 : Int)^shift)
      else correctedValue params a ah shift / (2 : Int)^shift) =
      if negative != sign then -(result.toNat : Int) else (result.toNat : Int) := by
    by_cases zero : wideValue a ah = 0
    · have valueZero : value = 0 := by rw [input,zero]; cases negative <;> rfl
      have qzero : correctedValue params a ah shift / (2 : Int)^shift = 0 := by
        rw [correctedValue,zero,params.correctionWord_value _ _ (by omega)]
        simp
      rw [qzero] at output
      have resultZero : result.toNat = 0 := by cases sign <;> simp_all
      simp [valueZero,qzero,resultZero]
    · have positive : 0 < (wideValue a ah : Int) := by omega
      cases negative with
      | false =>
        simp only [Bool.false_eq_true,ite_false] at input
        rw [input,ite_eq_right (by omega),←output]
        cases sign <;> rfl
      | true =>
        simp only [ite_true] at input
        rw [input,ite_eq_left (by omega),←output]
        cases sign <;> simp

  rw [signed] at theoremResult
  exact theoremResult

def magnitudeLow (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) : Limbs :=
  let r := correctedWords params a ah shift
  if r.2.2 = 0 then r.1 else negLow r.1

def magnitudeHigh (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) : BitVec 64 :=
  let r := correctedWords params a ah shift
  if r.2.2 = 0 then r.2.1 else negHigh r.1 r.2.1

def correctionNegative (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) : Bool :=
  decide ((correctedWords params a ah shift).2.2 ≠ 0)

theorem correctionProduct_value (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) :
    wideValue (correctionProduct params a ah shift).1 (correctionProduct params a ah shift).2 =
      (limbs params.modulusWords).toNat * (params.correctionWord (wideValue a ah) shift).toNat := by
  exact productWide_value _ _

set_option exponentiation.threshold 320 in
theorem magnitude_signed (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat) :
    (if correctionNegative params a ah shift then
      -(wideValue (magnitudeLow params a ah shift) (magnitudeHigh params a ah shift) : Int)
     else (wideValue (magnitudeLow params a ah shift) (magnitudeHigh params a ah shift) : Int)) =
      correctedValue params a ah shift := by
  have h := subWide_value a (correctionProduct params a ah shift).1 ah (correctionProduct params a ah shift).2
  change (correctedWords params a ah shift).2.2.toNat ≤ 1 ∧
    wideValue (correctedWords params a ah shift).1 (correctedWords params a ah shift).2.1 +
      wideValue (correctionProduct params a ah shift).1 (correctionProduct params a ah shift).2 =
      wideValue a ah + 2^320 * (correctedWords params a ah shift).2.2.toNat at h
  have ha := wideValue_lt a ah
  have hp := wideValue_lt (correctionProduct params a ah shift).1 (correctionProduct params a ah shift).2
  have hr := wideValue_lt (correctedWords params a ah shift).1 (correctedWords params a ah shift).2.1
  have product := correctionProduct_value params a ah shift
  rcases eq_zero_or_one h.1 with hz | ho
  · simp only [correctionNegative, magnitudeLow, magnitudeHigh, hz, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hz] at h
    change _ ∧ _ + _ = _ + 2^320 * 0 at h
    unfold correctedValue
    omega
  · simp only [correctionNegative, magnitudeLow, magnitudeHigh, ho,
      show (1 : BitVec 64) ≠ 0 by decide, show decide ((1 : BitVec 64) ≠ 0) = true by decide, ite_true, ite_false, negWide_value]
    rw [ho] at h
    change _ ∧ _ + _ = _ + 2^320 * 1 at h
    unfold correctedValue
    omega
theorem quotient_bound_signed (params : Parameters) (a : Limbs) (ah : BitVec 64) (shift : Nat)
    (hi : shift ≤ 62) (bound : wideValue a ah < 2^shift*(limbs params.modulusWords).toNat) :
    let m := wideValue (magnitudeLow params a ah shift) (magnitudeHigh params a ah shift)
    m / 2^shift < (limbs params.modulusWords).toNat ∧
    (if correctionNegative params a ah shift then -((m / 2^shift : Nat) : Int)
      else ((m / 2^shift : Nat) : Int)) = correctedValue params a ah shift / (2 : Int)^shift := by
  have signed := magnitude_signed params a ah shift
  have divisible := correctionWord_divisible params (wideValue a ah) shift hi
  change (2 : Int)^shift ∣ correctedValue params a ah shift at divisible
  have quotient := signed_magnitude_div (correctionNegative params a ah shift)
    (magnitude := wideValue (magnitudeLow params a ah shift) (magnitudeHigh params a ah shift))
    (by rw [signed]; exact divisible)
  rw [signed] at quotient
  have boundInt : (wideValue a ah : Int) < (2 : Int)^shift*((limbs params.modulusWords).toNat : Int) := by
    exact_mod_cast bound
  have correction := SafeGcd.modular_correction
    (modulus := ((limbs params.modulusWords).toNat : Int)) (by exact_mod_cast params.positive)
    (Int.pow_pos (by decide : (0 : Int) < 2)) (params.inverse_mod_two_pow (by omega : shift ≤ 64))
    (Int.natCast_nonneg (wideValue a ah)) boundInt
  have corrected : correctedValue params a ah shift = (wideValue a ah : Int) -
      (limbs params.modulusWords).toNat * (((wideValue a ah : Int)*params.inverseWord.toNat) % (2 : Int)^shift) := by
    rw [correctedValue,params.correctionWord_value _ _ (by omega)]
  dsimp only at correction ⊢
  rw [← corrected,quotient] at correction
  refine ⟨?_,quotient.symm⟩
  cases hn : correctionNegative params a ah shift <;>
    simp only [hn,Bool.false_eq_true,ite_false,ite_true] at correction <;> omega

end K256.Proofs.Verify.Core.Scalars.Inverse.Correction
