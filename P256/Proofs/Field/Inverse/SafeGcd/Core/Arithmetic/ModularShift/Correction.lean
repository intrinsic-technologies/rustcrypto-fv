import Std.Tactic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Correction

theorem corrected_divisible {modulus radix inverse magnitude : Int}
    (invertible : (modulus * inverse) % radix = 1 % radix) :
    radix ∣ magnitude - modulus * ((magnitude * inverse) % radix) := by
  apply Int.dvd_of_emod_eq_zero
  rw [Int.sub_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  have eq : modulus * (magnitude * inverse) = magnitude * (modulus * inverse) := by
    grind only
  rw [eq, Int.mul_emod magnitude, invertible, ← Int.mul_emod, Int.mul_one,
    Int.sub_self, Int.zero_emod]

theorem modular_correction {modulus radix inverse magnitude : Int}
    (modulusPositive : 0 < modulus) (radixPositive : 0 < radix)
    (invertible : (modulus * inverse) % radix = 1 % radix)
    (nonnegative : 0 ≤ magnitude) (bound : magnitude < radix * modulus) :
    let correction := (magnitude * inverse) % radix
    let quotient := (magnitude - modulus * correction) / radix
    (-modulus < quotient ∧ quotient < modulus ∧
      (radix * quotient) % modulus = magnitude % modulus) := by
  let correction := (magnitude * inverse) % radix
  have lower : 0 ≤ correction := Int.emod_nonneg _ (by omega)
  have upper : correction < radix := Int.emod_lt_of_pos _ radixPositive
  have divisible := corrected_divisible (magnitude := magnitude) invertible
  have exactDivision := Int.mul_ediv_cancel_of_dvd divisible
  change radix * ((magnitude - modulus * correction) / radix) =
    magnitude - modulus * correction at exactDivision
  have productNonnegative := Int.mul_nonneg (by omega : 0 ≤ modulus) lower
  have productBound := Int.mul_lt_mul_of_pos_left upper modulusPositive
  refine ⟨?_, ?_, ?_⟩
  · apply Int.lt_of_mul_lt_mul_left (a := radix) _ (by omega)
    rw [exactDivision]
    grind only
  · apply Int.lt_of_mul_lt_mul_left (a := radix) _ (by omega)
    rw [exactDivision]
    omega
  · rw [exactDivision, Int.sub_emod, Int.mul_emod]
    simp

theorem signed_modular_correction {modulus : Nat} (positive : 0 < modulus)
    (x inverse : Int) (shift : Nat)
    (invertible : ((modulus : Int) * inverse) % (2 : Int)^shift = 1 % (2 : Int)^shift)
    (bound : x.natAbs < 2^shift * modulus) :
    let radix : Int := 2^shift
    let correction := ((x.natAbs : Int) * inverse) % radix
    let quotient := ((x.natAbs : Int) - modulus * correction) / radix
    let result := if x < 0 then -quotient else quotient
    result.natAbs < modulus ∧ (radix * result) % modulus = x % modulus := by
  let radix : Int := 2^shift
  let magnitude : Int := x.natAbs
  let correction := (magnitude * inverse) % radix
  let quotient := (magnitude - modulus * correction) / radix
  have hp : 0 < (modulus : Int) := by exact_mod_cast positive
  have hr : 0 < radix := Int.pow_pos (by decide)
  have hm : 0 ≤ magnitude := Int.natCast_nonneg _
  have hb : magnitude < radix * modulus := by
    change (x.natAbs : Int) < (2 : Int)^shift * (modulus : Int)
    exact_mod_cast bound
  have corrected := modular_correction hp hr invertible hm hb
  change -(modulus : Int) < quotient ∧ quotient < modulus ∧
    (radix * quotient) % modulus = magnitude % modulus at corrected
  have absBound : quotient.natAbs < modulus := by
    by_cases nonnegative : 0 ≤ quotient
    · have abs := Int.natAbs_of_nonneg nonnegative
      omega
    · have abs := Int.ofNat_natAbs_of_nonpos (by omega : quotient ≤ 0)
      omega
  change (if x < 0 then -quotient else quotient).natAbs < modulus ∧
    (radix * (if x < 0 then -quotient else quotient)) % modulus = x % modulus
  by_cases negative : x < 0
  · simp only [ite_eq_left negative, Int.natAbs_neg]
    refine ⟨absBound, ?_⟩
    have abs : magnitude = -x := Int.ofNat_natAbs_of_nonpos (by omega)
    have negated := (Int.emod_sub_cancel_left (m := radix * quotient)
      (n := (modulus : Int)) (k := magnitude) 0).mpr corrected.2.2
    simpa only [Int.zero_sub, Int.mul_neg, abs, Int.neg_neg] using negated
  · simp only [ite_eq_right negative]
    refine ⟨absBound, ?_⟩
    have abs : magnitude = x := Int.natAbs_of_nonneg (by omega)
    simpa only [abs] using corrected.2.2

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Correction
