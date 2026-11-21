import K256.Proofs.Common.Field.Repr
import Std.Tactic

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd

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

def inverseWord : BitVec 64 := 0x27c7f6e22ddacacf

theorem inverse_mod_two_pow {shift : Nat} (bound : shift ≤ 64) :
    ((Common.Field.modulus : Int) * inverseWord.toNat) % (2 : Int)^shift = 1 % (2 : Int)^shift := by
  have divides : (2 : Int)^shift ∣ (2 : Int)^64 := by exact_mod_cast Nat.pow_dvd_pow 2 bound
  rw [← Int.emod_emod_of_dvd _ divides,
    show ((Common.Field.modulus : Int) * inverseWord.toNat) % (2 : Int)^64 = 1 by decide +kernel]

theorem shift_mask {width shift : Nat} (x : BitVec width) (hs : shift ≤ width) :
    (x <<< (width-shift)) >>> (width-shift) = (x.setWidth shift).setWidth width := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < shift
  · have hn : width-shift+i < width := by omega
    simp only [h,hi,hn,decide_true,Bool.true_and,
      show ¬ width-shift+i < width-shift by omega,decide_false,Bool.not_false]
    congr 1
    omega
  · have hn : ¬ width-shift+i < width := by omega
    simp [h,hi,hn]



def correctionWord (magnitude : Nat) (shift : Nat) : BitVec 64 :=
  ((inverseWord * BitVec.ofNat 64 magnitude) <<< (64-shift)) >>> (64-shift)

theorem correctionWord_eq (magnitude shift : Nat) (hs : shift ≤ 64) :
    correctionWord magnitude shift =
      (BitVec.ofNat shift (magnitude * inverseWord.toNat)).setWidth 64 := by
  rw [correctionWord, shift_mask _ hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mul_mod_mod, Nat.mul_comm inverseWord.toNat magnitude,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs)]

theorem correctionWord_value (magnitude shift : Nat) (hs : shift ≤ 64) :
    ((correctionWord magnitude shift).toNat : Int) =
      ((magnitude : Int) * inverseWord.toNat) % (2 : Int)^shift := by
  rw [correctionWord_eq magnitude shift hs, BitVec.toNat_setWidth]
  have hn : (BitVec.ofNat shift (magnitude * inverseWord.toNat)).toNat < 2^64 :=
    Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat]
  simp only [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd
