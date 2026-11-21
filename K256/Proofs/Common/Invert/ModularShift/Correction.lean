import K256.Proofs.Common.Invert.ModularShift.Wide

namespace K256.Proofs.Common.Invert.ModularShift

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

def correctionProduct (a : Limbs) (ah : BitVec 64) (shift : Nat) :=
  productWide prime (correctionWord (wideValue a ah) shift)

def correctedWords (a : Limbs) (ah : BitVec 64) (shift : Nat) :=
  subWide a (correctionProduct a ah shift).1 ah (correctionProduct a ah shift).2

def correctedValue (a : Limbs) (ah : BitVec 64) (shift : Nat) : Int :=
  (wideValue a ah : Int) - prime.toNat * (correctionWord (wideValue a ah) shift).toNat

theorem signed_quotient_result {a result : Limbs} {ah : BitVec 64} {shift : Nat}
    {negative sign : Bool} {value : Int} (hi : shift ≤ 62)
    (input : value = if negative then -(wideValue a ah : Int) else (wideValue a ah : Int))
    (output : (if sign then -(result.toNat : Int) else (result.toNat : Int)) =
      correctedValue a ah shift / (2 : Int)^shift)
    (bound : value.natAbs < 2^shift*prime.toNat) :
    (if negative != sign then -(result.toNat : Int) else (result.toNat : Int)).natAbs <
        prime.toNat ∧
      ((2 : Int)^shift*(if negative != sign then -(result.toNat : Int) else (result.toNat : Int))) %
        prime.toNat = value % prime.toNat := by
  have hm : value.natAbs = wideValue a ah := by
    rw [input]
    cases negative <;> simp
  have theoremResult := K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.signed_modular_correction prime_pos
    value K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.inverseWord.toNat shift (inverse_mod_two_pow (by omega)) bound
  have quotient : correctedValue a ah shift / (2 : Int)^shift =
      ((value.natAbs : Int)-prime.toNat*(((value.natAbs : Int)*K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.inverseWord.toNat)%(2 : Int)^shift)) /
        (2 : Int)^shift := by
    rw [hm,correctedValue,correctionWord_value _ _ (by omega)]
  dsimp only at theoremResult
  rw [←quotient] at theoremResult
  have signed : (if value < 0 then -(correctedValue a ah shift / (2 : Int)^shift)
      else correctedValue a ah shift / (2 : Int)^shift) =
      if negative != sign then -(result.toNat : Int) else (result.toNat : Int) := by
    by_cases zero : wideValue a ah = 0
    · have valueZero : value = 0 := by rw [input,zero]; cases negative <;> rfl
      have qzero : correctedValue a ah shift / (2 : Int)^shift = 0 := by
        rw [correctedValue,zero,correctionWord_value _ _ (by omega)]
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

end K256.Proofs.Common.Invert.ModularShift
