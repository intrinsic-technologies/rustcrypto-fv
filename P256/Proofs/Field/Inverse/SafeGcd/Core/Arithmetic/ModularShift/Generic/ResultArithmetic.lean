import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.Parameters
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.StageState

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

variable [parameters : Parameters]

open P256.Spec

theorem signed_quotient_result {a result : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {ah : BitVec 64} {shift : Nat}
    {negative sign : Bool} {value : Int} (hi : shift ≤ 62)
    (input : value = if negative then -(wideValue a ah : Int) else (wideValue a ah : Int))
    (output : (if sign then -(result.toNat : Int) else (result.toNat : Int)) =
      correctedValue a ah shift / (2 : Int)^shift)
    (bound : value.natAbs < 2^shift*parameters.modulus.toNat) :
    (if negative != sign then -(result.toNat : Int) else (result.toNat : Int)).natAbs <
        parameters.modulus.toNat ∧
      ((2 : Int)^shift*(if negative != sign then -(result.toNat : Int) else (result.toNat : Int))) %
        parameters.modulus.toNat = value % parameters.modulus.toNat := by
  have hm : value.natAbs = wideValue a ah := by
    rw [input]
    cases negative <;> simp
  have theoremResult := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Correction.signed_modular_correction parameters.positive
    value parameters.inverse.toNat shift (inverse_mod_two_pow (by omega)) bound
  have quotient : correctedValue a ah shift / (2 : Int)^shift =
      ((value.natAbs : Int)-parameters.modulus.toNat*(((value.natAbs : Int)*parameters.inverse.toNat)%(2 : Int)^shift)) /
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

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
