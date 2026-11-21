import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Final
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Correct
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.ResultArithmetic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open ModularShift
open P256.Proofs.Field.Inverse.SafeGcd

def resultNegative (p : Inputs) (sa sb : Bool) : Bool :=
  LinearCombination.resultNegative p.linear sa sb != decide (v1b1715 p ≠ 0)

theorem resultSign_eq (p : Inputs) (sa sb : Bool)
    (ha : p.linear.aSign = LinearCombination.signByte sa)
    (hb : p.linear.bSign = LinearCombination.signByte sb) :
    resultSign p = LinearCombination.signByte (resultNegative p sa sb) := by
  simp only [resultSign, v1b1930, Support.byte_merge, Correction.low_byte,
    Correction.shrink_byte, LinearCombination.resultSign_correct p.linear sa sb ha hb]
  simp only [resultNegative, ne_eq, decide_not]
  cases LinearCombination.resultNegative p.linear sa sb <;>
    cases decide (v1b1715 p = 0) <;> rfl

theorem wide_value (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) =
      P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.wideValue
        (LinearCombination.resultWords p.linear) := by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue, wideLow, wideHigh, Limbs.toNat,
    P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.wideValue,
    packFive, Vector.getElem_map, P256.Proofs.Field.Montgomery.wordBase]
  omega

theorem result_signed [parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hmod : parameters.modulus = limbs p.modulus)
    (hinv : p.inverse = parameters.inverse) (hi : p.shift.toNat ≤ 62)
    (sa sb : Bool)
    (ha : p.linear.aSign = LinearCombination.signByte sa)
    (hb : p.linear.bSign = LinearCombination.signByte sb)
    (hbound : (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt).natAbs <
        2^p.shift.toNat * parameters.modulus.toNat) :
    packFour ((resultWords p).map BitVec.toNat) < parameters.modulus.toNat ∧
    ((2 : Int)^p.shift.toNat *
      LinearCombination.inputValue (resultWords p) (resultNegative p sa sb)) %
        parameters.modulus.toNat =
      (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
        LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt) %
          parameters.modulus.toNat := by
  have hw : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) <
      2^p.shift.toNat * parameters.modulus.toNat := by
    rw [wide_value, LinearCombination.resultMagnitude_correct p.linear sa sb ha hb]
    exact hbound
  have hq := quotient_value p hmod hinv hi hw
  have hwords := resultWords_eq p (hmod ▸ hq.1) hq.2.1
  have input : LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt =
      if LinearCombination.resultNegative p.linear sa sb then
        -(P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) : Int)
      else (P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) : Int)
        := by
    rw [wide_value]
    exact (LinearCombination.resultWords_correct p.linear sa sb ha hb).symm
  have hs := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.signed_quotient_result hi input hq.2.2
    hbound
  have hp : packFour ((resultWords p).map BitVec.toNat) = (quotientLow p).toNat := by
    rw [hwords, Support.packed_limbs]
    rfl
  refine ⟨hp ▸ hq.1, ?_⟩
  simpa only [LinearCombination.inputValue, resultNegative, hp] using hs.2

theorem correct (p : Inputs) (sa sb : Bool)
    (ha : p.linear.aSign = LinearCombination.signByte sa)
    (hb : p.linear.bSign = LinearCombination.signByte sb)
    (hi : p.shift.toNat ≤ 62)
    (hpositive : 0 < packFour (p.modulus.map BitVec.toNat))
    (hinverse : ((packFour (p.modulus.map BitVec.toNat) : Int) * p.inverse.toNat) %
      (2 : Int)^64 = 1)
    (hbound : (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt).natAbs <
        2^p.shift.toNat * packFour (p.modulus.map BitVec.toNat)) :
    resultSign p = LinearCombination.signByte (resultNegative p sa sb) ∧
    packFour ((resultWords p).map BitVec.toNat) < packFour (p.modulus.map BitVec.toNat) ∧
    ((2 : Int)^p.shift.toNat *
      LinearCombination.inputValue (resultWords p) (resultNegative p sa sb)) %
        packFour (p.modulus.map BitVec.toNat) =
      (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
        LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt) %
          packFour (p.modulus.map BitVec.toNat) := by
  let parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters := {
    modulus := limbs p.modulus
    inverse := p.inverse
    positive := by simpa only [Support.packed_limbs, P256.Proofs.Field.Inverse.SafeGcd.Correction.limbs, limbs] using hpositive
    inverse_spec := by simpa only [Support.packed_limbs, P256.Proofs.Field.Inverse.SafeGcd.Correction.limbs, limbs] using hinverse
      }
  have hmod : parameters.modulus = limbs p.modulus := rfl
  have h := @result_signed parameters p hmod rfl hi sa sb ha hb
    (by simpa only [hmod, Support.packed_limbs, P256.Proofs.Field.Inverse.SafeGcd.Correction.limbs, limbs] using hbound)
  refine ⟨resultSign_eq p sa sb ha hb, ?_⟩
  simpa only [hmod, Support.packed_limbs, P256.Proofs.Field.Inverse.SafeGcd.Correction.limbs, limbs] using h

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic
