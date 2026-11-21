import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Correct
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Words
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shift.Values

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift

open P256.Proofs.Field.Schoolbook
open P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

theorem shiftedWords_value (p : Inputs) (hs : p.shift.toNat ≤ 64) :
    packFour ((shiftedWords p).map BitVec.toNat) =
      (packFive ((LinearCombination.resultWords p.linear).map BitVec.toNat) /
        2^p.shift.toNat) % 2^256 :=
  P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Words.shiftedWords_value _ _ hs

theorem shiftedWords_magnitude (p : Inputs) (sa sb : Bool)
    (ha : p.linear.aSign = LinearCombination.signByte sa) (hb : p.linear.bSign = LinearCombination.signByte sb)
    (hs : p.shift.toNat ≤ 64) :
    packFour ((shiftedWords p).map BitVec.toNat) =
      ((LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
        LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt).natAbs /
        2^p.shift.toNat) % 2^256 := by
  rw [shiftedWords_value p hs]
  rw [← LinearCombination.resultMagnitude_correct p.linear sa sb ha hb]
  rfl

theorem shiftedWords_signed (p : Inputs) (sa sb : Bool)
    (ha : p.linear.aSign = LinearCombination.signByte sa)
    (hb : p.linear.bSign = LinearCombination.signByte sb)
    (hs : p.shift.toNat ≤ 64)
    (hq : (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt).natAbs /
        2^p.shift.toNat < 2^256)
    (hd : (2 : Int)^p.shift.toNat ∣
      LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
      LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt) :
    LinearCombination.inputValue (shiftedWords p)
      (LinearCombination.resultNegative p.linear sa sb) =
      (LinearCombination.inputValue p.linear.a sa * p.linear.u.toInt +
        LinearCombination.inputValue p.linear.b sb * p.linear.v.toInt) / (2 : Int)^p.shift.toNat := by
  have hm := shiftedWords_magnitude p sa sb ha hb hs
  rw [Nat.mod_eq_of_lt hq, ← LinearCombination.resultMagnitude_correct p.linear sa sb ha hb] at hm
  have hw := LinearCombination.resultWords_correct p.linear sa sb ha hb
  rw [← hw] at hd ⊢
  unfold signedWideValue at hd ⊢
  rw [P256.Proofs.Field.Inverse.SafeGcd.Core.Shift.signed_magnitude_div _ hd]
  simp only [LinearCombination.inputValue, hm]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
