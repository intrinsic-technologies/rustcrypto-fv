import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Product

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86Proofs
open P256.Proofs.Field.Schoolbook (packFour)
open P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

def signByte (b : Bool) : BitVec 8 := if b then 1 else 0

theorem shift_sign (x : BitVec 64) : x >>> 63 = (signByte x.msb).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [P256.Proofs.SecretKeyFromBytes.Scalar.shift63_toNat]
  cases x.msb <;> rfl

theorem select_mask (c : Bool) (a b : BitVec 64) :
    (-(signByte c).setWidth 64 &&& (b ^^^ a)) ^^^ a = if c then b else a := by
  cases c
  · simp [signByte]
  · change (BitVec.allOnes 64 &&& (b ^^^ a)) ^^^ a = b
    simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem left_abs (p : Inputs) : v1b1106 p = p.u.abs := by
  simp only [v1b1106, v1b1103, v1b1100, v1b10fd, v1b10f0, v1b10e4,
    shift_sign, Correction.byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_eq, select_mask, BitVec.abs_eq]

theorem right_abs (p : Inputs) : v1b1162 p = p.v.abs := by
  simp only [v1b1162, v1b1152, v1b114f, v1b113f, v1b112a, v1b110c,
    shift_sign, Correction.byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_eq, select_mask, BitVec.abs_eq]

theorem abs_toNat (x : BitVec 64) : x.abs.toNat = x.toInt.natAbs := by
  have h := x.isLt
  have he := BitVec.toInt_eq_msb_cond x
  have ha := Int.natAbs_eq x.toInt
  rw [BitVec.toNat_abs]
  cases hm : x.msb <;> simp only [hm, Bool.false_eq_true, ite_false, ite_true] at he ⊢
  · omega
  · have hn := BitVec.toInt_neg_of_msb_true hm
    omega

theorem leftWords_value (p : Inputs) :
    wideValue (leftWords p) = p.u.toInt.natAbs * packFour (p.a.map BitVec.toNat) := by
  rw [leftWords_product, left_abs, abs_toNat]

theorem rightWords_value (p : Inputs) :
    wideValue (rightWords p) = p.v.toInt.natAbs * packFour (p.b.map BitVec.toNat) := by
  rw [rightWords_product, right_abs, abs_toNat]

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
