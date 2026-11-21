import K256.Proofs.Common.Invert.LinearCombination.Product

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

theorem byte_extend (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 := by
  simp

theorem low_byte (x : BitVec 32) : (x.setWidth 64).setWidth 8 = x.setWidth 8 := by
  simp
theorem widen_low (x : BitVec 8) : (x.setWidth 64).setWidth 32 = x.setWidth 32 := by
  simp
def signByte (b : Bool) : BitVec 8 := if b then 1 else 0

theorem shift_sign (x : BitVec 64) : x >>> 63 = (signByte x.msb).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [shift63_toNat]
  cases x.msb <;> rfl

theorem select_mask (c : Bool) (a b : BitVec 64) :
    (-(signByte c).setWidth 64 &&& (b ^^^ a)) ^^^ a = if c then b else a := by
  cases c
  · simp [signByte]
  · change (BitVec.allOnes 64 &&& (b ^^^ a)) ^^^ a = b
    simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem left_abs (p : Inputs) : v108516 p = p.u.abs := by
  simp only [v108516, v108513, v108510, v10850d, v108500, v1084f4,
    shift_sign, byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_eq, select_mask, BitVec.abs_eq]

theorem right_abs (p : Inputs) : v108572 p = p.v.abs := by
  simp only [v108572, v108562, v10855f, v10854f, v10853a, v10851c,
    shift_sign, byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
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

end K256.Proofs.Common.Invert.LinearCombination
