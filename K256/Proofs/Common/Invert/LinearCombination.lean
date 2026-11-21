import K256.Proofs.Common.Invert.LinearCombination.Flip

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

theorem signed64_natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2^63 := by
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  rcases Int.natAbs_eq x.toInt with h | h <;> omega
def inputValue (a : Vector (BitVec 64) 4) (negative : Bool) : Int :=
  if negative then -(packFour (a.map BitVec.toNat) : Int) else packFour (a.map BitVec.toNat)

theorem packed_lt (a : Vector (BitVec 64) 4) : packFour (a.map BitVec.toNat) < 2^256 := by
  have h0 := a[0].isLt
  have h1 := a[1].isLt
  have h2 := a[2].isLt
  have h3 := a[3].isLt
  simp only [packFour, Vector.getElem_map]
  omega

theorem products_bound (p : Inputs) :
    wideValue (leftWords p) + wideValue (rightWords p) < 2^320 := by
  have hu := signed64_natAbs_le p.u
  have hv := signed64_natAbs_le p.v
  have ha := packed_lt p.a
  have hb := packed_lt p.b
  have hu' := Nat.mul_le_mul_right (packFour (p.a.map BitVec.toNat)) hu
  have hv' := Nat.mul_le_mul_right (packFour (p.b.map BitVec.toNat)) hv
  have ha' := Nat.mul_lt_mul_of_pos_left ha (by decide : 0 < (2 : Nat)^63)
  have hb' := Nat.mul_lt_mul_of_pos_left hb (by decide : 0 < (2 : Nat)^63)
  rw [leftWords_value, rightWords_value]
  omega

theorem left_effective_sign (p : Inputs) (sa : Bool) (ha : p.aSign = signByte sa) :
    v1085b3 p = signByte (p.u.msb != sa) := by
  simp only [v1085b3, v1084f4, shift_sign, ha,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  cases p.u.msb <;> cases sa <;> rfl

theorem right_effective_sign (p : Inputs) (sb : Bool) (hb : p.bSign = signByte sb) :
    v1085e6 p = signByte (p.v.msb != sb) := by
  simp only [v1085e6, v10851c, shift_sign, hb,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  cases p.v.msb <;> cases sb <;> rfl

theorem signed_natAbs (x : BitVec 64) :
    (if x.msb then -(x.toInt.natAbs : Int) else (x.toInt.natAbs : Int)) = x.toInt := by
  cases h : x.msb
  · simpa only [h, Bool.false_eq_true, ite_false] using
      Int.natAbs_of_nonneg (BitVec.toInt_nonneg_of_msb_false h)
  · have he := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt (BitVec.toInt_neg_of_msb_true h))
    simp only [ite_true, he, Int.neg_neg]

theorem signed_product (x : BitVec 64) (a : Nat) (negative : Bool) :
    (if x.msb != negative then -((x.toInt.natAbs * a : Nat) : Int)
      else ((x.toInt.natAbs * a : Nat) : Int)) =
      (if negative then -(a : Int) else (a : Int)) * x.toInt := by
  calc
    _ = (if negative then -(a : Int) else (a : Int)) *
        (if x.msb then -(x.toInt.natAbs : Int) else (x.toInt.natAbs : Int)) := by
      cases x.msb <;> cases negative <;> simp [Int.mul_comm, Int.mul_neg, Int.neg_mul, Int.neg_neg]
    _ = _ := by rw [signed_natAbs]

theorem signed_left (p : Inputs) (sa : Bool) :
    signedWideValue (leftWords p) (p.u.msb != sa) = inputValue p.a sa * p.u.toInt := by
  simp only [signedWideValue, leftWords_value, inputValue]
  exact signed_product _ _ _

theorem signed_right (p : Inputs) (sb : Bool) :
    signedWideValue (rightWords p) (p.v.msb != sb) = inputValue p.b sb * p.v.toInt := by
  simp only [signedWideValue, rightWords_value, inputValue]
  exact signed_product _ _ _

def resultNegative (p : Inputs) (sa sb : Bool) : Bool :=
  coreNegative (leftWords p) (rightWords p) (p.u.msb != sa) (p.v.msb != sb)

theorem resultSign_correct (p : Inputs) (sa sb : Bool)
    (ha : p.aSign = signByte sa) (hb : p.bSign = signByte sb) :
    resultSign p = signByte (resultNegative p sa sb) :=
  resultSign_core p _ _ (left_effective_sign p sa ha) (right_effective_sign p sb hb)

theorem resultWords_correct (p : Inputs) (sa sb : Bool)
    (ha : p.aSign = signByte sa) (hb : p.bSign = signByte sb) :
    signedWideValue (resultWords p) (resultNegative p sa sb) =
      inputValue p.a sa * p.u.toInt + inputValue p.b sb * p.v.toInt := by
  rw [resultWords_core p _ _ (left_effective_sign p sa ha) (right_effective_sign p sb hb)]
  rw [resultNegative, ← signed_core_value _ _ _ _ (products_bound p), signed_left, signed_right]

theorem resultMagnitude_correct (p : Inputs) (sa sb : Bool)
    (ha : p.aSign = signByte sa) (hb : p.bSign = signByte sb) :
    wideValue (resultWords p) =
      (inputValue p.a sa * p.u.toInt + inputValue p.b sb * p.v.toInt).natAbs := by
  rw [← resultWords_correct p sa sb ha hb]
  unfold signedWideValue
  cases resultNegative p sa sb <;> simp

end K256.Proofs.Common.Invert.LinearCombination
