import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Core

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

open X86Proofs
open P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

def flipByte (p : Inputs) : BitVec 8 := if v1b1383 p = 0 then 0 else v1b1393 p

theorem difference_byte (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    v1b1393 p = signByte (sa != sb) := by
  simp only [v1b1393, v1b11e2, Support.byte_merge, Correction.low_byte,
    Correction.byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), ha, hb]
  cases sa <;> cases sb <;> rfl

theorem output_mask (p : Inputs) : v1b13e7 p = -(flipByte p).setWidth 64 := by
  unfold v1b13e7 flipByte
  by_cases h : v1b1383 p = 0
  · simp only [h, decide_true, ite_true, BitVec.reduceSetWidth, BitVec.neg_zero]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Support.byte_merge, Correction.byte_extend,
      Correction.widen_low, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

theorem output_sign (p : Inputs) : resultSign p =
    (v1b11d6 p &&& flipByte p) ||| ((flipByte p ^^^ 1) &&& v1b11a3 p) := by
  unfold resultSign v1b1466 v1b1447 v1b144c v1b1449 flipByte
  by_cases h : v1b1383 p = 0
  · simp only [h, decide_true, ite_true, Support.byte_merge, BitVec.reduceSetWidth]
    rfl
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, Support.byte_merge, Correction.byte_extend,
      Correction.widen_low, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

theorem outputWords_select (p : Inputs) (f : Bool) (hf : flipByte p = signByte f) :
    resultWords p = if f then negativeDifference p else differenceWords p := by
  have m1 : v1b13fa p = v1b13e7 p := rfl
  have m2 : v1b140e p = v1b13e7 p := rfl
  have m3 : v1b1422 p = v1b13e7 p := rfl
  have m4 : v1b1439 p = v1b13e7 p := rfl
  apply Vector.ext
  intro i hi
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases idx with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [resultWords, negativeDifference, differenceWords,
    Correction.vector_ite_get, Vector.getElem_mk, Array.reduceGetElem,
    v1b13ed, v1b13ea, v1b13e0, v1b1400, v1b13fd, v1b13f7,
    v1b1414, v1b1411, v1b140b, v1b1428, v1b1425, v1b141f,
    v1b143f, v1b143c, v1b1436, m1, m2, m3, m4, output_mask, hf, select_mask]

theorem flipByte_core (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    flipByte p = signByte (coreFlip (leftWords p) (rightWords p) sa sb) := by
  have hd := congrArg Prod.snd (differenceWords_eq p)
  simp only [selectedWords_eq p sa sb ha hb] at hd
  unfold coreFlip coreDifference
  rw [← hd]
  unfold flipByte
  rw [difference_byte p sa sb ha hb]
  by_cases h : v1b1383 p = 0
  · simp [h, signByte]
  · cases sa <;> cases sb <;> simp_all [signByte]

theorem resultWords_core (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    resultWords p = coreMagnitude (leftWords p) (rightWords p) sa sb := by
  have hd := congrArg Prod.fst (differenceWords_eq p)
  simp only [selectedWords_eq p sa sb ha hb] at hd
  rw [outputWords_select p _ (flipByte_core p sa sb ha hb), negativeDifference_eq, hd]
  rfl

theorem resultSign_core (p : Inputs) (sa sb : Bool)
    (ha : v1b11a3 p = signByte sa) (hb : v1b11d6 p = signByte sb) :
    resultSign p = signByte (coreNegative (leftWords p) (rightWords p) sa sb) := by
  rw [output_sign, ha, hb, flipByte_core p sa sb ha hb]
  unfold coreNegative
  cases coreFlip (leftWords p) (rightWords p) sa sb <;> cases sa <;> cases sb <;> rfl

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
