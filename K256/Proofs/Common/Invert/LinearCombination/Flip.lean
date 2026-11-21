import K256.Proofs.Common.Invert.LinearCombination.Core

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

def flipByte (p : Inputs) : BitVec 8 := if v108793 p = 0 then 0 else v1087a3 p

theorem difference_byte (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    v1087a3 p = signByte (sa != sb) := by
  simp only [v1087a3, v1085f2, byte_merge, low_byte,
    byte_extend, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), ha, hb]
  cases sa <;> cases sb <;> rfl

theorem output_mask (p : Inputs) : v1087f7 p = -(flipByte p).setWidth 64 := by
  unfold v1087f7 flipByte
  by_cases h : v108793 p = 0
  · simp only [h, decide_true, ite_true, BitVec.reduceSetWidth, BitVec.neg_zero]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, byte_merge, byte_extend,
      widen_low, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

theorem output_sign (p : Inputs) : resultSign p =
    (v1085e6 p &&& flipByte p) ||| ((flipByte p ^^^ 1) &&& v1085b3 p) := by
  unfold resultSign v108876 v108857 v10885c v108859 flipByte
  by_cases h : v108793 p = 0
  · simp only [h, decide_true, ite_true, byte_merge, BitVec.reduceSetWidth]
    rfl
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, byte_merge, byte_extend,
      widen_low, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]

theorem outputWords_select (p : Inputs) (f : Bool) (hf : flipByte p = signByte f) :
    resultWords p = if f then negativeDifference p else differenceWords p := by
  have m1 : v10880a p = v1087f7 p := rfl
  have m2 : v10881e p = v1087f7 p := rfl
  have m3 : v108832 p = v1087f7 p := rfl
  have m4 : v108849 p = v1087f7 p := rfl
  apply Vector.ext
  intro i hi
  have idx : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases idx with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [resultWords, negativeDifference, differenceWords,
    vector_ite_get, Vector.getElem_mk, Array.reduceGetElem,
    v1087fd, v1087fa, v1087f0, v108810, v10880d, v108807,
    v108824, v108821, v10881b, v108838, v108835, v10882f,
    v10884f, v10884c, v108846, m1, m2, m3, m4, output_mask, hf, select_mask]

theorem flipByte_core (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    flipByte p = signByte (coreFlip (leftWords p) (rightWords p) sa sb) := by
  have hd := congrArg Prod.snd (differenceWords_eq p)
  simp only [selectedWords_eq p sa sb ha hb] at hd
  unfold coreFlip coreDifference
  rw [← hd]
  unfold flipByte
  rw [difference_byte p sa sb ha hb]
  by_cases h : v108793 p = 0
  · simp [h, signByte]
  · cases sa <;> cases sb <;> simp_all [signByte]

theorem resultWords_core (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    resultWords p = coreMagnitude (leftWords p) (rightWords p) sa sb := by
  have hd := congrArg Prod.fst (differenceWords_eq p)
  simp only [selectedWords_eq p sa sb ha hb] at hd
  rw [outputWords_select p _ (flipByte_core p sa sb ha hb), negativeDifference_eq, hd]
  rfl

theorem resultSign_core (p : Inputs) (sa sb : Bool)
    (ha : v1085b3 p = signByte sa) (hb : v1085e6 p = signByte sb) :
    resultSign p = signByte (coreNegative (leftWords p) (rightWords p) sa sb) := by
  rw [output_sign, ha, hb, flipByte_core p sa sb ha hb]
  unfold coreNegative
  cases coreFlip (leftWords p) (rightWords p) sa sb <;> cases sa <;> cases sb <;> rfl

end K256.Proofs.Common.Invert.LinearCombination
