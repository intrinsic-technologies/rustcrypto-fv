import Std.Tactic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shift

theorem extract_shiftRight_limb {n offset shift : Nat} (x : BitVec n) (hs : shift ≤ 64) :
    (x.extractLsb' offset 64 >>> shift) |||
      (x.extractLsb' (offset+64) 64 <<< (64-shift)) =
      (x >>> shift).extractLsb' offset 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_extractLsb']
  by_cases h : shift + i < 64
  · have hn : i < 64-shift := by omega
    simp only [h,hi,hn,decide_true,Bool.not_true,Bool.false_and,Bool.and_false,
      Bool.true_and,Bool.or_false]
    congr 1
    omega
  · have hn : ¬ i < 64-shift := by omega
    have hr : i-(64-shift)<64 := by omega
    simp only [h,hi,hn,hr,decide_true,decide_false,Bool.not_false,Bool.true_and,
      Bool.false_and,Bool.false_or]
    congr 1
    omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shift
