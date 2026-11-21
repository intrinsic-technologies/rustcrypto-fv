import Std
import X86Proofs.Core.Gpr

namespace AesGcm.Proofs

theorem bne_left_comm (a b c : Bool) :
    (a != (b != c)) = (b != (a != c)) := Bool.xor_left_comm a b c

theorem bne_cancel_middle (a b : Bool) :
    (a != (b != a)) = b := by decide +kernel +revert

theorem add_self_eq_shift {w : Nat} (a : BitVec w) : a + a = a <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1
  omega

open X86Proofs

theorem setWidth_mergeGPR {n : Nat} (v : BitVec n) (x : BitVec 64) (hn : n ≤ 64) :
    (mergeGPR n v x).setWidth n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases h32 : n = 32
  · subst n
    simp [mergeGPR, hk]
  · simp only [mergeGPR, h32, ite_false, BitVec.getLsbD_setWidth,
      hk, decide_true, Bool.true_and]
    rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
    simp [hk]
theorem setWidth_mergeGPR_of_le {m n : Nat} (v : BitVec n) (x : BitVec 64)
    (hm : m ≤ n) (hn : n ≤ 64) :
    (mergeGPR n v x).setWidth m = v.setWidth m := by
  rw [← BitVec.setWidth_setWidth_of_le (mergeGPR n v x) hm, setWidth_mergeGPR v x hn]
theorem setWidth_mergeGPR16 (v : BitVec 16) (x : BitVec 64) :
    (mergeGPR 16 v x).setWidth 16 = v :=
  setWidth_mergeGPR v x (by decide)

end AesGcm.Proofs
