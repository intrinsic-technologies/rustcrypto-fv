import X86Proofs.Instructions.Sub.Operation

set_option autoImplicit false
open X86Proofs

namespace P256.Proofs.Common.Instructions
open X86 X86.Machine X86.UserProcess X86.Helpers
set_option maxHeartbeats 800000 in
theorem neg_operation {σ : Type} {n : Nat} (hsize : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (s : X86.State σ) (x : BitVec n) :
    (X86.Instructions.Operations.NEG n x).run s =
      (.ok (-x), setFlags s (subSpec 0 x).2) := by
  rcases hsize with rfl | rfl | rfl | rfl
  all_goals
    have hn : BitVec.ofInt _ (-(x.toNat : Int)) = -x := by
      simp [BitVec.ofInt_neg]
    have ha : max (-(x.toNat : Int) % 16) 0 = -((x.toNat : Int) % 16) ↔
        ¬ 0 < x.toNat % 16 := by omega
    have hc : x = BitVec.ofNat _ 0 ↔ x.toNat = 0 := by
      rw [← BitVec.toNat_inj]
      rfl
    unfold X86.Instructions.Operations.NEG
    simp only [isParityEven8_run]
    repeat spec_bind_rfl
    simp only [Int.reduceToNat, BitVec.ofNat_eq_ofNat, unsigned_eq, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.zero_mod, Int.cast_ofNat_Int, Int.toNat_one, Nat.pow_one,
      Int.add_zero, Int.zero_sub, Int.toNat_zero, Int.pow_zero, Int.ediv_one, hn,
      signed_eq, BitVec.toInt_zero, beq_iff_eq, Int.reduceSub, Nat.reduceAdd,
      extractLsb'_msb, beq_zero_eq_decide, BitVec.neg_eq_zero_iff, decide_eq_true_eq,
      Int.reduceAdd, BitVec.toNat_ofInt, Int.ofNat_toNat, BitVec.extractLsb'_zero,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Int.natCast_emod, ha,
      Nat.not_lt, Nat.le_zero_eq, specM_pure_run, setFlags, StatusFlags.store,
      subSpec, BitVec.zero_sub, ne_eq, decide_not]
    congr 2
    repeat rw [ite_zero_one]
    repeat rw [ite_one_zero]
    simp only [hc, decide_not, ← Nat.not_le, Nat.le_zero_eq, Bool.decide_eq_true]

end P256.Proofs.Common.Instructions
