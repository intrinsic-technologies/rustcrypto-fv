import X86Proofs.Core.Shift
import X86.Helpers.Std.Bits.Rotate_Right
import Sha2.Proofs.Common.Instructions.Ror.Spec



namespace X86Proofs

open X86 X86.Helpers


set_option maxRecDepth 4096 in
theorem ror_operation {σ : Type} (s : X86.State σ) (n : Nat)
    (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (x : BitVec n) (count : BitVec 8) :
    (X86.Instructions.Operations.ROR n x count).run s =
      let c := shiftCount n count
      let (r, flags) := rorSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (rorOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 n count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount n count = c := ⟨_, rfl⟩
  have hc32 : n ≠ 64 → count.toNat % 32 = c := fun h => by simp [← hc, shiftCount, h]
  have hc64 : n = 64 → count.toNat % 64 = c := fun h => by simp [← hc, shiftCount, h]
  rw [hc] at hlt ⊢
  simp only [rorSpec, rorOracleBits]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    unfold X86.Instructions.Operations.ROR
    repeat spec_bind_rfl
    simp only [Int.reduceToNat, Int.reduceSub, Int.reduceAdd, unsigned_extractLsb', Nat.reducePow]
    first | rw [hc32 (by decide)] | rw [hc64 rfl]
    rw [rotateRight_run_nat _ _ (by decide)]
    generalize x.rotateRight c = r
    rcases Nat.lt_or_ge c 2 with hc | hc
    · rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
      · simp
      · simp only [Nat.one_ne_zero, ↓reduceIte, or_true, oracleSkip_zero]
        rw [setFlags_eq_of_store]
        · rfl
        · rflags_ext
    · have h0 : c ≠ 0 := by omega
      have h1 : c ≠ 1 := by omega
      have e1 : ((c : Int) == 1) = false := by simp; omega
      have e2 : ((c : Int) != 0) = true := by simp; omega
      simp only [h0, h1, ↓reduceIte, or_self, e1, e2, Bool.false_eq_true]
      rw [setFlags_eq_of_store]
      · rfl
      · rflags_ext

end X86Proofs
