import P256.Proofs.Common.Instructions.Sar.Core
import P256.Proofs.Common.Instructions.Sar.Spec

namespace P256.Proofs.Common.Instructions

open X86 X86.Helpers X86Proofs

theorem sar_operation {σ : Type} (s : X86.State σ) (x : BitVec 64) (count : BitVec 8) :
    (X86.Instructions.Operations.SAR 64 x count).run s =
      let c := shiftCount 64 count
      let (r, flags) := sarSpec (StatusFlags.ofRFLAGS s.RFLAGS) (oracleBit s.oracle)
        (sarOracleAF s.oracle c) c x
      (.ok r, setFlags { s with oracle := oracleSkip s.oracle (sarOracleBits c) } flags) := by
  have hlt := shiftCount_lt_64 64 count
  obtain ⟨c, hc⟩ : ∃ c, shiftCount 64 count = c := ⟨_, rfl⟩
  have hc64 : count.toNat % 64 = c := by simpa [shiftCount] using hc
  rw [hc] at hlt ⊢
  simp only [sarSpec, sarOracleBits, sarOracleAF]
  unfold X86.Instructions.Operations.SAR
  simp only [isParityEven8_run]
  repeat spec_bind_rfl
  simp only [Int.reduceBEq, ↓reduceIte, Int.reduceToNat,
    unsigned_extractLsb', Nat.reducePow]
  rw [hc64]
  by_cases h0 : c = 0
  · subst h0
    simp
  have e0 : ((c : Int) != 0) = true := by
    simpa only [bne_iff_ne, ne_eq, Int.ofNat_eq_zero] using h0
  simp only [e0, h0, ↓reduceIte]
  spec_bind_rfl

  refine (specM_bind_run _ _ (specM_forIn_run _ _
    (fun _ (acc : BitVec _ × BitVec 1) => (acc.1.sshiftRight 1, acc.1.extractLsb' 0 1)) _ _ ?_)).trans ?_
  · intro _ _ _
    simp only [shiftRightArithmetic_one (by decide : 1 < 64)]
    rfl
  rw [sar_fold _ _ _ (by omega) (by omega)]
  generalize x.sshiftRight c = r
  by_cases h1 : c = 1
  · subst h1
    simp only [↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext
  · have e1 : ((c : Int) == 1) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    simp only [e1, h1, Bool.false_eq_true, ↓reduceIte]
    rw [setFlags_eq_of_store]
    · rfl
    · rflags_ext

end P256.Proofs.Common.Instructions
