import AesGcm.Proofs.AES16.KeySchedule.Generation.State
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def controlLabel (use256 : Bool) (round : Nat) : LIR.Label :=
  match use256 with
  | false => .l104413
  | true => if round % 2 = 0 then .l1058cb else .l105929

set_option maxHeartbeats 4000000 in
theorem advance_reaches (use256 : Bool) (code : CodeMap)
    (round : Nat) (hr : (variant use256).Nk / 4 ≤ round)
    (hrLast : round ≤ (variant use256).Nr)
    (before args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hready : Ready use256 round sp before)
    (hkeep : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] →
      args[r] = before[r])
    (hsp : args[4].get 64 = sp)
    (hindex : args[15].get 64 = BitVec.ofNat 64 (8 * round))
    (hTypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨controlLabel use256 round, args, mem⟩, []⟩
        ⟨⟨label use256 (round + 1), nextArgs, mem⟩, []⟩ ∧
      Ready use256 (round + 1) sp nextArgs ∧ SameFP before nextArgs := by
  have hc := hready.hcontrol
  have hb := hready.hbuffer
  have hd := hready.hDF
  have hf39 := hready.h39
  have hf50 := hready.h50
  have hf51 := hready.h51
  have hk3 := hkeep ⟨3, by decide⟩ (by decide)
  have hk5 := hkeep ⟨5, by decide⟩ (by decide)
  have hk12 := hkeep ⟨12, by decide⟩ (by decide)
  have hk13 := hkeep ⟨13, by decide⟩ (by decide)
  have hk14 := hkeep ⟨14, by decide⟩ (by decide)
  have hk22 := hkeep ⟨22, by decide⟩ (by decide)
  have hk39 := hkeep ⟨39, by decide⟩ (by decide)
  have hk50 := hkeep ⟨50, by decide⟩ (by decide)
  have hk51 := hkeep ⟨51, by decide⟩ (by decide)
  simp only [Fin.getElem_fin] at hk3 hk5 hk12 hk13 hk14 hk22 hk39 hk50 hk51
  rw [← hk3, ← hk5, ← hk12, ← hk13] at hc
  rw [← hk14] at hb
  rw [← hk22] at hd
  rw [← hk39] at hf39
  rw [← hk50] at hf50
  rw [← hk51] at hf51
  have hblock : ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code)
        ⟨controlLabel use256 round, args, mem⟩ =
        .jump ⟨label use256 (round + 1), nextArgs, mem⟩ ∧
      Ready use256 (round + 1) sp nextArgs ∧ SameFP before nextArgs := by
    cases use256
    · change 1 ≤ round at hr
      change round ≤ 10 at hrLast
      have hrange : round = 1 ∨ round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨
          round = 6 ∨ round = 7 ∨ round = 8 ∨ round = 9 ∨ round = 10 := by omega
      rcases hrange with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        rcases hc with ⟨h5, h12, h13⟩
        refine ⟨?_, ?run, ?_, ?_⟩
        case run =>
          dsimp only [controlLabel, label, variant, Variant.Nr]
          cfg_eval [hindex]
          rfl
        · constructor
          · exact hsp
          · runtime_typed
          · exact hd
          · exact hf39
          · exact hf50
          · exact hf51
          · exact hb
          · exact hindex
          · simp only [Bool.false_eq_true, ↓reduceIte]
            change (args[5].get 64 + 1 = _) ∧
              (args[12].get 64 + 16 = _) ∧ (args[13].get 64 + 18 = _)
            rw [h5, h12, h13]
            simp only [base, Bool.false_eq_true, ↓reduceIte, Nat.reduceSub,
              Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc]
            exact ⟨rfl, rfl, rfl⟩
        · exact ⟨hk39, hk50, hk51⟩
    · change 2 ≤ round at hr
      change round ≤ 14 at hrLast
      have hrange : round = 2 ∨ round = 3 ∨ round = 4 ∨ round = 5 ∨ round = 6 ∨
          round = 7 ∨ round = 8 ∨ round = 9 ∨ round = 10 ∨ round = 11 ∨ round = 12 ∨
          round = 13 ∨ round = 14 := by omega
      rcases hrange with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        simp only [↓reduceIte] at hc
        rcases hc with ⟨h3, h12, h13⟩
        refine ⟨?_, ?run, ?_, ?_⟩
        case run =>
          first
            | change LIR.program.runBlock (dialect code) ⟨.l1058cb, args, mem⟩ =
                .jump ⟨.l1058d4, _, mem⟩
            | change LIR.program.runBlock (dialect code) ⟨.l1058cb, args, mem⟩ =
                .jump ⟨.l10593a, _, mem⟩
            | change LIR.program.runBlock (dialect code) ⟨.l105929, args, mem⟩ =
                .jump ⟨.l105870, _, mem⟩
          cfg_eval [h13]
          rfl
        · constructor
          · exact hsp
          · runtime_typed
          · exact hd
          · exact hf39
          · exact hf50
          · exact hf51
          · exact hb
          · exact hindex
          · simp only [↓reduceIte]
            first
              | change (args[3].get 64 = _) ∧ (args[12].get 64 = _) ∧
                  (args[13].get 64 = _)
              | change (args[3].get 64 + 32 = _) ∧ (args[12].get 64 + 32 = _) ∧ _
            rw [h3, h12]
            try rw [h13]
            exact ⟨rfl, rfl, rfl⟩
        · exact ⟨hk39, hk50, hk51⟩
  obtain ⟨nextArgs, hblock, hnext, hfp⟩ := hblock
  refine ⟨nextArgs, .single ?_, hnext, hfp⟩
  change LIR.program.step (dialect code) _ = _
  simp only [Program.step, hblock, Transfer.next]

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
