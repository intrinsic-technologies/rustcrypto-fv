import AesGcm.Proofs.AES16.KeySchedule.Generation.Native.Evaluation

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem ready_of_preserved {use256 : Bool} {round : Nat} {sp : BitVec 64}
    {before after : Values Value Reg.count}
    (h : Ready use256 round sp before) (hsp : after[4].get 64 = sp)
    (hTypes : GPRsTyped after)
    (hkeep : ∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      after[r] = before[r]) : Ready use256 round sp after := by
  have h3 : after[3] = before[3] := hkeep 3 (by decide)
  have h5 : after[5] = before[5] := hkeep 5 (by decide)
  have h12 : after[12] = before[12] := hkeep 12 (by decide)
  have h13 : after[13] = before[13] := hkeep 13 (by decide)
  have h14 : after[14] = before[14] := hkeep 14 (by decide)
  have h15 : after[15] = before[15] := hkeep 15 (by decide)
  have h22 : after[22] = before[22] := hkeep 22 (by decide)
  have h39 : after[39] = before[39] := hkeep 39 (by decide)
  have h50 : after[50] = before[50] := hkeep 50 (by decide)
  have h51 : after[51] = before[51] := hkeep 51 (by decide)
  refine ⟨hsp, hTypes, h22.trans h.hDF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h39]; exact h.h39
  · rw [h50]; exact h.h50
  · rw [h51]; exact h.h51
  · rw [h14]; exact h.hbuffer
  · rw [h15]; exact h.hindex
  · simpa only [h3, h5, h12, h13] using h.hcontrol

theorem copyLabel_eq {use256 : Bool} {round : Nat}
    (hr : round ≤ (variant use256).Nr) :
    label use256 round = copyLabel use256 (oddRound round) := by
  have hne : round ≠ (variant use256).Nr + 1 := by omega
  cases use256 with
  | false => simp only [label, hne, Bool.false_eq_true, ↓reduceIte, copyLabel]
  | true =>
    by_cases he : round % 2 = 0
    · have ho : oddRound round = false := by simp [oddRound, he]
      simp only [label, hne, he, ↓reduceIte, ho, copyLabel]
    · have ho : oddRound round = true := by simp [oddRound, he]
      simp only [label, hne, he, ↓reduceIte, ho, copyLabel]

theorem subDestination_eq {use256 : Bool} {round : Nat} {sp : BitVec 64}
    {args : Values Value Reg.count} (h : Ready use256 round sp args) :
    subDestination use256 (oddRound round) sp args =
      base use256 sp + BitVec.ofNat 64 (16 * round) := by
  have hc := h.hcontrol
  cases use256 with
  | false =>
    change args[5].get 64 = _ ∧ args[12].get 64 = _ ∧ args[13].get 64 = _ at hc
    simp only [subDestination, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hc.2.1, base]
    bv_omega
  | true =>
    change args[3].get 64 = _ ∧ args[12].get 64 = _ ∧ args[13].get 64 = _ at hc
    by_cases he : round % 2 = 0
    · have hv : 32 * (round / 2) = 16 * round := by omega
      have ho : oddRound round = false := by simp [oddRound, he]
      simp only [subDestination, ho, Bool.not_false, Bool.and_self, ↓reduceIte, hc.1, hv, base]
      bv_omega
    · have hv : 16 + 32 * (round / 2) = 16 * round := by omega
      have ho : oddRound round = true := by simp [oddRound, he]
      simp only [subDestination, ho, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hc.2.1, hv, base]
      bv_omega

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
