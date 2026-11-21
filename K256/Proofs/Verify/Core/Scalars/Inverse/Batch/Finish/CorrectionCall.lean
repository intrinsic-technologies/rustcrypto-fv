import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.State

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
set_option maxRecDepth 4096 in
theorem correctionCallBlock {b : Registers} {p : Ram} {q dst : Word} (neg : Bool)
    (rsp : b[4].get 64 = q)
    (win : Writable Extracted.programImage p (q - 8) 344)
    (ptr : memLoad p (q + 288) 64 = dst)
    (modPtr : memLoad p (q + 88) 64 = 0x2021a0)
    (sign : memLoad p (q + 40) 8 = (if neg then 1 else 0))
    (nonzero : (((memLoad p (q + 280) 64 ||| memLoad p (q + 264) 64) |||
      memLoad p (q + 256) 64) ||| memLoad p (q + 272) 64) ≠ 0) :
    ∃ c : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l109948, b, p⟩ =
      .call ⟨.l109c00, c, memStore p (q - 8) (0x109989 : Word)⟩ ⟨.l109989,#v[],rfl,some ⟨64,0x109989⟩⟩ ∧
      c[4] = ⟨64, q - 8⟩ ∧ c[7] = ⟨64, dst⟩ ∧ c[14] = ⟨64, dst⟩ ∧
      c[3].width = 64 ∧ c[3].get 8 = 1 ∧ c[6].get 64 = q + 96 ∧
      c[1].get 64 = 0x2021a0 ∧ (c[2].get 8 &&& 1) = (if neg then 1 else 0) ∧
      ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i] := by
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [b_l109948, rsp, ptr, modPtr]
    segment_words [rsp, ptr, modPtr]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l109948)
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · change (mergeGPR 8 _ _).setWidth 8 = _
      simp [setWidth_mergeGPR8, orFlags]
      intro h₁ h₂ h₃ h₄
      exact nonzero (by simp [h₁, h₂, h₃, h₄])
    · have byte := extractLsb'_memLoad p (q + 40) (n := 32) 0 8 (by decide) (by decide) (by decide)
      change (memLoad p (q + 40) 32).setWidth 8 = memLoad p ((q + 40) + 0) 8 at byte
      rw [show q + 40 + 0 = q + 40 by bv_omega, sign] at byte
      change (((memLoad p (q + 40) 32).setWidth 64).setWidth 8 &&& 1) = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), byte]
      cases neg <;> decide
    · intro ⟨i, hi⟩ hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
