import Md5.Proofs.Buffered.FinalizeReset.Branch
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

def longEntry : Variant → BitVec 64
  | .original => 0x100af9
  | .finalize => 0x101189
  | .discard => 0x10166c

theorem branch [Bindings] {variant : Variant} {boundary : ReturnBoundary} {s : RamState}
    {position : Nat} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = variant.preparedRip)
    (hp : position < 64)
    (hRemaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if position < 56 then variant.paddedRip else longEntry variant) ∧
      AgreesExcept [.flags, .rip] s t := by
  cases variant
  case original =>
    have hCmp := cmp_r64_imm8_effect_step 0x100aef 0x48 0xfb 7
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    have hBytes : CodeIn (codeRange 0x100aef [0x48, 0x83, 0xfb, 7]) s :=
      program_text_slice hCode 0xaef 4 (by decide +kernel)
    obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
      (text_address_ne_return hOutside 0xaf3 (by decide +kernel))
    have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
    have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
      change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
      rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
      change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
      rw [hRemaining]
      exact FinalizeReset.padding_branch_condition position hp
    have hBranchBytes : CodeIn (codeRange 0x100af3 [0x0f, 0x87, 0xd6, 0, 0, 0]) u :=
      program_text_slice hCode' 0xaf3 6 (by decide +kernel)
    have hNext : (jccEffect 0x100af3 6 7 ((0xd6#32).signExtend 64) u).rip =
        (if position < 56 then 0x100bcf else 0x100af9) := by
      simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
      rfl
    have hNotBoundary : (jccEffect 0x100af3 6 7 ((0xd6#32).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside 0xbcf (by decide +kernel)
      · exact text_address_ne_return hOutside 0xaf9 (by decide +kernel)
    obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step 0x100af3 7 0xd6).advances
      hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
    refine ⟨t, hRun.trans hRun', hReady'',
      hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
    apply (hEffect.agrees.trans hEffect'.agrees).mono
    intro c hc
    simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc
  case finalize =>
    have hCmp := cmp_r64_imm8_effect_step 0x10117f 0x48 0xfb 7
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    have hBytes : CodeIn (codeRange 0x10117f [0x48, 0x83, 0xfb, 7]) s :=
      program_text_slice hCode 0x117f 4 (by decide +kernel)
    obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
      (text_address_ne_return hOutside 0x1183 (by decide +kernel))
    have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
    have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
      change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
      rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
      change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
      rw [hRemaining]
      exact FinalizeReset.padding_branch_condition position hp
    have hBranchBytes : CodeIn (codeRange 0x101183 [0x0f, 0x87, 0xd6, 0, 0, 0]) u :=
      program_text_slice hCode' 0x1183 6 (by decide +kernel)
    have hNext : (jccEffect 0x101183 6 7 ((0xd6#32).signExtend 64) u).rip =
        (if position < 56 then 0x10125f else 0x101189) := by
      simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
      rfl
    have hNotBoundary : (jccEffect 0x101183 6 7 ((0xd6#32).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside 0x125f (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1189 (by decide +kernel)
    obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step 0x101183 7 0xd6).advances
      hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
    refine ⟨t, hRun.trans hRun', hReady'',
      hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
    apply (hEffect.agrees.trans hEffect'.agrees).mono
    intro c hc
    simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc
  case discard =>
    have hCmp := cmp_r64_imm8_effect_step 0x101662 0x48 0xfb 7
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    have hBytes : CodeIn (codeRange 0x101662 [0x48, 0x83, 0xfb, 7]) s :=
      program_text_slice hCode 0x1662 4 (by decide +kernel)
    obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
      (text_address_ne_return hOutside 0x1666 (by decide +kernel))
    have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
    have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
      change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
      rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
      change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
      rw [hRemaining]
      exact FinalizeReset.padding_branch_condition position hp
    have hBranchBytes : CodeIn (codeRange 0x101666 [0x0f, 0x87, 0xeb, 0, 0, 0]) u :=
      program_text_slice hCode' 0x1666 6 (by decide +kernel)
    have hNext : (jccEffect 0x101666 6 7 ((0xeb#32).signExtend 64) u).rip =
        (if position < 56 then 0x101757 else 0x10166c) := by
      simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
      rfl
    have hNotBoundary : (jccEffect 0x101666 6 7 ((0xeb#32).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside 0x1757 (by decide +kernel)
      · exact text_address_ne_return hOutside 0x166c (by decide +kernel)
    obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step 0x101666 7 0xeb).advances
      hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
    refine ⟨t, hRun.trans hRun', hReady'',
      hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
    apply (hEffect.agrees.trans hEffect'.agrees).mono
    intro c hc
    simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding
