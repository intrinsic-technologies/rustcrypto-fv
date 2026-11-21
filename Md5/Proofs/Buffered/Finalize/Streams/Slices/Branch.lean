import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.FinalizeReset.Branch

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

theorem padding_branch {update : Bool} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {position : Nat} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = (BitVec.ofNat 64 (relocated update 0x100483)))
    (hp : position < 64)
    (hRemaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if position < 56 then (BitVec.ofNat 64 (relocated update 0x10053d)) else (BitVec.ofNat 64 (relocated update 0x10048d))) ∧
      AgreesExcept [.flags, .rip] s t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    have hCmp := cmp_r64_imm8_effect_step (BitVec.ofNat 64 (relocated update 0x100483)) 0x48 0xfb 7
      (by unfold RexWPrefix; decide) (by decide) (by decide)
    have hBytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x100483)) [0x48, 0x83, 0xfb, 7]) s :=
      by
        have hs := program_text_slice hCode (relocated update 0x483) 4 (by decide +kernel)
        have he : Extracted.textBytes.toListFrom (relocated update 0x483) 4 = [0x48, 0x83, 0xfb, 7] := by
          decide +kernel
        rw [he] at hs
        exact hs
    obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
      (text_address_ne_return hOutside (relocated update 0x487) (by decide +kernel))
    have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
    have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
      change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
      rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
      change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
      rw [hRemaining]
      exact FinalizeReset.padding_branch_condition position hp
    have hBranchBytes : CodeIn (codeRange (BitVec.ofNat 64 (relocated update 0x100487)) [0x0f, 0x87, 0xb0, 0, 0, 0]) u :=
      by
        have hs := program_text_slice hCode' (relocated update 0x487) 6 (by decide +kernel)
        have he : Extracted.textBytes.toListFrom (relocated update 0x487) 6 = [0x0f, 0x87, 0xb0, 0, 0, 0] := by
          decide +kernel
        rw [he] at hs
        exact hs
    have hNext : (jccEffect (BitVec.ofNat 64 (relocated update 0x100487)) 6 7 ((0xb0#32).signExtend 64) u).rip =
        (if position < 56 then (BitVec.ofNat 64 (relocated update 0x10053d)) else (BitVec.ofNat 64 (relocated update 0x10048d))) := by
      simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
      rfl
    have hNotBoundary : (jccEffect (BitVec.ofNat 64 (relocated update 0x100487)) 6 7 ((0xb0#32).signExtend 64) u).rip ≠
        boundary.rip := by
      rw [hNext]
      split
      · exact text_address_ne_return hOutside (relocated update 0x53d) (by decide +kernel)
      · exact text_address_ne_return hOutside (relocated update 0x48d) (by decide +kernel)
    obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step (BitVec.ofNat 64 (relocated update 0x100487)) 7 0xb0).advances
      hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
    refine ⟨t, hRun.trans hRun', hReady'',
      hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
    apply (hEffect.agrees.trans hEffect'.agrees).mono
    intro c hc
    simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Md5.Proofs.Buffered.Finalize.Streams.Slices
