import Sha1.Proofs.Buffered.Finalize.Digest.Branch
import Sha1.Proofs.Compress.Machine.Execution
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.Finalize.Family

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine Sha1.Spec.Program

theorem padding_branch [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {position : Nat} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = 0x101e2b)
    (hp : position < 64)
    (hRemaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if position < 56 then 0x101ef3 else 0x101e35) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hCmp := cmp_r64_imm8_effect_step 0x101e2b 0x48 0xfb 7
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hBytes : CodeIn (codeRange 0x101e2b [0x48, 0x83, 0xfb, 7]) s :=
    program_text_slice hCode 0x1e2b 4 (by decide +kernel)
  obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
    (text_address_ne_return hOutside 0x1e2f (by decide +kernel))
  have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
  have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
    change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
    rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
    change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
    rw [hRemaining]
    exact Digest.padding_branch_condition position hp
  have hBranchBytes : CodeIn (codeRange 0x101e2f [0x0f, 0x87, 0xbe, 0, 0, 0]) u :=
    program_text_slice hCode' 0x1e2f 6 (by decide +kernel)
  have hNext : (jccEffect 0x101e2f 6 7 ((0xbe#32).signExtend 64) u).rip =
      (if position < 56 then 0x101ef3 else 0x101e35) := by
    simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
    rfl
  have hNotBoundary : (jccEffect 0x101e2f 6 7 ((0xbe#32).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x1ef3 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1e35 (by decide +kernel)
  obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step 0x101e2f 7 0xbe).advances
    hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
  refine ⟨t, hRun.trans hRun', hReady'',
    hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
  apply (hEffect.agrees.trans hEffect'.agrees).mono
  intro c hc
  simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Sha1.Proofs.Buffered.Finalize.Family
