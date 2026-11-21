import Sha1.Proofs.Buffered.Finalize.Geometry
import Sha1.Proofs.Compress.Machine.Execution
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Sha1.Proofs.Buffered.Finalize.Digest

open X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Compress.Machine Sha1.Spec.Program

set_option maxRecDepth 2048 in
theorem padding_branch_condition (position : Nat) (hp : position < 64) :
    condHolds 7 (cmpSpec (BitVec.ofNat 64 (63 - position)) 7) = decide (position < 56) := by
  have h : ∀ p : Fin 64,
      condHolds 7 (cmpSpec (BitVec.ofNat 64 (63 - p.val)) 7) = decide (p.val < 56) := by
    decide +kernel
  exact h ⟨position, hp⟩

theorem padding_branch [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {position : Nat} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = 0x100132)
    (hp : position < 64)
    (hRemaining : (Operand.reg 14 : Operand 64).read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if position < 56 then 0x1001f2 else 0x10013c) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hCmp := cmp_r64_imm8_effect_step 0x100132 0x49 0xfe 7
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hBytes : CodeIn (codeRange 0x100132 [0x49, 0x83, 0xfe, 7]) s :=
    program_text_slice hCode 0x132 4 (by decide +kernel)
  obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
    (text_address_ne_return hOutside 0x136 (by decide +kernel))
  have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
  have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
    change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
    rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
    change condHolds 7 (cmpSpec ((Operand.reg 14 : Operand 64).read s) 7) = _
    rw [hRemaining]
    exact padding_branch_condition position hp
  have hBranchBytes : CodeIn (codeRange 0x100136 [0x0f, 0x87, 0xb6, 0, 0, 0]) u :=
    program_text_slice hCode' 0x136 6 (by decide +kernel)
  have hNext : (jccEffect 0x100136 6 7 ((0xb6#32).signExtend 64) u).rip =
      (if position < 56 then 0x1001f2 else 0x10013c) := by
    simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
    rfl
  have hNotBoundary : (jccEffect 0x100136 6 7 ((0xb6#32).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    split
    · exact text_address_ne_return hOutside 0x1f2 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x13c (by decide +kernel)
  obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step 0x100136 7 0xb6).advances
    hReady' hBranchBytes ⟨hEffect.rip, fun _ ↦ by decide +kernel⟩ hNotBoundary
  refine ⟨t, hRun.trans hRun', hReady'',
    hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
  apply (hEffect.agrees.trans hEffect'.agrees).mono
  intro c hc
  simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Sha1.Proofs.Buffered.Finalize.Digest
