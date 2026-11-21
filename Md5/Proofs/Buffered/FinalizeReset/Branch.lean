import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Block.Entry
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

namespace Md5.Proofs.Buffered.FinalizeReset

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block Md5.Spec.Program

set_option maxRecDepth 2048 in
theorem padding_branch_condition (position : Nat) (hp : position < 64) :
    condHolds 7 (cmpSpec (BitVec.ofNat 64 (63 - position)) 7) = decide (position < 56) := by
  have h : ∀ p : Fin 64,
      condHolds 7 (cmpSpec (BitVec.ofNat 64 (63 - p.val)) 7) = decide (p.val < 56) := by
    decide +kernel
  exact h ⟨position, hp⟩

theorem padding_branch {variant : Variant} [Bindings] {boundary : ReturnBoundary} {s : RamState}
    {position : Nat} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = (variant.address 0x1007e6))
    (hp : position < 64)
    (hRemaining : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 (63 - position)) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = (if position < 56 then (variant.address 0x1008a2) else (variant.address 0x1007f0)) ∧
      AgreesExcept [.flags, .rip] s t := by
  have hCmp := cmp_r64_imm8_effect_step (variant.address 0x1007e6) 0x48 0xfb 7
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  have hBytes : CodeIn (codeRange (variant.address 0x1007e6) [0x48, 0x83, 0xfb, 7]) s :=
    by have haddr := program_text_slice hCode (0x7e6 + (if variant = .saved then 0 else 0x6b0)) 4 (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  obtain ⟨u, hRun, hReady', hEffect⟩ := hCmp.advances hReady hBytes hRip
    (by have haddr := text_address_ne_return hOutside (0x7ea + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr)
  have hCode' := hEffect.codeIn (cmpR64Imm8Effect_avoids _ _ _ _ _) hCode
  have hCond : condHolds 7 (StatusFlags.ofRFLAGS u.RFLAGS) = decide (position < 56) := by
    change Bool.not ((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF) = _
    rw [hEffect.flags.1, hEffect.flags.2.2.2.1]
    change condHolds 7 (cmpSpec ((Operand.reg 3 : Operand 64).read s) 7) = _
    rw [hRemaining]
    exact padding_branch_condition position hp
  have hBranchBytes : CodeIn (codeRange (variant.address 0x1007ea) [0x0f, 0x87, 0xb2, 0, 0, 0]) u :=
    by have haddr := program_text_slice hCode' (0x7ea + (if variant = .saved then 0 else 0x6b0)) 6 (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  have hNext : (jccEffect (variant.address 0x1007ea) 6 7 ((0xb2#32).signExtend 64) u).rip =
      (if position < 56 then (variant.address 0x1008a2) else (variant.address 0x1007f0)) := by
    simp only [jccEffect, branchEffect, hCond, decide_eq_true_eq]
    cases variant <;> rfl
  have hNotBoundary : (jccEffect (variant.address 0x1007ea) 6 7 ((0xb2#32).signExtend 64) u).rip ≠
      boundary.rip := by
    rw [hNext]
    split
    · have haddr := text_address_ne_return hOutside (0x8a2 + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
    · have haddr := text_address_ne_return hOutside (0x7f0 + (if variant = .saved then 0 else 0x6b0)) (by cases variant <;> decide +kernel); cases variant <;> exact haddr
  obtain ⟨t, hRun', hReady'', hEffect'⟩ := (jcc_rel32_effect_step (variant.address 0x1007ea) 7 0xb2).advances
    hReady' hBranchBytes ⟨by have haddr := hEffect.rip; cases variant <;> exact haddr, fun _ ↦ by cases variant <;> decide +kernel⟩ hNotBoundary
  refine ⟨t, hRun.trans hRun', hReady'',
    hEffect'.codeIn (branchEffect_avoids _ _ _ _) hCode', hEffect'.rip.trans hNext, ?_⟩
  apply (hEffect.agrees.trans hEffect'.agrees).mono
  intro c hc
  simpa only [cmpR64Imm8Effect_components, jccEffect, branchEffect_components,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self, or_assoc] using hc

end Md5.Proofs.Buffered.FinalizeReset
