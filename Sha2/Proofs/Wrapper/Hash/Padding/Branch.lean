import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Padding

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxRecDepth 2048 in
theorem branch [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = (v.pc 0x1fc))
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .rbx).toNat < 8 then (v.pc 0x206) else (v.pc 0x2b4)) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, run, readyU, compare⟩ :=
    (cmp_r64_imm8_effect_step (v.pc 0x1fc) 0x48 0xfb 7
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x1fc) [0x48,0x83,0xfb,0x07]
        (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (by simpa only [cmpR64Imm8Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x200 < 1024)))
  have compareFrame : AgreesExcept [.flags,.rip] s u := compare.agrees
  obtain ⟨t, step, readyT, branchEffect⟩ := jcc_rel32_effect_step (v.pc 0x200) 7 0xae u readyU
    (programText_slice
      (compareFrame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      (v.textOffset + 0x200) [0x0f,0x87,0xae,0,0,0] (by cases v <;> decide) (by cases v <;> decide +kernel))
    ⟨by simpa only [cmpR64Imm8Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using compare.rip, fun _ => by cases v <;> decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = ((s.regValue .rbx).ult 7) :=
    compare.flags.1
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rbx - 7 == 0) :=
    compare.flags.2.2.2.1
  have target : t.RIP =
      (if (s.regValue .rbx).toNat < 8 then (v.pc 0x206) else (v.pc 0x2b4)) := by
    rw [branchEffect.rip]
    simp only [jccEffect, X86Proofs.branchEffect, branchTarget, BitVec.reduceSignExtend, Variant.pc_add]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then (v.pc 0x2b4) else (v.pc 0x206)) = _
    rw [carry, zero]
    have zero' : (s.regValue .rbx - 7 == 0) =
        decide ((s.regValue .rbx).toNat = 7) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · intro h; exact congrArg BitVec.toNat h
      · intro h; apply BitVec.eq_of_toNat_eq; exact h
    rw [zero']
    have cond : (!((s.regValue .rbx).ult 7 || decide ((s.regValue .rbx).toNat = 7))) =
        decide (8 ≤ (s.regValue .rbx).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [cond]
    by_cases small : (s.regValue .rbx).toNat < 8
    · simp [small, show ¬ 8 ≤ (s.regValue .rbx).toNat by omega]
    · simp [small, show 8 ≤ (s.regValue .rbx).toNat by omega]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · simpa only [cmpR64Imm8Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x206 < 1024))
    · simpa only [cmpR64Imm8Effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd] using boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x2b4 < 1024))
  exact ⟨t, run.trans advance, readyT, target,
    (compareFrame.trans branchEffect.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])⟩

end Sha2.Proofs.Wrapper.Hash.Padding
