import P256.Proofs.Program.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.BranchMachine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x10d774)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue .r14).toNat < 8 then 0x10d77e else 0x10d849) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, run, readyU, compare⟩ :=
    (cmp_r64_imm8_effect_step 0x10d774 0x49 0xfe 7
      (by simp [RexWPrefix]) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xd774 [0x49,0x83,0xfe,0x7]
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xd778 (by decide)))
  have compareFrame : AgreesExcept [.flags,.rip] s u := compare.agrees
  obtain ⟨t, step, readyT, branchEffect⟩ := jcc_rel32_effect_step 0x10d778 7 0xcb u readyU
    (programText_slice
      (compareFrame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      0xd778 [0xf,0x87,0xcb,0,0,0] (by decide) (by decide +kernel))
    ⟨compare.rip, fun _ => by decide⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = ((s.regValue .r14).ult 7) :=
    compare.flags.1
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .r14 - 7 == 0) :=
    compare.flags.2.2.2.1
  have target : t.RIP =
      (if (s.regValue .r14).toNat < 8 then 0x10d77e else 0x10d849) := by
    rw [branchEffect.rip]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then 0x10d849 else 0x10d77e) = _
    rw [carry, zero]
    have zero' : (s.regValue .r14 - 7 == 0) =
        decide ((s.regValue .r14).toNat = 7) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · intro h; exact congrArg BitVec.toNat h
      · intro h; apply BitVec.eq_of_toNat_eq; exact h
    rw [zero']
    have cond : (!((s.regValue .r14).ult 7 || decide ((s.regValue .r14).toNat = 7))) =
        decide (8 ≤ (s.regValue .r14).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [cond]
    by_cases small : (s.regValue .r14).toNat < 8
    · simp [small, show ¬ 8 ≤ (s.regValue .r14).toNat by omega]
    · simp [small, show 8 ≤ (s.regValue .r14).toNat by omega]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd77e (by decide))
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd849 (by decide))
  exact ⟨t, run.trans advance, readyT, target,
    (compareFrame.trans branchEffect.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])⟩

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.BranchMachine
