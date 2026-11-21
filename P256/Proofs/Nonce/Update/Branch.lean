import P256.Proofs.Nonce.Update.Phases
import P256.Proofs.Program.ScalarFrame.Work
import P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination.CompareMemory
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Keygen.Multiply.Inverse.SafeGcd.LinearCombination

theorem branch_after_zero [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (zero : RoundZeroDone initial s state input) :
    ∃ t, Advances boundary 2 s t ∧ FrameState initial t ∧
      t.RIP = (if initial.regValue .rdx == 0 then 0x10a8e1 else 0x10a455) ∧
      AgreesExcept [.flags, .rip] s t := by
  have address : stackPtr s + 424 = stackPtr initial - 256 := by
    rw [zero.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have readable : MemReadable s (stackPtr s + 424) 8 := by
    rw [address]
    exact readable_of_grow (stack_sub_readable pre.stack
      (offset := 256) (by decide) (by decide)) zero.allocated
  obtain ⟨u, compareRun, readyU, compare⟩ :=
    (cmp_m64_imm8_effect_step 0x10a446 (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl 0).advances
      (readyToStep zero.machine zero.bindingsSupported)
      (programText_slice (programLoaded_codeIn zero.loaded) 0xa446 _
        (by decide) (by decide +kernel)) ⟨zero.rip, readable⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa44f (by decide)))
  have compareFrame : AgreesExcept [.flags, .rip] s u := compare.agrees
  have count : memLoad s.external (stackPtr s + 424) 64 = initial.regValue .rdx := by
    rw [zero.rsp]
    exact zero.savedCount
  have flag : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (initial.regValue .rdx == 0) := by
    have h := compare.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((memLoad s.external (stackPtr s + 424) 64 - 0#64) == 0#64) at h
    rw [BitVec.sub_zero, count] at h
    exact h
  have loadedU := compareFrame.codeIn (by simp [Component.Covers])
    (programLoaded_codeIn zero.loaded)
  have target : (jccEffect 0x10a44f 6 4 ((1164 : BitVec 32).signExtend 64) u).rip =
      (if initial.regValue .rdx == 0 then 0x10a8e1 else 0x10a455) := by
    simp [jccEffect, branchEffect, branchTarget, condHolds, flag]
  obtain ⟨t, branchRun, readyT, branch⟩ :=
    (jcc_rel32_effect_step 0x10a44f 4 1164).advances readyU
      (programText_slice loadedU 0xa44f _ (by decide) (by decide +kernel))
      ⟨compare.rip, by intro; decide +kernel⟩
      (by
        rw [target]
        split
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa8e1 (by decide))
        · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xa455 (by decide)))
  have branchFrame : AgreesExcept [.rip] u t := branch.agrees
  have agrees : AgreesExcept [.flags, .rip] s t :=
    (compareFrame.trans branchFrame).mono (by simp)
  have frame : FrameState initial t := zero.toFrameState.after_registers readyT agrees
    (by simp [Component.Covers]) (by simp)
  exact ⟨t, compareRun.trans branchRun, frame, branch.rip.trans target, agrees⟩

theorem finish_empty [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateEmptyPre initial boundary state)
    (zero : RoundZeroDone initial s state .empty) :
    ∃ t, Advances boundary 2 s t ∧ Finished initial t (updateState false ByteArray.empty state) := by
  obtain ⟨t, run, frame, rip, agrees⟩ := branch_after_zero pre.toDrbgCalleePre zero
  refine ⟨t, run, frame, ?_, ?_⟩
  · simpa only [pre.inputCount, beq_self_eq_true, ↓reduceIte] using rip
  · have memory := agrees.external (by simp [Component.Covers])
    simpa only [updateState, Bool.false_eq_true, ↓reduceIte, UpdateInput.seed] using
      zero.drbg.copy (t := t) (fun _ _ => by rw [memory])

end P256.Proofs.Nonce.Update
