import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Control

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

abbrev compareRex (v : Variant) (form : Form) : UInt8 :=
  if paddingRegister v form = .rbx then 0x48 else 0x49

abbrev compareModRM (v : Variant) (form : Form) : UInt8 :=
  if paddingRegister v form = .rbx then 0xfb
  else if paddingRegister v form = .r14 then 0xfe else 0xff

macro "finalize_closed" v:Lean.Parser.Tactic.elimTarget "," form:Lean.Parser.Tactic.elimTarget : tactic => `(tactic|
  (cases $form with
   | slices => cases $v <;> decide +kernel
   | digest => cases $v <;> decide +kernel
   | reset stage =>
     by_cases h : stage.val = 2 <;> cases $v <;>
       simp only [branchOffset, lengthOffset, paddingRegister, compareRex, compareModRM,
         Variant.pc, Variant.textOffset, h, reduceIte, reduceCtorEq] <;> decide +kernel
   | finalizeIntoReset second => cases second <;> cases $v <;> decide +kernel
   | traitFinalizeIntoReset second => cases second <;> cases $v <;> decide +kernel))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem branch [Bindings] {v : Variant} {form : Form} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = (v.pc (branchOffset v form) form))
    (outside : ¬ InProgram boundary.rip)
    :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if (s.regValue (paddingRegister v form)).toNat < 16 then (v.pc (branchOffset v form + 10) form) else (v.pc (lengthOffset v form) form)) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, run, readyU, compare⟩ :=
    (cmp_r64_imm8_effect_step (v.pc (branchOffset v form) form) (compareRex v form) (compareModRM v form) 15
      (by have h : compareRex v form = 0x48 ∨ compareRex v form = 0x49 := by unfold compareRex; split <;> simp
          rcases h with h | h <;> simp [h, RexWPrefix]) (by finalize_closed v, form) (by finalize_closed v, form)).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset form + (branchOffset v form)) [compareRex v form,0x83,compareModRM v form,0x0f]
        (by finalize_closed v, form) (by finalize_closed v, form)) rip
      (by
        change v.pc (branchOffset v form) form + BitVec.ofNat 64 4 ≠ boundary.rip
        rw [Variant.pc_add v _ _ form]
        exact boundary_ne_program outside (inProgram_of_textOffset (v.textOffset form + _) (by finalize_closed v, form)))
  have compareFrame : AgreesExcept [.flags,.rip] s u := compare.agrees
  obtain ⟨t, step, readyT, branchEffect⟩ := jcc_rel32_effect_step (v.pc (branchOffset v form + 4) form) 7 (BitVec.ofNat 32 (lengthOffset v form - (branchOffset v form + 10))) u readyU
    (programText_slice
      (compareFrame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      (v.textOffset form + (branchOffset v form + 4)) (0x0f :: jccOpcode32 7 :: immBytes 32 (BitVec.ofNat 32 (lengthOffset v form - (branchOffset v form + 10)))) (by finalize_closed v, form) (by finalize_closed v, form))
    ⟨by
      have h : u.RIP = v.pc (branchOffset v form) form + BitVec.ofNat 64 4 := compare.rip
      exact h.trans (by simpa only [Nat.add_assoc] using Variant.pc_add v _ _ form),
      fun _ => by finalize_closed v, form⟩
  have carry : (StatusFlags.ofRFLAGS u.RFLAGS).CF = ((s.regValue (paddingRegister v form)).ult 15) := by
    have h : (.reg (gprNumber 0 (rexB (compareRex v form).toBitVec) (modrmRm (compareModRM v form))) : Operand 64).read s = s.regValue (paddingRegister v form) := by
      cases v <;> cases form <;> simp only [paddingRegister, compareRex, compareModRM, reduceIte, reduceCtorEq]
      all_goals first | rfl | (split <;> rfl)
    have flags := compare.flags.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).CF = ((.reg (gprNumber 0 (rexB (compareRex v form).toBitVec) (modrmRm (compareModRM v form))) : Operand 64).read s).ult 15 at flags
    simpa only [h] using flags
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue (paddingRegister v form) - 15 == 0) := by
    have h : (.reg (gprNumber 0 (rexB (compareRex v form).toBitVec) (modrmRm (compareModRM v form))) : Operand 64).read s = s.regValue (paddingRegister v form) := by
      cases v <;> cases form <;> simp only [paddingRegister, compareRex, compareModRM, reduceIte, reduceCtorEq]
      all_goals first | rfl | (split <;> rfl)
    have flags := compare.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (((.reg (gprNumber 0 (rexB (compareRex v form).toBitVec) (modrmRm (compareModRM v form))) : Operand 64).read s - 15 == 0)) at flags
    simpa only [h] using flags
  have target : t.RIP =
      (if (s.regValue (paddingRegister v form)).toNat < 16 then (v.pc (branchOffset v form + 10) form) else (v.pc (lengthOffset v form) form)) := by
    rw [branchEffect.rip]
    have taken : branchTarget (v.pc (branchOffset v form + 4) form) 6 (((BitVec.ofNat 32 (lengthOffset v form - (branchOffset v form + 10))) : BitVec 32).signExtend 64) = v.pc (lengthOffset v form) form := by
      finalize_closed v, form
    have fall : v.pc (branchOffset v form + 4) form + BitVec.ofNat 64 6 =
        v.pc (branchOffset v form + 10) form := by
      simpa only [Nat.add_assoc] using Variant.pc_add v _ _ form
    simp only [jccEffect, X86Proofs.branchEffect, taken]
    rw [fall]
    change (if !((StatusFlags.ofRFLAGS u.RFLAGS).CF || (StatusFlags.ofRFLAGS u.RFLAGS).ZF)
      then (v.pc (lengthOffset v form) form) else (v.pc (branchOffset v form + 10) form)) = _
    rw [carry, zero]
    have zero' : (s.regValue (paddingRegister v form) - 15 == 0) =
        decide ((s.regValue (paddingRegister v form)).toNat = 15) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.reduceAdd]
      constructor
      · intro h; exact congrArg BitVec.toNat h
      · intro h; apply BitVec.eq_of_toNat_eq; exact h
    rw [zero']
    have cond : (!((s.regValue (paddingRegister v form)).ult 15 || decide ((s.regValue (paddingRegister v form)).toNat = 15))) =
        decide (16 ≤ (s.regValue (paddingRegister v form)).toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, BitVec.ult_eq_decide,
        decide_eq_false_iff_not, BitVec.reduceToNat, decide_eq_true_eq]
      omega
    rw [cond]
    by_cases small : (s.regValue (paddingRegister v form)).toNat < 16
    · simp [small, show ¬ 16 ≤ (s.regValue (paddingRegister v form)).toNat by omega]
    · simp [small, show 16 ≤ (s.regValue (paddingRegister v form)).toNat by omega]
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    by_cases h : (s.regValue (paddingRegister v form)).toNat < 16
    · rw [ite_eq_left h]
      exact boundary_ne_program outside
        (inProgram_of_textOffset (v.textOffset form + _) (by finalize_closed v, form))
    · rw [ite_eq_right h]
      exact boundary_ne_program outside
        (inProgram_of_textOffset (v.textOffset form + _) (by finalize_closed v, form))
  exact ⟨t, run.trans advance, readyT, target,
    (compareFrame.trans branchEffect.agrees).mono (by simp [jccEffect, X86Proofs.branchEffect, Effect.components])⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Control
