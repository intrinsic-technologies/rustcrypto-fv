import Sha2.Proofs.Wrapper.Variant
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

set_option maxHeartbeats 1000000 in
theorem branch [Bindings] {v : Variant} {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = v.pc 0x85)
    (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      t.RIP = (if s.regValue .rsi = 0 then v.pc 0x1bb else v.pc 0x8e) ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, run, readyU, tested⟩ :=
    (test_r64_r64_effect_step (v.pc 0x85) 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x85)
        [0x48,0x85,0xf6] (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (boundary_ne_program outside (by
        have h := inProgram_of_textOffset (v.textOffset + 0x88) (by cases v <;> decide)
        have h' : InProgram (v.pc 0x85 + BitVec.ofNat 64 3) := by
          rw [Variant.pc_add]
          exact h
        simpa [testR64R64Effect, gprNumber, rexB, modrmRm, rexR, modrmReg] using h'))
  have frame : AgreesExcept [.flags,.rip] s u := tested.agrees
  have testedRip0 : u.RIP = v.pc 0x85 + BitVec.ofNat 64 3 := by
    simpa [testR64R64Effect, gprNumber, rexB, modrmRm, rexR, modrmReg] using tested.rip
  have testedRip : u.RIP = v.pc 0x88 := by
    rw [Variant.pc_add] at testedRip0
    exact testedRip0
  obtain ⟨t, step, readyT, jumped⟩ := jcc_rel32_effect_step (v.pc 0x88) 4 0x12d u readyU
    (programText_slice
      (frame.codeIn (by simp [Component.Covers]) (programLoaded_codeIn loaded))
      (v.textOffset + 0x88) [0x0f,0x84,0x2d,0x01,0x00,0x00]
      (by cases v <;> decide) (by cases v <;> decide +kernel))
    ⟨testedRip, fun _ => by cases v <;> decide⟩
  have zero : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi == 0) := by
    have zero := tested.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = (s.regValue .rsi &&& s.regValue .rsi == 0) at zero
    simpa only [BitVec.and_self] using zero
  have target : t.RIP = (if s.regValue .rsi = 0 then v.pc 0x1bb else v.pc 0x8e) := by
    rw [jumped.rip]
    simp only [jccEffect, branchEffect, branchTarget, condHolds]
    change (if (StatusFlags.ofRFLAGS u.RFLAGS).ZF then
      (v.pc 0x88 + BitVec.ofNat 64 6 + BitVec.signExtend 64 (BitVec.ofNat 32 0x12d))
      else v.pc 0x88 + BitVec.ofNat 64 6) = _
    rw [zero]
    simp only [beq_iff_eq]
    have hnext : v.pc 0x88 + BitVec.ofNat 64 6 = v.pc 0x8e := by
      exact Variant.pc_add v 0x88 6
    have hoff : BitVec.signExtend 64 (BitVec.ofNat 32 0x12d) = BitVec.ofNat 64 0x12d := by
      decide +kernel
    rw [hoff, hnext]
    split
    · rw [Variant.pc_add v 0x8e 0x12d]
    · rfl
  have advance : Advances boundary 1 u t := by
    apply Advances.of_step step
    left
    rw [target]
    split
    · exact boundary_ne_program outside (by
        apply Variant.pc_inProgram
        cases v <;> decide)
    · exact boundary_ne_program outside (by
        apply Variant.pc_inProgram
        cases v <;> decide)
  exact ⟨t, run.trans advance, readyT, target,
    (frame.trans jumped.agrees).mono (by simp [jccEffect, branchEffect, Effect.components])⟩

end Sha2.Proofs.Wrapper.Dispatch
