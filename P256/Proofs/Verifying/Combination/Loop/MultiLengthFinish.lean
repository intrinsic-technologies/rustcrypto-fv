import P256.Proofs.Verifying.Combination.Loop.MultiSelect

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f10e)
    (offset : t.regValue .rdi = 0) (count : t.regValue .rcx = 272) :
    ∃ w, Advances boundary 3 t w ∧ State s w ∧ w.RIP = 0x10f11a ∧
      AgreesExcept [.reg 7, .flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (add_r64_imm32_effect_step 0x10f10e 0x48 0xc7 272 (by simp [RexWPrefix]) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf10e _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf115 (by decide)))
  have frameA : AgreesExcept [.reg 7, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have offsetA : a.regValue .rdi = 272 := by
    have h := effectA.writes
    change a.regValue .rdi = t.regValue .rdi + 272 at h
    rw [offset] at h
    exact h.trans (by decide +kernel)
  have countA : a.regValue .rcx = 272 := (frameA.read (n := 64) (r := 1) (by simp)).trans count
  obtain ⟨b, runB, readyB, effectB⟩ :=
    (cmp_r64_r64_effect_step 0x10f115 0x48 0xf9 (by simp [RexWPrefix]) rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf115 _
        (by decide) (by decide +kernel)) effectA.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf118 (by decide)))
  have frameB : AgreesExcept [.flags, .rip] a b := effectB.agrees
  have stateB := stateA.after_registers readyB frameB (by simp [Component.Covers]) (by simp)
  have zeroB : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = true := by
    have h := effectB.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = (a.regValue .rcx - a.regValue .rdi == 0#64) at h
    rw [countA, offsetA] at h
    exact h.trans (by decide +kernel)
  have target : (jccEffect 0x10f118 2 5 ((0xe6 : BitVec 8).signExtend 64) b).rip = 0x10f11a := by
    simp only [jccEffect, branchEffect, condHolds, zeroB]
    rfl
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel8_effect_step 0x10f118 5 0xe6).advances readyB
      (programText_slice (programLoaded_codeIn stateB.loaded) 0xf118 _
        (by decide) (by decide +kernel))
      ⟨effectB.rip, by intro h; decide +kernel⟩
      (by
        rw [target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf11a (by decide)))
  have frameW : AgreesExcept [.rip] b w := effectW.agrees
  have frame : AgreesExcept [.reg 7, .flags, .rip] t w :=
    ((frameA.trans frameB).trans frameW).mono (by simp)
  exact ⟨w, (runA.trans runB).trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp),
    effectW.rip.trans target, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
