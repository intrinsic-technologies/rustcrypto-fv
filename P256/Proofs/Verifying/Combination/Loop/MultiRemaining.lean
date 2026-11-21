import P256.Proofs.Verifying.Combination.Loop.MultiLength

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem remaining_count [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f011)
    (total : t.regValue .rsi = 2) (next : t.regValue .rcx = 1) :
    ∃ w, Advances boundary 2 t w ∧ State s w ∧ w.RIP = 0x10f01a ∧
      w.regValue .rsi = 1 ∧ AgreesExcept [.reg 6, .flags, .rip] t w := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (sub_r64_r64_effect_step 0x10f011 0x48 0xce (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf011 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf014 (by decide)))
  have frameA : AgreesExcept [.reg 6, .flags, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp)
  have countA : a.regValue .rsi = 1 := by
    have h := effectA.writes
    change a.regValue .rsi = t.regValue .rsi - t.regValue .rcx at h
    rw [total, next] at h
    exact h.trans (by decide +kernel)
  have zeroA : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have h := effectA.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (t.regValue .rsi - t.regValue .rcx == 0#64) at h
    rw [total, next] at h
    exact h.trans (by decide +kernel)
  have target : (jccEffect 0x10f014 6 4 ((0x100 : BitVec 32).signExtend 64) a).rip = 0x10f01a := by
    simp only [jccEffect, branchEffect, condHolds, zeroA]
    rfl
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (jcc_rel32_effect_step 0x10f014 4 0x100).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf014 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, by intro h; decide +kernel⟩
      (by
        rw [target]
        exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf01a (by decide)))
  have frameW : AgreesExcept [.rip] a w := effectW.agrees
  have frame : AgreesExcept [.reg 6, .flags, .rip] t w :=
    (frameA.trans frameW).mono (by simp)
  exact ⟨w, runA.trans runW,
    state.after_registers readyW frame (by simp [Component.Covers]) (by simp),
    effectW.rip.trans target, (frameW.read (n := 64) (r := 6) (by simp)).trans countA, frame⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
