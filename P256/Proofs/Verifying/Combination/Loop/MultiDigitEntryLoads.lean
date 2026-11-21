import P256.Proofs.Verifying.Combination.Loop.MultiDigitState
import P256.Proofs.Verifying.Combination.Loop.MultiLength

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem load_inner_pointers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    (pre : MultiPre s boundary tables digits)
    (state : RoundState s t tables digits p q u v k point 0x10f1a3) :
    ∃ w, Advances boundary 2 t w ∧ RoundState s w tables digits p q u v k point 0x10f1ad ∧
      w.regValue .r12 = 2 ∧ w.regValue .rbp = tables := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r64_m64_effect_step 0x10f1a3 0x4c (by simp [RexWPrefix]) 4
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0xf1a3 _
        (by decide) (by decide +kernel))
      ⟨state.rip, stack_readable pre.toCalleePre state.toFrameState (offset := 8) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1a8 (by decide)))
  have frameA : AgreesExcept [.reg 12, .rip] t a := effectA.agrees
  have stateA := state.after_registers readyA frameA (by simp [Component.Covers]) (by simp) effectA.rip
  have countA : a.regValue .r12 = 2 := by
    have h := effectA.writes
    change a.regValue .r12 = memLoad t.external (stackPtr t + 8#64) 64 at h
    rw [scalar_stack_address state.rsp (offset := 8) (by decide) (by decide)] at h
    exact h.trans state.total
  obtain ⟨w, runW, readyW, effectW⟩ :=
    (mov_r64_m64_effect_step 0x10f1a8 0x48 (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn stateA.loaded) 0xf1a8 _
        (by decide) (by decide +kernel))
      ⟨effectA.rip, stack_readable pre.toCalleePre stateA.toFrameState (offset := 24) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xf1ad (by decide)))
  have frameW : AgreesExcept [.reg 5, .rip] a w := effectW.agrees
  refine ⟨w, runA.trans runW,
    stateA.after_registers readyW frameW (by simp [Component.Covers]) (by simp) effectW.rip,
    (frameW.read (n := 64) (r := 12) (by simp)).trans countA, ?_⟩
  have h := effectW.writes
  change w.regValue .rbp = memLoad a.external (stackPtr a + 24#64) 64 at h
  rw [scalar_stack_address stateA.rsp (offset := 24) (by decide) (by decide)] at h
  exact h.trans stateA.tableBase

end P256.Proofs.Verifying.Combination.Loop.Multi
