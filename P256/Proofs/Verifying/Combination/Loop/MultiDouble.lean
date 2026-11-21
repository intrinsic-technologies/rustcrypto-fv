import P256.Proofs.Verifying.Combination.Loop.MultiDouble.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem double_correct : DoubleCorrect := by
  intro _ s t boundary tables digits p q point u v k pre state
  obtain ⟨a, runA, memoryA, ripA, agreesA⟩ := double_branch pre state.toMemory state.rip
  have readyA := readyToStep memoryA.machine memoryA.bindingsSupported
  have stateA := state.after_registers readyA agreesA (by simp [Component.Covers]) (by simp) ripA
  cases h : (t.regValue .r14).getLsbD 0 with
  | false =>
    have pointEq := state.identity h
    have doubled : point.double = point := by rw [pointEq]; exact Algebra.identity_double
    refine ⟨2, a, runA, ?_⟩
    rw [doubled]
    simpa only [h, Bool.false_eq_true, ↓reduceIte] using stateA
  | true =>
    have start : RoundState s a tables digits p q u v k point 0x10f17a := by
      simpa only [h, ↓reduceIte] using stateA
    obtain ⟨n, w, runW, stateW⟩ := double_path pre start
    exact ⟨2+n, w, runA.trans runW, stateW⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
