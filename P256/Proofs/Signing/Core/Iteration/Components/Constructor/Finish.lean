import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Checks
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Branch
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512)
    (state : Decoded s t boundary r scalarS) :
    ∃ u, CalleeResult s u boundary 72 512 ∧ ConstructorResult u (s.regValue .rdi) r scalarS := by
  obtain ⟨a, ast, arip, aax, ax, ay⟩ :=
    Finish.Checks.check pre state.toStage false state.rip state.first state.second
  simp only [Bool.false_eq_true, ite_false] at arip aax
  obtain ⟨b, runb, readyb, brip, fb⟩ := Finish.zero_branch false
    (zero := decide (r = 0))
    (readyToStep ast.machine ast.bindingsSupported) ast.loaded pre.outerBoundary arip
    (by simpa only [decide_eq_true_eq] using aax)
  have bst := ast.after_registers runb readyb fb (by simp [Component.Covers]) (by simp)
  by_cases first : r = 0
  · obtain ⟨u, result, tag⟩ := Finish.reject pre bst
      (by simpa only [first, decide_true, ite_true] using brip)
    exact ⟨u, result, by simpa only [ConstructorResult, first, true_or, ite_true] using tag⟩
  · have bstart : b.RIP = 0x1099c5 := by simpa [first] using brip
    have memory := fb.external (by simp [Component.Covers])
    have rsp : stackPtr b = stackPtr a := fb.read (n := 64) (r := 4) (by simp)
    have bx : Nat256At b (stackPtr b + 64#64) r := by
      simpa only [Nat256At, memory, rsp] using ax
    have by' : Nat256At b (stackPtr b + 96#64) scalarS := by
      simpa only [Nat256At, memory, rsp] using ay
    obtain ⟨c, cst, crip, cax, cx, cy⟩ := Finish.Checks.check pre bst true bstart bx by'
    simp only [ite_true] at crip cax
    obtain ⟨d, rund, readyd, drip, fd⟩ := Finish.zero_branch true
      (zero := decide (scalarS = 0))
      (readyToStep cst.machine cst.bindingsSupported) cst.loaded pre.outerBoundary crip
      (by simpa only [decide_eq_true_eq] using cax)
    have dst := cst.after_registers rund readyd fd (by simp [Component.Covers]) (by simp)
    by_cases second : scalarS = 0
    · obtain ⟨u, result, tag⟩ := Finish.reject pre dst
        (by simpa only [second, decide_true, ite_true] using drip)
      exact ⟨u, result, by simpa only [ConstructorResult, second, or_true, ite_true] using tag⟩
    · have dstart : d.RIP = 0x109a2c := by simpa [second] using drip
      have memory := fd.external (by simp [Component.Covers])
      have rsp : stackPtr d = stackPtr c := fd.read (n := 64) (r := 4) (by simp)
      have dx : Nat256At d (stackPtr d + 64#64) r := by
        simpa only [Nat256At, memory, rsp] using cx
      have dy : Nat256At d (stackPtr d + 96#64) scalarS := by
        simpa only [Nat256At, memory, rsp] using cy
      obtain ⟨u, result, tag, ux, uy⟩ := Finish.accept pre dst dstart dx dy
      exact ⟨u, result, by simpa only [ConstructorResult, first, second, false_or, ite_false] using
        (And.intro tag ⟨ux, uy⟩)⟩

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
