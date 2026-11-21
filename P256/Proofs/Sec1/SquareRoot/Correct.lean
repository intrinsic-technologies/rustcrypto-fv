import P256.Proofs.Sec1.SquareRoot.Prepare
import P256.Proofs.Sec1.SquareRoot.Exponent
import P256.Proofs.Sec1.SquareRoot.ExponentCall
import P256.Proofs.Sec1.SquareRoot.Middle
import P256.Proofs.Sec1.SquareRoot.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem field_sqrt_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : Pre s boundary) (input : Field.MontgomeryAt s (s.regValue .rsi) x) :
    ∃ t, CalleeResult s t boundary 40 2176 ∧ SquareRootResultAt t (s.regValue .rdi) x := by
  obtain ⟨na, a, runA, stateA⟩ := field_sqrt_prepare pre input
  obtain ⟨nb, b, runB, stateB, ripB, r14B, inputB, candidateB⟩ :=
    exponent_stage pre stateA (fun _ ctx ↦ dynamic_pow_sqrt_correct ctx)
  obtain ⟨nc, c, runC, stateC, ripC, inputC, candidateC, squareC⟩ :=
    square_stage pre stateB ripB r14B inputB candidateB
  exact finish_square_root pre stateC ((runA.trans runB).trans runC) ripC
    inputC candidateC squareC

end P256.Proofs.Sec1.SquareRoot
