import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize
import P256.Proofs.Sec1.SquareRoot.Exponent.Loop
import P256.Proofs.Sec1.SquareRoot.Exponent.Finish
import P256.Proofs.Projective.Algebra.Field.Power
import P256.Proofs.Sec1.SquareRoot.Value

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess

theorem dynamic_pow_sqrt_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ t, CalleeResult s t boundary 32 1584 ∧ Field.MontgomeryAt t (s.regValue .rdi) (candidate x) := by
  obtain ⟨v, initialFuel, initialRun, initialState⟩ := exponent_initialize ctx
  obtain ⟨w, loopFuel, loopRun, finalState⟩ :=
    exponent_loop ctx initialState (by decide) (by decide)
  obtain ⟨t, result, residue⟩ := exponent_finish ctx finalState
    ⟨initialFuel + loopFuel, initialRun.trans loopRun⟩
  exact ⟨t, result, by simpa only [candidate,
    P256.Proofs.Projective.Algebra.FieldArithmetic.powMod_eq_pow_mod] using residue⟩

end P256.Proofs.Sec1.SquareRoot
