import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.ThirdMachine
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.StageArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem third_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Second s t v)
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Third s u v := by
  have _ := bound
  obtain ⟨u, run, result⟩ := Upper.third_machine pre state
  refine ⟨u, run, ⟨result.frame, result.rip, result.slots, result.inverse,
    result.inputPointer, result.rdi, result.rsi, result.rbp, result.carry, ?_⟩⟩
  have value := Upper.third_value state
  dsimp only at value
  rw [← result.words, ← result.carryValue] at value
  dsimp only [Limbs.toNat] at value
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
