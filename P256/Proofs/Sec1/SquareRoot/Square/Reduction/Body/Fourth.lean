import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.FourthMachine
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.StageArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fourth_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Third s t v)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Fourth s u v := by
  obtain ⟨u, run, result⟩ := Upper.FourthRound.machine pre state input
  refine ⟨u, run, ⟨result.frame, result.rip, result.slots, result.rdi, result.r11,
    result.top, ?_⟩⟩
  have value := Upper.fourth_value state bound
  dsimp only at value
  rw [← result.words, ← result.high] at value
  dsimp only [Limbs.toNat] at value
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
