import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First.Upper

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem first_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Entry s t boundary)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ First s u v := by
  have _ := bound
  obtain ⟨mid, ⟨fuel1, run1⟩, stage⟩ := FirstRound.lower pre state input
  obtain ⟨u, ⟨fuel2, run2⟩, frame, rip, slots, inverse, rcx, rsi, rdi, rbp, r13, value⟩ :=
    FirstRound.upper pre stage input
  refine ⟨u, ⟨fuel1+fuel2, run1.trans run2⟩, ⟨frame, rip, slots, inverse, rcx, rsi, rdi, rbp, r13, ?_⟩⟩
  have result := FirstRound.inputWords_value v
  rw [← value] at result
  dsimp only [Limbs.toNat] at result
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
