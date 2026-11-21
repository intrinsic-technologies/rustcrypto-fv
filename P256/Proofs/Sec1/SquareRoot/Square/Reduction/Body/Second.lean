import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Start
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Tail

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem second_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : First s t v)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Second s u v := by
  obtain ⟨fuel, mid, run, frame, effect⟩ := Second.prefix_correct pre state
  obtain ⟨u, ⟨rest, tail⟩, result⟩ := Second.tail_correct pre state effect frame input bound
  exact ⟨u, ⟨fuel + rest, run.trans tail⟩, result⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
