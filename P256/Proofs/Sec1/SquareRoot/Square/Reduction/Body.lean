import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.First
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Third
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Fourth
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem body_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (entry : Entry s t boundary)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      ScalarFrame.FrameState s u 32 112 112 ∧ u.RIP = 0x1137a3 ∧
      Nat256At u (s.regValue .rdi)
        (Field.Montgomery.subtractP (Field.Montgomery.reduceFour v)) := by
  obtain ⟨a, ⟨n1, e1⟩, h1⟩ := Body.first_correct pre entry input bound
  obtain ⟨b, ⟨n2, e2⟩, h2⟩ := Body.second_correct pre h1 input bound
  obtain ⟨c, ⟨n3, e3⟩, h3⟩ := Body.third_correct pre h2 bound
  obtain ⟨d, ⟨n4, e4⟩, h4⟩ := Body.fourth_correct pre h3 input bound
  obtain ⟨u, ⟨n5, e5⟩, state, rip, output⟩ := Body.correction_correct pre h4 bound
  exact ⟨u, ⟨n1+n2+n3+n4+n5, (((e1.trans e2).trans e3).trans e4).trans e5⟩,
    state, rip, output⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction
