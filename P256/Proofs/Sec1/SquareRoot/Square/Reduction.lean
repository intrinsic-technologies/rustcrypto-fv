import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Return

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square

open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reduction_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256)))
    (bound : v < P256.Spec.Operations.domain.p * 2^256) :
    ∃ t, CalleeResult s t boundary 32 112 ∧
      Nat256At t (s.regValue .rdi)
        (Field.Montgomery.subtractP (Field.Montgomery.reduceFour v)) := by
  obtain ⟨t, entry⟩ := Reduction.entry_correct pre
  obtain ⟨u, ⟨fuel, run⟩, state, rip, value⟩ :=
    Reduction.body_correct pre entry input bound
  obtain ⟨final, result, memory⟩ := Reduction.epilogue pre state
    ⟨7 + fuel, entry.execution.trans run⟩ rip
  exact ⟨final, result, value.1, fun i hi => by rw [memory]; exact value.2 i hi⟩

end P256.Proofs.Sec1.SquareRoot.Square
