import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part1

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 9000
set_option maxHeartbeats 1200000
set_option pp.maxSteps 120
theorem spillValid (x : Input) (fr : Activation) (blocks : Bool) (h : x.n >>> 6 ≠ 0 ↔ blocks = true) : Micro.Valid (spillStep x fr blocks) := by
  unfold Micro.Valid
  cases blocks <;> simp at h
  all_goals refine_one [Micro.program,spillStep,blockPtr,BitVec.add_assoc]
  all_goals first | assumption | rfl | contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
