import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part1

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 9000
set_option maxHeartbeats 1200000
set_option pp.maxSteps 120
theorem prepareValid (x : Input) (fr : Activation) : Micro.Valid (prepareStep x fr) := by
  unfold Micro.Valid
  all_goals refine_one [Micro.program,prepareStep,blockPtr,BitVec.add_assoc]
  all_goals first | assumption | rfl | contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
