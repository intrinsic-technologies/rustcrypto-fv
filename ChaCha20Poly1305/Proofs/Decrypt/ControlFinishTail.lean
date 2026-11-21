import ChaCha20Poly1305.Proofs.Decrypt.TailControl
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part4

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 8000
set_option maxHeartbeats 450000
set_option pp.maxSteps 120
theorem finishTailValid (x : Input) (fr : Activation) : Micro.Valid (finishTail x fr ) := by
  unfold Micro.Valid
  all_goals refine_one [Micro.program,finishTail,tailPtr,groups,rem4]
  all_goals first | assumption | rfl | contradiction | (congr 1 <;> bv_omega)

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
