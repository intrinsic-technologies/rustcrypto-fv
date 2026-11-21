import ChaCha20Poly1305.Proofs.Decrypt.StreamControl
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part2

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 9000
set_option maxHeartbeats 1200000
set_option pp.maxSteps 120
theorem loadValid (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8) : Micro.Valid (loadStep x j fr v) := by
  unfold Micro.Valid
  all_goals x86_refine [Micro.program,loadStep,blockPtr]
  all_goals first | assumption | rfl | contradiction

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
