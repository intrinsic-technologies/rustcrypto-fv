import ChaCha20Poly1305.Proofs.Decrypt.TailKernel
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part4

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

set_option maxRecDepth 8000
set_option maxHeartbeats 600000
set_option pp.maxSteps 100
theorem counterStep (x : Input) : (layout x).BlockSimulation fnCode .counter := by
  refine_one [program,base64]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
