import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101ce0

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step5 (x : Input) :
    (Layout.withFrame Fn101ce0.active Fn101ce0.doneAt (core x)).BlockSimulation fnCode .s5 := by
  x86_refine [program]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
