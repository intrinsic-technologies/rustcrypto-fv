import ChaCha20Poly1305.Proofs.Decrypt.PolyMul
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step6 (x : Input) :
    (Layout.withFrame Fn101e30.active Fn101e30.doneAt (core x)).BlockSimulation fnCode .s6 := by
  x86_refine [program, v101c13, v101c16, v101c1a, v101c1d, v101c23, v101c27, v101c2a, v101c2e, v101c32, v101c35, v101c38, v101c3c, v101c42, v101c46, v101c50, v101c58, v101c5c]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
