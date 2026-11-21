import ChaCha20Poly1305.Proofs.Decrypt.PolyMul
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step7 (x : Input) :
    (Layout.withFrame Fn101e30.active Fn101e30.doneAt (core x)).BlockSimulation fnCode .s7 := by
  x86_refine [program, v101c66, v101c6d, v101c73, v101c79, v101c7f, v101c85, v101c89, v101c8c, v101c91, v101c94, v101c97]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
