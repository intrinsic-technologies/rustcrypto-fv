import ChaCha20Poly1305.Proofs.Decrypt.PolyMul
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step4 (x : Input) :
    (Layout.withFrame Fn101e30.active Fn101e30.doneAt (core x)).BlockSimulation fnCode .s4 := by
  x86_refine [program, v101b88, v101b8e, v101b99, v101b9d, v101ba0, v101ba8, v101bac, v101bbc, v101bc3, v101bc7]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
