import ChaCha20Poly1305.Proofs.Decrypt.PolyMul
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101e30

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step2 (x : Input) :
    (Layout.withFrame Fn101e30.active Fn101e30.doneAt (core x)).BlockSimulation fnCode .s2 := by
  x86_refine [program, v101af1, v101af9, v101b02, v101b05, v101b10, v101b13, v101b19, v101b1d, v101b21, v101b28, v101b2f, v101b32, v101b39, v101b3c]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
