import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn101ce0

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 6000
set_option maxHeartbeats 800000
set_option pp.maxSteps 1000

theorem step3 (x : Input) :
    (Layout.withFrame Fn101ce0.active Fn101ce0.doneAt (core x)).BlockSimulation fnCode .s3 := by
  x86_refine [program, v101db0, v101db2, v101db4, v101db6, v101db9, v101dbc, v101dc2, v101dc6, v101dc9, v101dd0, v101dd4, v101dd7, v101ddd, v101de1, v101de4, v101de7, v101dea]
  all_goals first | rfl | assumption | ac_rfl

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
