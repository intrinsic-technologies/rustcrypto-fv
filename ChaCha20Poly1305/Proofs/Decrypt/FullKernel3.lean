import ChaCha20Poly1305.Proofs.Decrypt.FullKernel
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part2

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

set_option maxRecDepth 8000
set_option maxHeartbeats 600000
set_option pp.maxSteps 120
theorem secondStep (x : Input) (j : BitVec 64) : (layout x j).BlockSimulation fnCode .second := by
  refine_one [program]
  all_goals try rfl

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
