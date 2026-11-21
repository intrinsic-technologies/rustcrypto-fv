import ChaCha20Poly1305.Proofs.Decrypt.Stream
import ChaCha20Poly1305.Proofs.Decrypt.Refine
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part1

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
set_option pp.maxSteps 150
theorem entryBlock (x : Input) :
    (Layout.withFrame Fn100a80.active Fn100a80.doneAt (core x)).BlockSimulation fnCode .entry := by
  have hn := x.len
  refine_one [program]
  all_goals try assumption

end ChaCha20Poly1305.Proofs.Decrypt.Stream
