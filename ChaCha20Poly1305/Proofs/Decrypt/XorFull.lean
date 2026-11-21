import ChaCha20Poly1305.Proofs.Decrypt.Xor
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part2

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 8000
set_option maxHeartbeats 1800000
set_option pp.maxSteps 120
theorem fullStep (x : Input) (exitLoop : Bool) (h : done .full x ↔ exitLoop = true) :
    (layout .full x exitLoop).BlockSimulation fnCode .start := by
  cases exitLoop <;> simp [done,bytes] at h
  all_goals refine_one [program,begins,ends,bytes,setWidth_mergeGPR8]
  all_goals try assumption

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
