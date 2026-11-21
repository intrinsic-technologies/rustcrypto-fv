import ChaCha20Poly1305.Proofs.Decrypt.TailRounds
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn100a80.Part3

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.TailRounds
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

set_option maxRecDepth 4000
set_option maxHeartbeats 250000
set_option pp.maxSteps 2000

theorem step1 : layout.BlockSimulation fnCode .q1 := by
  x86_refine [program, advance]
  all_goals simp +decide only [qround, Vector.getElem_set] 
  all_goals rfl

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.TailRounds
