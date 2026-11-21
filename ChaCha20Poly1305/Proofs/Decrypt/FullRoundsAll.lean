import ChaCha20Poly1305.Proofs.Decrypt.FullRounds0
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds1
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds2
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds3
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds4
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds5
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds6
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds7
import ChaCha20Poly1305.Proofs.Decrypt.FullRounds8

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.FullRounds
open ChaCha20Poly1305.Proofs.Decrypt.Lifted (fnCode)

theorem blocks : ∀ l, l ≠ .finish → layout.BlockSimulation fnCode l
  | .q0, _ => step0
  | .q1, _ => step1
  | .q2, _ => step2
  | .q3, _ => step3
  | .q4, _ => step4
  | .q5, _ => step5
  | .q6, _ => step6
  | .q7, _ => step7
  | .count, _ => step8
  | .finish, h => False.elim (h rfl)

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound.FullRounds
