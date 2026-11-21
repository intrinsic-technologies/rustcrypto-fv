import P256.Proofs.Verifying.Message.Hash.Absorb
import P256.Proofs.Verifying.Message.Hash.Finalize.Correct
import P256.Proofs.Verifying.Message.Hash.Serialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

theorem correct : Correct := by
  intro bindings initial s boundary message pre initialized
  obtain ⟨a, buffered⟩ := absorb pre initialized
  obtain ⟨b, finalized⟩ := Finalize.correct pre buffered
  exact Serialize.correct pre finalized

end P256.Proofs.Verifying.Message.Hash
