import P256.Proofs.Verifying.Message.Correct
import P256.Proofs.Verifying.Message.Hash
import P256.Proofs.Verifying.Core

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

theorem correct : Correct := correct_of_hash_core Hash.correct Core.correct

end P256.Proofs.Verifying.Message
