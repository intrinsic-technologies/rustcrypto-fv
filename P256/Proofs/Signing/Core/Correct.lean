import P256.Proofs.Signing.Core
import P256.Proofs.Signing.Core.Initialize
import P256.Proofs.Signing.Core.NextNonce
import P256.Proofs.Signing.Core.Iteration

set_option autoImplicit false

namespace P256.Proofs.Signing

theorem core_correct : CoreContract :=
  core_correct_of_contracts Core.Initialize.correct Core.nextNonce_correct Core.Iteration.correct

end P256.Proofs.Signing
