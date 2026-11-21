import P256.Proofs.Signing.Core.Iteration.Compose
import P256.Proofs.Signing.Core.Iteration.Components.Correct
import P256.Proofs.Signing.Core.Iteration.Point.Correct
import P256.Proofs.Signing.Core.Iteration.Output

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

theorem correct : IterationContract :=
  correct_of_contracts Point.correct Components.correct Output.correct

end P256.Proofs.Signing.Core.Iteration
