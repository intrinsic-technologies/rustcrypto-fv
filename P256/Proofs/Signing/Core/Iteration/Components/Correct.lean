import P256.Proofs.Signing.Core.Iteration.Components.Conditional
import P256.Proofs.Signing.Core.Iteration.Components.Addition.Correct
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

theorem correct : ComponentsContract :=
  correct_of_callees Addition.correct Constructor.correct

end P256.Proofs.Signing.Core.Iteration.Components
