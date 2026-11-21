import P256.Proofs.Verifying.Core.Correct
import P256.Proofs.Verifying.Core.Inverse.Correct
import P256.Proofs.Verifying.Combination.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

theorem correct : Correct := correct_of_combination Combination.correct

end P256.Proofs.Verifying.Core
