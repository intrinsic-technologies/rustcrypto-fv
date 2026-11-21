import P256.Proofs.Verifying.Combination.Compose
import P256.Proofs.Verifying.Combination.Table.Correct
import P256.Proofs.Verifying.Combination.Preparation.Naf.Correct
import P256.Proofs.Verifying.Combination.Loop.Multi

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination

theorem correct : Correct :=
  correct_of_contracts Table.correct Preparation.Naf.correct Loop.multi_correct

end P256.Proofs.Verifying.Combination
