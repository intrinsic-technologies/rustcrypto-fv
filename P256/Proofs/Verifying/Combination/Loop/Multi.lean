import P256.Proofs.Verifying.Combination.Loop.MultiIteration
import P256.Proofs.Verifying.Combination.Loop.MultiDouble
import P256.Proofs.Verifying.Combination.Loop.MultiSelection
import P256.Proofs.Verifying.Combination.Loop.MultiNegative

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop

theorem multi_correct : MultiCorrect :=
  Multi.multi_of_stages Multi.double_correct (Multi.selection_correct Multi.negative_correct)

end P256.Proofs.Verifying.Combination.Loop
