import Sha2.Proofs.Common.SHA512.Compression.Assembly
import Sha2.Proofs.Common.SHA512.Compression.Values.Complete
import Sha2.Proofs.Common.SHA512.Compression.Values.Endpoints

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression

open X86.Machine

theorem block_correct [Bindings] : BlockCorrect := by
  intro initial boundary hash block ready loaded outside pre
  exact block_result_of_values ready loaded outside pre
    (Values.Correctness.hashState_correct Values.Correctness.run_correct
      loaded pre.registers pre.inputBytes)

end Sha2.Proofs.Common.SHA512.Compression
