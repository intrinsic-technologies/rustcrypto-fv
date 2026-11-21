import Sha2.Proofs.Common.SHA256.Compression.Assembly
import Sha2.Proofs.Common.SHA256.Compression.Values.Complete

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression

open X86.Machine

theorem block_correct [Bindings] : BlockCorrect := by
  intro initial boundary hash block ready loaded outside pre
  exact block_result_of_values ready loaded outside pre
    (Values.Correctness.hashState_correct pre.registers pre.inputBytes)

end Sha2.Proofs.Common.SHA256.Compression
