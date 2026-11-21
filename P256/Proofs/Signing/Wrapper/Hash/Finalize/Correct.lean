import P256.Proofs.Signing.Wrapper.Hash.Finalize.Copy.Correct
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad.Correct
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Correct
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Serialize.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

theorem correct : Correct := by
  intro _ initial start s secret message pre state
  obtain ⟨a, copied⟩ := copy pre state
  obtain ⟨b, padded⟩ := pad pre copied
  obtain ⟨c, compressed⟩ := compress pre padded
  exact Serialize.correct pre compressed

end P256.Proofs.Signing.Wrapper.Hash.Finalize
