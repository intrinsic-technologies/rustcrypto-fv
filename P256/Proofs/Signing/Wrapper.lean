import P256.Proofs.Signing.Wrapper.Compose
import P256.Proofs.Signing.Wrapper.Entry
import P256.Proofs.Signing.Wrapper.Hash
import P256.Proofs.Signing.Wrapper.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper

theorem correct : WrapperContract :=
  wrapper_of_contracts Entry.correct Hash.correct finish_correct

end P256.Proofs.Signing.Wrapper
