import P256.Proofs.Signing.Wrapper.Entry.Stages
import P256.Proofs.Signing.Wrapper.Entry.Compose
import P256.Proofs.Signing.Wrapper.Entry.Decode
import P256.Proofs.Signing.Wrapper.Entry.Construct
import P256.Proofs.Signing.Wrapper.Entry.HashCall

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry

theorem correct : EntryContract :=
  correct_of_contracts decode_correct Construct.correct HashCall.correct

end P256.Proofs.Signing.Wrapper.Entry
