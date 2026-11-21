import P256.Proofs.Sec1Serialize.Conversion
import P256.Proofs.Sec1Serialize.Tail

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open Prelude X86 X86.Machine

theorem serializer_correct (bindings : Bindings) : Contract bindings :=
  contract_of_stages conversion_correct tail_correct

end P256.Proofs.Sec1Serialize
