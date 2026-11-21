import Sha2.Proofs.NIST.SHA512
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Encoding

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
export Sha2.Proofs.Common.SHA256 (octetsToBits_size octetsToBits_getElem! octetsToBits_getElem
  octetsToBits_append octetsToBits_extract octetsToBits_replicate_zero
  octetsToBits_paddingMarker octetsToBits_natToOctets)
end Sha2.Proofs.Common.SHA512
