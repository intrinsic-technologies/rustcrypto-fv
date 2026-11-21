import Hkdf.Proofs.NIST.Encoding
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Encoding

open Hkdf.Proofs.NIST.Encoding

theorem natToOctets_size (length value : Nat) :
    (natToOctets length value).size = length := by
  simp [natToOctets, ByteArray.size]

theorem natToOctets_getElem (length value i : Nat) (hi : i < length) :
    (natToOctets length value).data[i]'(by simpa only [ByteArray.size_data,
      natToOctets_size] using hi) =
      UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256) := by
  simp [natToOctets]

theorem natToOctets_getElem? (length value i : Nat) (hi : i < length) :
    (natToOctets length value).data[i]? =
      some (UInt8.ofNat (value / 256 ^ (length - 1 - i) % 256)) := by
  simp [natToOctets, hi]

end Hkdf.Proofs.Common.Encoding
