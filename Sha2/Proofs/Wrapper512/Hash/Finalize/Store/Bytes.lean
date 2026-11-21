import Sha2.Proofs.Wrapper.Hash.LengthEncoding

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Store

open Sha2.Proofs.NIST
open Sha2.Proofs.Common.Encoding

 theorem length_high_byte (n i : Nat) (bound : i < 8) :
    (Encoding.natToOctets 8 (n / 2^64)).data[i]'(by simpa only [ByteArray.size_data, natToOctets_size] using bound) =
      (Encoding.natToOctets 16 n).data[i]'(by simp only [ByteArray.size_data, natToOctets_size]; omega) := by
  rw [natToOctets_getElem _ _ _ bound, natToOctets_getElem _ _ _ (by omega)]
  congr 1
  rw [Nat.div_div_eq_div_mul]
  have power : 256 ^ (16 - 1 - i) = 2^64 * 256 ^ (8 - 1 - i) := by
    rw [show 16 - 1 - i = 8 + (8 - 1 - i) by omega, Nat.pow_add]
  rw [power]

 theorem length_low_byte (n i : Nat) (bound : i < 8) :
    (Encoding.natToOctets 8 n).data[i]'(by simpa only [ByteArray.size_data, natToOctets_size] using bound) =
      (Encoding.natToOctets 16 n).data[8+i]'(by simp only [ByteArray.size_data, natToOctets_size]; omega) := by
  rw [natToOctets_getElem _ _ _ bound, natToOctets_getElem _ _ _ (by omega)]
  rw [show 16 - 1 - (8+i) = 8 - 1 - i by omega]

end Sha2.Proofs.Wrapper512.Hash.Finalize.Store
