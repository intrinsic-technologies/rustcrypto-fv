import P256.Proofs.SHA256.LengthEncoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail

theorem full_length_ofNat {n : Nat} (bound : n < 2^32) :
    BitVec.ofNat 64 n &&& 0x7fffffffffffffc0 = BitVec.ofNat 64 (64 * (n / 64)) := by
  have value : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.and_comm, SHA256.full_length _ (by rw [value]; omega), value]

theorem tail_length_ofNat {n : Nat} (bound : n < 2^32) :
    (((BitVec.ofNat 64 n).setWidth 32) &&& 63).setWidth 64 = BitVec.ofNat 64 (n % 64) := by
  have value : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [SHA256.tail_length, value]

end P256.Proofs.Verifying.Message.Hash.Long.Tail
