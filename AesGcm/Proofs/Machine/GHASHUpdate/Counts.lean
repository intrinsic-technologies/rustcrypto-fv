import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.GHASHUpdate
open X86Proofs X86Proofs.Refine

theorem nat_and_shifted_mask (x lo hi : Nat) :
    x &&& ((2^hi-1)*2^lo) = (x / 2^lo % 2^hi) * 2^lo := by
  have hd : (x &&& ((2^hi-1)*2^lo)) / 2^lo = x / 2^lo % 2^hi := by
    rw [Nat.and_div_two_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos lo), Nat.and_two_pow_sub_one_eq_mod]
  have hm : (x &&& ((2^hi-1)*2^lo)) % 2^lo = 0 := by
    rw [Nat.and_mod_two_pow, Nat.mul_mod_left, Nat.and_zero]
  have h := Nat.mod_add_div (x &&& ((2^hi-1)*2^lo)) (2^lo)
  rw [hd, hm, Nat.zero_add, Nat.mul_comm] at h
  exact h.symm

theorem shift_count_toNat (count : BitVec 64) (h : 16*count.toNat ≤ 2^32) :
    (count <<< 4).toNat = 16*count.toNat := by
  rw [BitVec.toNat_shiftLeft]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem batch_count_mask (count : BitVec 64) (h : 16*count.toNat ≤ 2^32) :
    (0x7fffffffffffffc0#64 &&& (count <<< 4)).toNat = 64*(count.toNat/4) := by
  rw [BitVec.toNat_and, shift_count_toNat count h, Nat.and_comm]
  change (16*count.toNat &&& ((2^57-1)*2^6)) = _
  rw [nat_and_shifted_mask]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem tail_count_mask (count : BitVec 64) (h : 16*count.toNat ≤ 2^32) :
    ((count <<< 4) &&& 0x30#64).toNat = 16*(count.toNat%4) := by
  rw [BitVec.toNat_and, shift_count_toNat count h]
  change (16*count.toNat &&& ((2^2-1)*2^4)) = _
  rw [nat_and_shifted_mask]
  simp only [Nat.reducePow]
  omega

theorem tail_count_offset (count : BitVec 64) (h : 16*count.toNat ≤ 2^32) :
    ((count &&& 0x7fffffffffffffc#64) <<< 4).toNat = 64*(count.toNat/4) := by
  have hn : 16*(count &&& 0x7fffffffffffffc#64).toNat ≤ 2^32 := by
    rw [BitVec.toNat_and]
    have := Nat.and_le_left (n := count.toNat) (m := (0x7fffffffffffffc#64).toNat)
    omega
  rw [shift_count_toNat _ hn, BitVec.toNat_and]
  change 16*(count.toNat &&& ((2^57-1)*2^2)) = _
  rw [nat_and_shifted_mask]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end AesGcm.Proofs.Machine.GHASHUpdate
