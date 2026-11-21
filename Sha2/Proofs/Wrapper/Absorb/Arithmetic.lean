import Sha2.Proofs.Wrapper.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem full_length (n : BitVec 64) (bound : n.toNat < 2^61) :
    0x7fffffffffffffc0 &&& n = BitVec.ofNat 64 (64 * (n.toNat / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have div := Nat.and_div_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) / 64 = (2^57-1) &&& (n.toNat/64) at div
  rw [Nat.and_comm (2^57-1) (n.toNat/64), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := 0x7fffffffffffffc0) (b := n.toNat) (n := 6)
  change (0x7fffffffffffffc0 &&& n.toNat) % 64 = 0 &&& (n.toNat%64) at rem
  simp only [Nat.zero_and] at rem
  change (0x7fffffffffffffc0 &&& n.toNat) = (64*(n.toNat/64)) % 2^64
  omega

theorem tail_length (n : BitVec 64) :
    ((n.setWidth 32) &&& 63).setWidth 64 = BitVec.ofNat 64 (n.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (n.setWidth 32).toNat &&& (2^6-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have mod := Nat.mod_mod_of_dvd n.toNat (show 64 ∣ 2^32 by decide)
  have bound := Nat.mod_lt n.toNat (by decide : 0 < 64)
  omega

theorem block_count (n : BitVec 64) : n >>> 6 = BitVec.ofNat 64 (n.toNat / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow, BitVec.toNat_ofNat]
  have := n.isLt
  omega

end Sha2.Proofs.Wrapper.Absorb
