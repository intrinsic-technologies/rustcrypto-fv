import Sha2.Proofs.Wrapper512.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem full_length (n : BitVec 64) (bound : n.toNat < 2^58) :
    0xffffffffffffff80 &&& n = BitVec.ofNat 64 (128 * (n.toNat / 128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have div := Nat.and_div_two_pow (a := 0xffffffffffffff80) (b := n.toNat) (n := 7)
  change (0xffffffffffffff80 &&& n.toNat) / 128 = (2^57-1) &&& (n.toNat/128) at div
  rw [Nat.and_comm (2^57-1) (n.toNat/128), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := 0xffffffffffffff80) (b := n.toNat) (n := 7)
  change (0xffffffffffffff80 &&& n.toNat) % 128 = 0 &&& (n.toNat%128) at rem
  simp only [Nat.zero_and] at rem
  change (0xffffffffffffff80 &&& n.toNat) = (128*(n.toNat/128)) % 2^64
  omega

theorem tail_length (n : BitVec 64) :
    ((n.setWidth 32) &&& 127).setWidth 64 = BitVec.ofNat 64 (n.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (n.setWidth 32).toNat &&& (2^7-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have mod := Nat.mod_mod_of_dvd n.toNat (show 128 ∣ 2^32 by decide)
  have bound := Nat.mod_lt n.toNat (by decide : 0 < 128)
  omega

theorem block_count (n : BitVec 64) : n >>> 7 = BitVec.ofNat 64 (n.toNat / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow,
    BitVec.toNat_ofNat]
  have h := n.isLt
  omega

end Sha2.Proofs.Wrapper512.Absorb
