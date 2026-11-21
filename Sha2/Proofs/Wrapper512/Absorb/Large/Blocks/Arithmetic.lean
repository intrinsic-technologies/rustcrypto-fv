import Sha2.Proofs.Wrapper512.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem full_length (n : BitVec 64) (bound : n.toNat < 2^58) :
    0x7fffffffffffff80 &&& n = BitVec.ofNat 64 (128 * (n.toNat / 128)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have div := Nat.and_div_two_pow (a := 0x7fffffffffffff80) (b := n.toNat) (n := 7)
  change (0x7fffffffffffff80 &&& n.toNat) / 128 = (2^56-1) &&& (n.toNat/128) at div
  rw [Nat.and_comm (2^56-1) (n.toNat/128), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (by omega)] at div
  have rem := Nat.and_mod_two_pow (a := 0x7fffffffffffff80) (b := n.toNat) (n := 7)
  change (0x7fffffffffffff80 &&& n.toNat) % 128 = 0 &&& (n.toNat%128) at rem
  simp only [Nat.zero_and] at rem
  change (0x7fffffffffffff80 &&& n.toNat) = (128*(n.toNat/128)) % 2^64
  omega

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
