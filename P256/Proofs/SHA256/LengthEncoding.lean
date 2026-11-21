import P256.Proofs.SHA256.Interface
import Standards.SECG.ECC.Encoding
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Program.ReadWrite.Bytes
import P256.Proofs.ReadBe.Input

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem tail_zero_count (tail : Nat) (bound : tail < 64) :
    BitVec.ofNat 64 tail ^^^ 63 = BitVec.ofNat 64 (63 - tail) := by
  have computed : ∀ tail : Fin 64,
      BitVec.ofNat 64 tail.val ^^^ 63 = BitVec.ofNat 64 (63 - tail.val) := by
    decide +kernel
  exact computed ⟨tail, bound⟩

theorem bswap64_ofNat_storedByte (value : Nat) {i : Nat} (hi : i < 8) :
    storedByte (bswap64 (BitVec.ofNat 64 value)) i =
      (Standards.SECG.ECC.Encoding.natToOctets 8 value)[i]'(by
        simpa only [Standards.SECG.ECC.Encoding.natToOctets, ByteArray.size,
          Array.size_map, Array.size_range] using hi) := by
  rw [storedByte_eq_extract, bswap64_byte _ _ hi, ← storedByte_eq_extract]
  rw [P256.Proofs.ReadBe.storedByte_ofNat64 _ _ (by omega)]
  simp only [Standards.SECG.ECC.Encoding.natToOctets, ByteArray.getElem_eq_getElem_data,
    Array.getElem_map, Array.getElem_range]


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

end P256.Proofs.SHA256
