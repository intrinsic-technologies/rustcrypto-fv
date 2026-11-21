import P256.Proofs.Program.Compare.Model

namespace P256.Proofs.Program.Compare

theorem aligned_length (length : BitVec 64) :
    (length &&& (0xf0#8).signExtend 64).toNat = 16 * (length.toNat / 16) := by
  have hm : (0xf0#8).signExtend 64 = BitVec.allOnes 64 <<< 4 := by decide +kernel
  rw [hm, ← BitVec.shiftLeft_ushiftRight]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  change (length.toNat / 16 * 16) % 2^64 = 16 * (length.toNat / 16)
  rw [Nat.mod_eq_of_lt (by have := length.isLt; omega)]
  omega

theorem remaining_length (length : BitVec 64) :
    ((length.setWidth 32 &&& 15).zeroExtend 64).toNat = length.toNat % 16 := by
  simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_and]
  change ((length.toNat % 2^32) &&& 15) % 2^64 = length.toNat % 16
  rw [show 15 = 2^4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

end P256.Proofs.Program.Compare
