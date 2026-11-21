import Md5.Proofs.MemoryRoutines.Memset.Preparation

namespace Md5.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs

def broadcast (b : BitVec 8) : BitVec 64 := 0x0101010101010101 * b.setWidth 64

theorem broadcast_storedByte (b : BitVec 8) (i : Nat) (hi : i < 8) :
    storedByte (broadcast b) i = UInt8.ofBitVec b := by
  have h : ∀ b : BitVec 8, ∀ i : Fin 8,
      storedByte (broadcast b) i.val = UInt8.ofBitVec b := by decide +kernel
  exact h b ⟨i, hi⟩

theorem broadcast_lowByte (b : BitVec 8) : (broadcast b).setWidth 8 = b := by
  have h : ∀ b : BitVec 8, (broadcast b).setWidth 8 = b := by decide +kernel
  exact h b

theorem byte_storedByte (b : BitVec 8) : storedByte b 0 = UInt8.ofBitVec b := by
  have h : ∀ b : BitVec 8, storedByte b 0 = UInt8.ofBitVec b := by decide +kernel
  exact h b

theorem sub_toNat (x y : BitVec 64) (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat :=
  BitVec.toNat_sub_of_le h

theorem shr_three_toNat (x : BitVec 64) : (x >>> 3).toNat = x.toNat / 8 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem low32_mask_toNat (x : BitVec 64) :
    (((x.setWidth 32) &&& (7 : BitVec 32)).setWidth 64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
    mask7_toNat _ (by decide), BitVec.toNat_setWidth]
  omega

end Md5.Proofs.MemoryRoutines.Memset
