import Base16ct.Spec.Base16

namespace Base16ct.Proofs.EncodeStr.Lower

open Standards.RFC.BaseEncodings

def lowerDigit (value : BitVec 32) : BitVec 8 :=
  ((((57#32 - (value ||| 48#32)) >>> 8).extractLsb' 0 8) &&& 39#8) +
    (value ||| 48#32).extractLsb' 0 8

def lowerHighDigit (b : UInt8) : BitVec 8 :=
  lowerDigit (BitVec.ofNat 32 b.toNat >>> 4)

def lowerLowDigit (b : UInt8) : BitVec 8 :=
  lowerDigit (BitVec.ofNat 32 b.toNat &&& 15#32)

theorem lowerDigit_character (value : Nat) (h : value < 16) :
    lowerDigit (BitVec.ofNat 32 value) =
      (Alphabet.base16Lower.character value).toBitVec := by
  exact (by decide +kernel : ∀ n : Fin 16,
    lowerDigit (BitVec.ofNat 32 n.val) =
      (Alphabet.base16Lower.character n.val).toBitVec) ⟨value, h⟩

theorem lowerHighNibble_eq (b : UInt8) :
    BitVec.ofNat 32 b.toNat >>> 4 = BitVec.ofNat 32 (b.toNat / 16) := by
  have hb := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem lowerLowNibble_eq (b : UInt8) :
    BitVec.ofNat 32 b.toNat &&& 15#32 = BitVec.ofNat 32 (b.toNat % 16) := by
  have hb := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change (b.toNat % 2 ^ 32) &&& (2 ^ 4 - 1) = (b.toNat % 16) % 2 ^ 32
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem lowerHighDigit_character (b : UInt8) :
    lowerHighDigit b = (Alphabet.base16Lower.character (b.toNat / 16)).toBitVec := by
  rw [lowerHighDigit, lowerHighNibble_eq]
  apply lowerDigit_character
  have hb := b.toNat_lt
  omega

theorem lowerLowDigit_character (b : UInt8) :
    lowerLowDigit b = (Alphabet.base16Lower.character (b.toNat % 16)).toBitVec := by
  rw [lowerLowDigit, lowerLowNibble_eq]
  exact lowerDigit_character _ (Nat.mod_lt _ (by decide))

theorem lengthMask_eq (n : BitVec 64) (h : n.toNat < 2 ^ 32) :
    n &&& 0x3fffffffffffffff#64 = n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  change n.toNat &&& (2 ^ 62 - 1) = n.toNat
  apply Nat.and_two_pow_sub_one_of_lt_two_pow
  omega

theorem lengthDouble_toNat (n : BitVec 64) (h : n.toNat < 2 ^ 32) :
    (n + n).toNat = 2 * n.toNat := by
  simp only [BitVec.toNat_add]
  omega

theorem lengthDouble_lt (n : BitVec 64) (h : n.toNat < 2 ^ 32) :
    (n + n).toNat < 2 ^ 33 := by
  rw [lengthDouble_toNat n h]
  omega

end Base16ct.Proofs.EncodeStr.Lower
