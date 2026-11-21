import Base16ct.Proofs.EncodeStr.Upper.Encoding
import X86Proofs.Core.Gpr

set_option autoImplicit false

namespace Base16ct.Proofs.EncodeStr.Upper

open Standards.RFC.BaseEncodings X86Proofs

def nibbleCharacter (n : BitVec 32) : BitVec 8 :=
  ((((57 - n) >>> 8).setWidth 8) &&& 7) + n.setWidth 8

theorem nibbleCharacter_eq (n : Nat) (h : n < 16) :
    UInt8.ofBitVec (nibbleCharacter (BitVec.ofNat 32 n ||| 0x30)) =
      Alphabet.base16Upper.character n := by
  have hn : ∀ i : Fin 16,
      UInt8.ofBitVec (nibbleCharacter (BitVec.ofNat 32 i.val ||| 0x30)) =
        Alphabet.base16Upper.character i.val := by
    decide +kernel
  exact hn ⟨n, h⟩

theorem byte_shiftRight_four (b : UInt8) :
    b.toBitVec.setWidth 32 >>> 4 = BitVec.ofNat 32 (b.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.toNat_lt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 32),
    UInt8.toNat_toBitVec, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

theorem byte_and_fifteen (b : UInt8) :
    b.toBitVec.setWidth 32 &&& 0xf = BitVec.ofNat 32 (b.toNat % 16) := by
  rw [← BitVec.ofNat_toNat 32 b.toBitVec]
  change BitVec.ofNat 32 b.toNat &&& BitVec.ofNat 32 (2^4 - 1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

theorem nibbleCharacter_high (b : UInt8) :
    UInt8.ofBitVec (nibbleCharacter ((b.toBitVec.setWidth 32 >>> 4) ||| 0x30)) =
      Alphabet.base16Upper.character (b.toNat / 16) := by
  rw [byte_shiftRight_four]
  exact nibbleCharacter_eq _ (by have := b.toNat_lt; omega)

theorem nibbleCharacter_low (b : UInt8) :
    UInt8.ofBitVec (nibbleCharacter ((b.toBitVec.setWidth 32 &&& 0xf) ||| 0x30)) =
      Alphabet.base16Upper.character (b.toNat % 16) := by
  rw [byte_and_fifteen]
  exact nibbleCharacter_eq _ (by omega)

theorem encodeByte_eq_nibbleCharacter (b : UInt8) :
    encodeByte b =
      [UInt8.ofBitVec (nibbleCharacter ((b.toBitVec.setWidth 32 >>> 4) ||| 0x30)),
       UInt8.ofBitVec (nibbleCharacter ((b.toBitVec.setWidth 32 &&& 0xf) ||| 0x30))] := by
  rw [nibbleCharacter_high, nibbleCharacter_low]
  rfl

theorem mergeGPR_setWidth {n k : Nat} (value : BitVec n) (old : BitVec 64)
    (hn : k ≤ n) (hk : k ≤ 64) :
    (mergeGPR n value old).setWidth k = value.setWidth k := by
  by_cases h32 : n = 32
  · simp only [mergeGPR, h32, ↓reduceIte, BitVec.setWidth_setWidth_of_le _ hk]
  · simp only [mergeGPR, h32, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hi64 : i < 64 := by omega
    have hin : i < n := by omega
    simp [getLsbD_setSlice _ _ _ _ _ hi64, hi, hin]

theorem or_signExtend_fe_of_lowByte (value : BitVec 64) (h : value.setWidth 8 = 1) :
    value ||| (0xfe#8).signExtend 64 = -1 := by
  have hf : ∀ i : Fin 64,
      ((0xfe#8).signExtend 64).getLsbD i.val = decide (i.val ≠ 0) := by
    decide +kernel
  have hzero : value.getLsbD 0 = true := by
    have hz := congrArg (fun v : BitVec 8 => v.getLsbD 0) h
    simpa using hz
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, hf ⟨i, hi⟩,
    show (-1 : BitVec 64) = BitVec.allOnes 64 by decide +kernel]
  simp only [BitVec.getLsbD_allOnes, hi, decide_true]
  by_cases hz : i = 0
  · subst i; simp [hzero]
  · simp [hz]

end Base16ct.Proofs.EncodeStr.Upper
