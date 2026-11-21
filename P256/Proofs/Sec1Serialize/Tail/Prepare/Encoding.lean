import P256.Proofs.Sec1Serialize.State
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Common.Instructions.Bswap
import X86Proofs.Program.ReadWrite.Bytes
import Init.Data.Nat.Mod

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64 bswap64_byte)

namespace P256.Proofs.Sec1Serialize.Prepare

open X86Proofs

theorem canonicalLimb_byte (value index byte : Nat) (hbyte : byte < 8) :
    storedByte (canonicalLimb value index) byte =
      UInt8.ofNat (value / 256 ^ (8 * index + byte) % 256) := by
  have hpow (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
  apply UInt8.toNat.inj
  simp only [storedByte, canonicalLimb, UInt8.toNat_ofNat', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  have hsplit : 2^64 = 2^(8*byte) * 2^(64-8*byte) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (show 256 ∣ 2^(64-8*byte) from
    Nat.pow_dvd_pow 2 (show 8 ≤ 64-8*byte by omega))]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hpow]
  congr 3
  omega

theorem canonicalLimb_bigEndian_byte (value i : Nat) (hi : i < 32) :
    storedByte (bswap64 (canonicalLimb value (3 - i / 8))) (i % 8) =
      UInt8.ofNat (value / 256 ^ (31 - i) % 256) := by
  rw [storedByte_eq_extract, bswap64_byte _ _ (Nat.mod_lt _ (by decide))]
  rw [← storedByte_eq_extract]
  rw [canonicalLimb_byte value _ _ (by omega)]
  have he : 8 * (3 - i / 8) + (7 - i % 8) = 31 - i := by omega
  rw [he]

open P256.Spec Standards.SECG.ECC.Encoding
open P256.Proofs.SecretKeyFromBytes.Encoding

theorem encode_affine (x y : Nat) :
    Points.encode (.affine x y) =
      ⟨#[4]⟩ ++ natToOctets 32 x ++ natToOctets 32 y := by
  have width : (Operations.domain.p.log2 + 8) / 8 = 32 := by decide +kernel
  simp only [Points.encode, Points.encodeWith, Standards.SECG.ECC.Points.encodePoint,
    Bool.false_eq_true, ite_false, width]

theorem encodePoint_uncompressed_size (x y : Nat) :
    (Points.encode (.affine x y)).size = 65 := by
  simp only [encode_affine, ByteArray.size_append, natToOctets_size]
  rfl

theorem encodePoint_uncompressed_tag (x y : Nat) :
    (Points.encode (.affine x y)).data[0]? = some 4 := by
  simp [encode_affine, ByteArray.data_append, Array.getElem?_append]

theorem encodePoint_uncompressed_x (x y i : Nat) (hi : i < 32) :
    (Points.encode (.affine x y)).data[1 + i]? =
      some (UInt8.ofNat (x / 256 ^ (31 - i) % 256)) := by
  simp only [encode_affine, ByteArray.data_append,
    Array.getElem?_append]
  simp only [Array.size_append, Array.size_singleton, ByteArray.size_data,
    natToOctets_size]
  rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  simpa only [Nat.add_sub_cancel_left] using natToOctets_getElem? 32 x i hi

theorem encodePoint_uncompressed_y (x y i : Nat) (hi : i < 32) :
    (Points.encode (.affine x y)).data[33 + i]? =
      some (UInt8.ofNat (y / 256 ^ (31 - i) % 256)) := by
  simp only [encode_affine, ByteArray.data_append,
    Array.getElem?_append, Array.size_append, Array.size_singleton,
    ByteArray.size_data, natToOctets_size]
  rw [ite_eq_right (by omega)]
  simpa only [Nat.add_sub_cancel_left] using natToOctets_getElem? 32 y i hi

end P256.Proofs.Sec1Serialize.Prepare
