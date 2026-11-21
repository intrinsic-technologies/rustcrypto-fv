import Hkdf.Proofs.Common.SHA256.FIPS180
import Hkdf.Proofs.Common.HMAC
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Compression
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail

namespace Hkdf.Proofs.Common

open Hkdf.Proofs.Common.SHA256

theorem compressBlocks_append_buffered (hash : Array UInt32) (a b : ByteArray) :
    compressBlocks hash (a ++ b) =
      compressBlocks (compressBlocks hash a) (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  rw [compressBlocks_append _ _ _ (by rw [fullBlocks_size]; omega), compressBlocks_fullBlocks]

theorem remainderBytes_append_aligned (a b : ByteArray) (ha : a.size % 64 = 0) :
    remainderBytes (a ++ b) = remainderBytes b := by
  have hs : 64*((a.size+b.size)/64) = a.size+64*(b.size/64) := by omega
  simp only [remainderBytes, ByteArray.size_append, hs, ByteArray.extract_append_size_add]

theorem remainderBytes_append_buffered (a b : ByteArray) :
    remainderBytes (a ++ b) = remainderBytes (remainderBytes a ++ b) := by
  conv => lhs; rw [← fullBlocks_append_remainderBytes a, ByteArray.append_assoc]
  exact remainderBytes_append_aligned _ _ (by rw [fullBlocks_size]; omega)


theorem compressBlocks_short (hash : Array UInt32) (input : ByteArray) (h : input.size < 64) :
    compressBlocks hash input = hash := by
  simp only [compressBlocks, Nat.div_eq_of_lt h, compressBlocksFrom]


theorem compressBlocks_append_short (hash : Array UInt32) (a b : ByteArray)
    (h : b.size < 64 - a.size % 64) :
    compressBlocks hash (a ++ b) = compressBlocks hash a := by
  rw [compressBlocks_append_buffered, compressBlocks_short]
  rw [ByteArray.size_append, remainderBytes_size]
  omega


theorem serializeHash_compressBlocks_bytePadding_eq_hashBytes (input : ByteArray) :
    serializeHash (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (bytePadding input)) =
      Standards.NIST.SHA2.SHA256.hashBytes input := by
  rw [serializeHash_compressBlocks_bytePadding]
  exact ByteArray.ext (Hkdf.Proofs.FIPS180.sha256_eq_fips180 input)

theorem serializeHash_tail_compressions_eq_hashBytes (input : ByteArray) :
    serializeHash (if input.size % 64 < 56 then
      Hkdf.Proofs.NIST.SHA256.compress
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash input)
        (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst input))
    else
      Hkdf.Proofs.NIST.SHA256.compress
        (Hkdf.Proofs.NIST.SHA256.compress
          (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash input)
          (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst input)))
        (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailLast input))) =
      Standards.NIST.SHA2.SHA256.hashBytes input := by
  rw [serializeHash_tail_compressions]
  exact ByteArray.ext (Hkdf.Proofs.FIPS180.sha256_eq_fips180 input)

theorem bitLength_eq (length : Nat) :
    ((BitVec.ofNat 64 (length / 64) <<< 9) |||
      (BitVec.ofNat 64 (length % 64) <<< 3)) = BitVec.ofNat 64 (8 * length) := by
  have shift (value amount : Nat) :
      BitVec.ofNat 64 value <<< amount = BitVec.ofNat 64 (value <<< amount) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  rw [shift, shift, ← BitVec.ofNat_or]
  have low : (length % 64) <<< 3 < 2 ^ 9 := by
    rw [Nat.shiftLeft_eq]
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt low (length / 64)]
  congr 1
  simp only [Nat.shiftLeft_eq]
  omega

theorem serializeHash_hmac_sha256_outer (key message : ByteArray) :
    serializeHash (Hkdf.Proofs.NIST.SHA256.compress
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c))
      (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst
        (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++ Standards.NIST.SHA2.SHA256.hashBytes
          (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))))) =
      Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message := by
  have short :
      (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++ Standards.NIST.SHA2.SHA256.hashBytes
        (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message)).size % 64 < 56 := by
    rw [ByteArray.size_append, HMAC.xorPad_keyBlock_size, HMAC.sha256_hashBytes_size]
    decide +kernel
  have unchanged := Hkdf.Proofs.Common.compressBlocks_append_short
    Hkdf.Proofs.NIST.SHA256.initialHash (HMAC.xorPad (HMAC.keyBlock key) 0x5c)
    (Standards.NIST.SHA2.SHA256.hashBytes (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))
    (by rw [HMAC.sha256_hashBytes_size, HMAC.xorPad_keyBlock_size]; decide +kernel)
  have digest := serializeHash_tail_compressions_eq_hashBytes
    (HMAC.xorPad (HMAC.keyBlock key) 0x5c ++ Standards.NIST.SHA2.SHA256.hashBytes
      (HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message))
  simp only [short, ↓reduceIte, unchanged] at digest
  exact digest.trans (HMAC.hmac_sha256_eq key message).symm

end Hkdf.Proofs.Common
