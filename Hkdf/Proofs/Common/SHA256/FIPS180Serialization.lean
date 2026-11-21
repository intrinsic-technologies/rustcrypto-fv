import Hkdf.Proofs.NIST.Encoding
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Serialization

namespace Hkdf.Proofs.Common.SHA256
open Standards.NIST.SHA2
open Hkdf.Proofs.Common.SHA256

theorem bitsToWord_getMsbD {w : Nat} (bits : Vector Bool w) (i : Nat) (hi : i < w) :
    (bitsToWord bits).getMsbD i = bits[i] := by
  simp [bitsToWord, BitVec.getMsbD_ofBoolListBE, List.getD, hi]

def digestOfHash (H : Vector (BitVec 32) 8) : Digest 32 :=
  Digest.ofBits (Vector.ofFn fun j : Fin 256 =>
    (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))

theorem digestOfHash_getElem (H : Vector (BitVec 32) 8) (i : Nat) (hi : i < 32) :
    (digestOfHash H).bytes[i] = UInt8.ofNat ((H[i/4]'(by omega)).toNat / 256^(3-i%4) % 256) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getMsbD_eq
  intro j hj
  simp only [digestOfHash, Digest.ofBits, Vector.getElem_ofFn, UInt8.toBitVec_ofBitVec]
  rw [bitsToWord_getMsbD _ j hj]
  simp only [Vector.getElem_ofFn, UInt8.toBitVec_ofNat']
  have hdiv : (8*i+j)/32 = i/4 := by omega
  have hmod : (8*i+j)%32 = 8*(i%4)+j := by omega
  simp only [hdiv, hmod]
  simp only [BitVec.getMsbD, BitVec.getLsbD_ofNat]
  simp only [show 8*(i%4)+j < 32 by omega, hj, decide_true, Bool.true_and, BitVec.getLsbD]
  simp only [show (256 : Nat) = 2^8 from rfl, Nat.testBit_mod_two_pow,
    ← Nat.pow_mul, Nat.testBit_div_two_pow]
  simp only [show 7-j < 8 by omega, decide_true, Bool.true_and]
  congr 1
  omega

theorem serializeHash_eq_digestOfHash (H : Vector (BitVec 32) 8) :
    (serializeHash (H.toArray.map UInt32.ofBitVec)).data = (digestOfHash H).bytes.toArray := by
  apply Array.ext
  · simp only [ByteArray.size_data, serializeHash_size, Array.size_map, Vector.size_toArray]
  · intro i hi hi'
    have hi32 : i < 32 := by simpa only [Vector.size_toArray] using hi'
    have hget := serializeHash_getElem (H.toArray.map UInt32.ofBitVec) i
      (by simpa only [serializeHash_size, Array.size_map, Vector.size_toArray] using hi32)
    simp only [ByteArray.getElem_eq_getElem_data] at hget
    rw [hget, Vector.getElem_toArray, digestOfHash_getElem H i hi32]
    simp [show i/4 < 8 by omega]

end Hkdf.Proofs.Common.SHA256
