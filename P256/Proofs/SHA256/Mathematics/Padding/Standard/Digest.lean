import P256.Proofs.SHA256.Mathematics.Padding.Standard.Serialization

set_option autoImplicit false

namespace P256.Proofs.SHA256

private theorem bitsToWord_getMsbD {w : Nat} (bits : Vector Bool w) (i : Nat)
    (hi : i < w) :
    (Standards.NIST.SHA2.bitsToWord bits).getMsbD i = bits[i] := by
  simp [Standards.NIST.SHA2.bitsToWord, List.getD, hi]

private theorem bitsToWord_byte (word : BitVec 32) (b : Nat) (hb : b < 4) :
    Standards.NIST.SHA2.bitsToWord
        (Vector.ofFn fun n : Fin 8 => word.getMsbD (8 * b + n.val)) =
      word.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  rw [bitsToWord_getMsbD _ _ hi, Vector.getElem_ofFn,
    BitVec.getMsbD_extractLsb']
  simp only [hi, decide_true, Bool.true_and,
    show 8 * (3 - b) + 8 - i ≤ 32 by omega]
  congr 1
  omega

private theorem digestOfBits_getElem (H : Vector (BitVec 32) 8) (i : Nat) (hi : i < 32) :
    (Standards.NIST.SHA2.Digest.ofBits (byteCount := 32)
      (Vector.ofFn (n := 256) fun j =>
        (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))).bytes[i] =
      UInt8.ofBitVec ((H[i / 4]'(by omega)).extractLsb' (8 * (3 - i % 4)) 8) := by
  simp only [Standards.NIST.SHA2.Digest.ofBits, Vector.getElem_ofFn]
  have hbits : (Vector.ofFn fun n : Fin 8 =>
      (H[(8 * i + n.val) / 32]'(by omega)).getMsbD ((8 * i + n.val) % 32)) =
      Vector.ofFn fun n : Fin 8 => (H[i / 4]'(by omega)).getMsbD (8 * (i % 4) + n.val) := by
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_ofFn]
    have hq : (8 * i + k) / 32 = i / 4 := by omega
    have hm : (8 * i + k) % 32 = 8 * (i % 4) + k := by omega
    simp only [hq, hm]
  rw [hbits, bitsToWord_byte _ _ (Nat.mod_lt _ (by decide))]

theorem serializeHash_eq_digestOfBits (H : Vector (BitVec 32) 8) :
    serializeHash (H.toArray.map UInt32.ofBitVec) =
      ByteArray.mk (Standards.NIST.SHA2.Digest.ofBits (byteCount := 32)
        (Vector.ofFn (n := 256) fun j =>
          (H[j.val / 32]'(by omega)).getMsbD (j.val % 32))).bytes.toArray := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size_data, serializeHash_size, Array.size_map, Vector.size_toArray]
  · intro i hi hj
    have hi32 : i < 32 := by
      simpa only [ByteArray.size_data, serializeHash_size, Array.size_map,
        Vector.size_toArray] using hi
    have hser := serializeHash_getElem (H.toArray.map UInt32.ofBitVec) i
      (by simpa only [ByteArray.size_data] using hi)
    rw [ByteArray.getElem_eq_getElem_data] at hser
    rw [hser]
    simp only [Vector.getElem_toArray, digestOfBits_getElem H i hi32]
    have hq : i / 4 < H.toArray.size := by
      simpa only [Vector.size_toArray] using (show i / 4 < 8 by omega)
    have hmap : i / 4 < (H.toArray.map UInt32.ofBitVec).size := by
      simpa only [Array.size_map] using hq
    simp only [getElem!_pos, Array.getElem_map, hmap]
    simp only [Vector.getElem_toArray, UInt32.toNat_ofBitVec]
    apply UInt8.toNat.inj
    simp only [UInt8.toNat_ofNat', Nat.mod_mod, UInt8.toNat_ofBitVec,
      BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    congr 2
    rw [Nat.pow_mul]

end P256.Proofs.SHA256
