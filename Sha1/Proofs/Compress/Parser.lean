import Standards.NIST.SHA2.Preprocessing

namespace Sha1.Proofs.Compress.Parser

open Standards.NIST.SHA2

theorem bytesToBits_size (bytes : ByteArray) :
    (bytesToBits bytes).size = 8 * bytes.size := by
  change ((bytes.data.toVector.flatMap fun x => wordToBits x.toBitVec).toArray).size = _
  rw [Vector.size_toArray, ByteArray.size_data, Nat.mul_comm]

theorem bytesToBits_getElem (bytes : ByteArray) (i : Nat)
    (hi : i < (bytesToBits bytes).size) :
    (bytesToBits bytes)[i] = (bytes[i / 8]?.getD 0).toBitVec.getMsbD (i % 8) := by
  have hbyte : i / 8 < bytes.size := by
    rw [bytesToBits_size] at hi
    omega
  change (bytes.data.toVector.flatMap fun x => wordToBits x.toBitVec)[i]'(by
    rw [bytesToBits_size] at hi
    rw [ByteArray.size_data]
    omega) = _
  rw [Vector.getElem_flatMap]
  simp only [wordToBits, Vector.getElem_ofFn, Array.toVector,
    Vector.getElem_mk, getElem?_pos bytes (i / 8) hbyte, Option.getD_some]
  rfl

theorem bitsToWord_getMsbD {width : Nat} (bits : Vector Bool width) (i : Nat)
    (hi : i < width) :
    (bitsToWord bits).getMsbD i = bits[i] := by
  simp [bitsToWord, BitVec.getMsbD_ofBoolListBE, List.getD, hi]

theorem parse_size (bytes : ByteArray) :
    (SHA256.parse (bytesToBits bytes)).size = bytes.size / 64 := by
  simp only [SHA256.parse, Array.size_ofFn, bytesToBits_size]
  omega

def blockWord (bytes : ByteArray) (block word : Nat) : BitVec 32 :=
  (bytes[64 * block + 4 * word]?.getD 0).toBitVec ++
  (bytes[64 * block + 4 * word + 1]?.getD 0).toBitVec ++
  (bytes[64 * block + 4 * word + 2]?.getD 0).toBitVec ++
  (bytes[64 * block + 4 * word + 3]?.getD 0).toBitVec

theorem blockWord_getMsbD (bytes : ByteArray) (block word bit : Nat) (hbit : bit < 32) :
    (blockWord bytes block word).getMsbD bit =
      (bytes[64 * block + 4 * word + bit / 8]?.getD 0).toBitVec.getMsbD (bit % 8) := by
  simp only [blockWord, BitVec.getMsbD_append]
  by_cases h0 : bit < 8
  · simp only [show ¬ 24 ≤ bit by omega, show ¬ 16 ≤ bit by omega,
      show ¬ 8 ≤ bit by omega, ite_false, show bit / 8 = 0 by omega,
      show bit % 8 = bit by omega, Nat.add_zero]
  · by_cases h1 : bit < 16
    · simp only [show ¬ 24 ≤ bit by omega, show ¬ 16 ≤ bit by omega,
        show 8 ≤ bit by omega, ite_false, ite_true, show bit / 8 = 1 by omega,
        show bit % 8 = bit - 8 by omega]
    · by_cases h2 : bit < 24
      · simp only [show ¬ 24 ≤ bit by omega, show 16 ≤ bit by omega,
          ite_false, ite_true, show bit / 8 = 2 by omega,
          show bit % 8 = bit - 16 by omega]
      · simp only [show 24 ≤ bit by omega, ite_true, show bit / 8 = 3 by omega,
          show bit % 8 = bit - 24 by omega]

theorem parse_getElem (bytes : ByteArray) (block word : Nat)
    (hblock : block < bytes.size / 64) (hword : word < 16) :
    ((SHA256.parse (bytesToBits bytes))[block]'(by rw [parse_size]; exact hblock))[word] =
      blockWord bytes block word := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit hbit
  simp only [SHA256.parse, Array.getElem_ofFn, Vector.getElem_ofFn]
  rw [bitsToWord_getMsbD _ bit hbit]
  simp only [Vector.getElem_ofFn]
  rw [bytesToBits_getElem, blockWord_getMsbD _ _ _ bit hbit]
  rw [show (512 * block + 32 * word + bit) / 8 =
    64 * block + 4 * word + bit / 8 by omega,
    show (512 * block + 32 * word + bit) % 8 = bit % 8 by omega]

theorem blockWord_append_left (a b : ByteArray) (block word : Nat)
    (hblock : block < a.size / 64) (hword : word < 16) :
    blockWord (a ++ b) block word = blockWord a block word := by
  have hget (k : Nat) (hk : k < 4) :
      ((a ++ b)[64 * block + 4 * word + k]?.getD 0) =
        (a[64 * block + 4 * word + k]?.getD 0) := by
    have hidx : 64 * block + 4 * word + k < a.size := by omega
    rw [getElem?_pos (a ++ b) _ (by rw [ByteArray.size_append]; omega),
      getElem?_pos a _ hidx, ByteArray.getElem_append_left hidx]
  have hzero := hget 0 (by omega)
  simp only [Nat.add_zero] at hzero
  simp only [blockWord, hzero, hget 1 (by omega), hget 2 (by omega), hget 3 (by omega)]

theorem blockWord_append_right (a b : ByteArray) (block word : Nat)
    (haligned : a.size % 64 = 0) (hblock : block < b.size / 64) (hword : word < 16) :
    blockWord (a ++ b) (a.size / 64 + block) word = blockWord b block word := by
  have hget (k : Nat) (hk : k < 4) :
      ((a ++ b)[64 * (a.size / 64 + block) + 4 * word + k]?.getD 0) =
        (b[64 * block + 4 * word + k]?.getD 0) := by
    have hidx : 64 * block + 4 * word + k < b.size := by omega
    have heq : 64 * (a.size / 64 + block) + 4 * word + k =
        a.size + (64 * block + 4 * word + k) := by omega
    rw [heq, getElem?_pos (a ++ b) _ (by rw [ByteArray.size_append]; omega),
      getElem?_pos b _ hidx, ByteArray.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
  have hzero := hget 0 (by omega)
  simp only [Nat.add_zero] at hzero
  simp only [blockWord, hzero, hget 1 (by omega), hget 2 (by omega), hget 3 (by omega)]

theorem parse_empty : SHA256.parse (bytesToBits ByteArray.empty) = #[] := by
  apply Array.eq_empty_of_size_eq_zero
  rw [parse_size, ByteArray.size_empty]

theorem parse_append (a b : ByteArray) (haligned : a.size % 64 = 0) :
    SHA256.parse (bytesToBits (a ++ b)) =
      SHA256.parse (bytesToBits a) ++ SHA256.parse (bytesToBits b) := by
  apply Array.ext
  · simp only [Array.size_append, parse_size, ByteArray.size_append]
    omega
  · intro block hb hb'
    have hblock : block < (a.size + b.size) / 64 := by
      simpa only [parse_size, ByteArray.size_append] using hb
    apply Vector.ext
    intro word hword
    rw [parse_getElem _ block word (by rw [ByteArray.size_append]; exact hblock) hword]
    by_cases hleft : block < a.size / 64
    · rw [Array.getElem_append_left (by rw [parse_size]; exact hleft),
        parse_getElem _ block word hleft hword, blockWord_append_left _ _ _ _ hleft hword]
    · have hright : block - a.size / 64 < b.size / 64 := by omega
      rw [Array.getElem_append_right (by rw [parse_size]; omega)]
      simp only [parse_size]
      rw [parse_getElem _ _ word hright hword]
      have heq : block = a.size / 64 + (block - a.size / 64) := by omega
      calc
        blockWord (a ++ b) block word =
            blockWord (a ++ b) (a.size / 64 + (block - a.size / 64)) word := by
          exact congrArg (fun i => blockWord (a ++ b) i word) heq
        _ = _ := blockWord_append_right a b _ word haligned hright hword

end Sha1.Proofs.Compress.Parser
