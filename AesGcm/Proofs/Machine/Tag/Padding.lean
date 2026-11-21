import AesGcm.Proofs.Common.Detached

namespace AesGcm.Proofs.Machine.Tag
open Standards.NIST.GCM

theorem blocks_append_aligned (a : Vector Bool n) (b : Vector Bool m)
    (ha : n % 128 = 0) :
    blocks (a ++ b) = blocks a ++ blocks b := by
  apply Array.ext
  · simp only [blocks, Array.size_ofFn, Array.size_append]
    omega
  · intro i hleft hright
    simp only [blocks, Array.getElem_ofFn, Array.getElem_append]
    apply Vector.ext
    intro j hj
    by_cases hi : i < n / 128
    · simp only [Array.size_ofFn, hi, dite_true,
        Vector.getElem_ofFn, Vector.getElem_append]
      rw [dite_eq_left (by omega)]
    · simp only [Array.size_ofFn, hi, dite_false,
        Vector.getElem_ofFn, Vector.getElem_append]
      rw [dite_eq_right (by omega)]
      congr 1
      omega

theorem blocks_cast (a : Vector Bool n) (h : n = m) :
    blocks (a.cast h) = blocks a := by
  subst m
  rfl

theorem blocks_single (a : Vector Bool 128) : blocks a = #[a] := by
  apply Array.ext
  · simp only [blocks, Array.size_ofFn, Array.size_singleton]
  · intro i hi hi'
    have he : i = 0 := by
      simp only [blocks, Array.size_ofFn] at hi
      omega
    subst i
    simp only [blocks, Array.getElem_ofFn, Array.getElem_singleton]
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]

theorem padded_length (n : Nat) :
    n + (128 * ((n + 127) / 128) - n) = 128 * ((n + 127) / 128) := by
  omega

theorem blocks_authentication_input (a : Vector Bool n) (c : Vector Bool m) :
    let v := 128 * ((n + 127) / 128) - n
    let u := 128 * ((m + 127) / 128) - m
    blocks (a ++ zeros v ++ c ++ zeros u ++ integerToString 64 n ++ integerToString 64 m) =
      blocks (a ++ zeros v) ++ blocks (c ++ zeros u) ++
        #[integerToString 64 n ++ integerToString 64 m] := by
  dsimp only
  rw [Vector.append_assoc, blocks_cast]
  rw [blocks_append_aligned _ _ (by rw [padded_length]; omega), blocks_single]
  rw [Vector.append_assoc, blocks_cast]
  rw [blocks_append_aligned _ _ (by rw [padded_length]; omega)]

def paddedBlock (bytes : ByteArray) (j : Nat) : Vector Bool 128 :=
  Vector.ofFn fun i ↦ if h : 16 * j + i.val / 8 < bytes.size then
    (bytes[16 * j + i.val / 8]).toNat.testBit (7 - i.val % 8) else false

def paddedBlocks (bytes : ByteArray) : Array (Vector Bool 128) :=
  blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes ++
    zeros (128 * ((8 * bytes.size + 127) / 128) - 8 * bytes.size))

theorem paddedBlocks_size (bytes : ByteArray) :
    (paddedBlocks bytes).size = (bytes.size + 15) / 16 := by
  simp only [paddedBlocks, blocks, Array.size_ofFn, padded_length]
  omega

theorem paddedBlocks_getElem (bytes : ByteArray) (j : Nat)
    (hj : j < (paddedBlocks bytes).size) :
    (paddedBlocks bytes)[j] = paddedBlock bytes j := by
  apply Vector.ext
  intro i hi
  simp only [paddedBlocks, blocks, Array.getElem_ofFn, Vector.getElem_ofFn,
    Vector.getElem_append, paddedBlock]
  have hd : (128 * j + i) / 8 = 16 * j + i / 8 := by omega
  have hm : (128 * j + i) % 8 = i % 8 := by omega
  by_cases h : 16 * j + i / 8 < bytes.size
  · simp only [show 128 * j + i < 8 * bytes.size by omega, dite_true,
      AesGcm.Spec.GCM.bitsOfByteArray, bitsOfBytes, Vector.getElem_ofFn, hd, hm, h]
    rfl
  · simp only [show ¬ 128 * j + i < 8 * bytes.size by omega, dite_false,
      zeros, Vector.getElem_replicate, h]

theorem fullBlocks_size (bytes : ByteArray) :
    (blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).size = bytes.size / 16 := by
  simp only [blocks, Array.size_ofFn]
  omega

theorem fullBlocks_getElem (bytes : ByteArray) (j : Nat)
    (hj : j < (blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).size) :
    (blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes))[j] = paddedBlock bytes j := by
  rw [fullBlocks_size] at hj
  apply Vector.ext
  intro i hi
  simp only [blocks, Array.getElem_ofFn, Vector.getElem_ofFn,
    AesGcm.Spec.GCM.bitsOfByteArray, bitsOfBytes, paddedBlock,
    show 16 * j + i / 8 < bytes.size by omega, dite_true]
  have hd : (128 * j + i) / 8 = 16 * j + i / 8 := by omega
  have hm : (128 * j + i) % 8 = i % 8 := by omega
  simp only [hd, hm]
  rfl

theorem paddedBlocks_eq_full_tail (bytes : ByteArray) :
    paddedBlocks bytes = blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes) ++
      (if bytes.size % 16 = 0 then #[] else #[paddedBlock bytes (bytes.size / 16)]) := by
  apply Array.ext
  · simp only [paddedBlocks_size, Array.size_append, fullBlocks_size]
    split <;> simp only [Array.size_empty, Array.size_singleton] <;> omega
  · intro j hj hj'
    rw [paddedBlocks_getElem, Array.getElem_append]
    split
    · rw [fullBlocks_getElem]
    · rename_i h
      rw [fullBlocks_size] at h
      have hjbound := hj
      rw [paddedBlocks_size] at hjbound
      have he : j = bytes.size / 16 := by omega
      subst j
      simp only [fullBlocks_size, Nat.sub_self]
      split
      · rename_i hz
        omega
      · simp only [Array.getElem_singleton]

end AesGcm.Proofs.Machine.Tag
