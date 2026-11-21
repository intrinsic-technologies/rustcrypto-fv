import AesGcm.Proofs.Common.Detached

namespace AesGcm.Proofs.Machine.CTR

open Standards.NIST.GCM

theorem gctr_getElem (cipher : Vector Bool 128 → Vector Bool 128)
    (counter : Vector Bool 128) (input : Vector Bool n) (i : Nat) (hi : i < n) :
    (GCTR cipher counter input)[i] =
      (input[i] ^^ (cipher (Nat.repeat (inc 32) (i / 128) counter))[i % 128]'(by omega)) := by
  simp [GCTR]

theorem gctr_short (cipher : Vector Bool 128 → Vector Bool 128)
    (counter : Vector Bool 128) (input : Vector Bool n) (hn : n ≤ 128) :
    GCTR cipher counter input =
      Vector.ofFn (fun i : Fin n ↦ input[i] ^^ (cipher counter)[i.val]'(by omega)) := by
  apply Vector.ext
  intro i hi
  rw [gctr_getElem]
  simp only [Vector.getElem_ofFn, show i / 128 = 0 by omega,
    show i % 128 = i from Nat.mod_eq_of_lt (by omega), Nat.repeat, Fin.getElem_fin]

private theorem repeat_add {α : Type} (f : α → α) (n m : Nat) (x : α) :
    Nat.repeat f (n + m) x = Nat.repeat f m (Nat.repeat f n x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change f (Nat.repeat f (n + m) x) = f (Nat.repeat f m (Nat.repeat f n x))
    rw [ih]

theorem gctr_append_blocks (cipher : Vector Bool 128 → Vector Bool 128)
    (counter : Vector Bool 128) (blockCount : Nat) (front : Vector Bool (128 * blockCount))
    (tail : Vector Bool n) :
    GCTR cipher counter (front ++ tail) =
      GCTR cipher counter front ++
        GCTR cipher (Nat.repeat (inc 32) blockCount counter) tail := by
  apply Vector.ext
  intro i hi
  rw [gctr_getElem, Vector.getElem_append, Vector.getElem_append]
  by_cases h : i < 128 * blockCount
  · simp only [h, dite_true, gctr_getElem]
  · simp only [h, dite_false, gctr_getElem]
    have hd : i / 128 = blockCount + (i - 128 * blockCount) / 128 := by omega
    have hm : i % 128 = (i - 128 * blockCount) % 128 := by omega
    simp only [hd, hm, repeat_add]

end AesGcm.Proofs.Machine.CTR

namespace AesGcm.Proofs.Machine.CTR
open Standards.NIST.GCM AesGcm.Spec.GCM

private theorem outputByte_eq {m n : Nat} (x : Vector Bool (8 * m)) (y : Vector Bool (8 * n))
    (i j : Nat) (hi : i < m) (hj : j < n)
    (h : ∀ b : Fin 8, x[8 * i + b.val]'(by omega) = y[8 * j + b.val]'(by omega)) :
    (byteArrayOfBits x).data[i]'(by simpa [byteArrayOfBits] using hi) = (byteArrayOfBits y).data[j]'(by simpa [byteArrayOfBits] using hj) := by
  change (bytesOfBits x)[i] = (bytesOfBits y)[j]
  simp only [bytesOfBits, Vector.getElem_ofFn]
  congr 2
  funext acc b
  rw [h b]

theorem gctr_bytes_append_blocks (cipher : Vector Bool 128 → Vector Bool 128)
    (counter : Vector Bool 128) (front tail : ByteArray) (blockCount : Nat)
    (hfront : front.size = 16 * blockCount) :
    byteArrayOfBits (GCTR cipher counter (bitsOfByteArray (front ++ tail))) =
      byteArrayOfBits (GCTR cipher counter (bitsOfByteArray front)) ++
      byteArrayOfBits (GCTR cipher (Nat.repeat (inc 32) blockCount counter) (bitsOfByteArray tail)) := by
  apply ByteArray.ext
  apply Array.ext
  · simp [byteArrayOfBits, ByteArray.data_append, ByteArray.size_append]
  · intro i hi hj
    have hi' : i < front.size + tail.size := by
      simpa only [byteArrayOfBits, Vector.size_toArray, ByteArray.size_append] using hi
    change (byteArrayOfBits (GCTR cipher counter (bitsOfByteArray (front ++ tail)))).data[i] = _
    simp only [ByteArray.data_append]
    by_cases h : i < front.size
    · rw [Array.getElem_append_left (by simpa [byteArrayOfBits] using h)]
      apply outputByte_eq _ _ i i (by simpa only [ByteArray.size_append] using hi') h
      intro b
      simp only [gctr_getElem, bitsOfByteArray, bitsOfBytes, Vector.getElem_ofFn,
        Vector.getElem_mk]
      have hx : (8 * i + b.val) / 8 < front.size := by omega
      change (((front ++ tail)[(8 * i + b.val) / 8]'(by rw [ByteArray.size_append]; omega)).toNat.testBit _ ^^ _) = _
      rw [ByteArray.getElem_append_left hx]
      rfl
    · rw [Array.getElem_append_right (by simpa [byteArrayOfBits] using Nat.le_of_not_gt h)]
      simp only [byteArrayOfBits, Vector.size_toArray]
      change (byteArrayOfBits (GCTR cipher counter (bitsOfByteArray (front ++ tail)))).data[i] =
        (byteArrayOfBits (GCTR cipher (Nat.repeat (inc 32) blockCount counter) (bitsOfByteArray tail))).data[i - front.size]'(by simpa [byteArrayOfBits] using (show i - front.size < tail.size by omega))
      apply outputByte_eq _ _ i (i - front.size) (by simpa only [ByteArray.size_append] using hi') (by omega)
      intro b
      simp only [gctr_getElem, bitsOfByteArray, bitsOfBytes, Vector.getElem_ofFn,
        Vector.getElem_mk]
      have hd : (8 * i + b.val) / 128 = blockCount + (8 * (i - front.size) + b.val) / 128 := by omega
      have hm : (8 * i + b.val) % 128 = (8 * (i - front.size) + b.val) % 128 := by omega
      have h8 : (8 * i + b.val) / 8 = i := by omega
      have h8' : (8 * (i - front.size) + b.val) / 8 = i - front.size := by omega
      have hb : (8 * i + b.val) % 8 = (8 * (i - front.size) + b.val) % 8 := by omega
      simp only [hd, hm, h8, h8', hb, repeat_add, ByteArray.data_append]
      rw [Array.getElem_append_right (show front.data.size ≤ i from Nat.le_of_not_gt h)]
      rfl

theorem gctr_bytes_extract_zero (cipher : Vector Bool 128 → Vector Bool 128)
    (counter : Vector Bool 128) (bytes : ByteArray) (count : Nat) (hc : count ≤ bytes.size) :
    (byteArrayOfBits (GCTR cipher counter (bitsOfByteArray bytes))).extract 0 count =
      byteArrayOfBits (GCTR cipher counter (bitsOfByteArray (bytes.extract 0 count))) := by
  have hs : (bytes.extract 0 count).size = count := by
    simp [ByteArray.size_extract, Nat.min_eq_left hc]
  apply ByteArray.ext
  apply Array.ext
  · simp [ByteArray.data_extract, Array.size_extract, byteArrayOfBits,
      ByteArray.size_extract, Nat.min_eq_left hc]
  · intro i hi hj
    have hi' : i < count := by simpa only [byteArrayOfBits, Vector.size_toArray, hs] using hj
    have he := outputByte_eq
      (GCTR cipher counter (bitsOfByteArray bytes))
      (GCTR cipher counter (bitsOfByteArray (bytes.extract 0 count)))
      i i (by omega) (by omega) (fun b => ?_)
    · simpa only [ByteArray.data_extract, Array.getElem_extract, Nat.zero_add] using he
    · simp only [gctr_getElem, bitsOfByteArray, bitsOfBytes, Vector.getElem_ofFn,
        Vector.getElem_mk, ByteArray.data_extract, Array.getElem_extract, Nat.zero_add]

end AesGcm.Proofs.Machine.CTR
