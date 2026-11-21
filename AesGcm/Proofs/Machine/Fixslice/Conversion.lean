import AesGcm.Proofs.Machine.Fixslice.Representation

namespace AesGcm.Proofs.Machine.Fixslice

def deltaSwap2 (a b : BitVec 64) (shift : Nat) (mask : BitVec 64) :
    BitVec 64 × BitVec 64 :=
  let t := (a ^^^ (b >>> shift)) &&& mask
  (a ^^^ t, b ^^^ (t <<< shift))

theorem getLsbD_deltaSwap2_fst (a b mask : BitVec 64) (s i : Nat) :
    (deltaSwap2 a b s mask).1.getLsbD i =
      if mask.getLsbD i then b.getLsbD (s + i) else a.getLsbD i := by
  simp only [deltaSwap2, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight]
  cases mask.getLsbD i <;> simp

theorem getLsbD_deltaSwap2_snd (a b mask : BitVec 64) (s i : Nat) (hi : i < 64) :
    (deltaSwap2 a b s mask).2.getLsbD i =
      if s ≤ i ∧ mask.getLsbD (i - s) then a.getLsbD (i - s) else b.getLsbD i := by
  simp only [deltaSwap2, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases hs : s ≤ i
  · simp only [hi, decide_true, Bool.true_and, Nat.not_lt.mpr hs, decide_false,
      Bool.not_false, Nat.add_sub_of_le hs, hs, true_and]
    cases mask.getLsbD (i - s) <;> simp [Bool.xor_left_comm]
  · simp [hs, Nat.lt_of_not_ge hs]

def swapShift (k : Fin 3) : Nat := 2 ^ k.val

def swapMask (k : Fin 3) : BitVec 64 :=
  match k.val with
  | 0 => 0x5555555555555555
  | 1 => 0x3333333333333333
  | _ => 0x0f0f0f0f0f0f0f0f

def swapLow (k : Fin 3) (p : Fin 8) : Fin 8 :=
  ⟨(p.val / (2 * swapShift k) * (2 * swapShift k) + p.val % swapShift k) % 8,
    Nat.mod_lt _ (by decide)⟩

def swapHigh (k : Fin 3) (p : Fin 8) : Fin 8 :=
  ⟨(swapLow k p).val + swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8), (swapLow k p).val + swapShift k < 8 :=
      by decide +kernel
    exact h k p⟩

def swapStage (k : Fin 3) (x : Planes) : Planes := fun p ↦
  let ab := deltaSwap2 (x (swapHigh k p)) (x (swapLow k p)) (swapShift k) (swapMask k)
  if p.val / swapShift k % 2 = 0 then ab.2 else ab.1

def swapPlane (k : Fin 3) (p : Fin 8) (i : Fin 64) : Fin 8 :=
  ⟨(swapLow k p).val + i.val / swapShift k % 2 * swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 64),
        (swapLow k p).val + i.val / swapShift k % 2 * swapShift k < 8 :=
      by decide +kernel
    exact h k p i⟩

def swapBit (k : Fin 3) (p : Fin 8) (i : Fin 64) : Fin 64 :=
  ⟨i.val / (2 * swapShift k) * (2 * swapShift k) +
      p.val / swapShift k % 2 * swapShift k + i.val % swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 64),
        i.val / (2 * swapShift k) * (2 * swapShift k) +
          p.val / swapShift k % 2 * swapShift k + i.val % swapShift k < 64 :=
      by decide +kernel
    exact h k p i⟩

def swapRoute (k : Fin 3) (p : Fin 8) (i : Fin 64) : Fin 8 × Nat :=
  if p.val / swapShift k % 2 = 0 then
    if swapShift k ≤ i.val ∧ (swapMask k).getLsbD (i.val - swapShift k) then
      (swapHigh k p, i.val - swapShift k)
    else (swapLow k p, i.val)
  else if (swapMask k).getLsbD i.val then
    (swapLow k p, swapShift k + i.val)
  else (swapHigh k p, i.val)

theorem swapRoute_eq (k : Fin 3) (p : Fin 8) (i : Fin 64) :
    swapRoute k p i = (swapPlane k p i, (swapBit k p i).val) := by
  have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 64),
      swapRoute k p i = (swapPlane k p i, (swapBit k p i).val) := by decide +kernel
  exact h k p i

theorem getLsbD_swapStage (k : Fin 3) (x : Planes) (p : Fin 8) (i : Fin 64) :
    (swapStage k x p).getLsbD i.val =
      (x (swapPlane k p i)).getLsbD (swapBit k p i).val := by
  have hr : (swapStage k x p).getLsbD i.val =
      (x (swapRoute k p i).1).getLsbD (swapRoute k p i).2 := by
    simp only [swapStage, swapRoute]
    split
    · rw [getLsbD_deltaSwap2_snd _ _ _ _ _ i.isLt]
      split <;> rfl
    · rw [getLsbD_deltaSwap2_fst]
      split <;> rfl
  rw [hr, swapRoute_eq]

def bitsliceSwaps (x : Planes) : Planes :=
  swapStage 2 (swapStage 1 (swapStage 0 x))

theorem getLsbD_bitsliceSwaps (x : Planes) (p : Fin 8) (i : Fin 64) :
    (bitsliceSwaps x p).getLsbD i.val =
      (x ⟨i.val % 8, by omega⟩).getLsbD (i.val / 8 * 8 + p.val) := by
  simp only [bitsliceSwaps, getLsbD_swapStage]
  have h : ∀ (p : Fin 8) (i : Fin 64),
      (swapPlane 0 (swapPlane 1 (swapPlane 2 p i) (swapBit 2 p i))
        (swapBit 1 (swapPlane 2 p i) (swapBit 2 p i))).val = i.val % 8 ∧
      (swapBit 0 (swapPlane 1 (swapPlane 2 p i) (swapBit 2 p i))
        (swapBit 1 (swapPlane 2 p i) (swapBit 2 p i))).val =
          i.val / 8 * 8 + p.val := by decide +kernel
  rw [(h p i).2]
  congr 2
  exact Fin.ext (h p i).1

theorem getLsbD_packByte (b : BitVec 8) (k : Fin 8) (i : Fin 64) :
    ((b.setWidth 64) <<< (8 * k.val)).getLsbD i.val =
      if i.val / 8 = k.val then b.getLsbD (i.val % 8) else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    i.isLt, decide_true, Bool.true_and]
  by_cases h : i.val / 8 = k.val
  · have hge : ¬ i.val < 8 * k.val := by omega
    have hsub : i.val - 8 * k.val = i.val % 8 := by omega
    have hr : i.val % 8 < 64 := by omega
    simp [h, hge, hsub, hr]
  · by_cases hlt : i.val < 8 * k.val
    · simp [h, hlt]
    · have hsub : 8 ≤ i.val - 8 * k.val := by omega
      simp [h, BitVec.getLsbD_of_ge _ _ hsub]

def packBytes (x : Fin 8 → BitVec 8) : BitVec 64 :=
  (x 0).setWidth 64 |||
  ((x 2).setWidth 64) <<< 16 |||
  ((x 4).setWidth 64) <<< 32 |||
  ((x 6).setWidth 64) <<< 48 |||
  ((x 1).setWidth 64) <<< 8 |||
  ((x 3).setWidth 64) <<< 24 |||
  ((x 5).setWidth 64) <<< 40 |||
  ((x 7).setWidth 64) <<< 56

theorem getLsbD_packBytes (x : Fin 8 → BitVec 8) (i : Fin 64) :
    (packBytes x).getLsbD i.val =
      (x ⟨i.val / 8, by omega⟩).getLsbD (i.val % 8) := by
  simp only [packBytes, BitVec.getLsbD_or]
  have h0 := getLsbD_packByte (x 0) ⟨0, by decide⟩ i
  have h1 := getLsbD_packByte (x 1) ⟨1, by decide⟩ i
  have h2 := getLsbD_packByte (x 2) ⟨2, by decide⟩ i
  have h3 := getLsbD_packByte (x 3) ⟨3, by decide⟩ i
  have h4 := getLsbD_packByte (x 4) ⟨4, by decide⟩ i
  have h5 := getLsbD_packByte (x 5) ⟨5, by decide⟩ i
  have h6 := getLsbD_packByte (x 6) ⟨6, by decide⟩ i
  have h7 := getLsbD_packByte (x 7) ⟨7, by decide⟩ i
  change ((x 0).setWidth 64 <<< (0 : Nat)).getLsbD i.val =
    (if i.val / 8 = 0 then (x 0).getLsbD (i.val % 8) else false) at h0
  change ((x 1).setWidth 64 <<< (8 : Nat)).getLsbD i.val =
    (if i.val / 8 = 1 then (x 1).getLsbD (i.val % 8) else false) at h1
  change ((x 2).setWidth 64 <<< (16 : Nat)).getLsbD i.val =
    (if i.val / 8 = 2 then (x 2).getLsbD (i.val % 8) else false) at h2
  change ((x 3).setWidth 64 <<< (24 : Nat)).getLsbD i.val =
    (if i.val / 8 = 3 then (x 3).getLsbD (i.val % 8) else false) at h3
  change ((x 4).setWidth 64 <<< (32 : Nat)).getLsbD i.val =
    (if i.val / 8 = 4 then (x 4).getLsbD (i.val % 8) else false) at h4
  change ((x 5).setWidth 64 <<< (40 : Nat)).getLsbD i.val =
    (if i.val / 8 = 5 then (x 5).getLsbD (i.val % 8) else false) at h5
  change ((x 6).setWidth 64 <<< (48 : Nat)).getLsbD i.val =
    (if i.val / 8 = 6 then (x 6).getLsbD (i.val % 8) else false) at h6
  change ((x 7).setWidth 64 <<< (56 : Nat)).getLsbD i.val =
    (if i.val / 8 = 7 then (x 7).getLsbD (i.val % 8) else false) at h7
  simp only [BitVec.shiftLeft_zero] at h0
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have h : i.val / 8 = 0 ∨ i.val / 8 = 1 ∨ i.val / 8 = 2 ∨ i.val / 8 = 3 ∨
      i.val / 8 = 4 ∨ i.val / 8 = 5 ∨ i.val / 8 = 6 ∨ i.val / 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [h]

def readReordered (x : Fin 16 → BitVec 8) (h : Fin 2) : BitVec 64 :=
  packBytes fun q ↦ x ⟨4 * h.val + 8 * (q.val % 2) + q.val / 2, by omega⟩

def inputPacking (x : Blocks) : Planes := fun p ↦
  readReordered (x ⟨p.val % 4, by omega⟩) ⟨p.val / 4, by omega⟩

def bitslice (x : Blocks) : Planes := bitsliceSwaps (inputPacking x)

def writeReordered (columns : BitVec 64) (r : Fin 4) (h : Fin 2) : BitVec 8 :=
  (columns >>> (16 * r.val + 8 * h.val)).setWidth 8

def outputExtraction (x : Planes) : Blocks := fun b j ↦
  writeReordered (x ⟨4 * (j.val / 4 % 2) + b.val, by omega⟩)
    ⟨j.val % 4, by omega⟩ ⟨j.val / 8, by omega⟩

def invBitslice (x : Planes) : Blocks := outputExtraction (bitsliceSwaps x)

theorem getLsbD_readReordered (x : Fin 16 → BitVec 8) (h : Fin 2) (i : Fin 64) :
    (readReordered x h).getLsbD i.val =
      (x ⟨4 * h.val + 8 * (i.val / 8 % 2) + i.val / 8 / 2, by omega⟩).getLsbD
        (i.val % 8) := by
  exact getLsbD_packBytes _ i

theorem getLsbD_writeReordered (x : BitVec 64) (r : Fin 4) (h : Fin 2) (p : Fin 8) :
    (writeReordered x r h).getLsbD p.val =
      x.getLsbD (16 * r.val + 8 * h.val + p.val) := by
  simp only [writeReordered, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    p.isLt, decide_true, Bool.true_and]

theorem bitslice_eq_encode (x : Blocks) : bitslice x = encode x := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 64).val from rfl]
  simp only [bitslice]
  rw [getLsbD_bitsliceSwaps _ p ⟨i, hi⟩]
  simp only [inputPacking]
  rw [getLsbD_readReordered _ _ ⟨i / 8 * 8 + p.val, by omega⟩,
    getLsbD_encode x p ⟨i, hi⟩]
  have h : ∀ (p : Fin 8) (i : Fin 64),
      (i.val % 8) % 4 = i.val % 4 ∧
      4 * ((i.val % 8) / 4) +
        8 * ((i.val / 8 * 8 + p.val) / 8 % 2) + (i.val / 8 * 8 + p.val) / 8 / 2 =
          4 * (i.val / 4 % 4) + i.val / 16 ∧
      (i.val / 8 * 8 + p.val) % 8 = p.val := by decide +kernel
  rw [(h p ⟨i, hi⟩).2.2]
  congr 2 <;> apply Fin.ext
  · exact (h p ⟨i, hi⟩).1
  · exact (h p ⟨i, hi⟩).2.1

theorem invBitslice_eq_decode (x : Planes) : invBitslice x = decode x := by
  funext b j
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [show p = (⟨p, hp⟩ : Fin 8).val from rfl]
  simp only [invBitslice, outputExtraction]
  rw [getLsbD_writeReordered _ _ _ ⟨p, hp⟩]
  rw [getLsbD_bitsliceSwaps _ _
    ⟨16 * (j.val % 4) + 8 * (j.val / 8) + p, by omega⟩,
    getLsbD_decode x b j ⟨p, hp⟩]
  have h : ∀ (b : Fin 4) (j : Fin 16) (p : Fin 8),
      (16 * (j.val % 4) + 8 * (j.val / 8) + p.val) % 8 = p.val ∧
      (16 * (j.val % 4) + 8 * (j.val / 8) + p.val) / 8 * 8 +
        (4 * (j.val / 4 % 2) + b.val) =
          16 * (j.val % 4) + 4 * (j.val / 4) + b.val := by decide +kernel
  rw [(h b j ⟨p, hp⟩).2]
  congr 2
  exact Fin.ext (h b j ⟨p, hp⟩).1

theorem invBitslice_bitslice (x : Blocks) : invBitslice (bitslice x) = x := by
  rw [bitslice_eq_encode, invBitslice_eq_decode, decode_encode]

theorem bitslice_invBitslice (x : Planes) : bitslice (invBitslice x) = x := by
  rw [invBitslice_eq_decode, bitslice_eq_encode, encode_decode]

end AesGcm.Proofs.Machine.Fixslice
