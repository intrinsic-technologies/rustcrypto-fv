import AesGcm.Proofs.Machine.Fixslice16.Representation

namespace AesGcm.Proofs.Machine.Fixslice16

def deltaSwap2 (a b : BitVec 16) (shift : Nat) (mask : BitVec 16) :
    BitVec 16 × BitVec 16 :=
  let t := (a ^^^ (b >>> shift)) &&& mask
  (a ^^^ t, b ^^^ (t <<< shift))

theorem getLsbD_deltaSwap2_fst (a b mask : BitVec 16) (s i : Nat) :
    (deltaSwap2 a b s mask).1.getLsbD i =
      if mask.getLsbD i then b.getLsbD (s + i) else a.getLsbD i := by
  simp only [deltaSwap2, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_ushiftRight]
  cases mask.getLsbD i <;> simp

theorem getLsbD_deltaSwap2_snd (a b mask : BitVec 16) (s i : Nat) (hi : i < 16) :
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

def swapMask (k : Fin 3) : BitVec 16 :=
  match k.val with
  | 0 => 0x5555
  | 1 => 0x3333
  | _ => 0x0f0f

def swapLow (k : Fin 3) (p : Fin 8) : Fin 8 :=
  ⟨(p.val / (2 * swapShift k) * (2 * swapShift k) + p.val % swapShift k) % 8,
    Nat.mod_lt _ (by decide)⟩

def swapHigh (k : Fin 3) (p : Fin 8) : Fin 8 :=
  ⟨(swapLow k p).val + swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8), (swapLow k p).val + swapShift k < 8 :=
      by decide +kernel
    exact h k p⟩

def swapStage (k : Fin 3) (x : Planes16) : Planes16 := fun p ↦
  let ab := deltaSwap2 (x (swapHigh k p)) (x (swapLow k p)) (swapShift k) (swapMask k)
  if p.val / swapShift k % 2 = 0 then ab.2 else ab.1

def swapPlane (k : Fin 3) (p : Fin 8) (i : Fin 16) : Fin 8 :=
  ⟨(swapLow k p).val + i.val / swapShift k % 2 * swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 16),
        (swapLow k p).val + i.val / swapShift k % 2 * swapShift k < 8 :=
      by decide +kernel
    exact h k p i⟩

def swapBit (k : Fin 3) (p : Fin 8) (i : Fin 16) : Fin 16 :=
  ⟨i.val / (2 * swapShift k) * (2 * swapShift k) +
      p.val / swapShift k % 2 * swapShift k + i.val % swapShift k, by
    have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 16),
        i.val / (2 * swapShift k) * (2 * swapShift k) +
          p.val / swapShift k % 2 * swapShift k + i.val % swapShift k < 16 :=
      by decide +kernel
    exact h k p i⟩

def swapRoute (k : Fin 3) (p : Fin 8) (i : Fin 16) : Fin 8 × Nat :=
  if p.val / swapShift k % 2 = 0 then
    if swapShift k ≤ i.val ∧ (swapMask k).getLsbD (i.val - swapShift k) then
      (swapHigh k p, i.val - swapShift k)
    else (swapLow k p, i.val)
  else if (swapMask k).getLsbD i.val then
    (swapLow k p, swapShift k + i.val)
  else (swapHigh k p, i.val)

theorem swapRoute_eq (k : Fin 3) (p : Fin 8) (i : Fin 16) :
    swapRoute k p i = (swapPlane k p i, (swapBit k p i).val) := by
  have h : ∀ (k : Fin 3) (p : Fin 8) (i : Fin 16),
      swapRoute k p i = (swapPlane k p i, (swapBit k p i).val) := by decide +kernel
  exact h k p i

theorem getLsbD_swapStage (k : Fin 3) (x : Planes16) (p : Fin 8) (i : Fin 16) :
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

def bitsliceSwaps (x : Planes16) : Planes16 :=
  swapStage 2 (swapStage 1 (swapStage 0 x))

theorem getLsbD_bitsliceSwaps (x : Planes16) (p : Fin 8) (i : Fin 16) :
    (bitsliceSwaps x p).getLsbD i.val =
      (x ⟨i.val % 8, by omega⟩).getLsbD (i.val / 8 * 8 + p.val) := by
  simp only [bitsliceSwaps, getLsbD_swapStage]
  have h : ∀ (p : Fin 8) (i : Fin 16),
      (swapPlane 0 (swapPlane 1 (swapPlane 2 p i) (swapBit 2 p i))
        (swapBit 1 (swapPlane 2 p i) (swapBit 2 p i))).val = i.val % 8 ∧
      (swapBit 0 (swapPlane 1 (swapPlane 2 p i) (swapBit 2 p i))
        (swapBit 1 (swapPlane 2 p i) (swapBit 2 p i))).val =
          i.val / 8 * 8 + p.val := by decide +kernel
  rw [(h p i).2]
  congr 2
  exact Fin.ext (h p i).1

def packBytes (lo hi : BitVec 8) : BitVec 16 :=
  lo.zeroExtend 16 ||| (hi.zeroExtend 16 <<< 8)

theorem getLsbD_packBytes (lo hi : BitVec 8) (i : Fin 16) :
    (packBytes lo hi).getLsbD i.val =
      if i.val < 8 then lo.getLsbD i.val else hi.getLsbD (i.val - 8) := by
  simp only [packBytes, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, i.isLt, decide_true, Bool.true_and]
  by_cases h : i.val < 8
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.or_false, ite_true]
  · have hge : lo.getLsbD i.val = false := BitVec.getLsbD_of_ge _ _ (by omega)
    have hlt : i.val - 8 < 16 := by omega
    simp only [h, decide_false, Bool.not_false, Bool.true_and, hge, Bool.false_or,
      hlt, decide_true, ite_false]

def inputPacking (x : Block) : Planes16 := fun p ↦
  packBytes (x ⟨4 * (p.val % 4) + p.val / 4, by omega⟩)
    (x ⟨4 * (p.val % 4) + p.val / 4 + 2, by omega⟩)

def bitslice (x : Block) : Planes16 := bitsliceSwaps (inputPacking x)

def outputExtraction (x : Planes16) : Block := fun j ↦
  ((x ⟨4 * (j.val % 2) + j.val / 4, by omega⟩) >>> (8 * (j.val / 2 % 2))).setWidth 8

def invBitslice (x : Planes16) : Block := outputExtraction (bitsliceSwaps x)

theorem bitslice_eq_encode (x : Block) : bitslice x = encode x := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 16).val from rfl]
  simp only [bitslice]
  rw [getLsbD_bitsliceSwaps _ p ⟨i, hi⟩]
  simp only [inputPacking]
  rw [getLsbD_packBytes _ _ ⟨i / 8 * 8 + p.val, by omega⟩, getLsbD_encode x p ⟨i, hi⟩]
  dsimp only
  have h : ∀ (p : Fin 8) (i : Fin 16),
      (if i.val / 8 * 8 + p.val < 8 then
        4 * (i.val % 8 % 4) + (i.val % 8) / 4 else
        4 * (i.val % 8 % 4) + (i.val % 8) / 4 + 2) = (transposeIndex i).val ∧
      (if i.val / 8 * 8 + p.val < 8 then i.val / 8 * 8 + p.val else
        i.val / 8 * 8 + p.val - 8) = p.val := by decide +kernel
  split <;> rename_i hc
  · have hj := (h p ⟨i, hi⟩).1
    have hp := (h p ⟨i, hi⟩).2
    simp only [hc, ite_true] at hj hp
    rw [hp]
    congr 2
    exact Fin.ext hj
  · have hj := (h p ⟨i, hi⟩).1
    have hp := (h p ⟨i, hi⟩).2
    simp only [hc, ite_false] at hj hp
    rw [hp]
    congr 2
    exact Fin.ext hj

theorem invBitslice_eq_decode (x : Planes16) : invBitslice x = decode x := by
  funext j
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  simp only [invBitslice, outputExtraction, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and]
  rw [getLsbD_bitsliceSwaps _ _ ⟨8 * (j.val / 2 % 2) + p, by omega⟩,
    getLsbD_decode _ _ ⟨p, hp⟩]
  have h : ∀ (j : Fin 16) (p : Fin 8),
      (8 * (j.val / 2 % 2) + p.val) % 8 = p.val ∧
      (8 * (j.val / 2 % 2) + p.val) / 8 * 8 + (4 * (j.val % 2) + j.val / 4) =
        (transposeIndex j).val := by decide +kernel
  dsimp only
  rw [(h j ⟨p, hp⟩).2]
  congr 2
  exact Fin.ext (h j ⟨p, hp⟩).1

theorem invBitslice_bitslice (x : Block) : invBitslice (bitslice x) = x := by
  rw [bitslice_eq_encode, invBitslice_eq_decode, decode_encode]

theorem bitslice_invBitslice (x : Planes16) : bitslice (invBitslice x) = x := by
  rw [invBitslice_eq_decode, bitslice_eq_encode, encode_decode]

end AesGcm.Proofs.Machine.Fixslice16
