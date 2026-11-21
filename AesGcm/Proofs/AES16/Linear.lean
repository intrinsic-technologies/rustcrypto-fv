import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.Machine.Fixslice16.Widening
import AesGcm.Proofs.Machine.Fixslice.Linear

namespace AesGcm.Proofs.Machine.AES16

open Fixslice16

def rotateRowsColumnsIndex (r c i : Nat) : Nat :=
  4 * ((i / 4 + r) % 4) + (i % 4 + c) % 4

def shiftRowsIndex (n i : Nat) : Nat := 4 * (i / 4) + (i % 4 + n * (i / 4)) % 4

def deltaSwap1 (x : BitVec 16) (shift : Nat) (mask : BitVec 16) : BitVec 16 :=
  let t := (x ^^^ (x >>> shift)) &&& mask
  x ^^^ t ^^^ (t <<< shift)

def shiftRowsWord1 (x : BitVec 16) : BitVec 16 :=
  deltaSwap1 (deltaSwap1 x 2 0x2310) 1 0x5050

def shiftRowsWord2 (x : BitVec 16) : BitVec 16 := deltaSwap1 x 2 0x3030

def shiftRowsWord3 (x : BitVec 16) : BitVec 16 :=
  deltaSwap1 (deltaSwap1 x 2 0x1320) 1 0x5050

def rotateRows1 (x : BitVec 16) : BitVec 16 := x.rotateRight 4
def rotateRows2 (x : BitVec 16) : BitVec 16 := x.rotateRight 8

def rotateRowsAndColumns11 (x : BitVec 16) : BitVec 16 :=
  (x.rotateRight 5 &&& 0x7777) ||| (x.rotateRight 1 &&& 0x8888)
def rotateRowsAndColumns12 (x : BitVec 16) : BitVec 16 :=
  (x.rotateRight 6 &&& 0x3333) ||| (x.rotateRight 2 &&& 0xcccc)
def rotateRowsAndColumns13 (x : BitVec 16) : BitVec 16 :=
  (x.rotateRight 7 &&& 0x1111) ||| (x.rotateRight 3 &&& 0xeeee)
def rotateRowsAndColumns22 (x : BitVec 16) : BitVec 16 :=
  (x.rotateRight 10 &&& 0x3333) ||| (x.rotateRight 6 &&& 0xcccc)

theorem getLsbD_rotateRows1 (x : BitVec 16) (i : Fin 16) :
    (rotateRows1 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 0 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRows1, rotateRowsColumnsIndex]

theorem projectWord_rotateRows1 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRows1 x) b = rotateRows1 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 1 0 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRows1 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRows1 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_rotateRows2 (x : BitVec 16) (i : Fin 16) :
    (rotateRows2 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 2 0 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRows2, rotateRowsColumnsIndex]

theorem projectWord_rotateRows2 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRows2 x) b = rotateRows2 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 2 0 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRows2 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRows2 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_rotateRowsAndColumns11 (x : BitVec 16) (i : Fin 16) :
    (rotateRowsAndColumns11 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 1 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns11, rotateRowsColumnsIndex]

theorem projectWord_rotateRowsAndColumns11 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRowsAndColumns11 x) b = rotateRowsAndColumns11 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 1 1 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRowsAndColumns11 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRowsAndColumns11 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_rotateRowsAndColumns12 (x : BitVec 16) (i : Fin 16) :
    (rotateRowsAndColumns12 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns12, rotateRowsColumnsIndex]

theorem projectWord_rotateRowsAndColumns12 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRowsAndColumns12 x) b = rotateRowsAndColumns12 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 1 2 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRowsAndColumns12 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRowsAndColumns12 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_rotateRowsAndColumns13 (x : BitVec 16) (i : Fin 16) :
    (rotateRowsAndColumns13 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 1 3 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns13, rotateRowsColumnsIndex]

theorem projectWord_rotateRowsAndColumns13 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRowsAndColumns13 x) b = rotateRowsAndColumns13 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 1 3 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRowsAndColumns13 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRowsAndColumns13 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_rotateRowsAndColumns22 (x : BitVec 16) (i : Fin 16) :
    (rotateRowsAndColumns22 x).getLsbD i.val = x.getLsbD (rotateRowsColumnsIndex 2 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, rotateRowsAndColumns22, rotateRowsColumnsIndex]

theorem projectWord_rotateRowsAndColumns22 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.rotateRowsAndColumns22 x) b = rotateRowsAndColumns22 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : rotateRowsColumnsIndex 2 2 i < 16 := by simp only [rotateRowsColumnsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_rotateRowsAndColumns22 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_rotateRowsAndColumns22 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.rotateRowsColumnsIndex, rotateRowsColumnsIndex]
  omega

theorem getLsbD_shiftRowsWord1 (x : BitVec 16) (i : Fin 16) :
    (shiftRowsWord1 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 1 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord1, shiftRowsIndex, deltaSwap1,
    Bool.xor, bne_left_comm, bne_cancel_middle]

theorem projectWord_shiftRowsWord1 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.shiftRowsWord1 x) b = shiftRowsWord1 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : shiftRowsIndex 1 i < 16 := by simp only [shiftRowsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_shiftRowsWord1 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_shiftRowsWord1 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.shiftRowsIndex, shiftRowsIndex]
  omega

theorem getLsbD_shiftRowsWord2 (x : BitVec 16) (i : Fin 16) :
    (shiftRowsWord2 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 2 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord2, shiftRowsIndex, deltaSwap1,
    Bool.xor, bne_left_comm]

theorem projectWord_shiftRowsWord2 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.shiftRowsWord2 x) b = shiftRowsWord2 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : shiftRowsIndex 2 i < 16 := by simp only [shiftRowsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_shiftRowsWord2 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_shiftRowsWord2 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.shiftRowsIndex, shiftRowsIndex]
  omega

theorem getLsbD_shiftRowsWord3 (x : BitVec 16) (i : Fin 16) :
    (shiftRowsWord3 x).getLsbD i.val = x.getLsbD (shiftRowsIndex 3 i.val) := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [h, shiftRowsWord3, shiftRowsIndex, deltaSwap1,
    Bool.xor, bne_left_comm, bne_cancel_middle]

theorem projectWord_shiftRowsWord3 (x : BitVec 64) (b : Fin 4) :
    projectWord (Fixslice.shiftRowsWord3 x) b = shiftRowsWord3 (projectWord x b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : shiftRowsIndex 3 i < 16 := by simp only [shiftRowsIndex]; omega
  rw [getLsbD_projectWord _ b ⟨i, hi⟩,
    Fixslice.getLsbD_shiftRowsWord3 x ⟨4 * i + b.val, by omega⟩,
    getLsbD_shiftRowsWord3 _ ⟨i, hi⟩, getLsbD_projectWord _ b ⟨_, hj⟩]
  congr 1
  simp only [Fixslice.shiftRowsIndex, shiftRowsIndex]
  omega

def shiftRows1 (a : Planes16) : Planes16 := fun p ↦ shiftRowsWord1 (a p)

theorem projectPlanes_shiftRows1 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.shiftRows1 x) b = shiftRows1 (projectPlanes x b) := by
  funext p
  exact projectWord_shiftRowsWord1 (x p) b

theorem shiftRows1_encode (x : Block) :
    shiftRows1 (encode x) =
      encode (Fixslice.shiftRowsBlocks 1 (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.shiftRows1_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_shiftRows1, projectPlanes_encode, Fixslice.broadcast] using h

def shiftRows2 (a : Planes16) : Planes16 := fun p ↦ shiftRowsWord2 (a p)

theorem projectPlanes_shiftRows2 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.shiftRows2 x) b = shiftRows2 (projectPlanes x b) := by
  funext p
  exact projectWord_shiftRowsWord2 (x p) b

theorem shiftRows2_encode (x : Block) :
    shiftRows2 (encode x) =
      encode (Fixslice.shiftRowsBlocks 2 (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.shiftRows2_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_shiftRows2, projectPlanes_encode, Fixslice.broadcast] using h

def shiftRows3 (a : Planes16) : Planes16 := fun p ↦ shiftRowsWord3 (a p)

theorem projectPlanes_shiftRows3 (x : Fixslice.Planes) (b : Fin 4) :
    projectPlanes (Fixslice.shiftRows3 x) b = shiftRows3 (projectPlanes x b) := by
  funext p
  exact projectWord_shiftRowsWord3 (x p) b

theorem shiftRows3_encode (x : Block) :
    shiftRows3 (encode x) =
      encode (Fixslice.shiftRowsBlocks 3 (Fixslice.broadcast x) 0) := by
  have h := congrArg (fun a ↦ projectPlanes a 0)
    (Fixslice.shiftRows3_encode (Fixslice.broadcast x))
  simpa only [projectPlanes_shiftRows3, projectPlanes_encode, Fixslice.broadcast] using h

end AesGcm.Proofs.Machine.AES16
