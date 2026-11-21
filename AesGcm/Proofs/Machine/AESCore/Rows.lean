import Standards.NIST.AES.Transformations

namespace AesGcm.Proofs.Machine.AESCore

open Standards.NIST.AES

def rowIndex (n : Nat) (j : Fin 16) : Fin 16 :=
  ⟨j.val % 4 + 4 * ((j.val / 4 + n % 4 * (j.val % 4)) % 4), by omega⟩

def shiftRowsBy (n : Nat) (block : Block) : Block :=
  Vector.ofFn fun j ↦ block[rowIndex n j]

theorem rowIndex_mod (n : Nat) (j : Fin 16) : rowIndex (n % 4) j = rowIndex n j := by
  simp only [rowIndex, Nat.mod_mod]

theorem rowIndex_zero (j : Fin 16) : rowIndex 0 j = j := by
  apply Fin.ext
  simp only [rowIndex, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
  omega

theorem rowIndex_add (n m : Nat) (j : Fin 16) :
    rowIndex m (rowIndex n j) = rowIndex (n + m) j := by
  have h : ∀ (n m : Fin 4) (j : Fin 16),
      rowIndex m.val (rowIndex n.val j) = rowIndex (n.val + m.val) j := by decide +kernel
  simpa only [rowIndex, Nat.add_mod, Nat.mod_mod] using
    h ⟨n % 4, by omega⟩ ⟨m % 4, by omega⟩ j

theorem shiftRowsBy_mod (n : Nat) (block : Block) :
    shiftRowsBy (n % 4) block = shiftRowsBy n block := by
  simp only [shiftRowsBy, rowIndex_mod]

theorem shiftRowsBy_zero (block : Block) : shiftRowsBy 0 block = block := by
  apply Vector.ext
  intro j hj
  simp only [shiftRowsBy, Vector.getElem_ofFn, rowIndex_zero, Fin.getElem_fin]

theorem shiftRowsBy_add (n m : Nat) (block : Block) :
    shiftRowsBy n (shiftRowsBy m block) = shiftRowsBy (n + m) block := by
  apply Vector.ext
  intro j hj
  simp only [shiftRowsBy, Vector.getElem_ofFn, Fin.getElem_fin]
  change block[(rowIndex m (rowIndex n ⟨j, hj⟩)).val] =
    block[(rowIndex (n + m) ⟨j, hj⟩).val]
  exact congrArg (fun i : Fin 16 ↦ block[i]) (rowIndex_add n m ⟨j, hj⟩)

theorem shiftRowsBy_one (block : Block) : shiftRowsBy 1 block = shiftRows block := by
  apply Vector.ext
  intro j hj
  simp only [shiftRowsBy, shiftRows, Vector.getElem_ofFn, rowIndex,
    Nat.reduceMod, Nat.one_mul, Fin.getElem_fin]

theorem shiftRowsBy_three (block : Block) : shiftRowsBy 3 block = invShiftRows block := by
  apply Vector.ext
  intro j hj
  simp only [shiftRowsBy, invShiftRows, Vector.getElem_ofFn, rowIndex,
    Nat.reduceMod, Fin.getElem_fin]
  congr 1
  have h : ∀ j : Fin 16,
      j.val % 4 + 4 * ((j.val / 4 + 3 * (j.val % 4)) % 4) =
        j.val % 4 + 4 * ((j.val / 4 + 4 - j.val % 4) % 4) := by decide +kernel
  exact h ⟨j, hj⟩

theorem shiftRowsBy_subBytes (n : Nat) (block : Block) :
    shiftRowsBy n (subBytes block) = subBytes (shiftRowsBy n block) := by
  apply Vector.ext
  intro j hj
  simp only [shiftRowsBy, subBytes, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]


end AesGcm.Proofs.Machine.AESCore
