import AesGcm.Proofs.AES16.MixColumnsAlgebra
namespace AesGcm.Proofs.Machine.AES16.KeySchedule
open Fixslice16

theorem projectWord_and (x y : BitVec 64) (b : Fin 4) :
    projectWord (x &&& y) b = projectWord x b &&& projectWord y b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, getLsbD_projectWord _ b ⟨i, hi⟩]

theorem projectWord_shiftLeft (x : BitVec 64) (b : Fin 4) (n : Nat) :
    projectWord (x <<< (4 * n)) b = projectWord x b <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_projectWord _ b ⟨i, hi⟩]
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hn : n ≤ i
  · have h1 : 4 * n ≤ 4 * i + b.val := by omega
    have he : 4 * i + b.val - 4 * n = 4 * (i - n) + b.val := by omega
    simp only [hi, show 4 * i + b.val < 64 by omega,
      show ¬i < n by omega, show ¬4 * i + b.val < 4 * n by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, he,
      getLsbD_projectWord _ b ⟨i - n, by omega⟩]
  · have h1 : ¬4 * n ≤ 4 * i + b.val := by have := b.isLt; omega
    simp only [show i < n by omega, show 4 * i + b.val < 4 * n by omega,
      decide_true, Bool.not_true, Bool.and_false, Bool.false_and]

theorem projectWord_rotateRight (x : BitVec 64) (b : Fin 4) (n : Nat) :
    projectWord (x.rotateRight (4 * n)) b = (projectWord x b).rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_projectWord _ b ⟨i, hi⟩]
  simp only [BitVec.getLsbD_rotateRight, hi, show 4 * i + b.val < 64 by omega,
    decide_true, Bool.true_and]
  have hn : 4 * n % 64 = 4 * (n % 16) := by omega
  rw [hn]
  by_cases h : i < 16 - n % 16
  · have h64 : 4 * i + b.val < 64 - 4 * (n % 16) := by omega
    simp only [h, h64, ↓reduceIte]
    rw [getLsbD_projectWord _ b ⟨n % 16 + i, by omega⟩]
    congr 1
    dsimp only
    omega
  · have h64 : ¬4 * i + b.val < 64 - 4 * (n % 16) := by omega
    simp only [h, h64, ↓reduceIte]
    rw [getLsbD_projectWord _ b ⟨i - (16 - n % 16), by omega⟩]
    congr 1
    dsimp only
    omega

end AesGcm.Proofs.Machine.AES16.KeySchedule
