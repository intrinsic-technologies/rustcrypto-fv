import Std

namespace AesGcm.Proofs.Machine.Fixslice

abbrev Planes := Fin 8 → BitVec 64
abbrev Blocks := Fin 4 → Fin 16 → BitVec 8

def fromBits {n : Nat} (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

theorem getLsbD_fromBits {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (fromBits f).getLsbD i.val = f i := by
  simp only [fromBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD, i.isLt]

def encode (x : Blocks) : Planes := fun p ↦ fromBits fun i ↦
  (x ⟨i.val % 4, by omega⟩ ⟨4 * (i.val / 4 % 4) + i.val / 16, by omega⟩).getLsbD p.val

def decode (x : Planes) : Blocks := fun b j ↦ fromBits fun p ↦
  (x p).getLsbD (16 * (j.val % 4) + 4 * (j.val / 4) + b.val)

theorem getLsbD_encode (x : Blocks) (p : Fin 8) (i : Fin 64) :
    (encode x p).getLsbD i.val =
      (x ⟨i.val % 4, by omega⟩ ⟨4 * (i.val / 4 % 4) + i.val / 16, by omega⟩).getLsbD p.val :=
  getLsbD_fromBits _ _

theorem getLsbD_decode (x : Planes) (b : Fin 4) (j : Fin 16) (p : Fin 8) :
    (decode x b j).getLsbD p.val =
      (x p).getLsbD (16 * (j.val % 4) + 4 * (j.val / 4) + b.val) :=
  getLsbD_fromBits _ _

theorem decode_encode (x : Blocks) : decode (encode x) = x := by
  funext b j
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [show p = (⟨p, hp⟩ : Fin 8).val from rfl, getLsbD_decode,
    getLsbD_encode _ _ ⟨16 * (j.val % 4) + 4 * (j.val / 4) + b.val, by omega⟩]
  have h : ∀ (b : Fin 4) (j : Fin 16),
      ((16 * (j.val % 4) + 4 * (j.val / 4) + b.val) % 4 = b.val) ∧
      (4 * ((16 * (j.val % 4) + 4 * (j.val / 4) + b.val) / 4 % 4) +
        (16 * (j.val % 4) + 4 * (j.val / 4) + b.val) / 16 = j.val) := by decide +kernel
  congr 2 <;> apply Fin.ext
  · exact (h b j).1
  · exact (h b j).2

theorem encode_decode (x : Planes) : encode (decode x) = x := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 64).val from rfl, getLsbD_encode, getLsbD_decode]
  congr 1
  have h : ∀ i : Fin 64,
      16 * ((4 * (i.val / 4 % 4) + i.val / 16) % 4) +
        4 * ((4 * (i.val / 4 % 4) + i.val / 16) / 4) + i.val % 4 = i.val := by decide +kernel
  exact h ⟨i, hi⟩

end AesGcm.Proofs.Machine.Fixslice
