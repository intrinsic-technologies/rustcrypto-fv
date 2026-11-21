import AesGcm.Proofs.Machine.Fixslice.Representation

namespace AesGcm.Proofs.Machine.Fixslice16

open AesGcm.Proofs.Machine.Fixslice (fromBits getLsbD_fromBits)

abbrev Planes16 := Fin 8 → BitVec 16
abbrev Block := Fin 16 → BitVec 8

def transposeIndex (i : Fin 16) : Fin 16 := ⟨4 * (i.val % 4) + i.val / 4, by omega⟩

theorem transposeIndex_transposeIndex (i : Fin 16) : transposeIndex (transposeIndex i) = i := by
  apply Fin.ext
  have h : ∀ i : Fin 16, (transposeIndex (transposeIndex i)).val = i.val := by decide +kernel
  exact h i

def encode (x : Block) : Planes16 := fun p ↦ fromBits fun i ↦
  (x (transposeIndex i)).getLsbD p.val

def decode (x : Planes16) : Block := fun j ↦ fromBits fun p ↦
  (x p).getLsbD (transposeIndex j).val

theorem getLsbD_encode (x : Block) (p : Fin 8) (i : Fin 16) :
    (encode x p).getLsbD i.val = (x (transposeIndex i)).getLsbD p.val :=
  getLsbD_fromBits _ _

theorem getLsbD_decode (x : Planes16) (j : Fin 16) (p : Fin 8) :
    (decode x j).getLsbD p.val = (x p).getLsbD (transposeIndex j).val :=
  getLsbD_fromBits _ _

theorem decode_encode (x : Block) : decode (encode x) = x := by
  funext j
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [show p = (⟨p, hp⟩ : Fin 8).val from rfl, getLsbD_decode, getLsbD_encode,
    transposeIndex_transposeIndex]

theorem encode_decode (x : Planes16) : encode (decode x) = x := by
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show i = (⟨i, hi⟩ : Fin 16).val from rfl, getLsbD_encode, getLsbD_decode,
    transposeIndex_transposeIndex]

theorem encode_injective {x y : Block} (h : encode x = encode y) : x = y := by
  simpa only [decode_encode] using congrArg decode h

theorem decode_injective {x y : Planes16} (h : decode x = decode y) : x = y := by
  simpa only [encode_decode] using congrArg encode h

end AesGcm.Proofs.Machine.Fixslice16
