import K256.Proofs.Generate.Generator.Multiply.Coordinates
import K256.Proofs.Common.Image
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open Standards.SECG.DomainParameters.Secp256k1

local instance : NeZero modulus := ⟨by decide⟩

private def coordinateWords (x : Fin modulus) : Limbs :=
  Vector.ofFn fun i => BitVec.ofNat 64 (x.val / radix ^ i.val % radix)

private def StoredCoordinate (offset : Nat) (x : Fin modulus) : Prop :=
  ∀ i : Fin 5, chunkedRead Extracted.rodataBytes (offset + 8 * i.val) 8 =
    wordBytes (coordinateWords x)[i.val]

private theorem readCoordinate {mem : Ram}
    (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2)
    {offset : Nat} {x : Fin modulus} (fits : offset + 40 ≤ 15952)
    (stored : StoredCoordinate offset x) :
    WordsAt mem (Extracted.rodataAddress + BitVec.ofNat 64 offset) 64 (coordinateWords x) := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  intro i hi
  let p := wordAddr (Extracted.rodataAddress + BitVec.ofNat 64 offset) 64 i
  have image := codeRange_sub_section hs (offset + 8 * i) 8 (stored ⟨i, hi⟩)
    (by decide +kernel) (by change _ ≤ Extracted.rodataBytes.size; rw [Common.rodataBytes_size]; omega)
    (p := p) (by simp only [p, wordAddr, BitVec.ofNat_add, BitVec.add_assoc]; rfl)
  have bytes : Bytes mem p 8 (storedByte (coordinateWords x)[i]) := by
    intro j hj
    apply loaded (p + BitVec.ofNat 64 j, storedByte (coordinateWords x)[i] j)
    apply image
    have h := mem_codeRange p (wordBytes (coordinateWords x)[i]) j
      (by simp only [wordBytes, List.length_ofFn]; omega)
    simpa only [wordBytes, List.getElem_ofFn] using h
  exact bytes.memLoad (by decide) (by decide)

private def gx : Fin modulus :=
  ⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798, by decide⟩
private def gy : Fin modulus :=
  ⟨0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8, by decide⟩

def generator : Projective := ⟨gx, gy, 1⟩

def identity : Projective := ⟨0, 1, 0⟩

theorem generator_valid : generator.valid := by
  unfold Projective.valid
  decide +kernel

theorem generator_value : generator.value = domain.G := by decide +kernel

theorem identity_valid : identity.valid := by
  unfold Projective.valid
  decide +kernel

theorem identity_value : identity.value = .infinity := rfl

private theorem readPoint {mem : Ram}
    (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2)
    {offset : Nat} {p : Projective} (fits : offset + 120 ≤ 15952)
    (x : StoredCoordinate offset p.x) (y : StoredCoordinate (offset + 40) p.y)
    (z : StoredCoordinate (offset + 80) p.z)
    (rx : FieldRepr (coordinateWords p.x) p.x 1) (ry : FieldRepr (coordinateWords p.y) p.y 1)
    (rz : FieldRepr (coordinateWords p.z) p.z 1) :
    p.Stored mem (Extracted.rodataAddress + BitVec.ofNat 64 offset) := by
  refine ⟨_, _, _, readCoordinate loaded (by omega) x, ?_, ?_, rx, ry, rz⟩
  · rw [show Extracted.rodataAddress + BitVec.ofNat 64 offset + 40 =
        Extracted.rodataAddress + BitVec.ofNat 64 (offset + 40) by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl]
    exact readCoordinate loaded (by omega) y
  · rw [show Extracted.rodataAddress + BitVec.ofNat 64 offset + 80 =
        Extracted.rodataAddress + BitVec.ofNat 64 (offset + 80) by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl]
    exact readCoordinate loaded (by omega) z

theorem generator_stored {mem : Ram} (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2) :
    generator.Stored mem 0x202bc8 := by
  apply readPoint loaded (offset := 0x2bc8) (by decide)
  all_goals first | unfold StoredCoordinate; decide +kernel | unfold FieldRepr; decide +kernel

theorem identity_stored {mem : Ram} (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2)
    {addr : Word} (h : addr = 0x202c40 ∨ addr = 0x203258) : identity.Stored mem addr := by
  rcases h with rfl | rfl
  · apply readPoint loaded (offset := 0x2c40) (by decide)
    all_goals first | unfold StoredCoordinate; decide +kernel | unfold FieldRepr; decide +kernel
  · apply readPoint loaded (offset := 0x3258) (by decide)
    all_goals first | unfold StoredCoordinate; decide +kernel | unfold FieldRepr; decide +kernel

theorem generatorAt {mem : Ram}
    (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2) :
    Affine.ProjectiveAt mem 0x202bc8 domain.G := generator_value ▸ (generator_stored loaded).projectiveAt

theorem identityAt {mem : Ram}
    (loaded : ∀ a ∈ Extracted.programImage, mem[a.1]? = some a.2) :
    Affine.ProjectiveAt mem 0x202c40 .infinity := (identity_stored loaded (Or.inl rfl)).projectiveAt

end K256.Proofs.Generate.Generator.Multiply
