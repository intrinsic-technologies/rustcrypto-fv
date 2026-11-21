import K256.Proofs.Generate.Generator.Affine.Invert.Contract

namespace K256.Proofs.Generate.Generator.Affine.Invert

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.Refine K256.Proofs.Lift K256.Proofs.Common.Field

def modulusWords : Vector Word 4 := #v[0xfffffffefffffc2f, -1, -1, -1]

def unitWords : Vector Word 4 := #v[1, 0, 0, 0]

private theorem wordsInImage {m : Ram}
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    {offset : Nat} (v : Vector Word 4) (fits : offset + 32 ≤ 15952)
    (stored : ∀ i : Fin 4, chunkedRead Extracted.rodataBytes (offset + 8*i.val) 8 =
      wordBytes v[i]) :
    ∀ i : Fin 4,
      let addr := wordAddr (Extracted.rodataAddress + BitVec.ofNat 64 offset) 64 i
      Readable m addr 8 ∧ memLoad m addr 64 = v[i] := by
  intro i
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  let addr := wordAddr (Extracted.rodataAddress + BitVec.ofNat 64 offset) 64 i
  have image := codeRange_sub_section hs (offset + 8*i.val) 8 (stored i)
    (by decide +kernel) (by change _ ≤ Extracted.rodataBytes.size; rw [Common.rodataBytes_size]; omega)
    (p := addr) (by simp only [addr, wordAddr, BitVec.ofNat_add, BitVec.add_assoc]; rfl)
  have bytes : Bytes m addr 8 (storedByte v[i]) := by
    intro j hj
    apply loaded (addr + BitVec.ofNat 64 j, storedByte v[i] j)
    apply image
    have h := mem_codeRange addr (wordBytes v[i]) j
      (by simp only [wordBytes, List.length_ofFn]; omega)
    simpa only [wordBytes, List.getElem_ofFn] using h
  refine ⟨⟨?_, fun j hj => by rw [bytes j hj]; rfl⟩, bytes.memLoad (by decide) (by decide)⟩
  simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceDiv]
  change ((2097152 + offset % 2^64) % 2^64 + (8*i.val) % 2^64) % 2^64 + 8 ≤ 2^32
  omega

theorem modulus_loaded {m : Ram}
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    ∀ i : Fin 4,
      let addr := wordAddr 0x2021e0 64 i
      Readable m addr 8 ∧ memLoad m addr 64 = modulusWords[i] :=
  wordsInImage loaded (offset := 0x21e0) modulusWords (by decide) (by decide +kernel)

theorem unit_loaded {m : Ram}
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2) :
    ∀ i : Fin 4,
      let addr := wordAddr 0x202180 64 i
      Readable m addr 8 ∧ memLoad m addr 64 = unitWords[i] :=
  wordsInImage loaded (offset := 0x2180) unitWords (by decide) (by decide +kernel)

theorem modulus_value : value modulusWords = modulus := by decide +kernel

theorem unit_value : value unitWords = 1 := by decide +kernel

theorem modulus_inverse_word : modulusWords[0] * 0x27c7f6e22ddacacf = 1 := by decide +kernel

end K256.Proofs.Generate.Generator.Affine.Invert
