import K256.Proofs.Generate.Curve
import K256.Proofs.Generate.Generator.Multiply.Constants
import K256.Proofs.Common.Field.Multiply

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism

open K256.Spec.Program K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field
  Prelude X86.Machine X86.UserProcess X86Proofs Standards.SECG.DomainParameters.Secp256k1

private def generatorX : Limbs := #v[0x2815b16f81798, 0xdb2dce28d959f, 0xe870b07029bfc, 0xbbac55a06295c, 0x79be667ef9dc]
private def generatorY : Limbs := #v[0x7d08ffb10d4b8, 0x48a68554199c4, 0xe1108a8fd17b4, 0xc4655da4fbfc0, 0x483ada7726a3]
private def generatorZ : Limbs := #v[0x1, 0x0, 0x0, 0x0, 0x0]
private def productX : Limbs := #v[0xba04400b88fcb, 0x67f15e98da7b, 0x6902325872844, 0x1887ab0102b69, 0xbcace2e99da0]

def inputWords : Vector Word 15 := generatorX ++ generatorY ++ generatorZ
def outputWords : Vector Word 15 := productX ++ generatorY ++ generatorZ

theorem sourceWords {m : Ram} {src : Word}
    (loaded : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (input : ∀ i : Fin 15, memLoad m (wordAddr src 64 i.val) 64 =
      memLoad m (wordAddr 0x202bc8 64 i.val) 64) : WordsAt m src 64 inputWords := by
  let sec : ImageSection := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩
  have hs : sec ∈ Extracted.programSections := by simp [sec, Extracted.programSections]
  have data : ∀ i : Fin 15, chunkedRead Extracted.rodataBytes (0x2bc8 + 8*i.val) 8 =
      wordBytes inputWords[i.val] := by decide +kernel
  intro i hi
  rw [input ⟨i,hi⟩]
  have addr : Extracted.rodataAddress + BitVec.ofNat 64 (0x2bc8 + 8*i) =
      wordAddr 0x202bc8 64 i := by rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  have sub := codeRange_sub_section hs _ _ (data ⟨i,hi⟩) (by decide +kernel)
    (by change 0x2bc8 + 8*i + 8 ≤ Extracted.rodataBytes.size; rw [Common.rodataBytes_size]; omega)
    addr
  apply Bytes.memLoad _ (by decide) (by decide)
  intro j hj
  apply loaded (wordAddr 0x202bc8 64 i + BitVec.ofNat 64 j, storedByte inputWords[i] j) (sub _ ?_)
  have h := mem_codeRange (wordAddr 0x202bc8 64 i) (wordBytes inputWords[i]) j
    (by simp only [wordBytes, List.length_ofFn]; omega)
  simpa only [wordBytes, List.getElem_ofFn] using h

local instance : NeZero modulus := ⟨by decide⟩

private def beta : Fin modulus := ⟨0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee, by decide⟩
private def betaWords : Limbs := #v[0x96c28719501ee, 0x7512f58995c13, 0xc3434e99cf049, 0x7106e64479ea, 0x7ae96a2b657c]
private def point : Projective := ⟨let gx : Fin modulus := generator.x; gx * beta, generator.y, generator.z⟩

private theorem product : mulWords generatorX betaWords = productX := by decide +kernel

theorem resultOfWords {m : Ram} {dst : Word} (words : WordsAt m dst 64 outputWords) :
    ∃ p : Projective, p.valid ∧ p.Stored m dst ∧ p.value = Curve.endomorphism domain.G := by
  refine ⟨point, by unfold Projective.valid; decide +kernel, ?_, by decide +kernel⟩
  have repr := mulWords_repr generatorX betaWords generator.x beta (by unfold FieldRepr; decide +kernel)
    (by unfold FieldRepr; decide +kernel)
  rw [product] at repr
  have slice (k : Nat) (limbs : Limbs) (bound : k + 5 ≤ 15)
      (matchWords : ∀ i : Fin 5, outputWords[k+i.val] = limbs[i.val]) :
      WordsAt m (wordAddr dst 64 k) 64 limbs := by
    intro i hi
    have h := (words (k+i) (by omega)).trans (matchWords ⟨i,hi⟩)
    simpa only [wordAddr, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc] using h
  refine ⟨productX, generatorY, generatorZ, ?_, slice 5 _ (by decide) (by decide +kernel),
    slice 10 _ (by decide) (by decide +kernel), repr,
    by unfold FieldRepr; decide +kernel, by unfold FieldRepr; decide +kernel⟩
  simpa only [wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    slice 0 productX (by decide) (by decide +kernel)

end K256.Proofs.Generate.Generator.Multiply.Prepare.Endomorphism
