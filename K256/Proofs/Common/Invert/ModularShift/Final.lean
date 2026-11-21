import K256.Proofs.Common.Invert.ModularShift.Quotient

namespace K256.Proofs.Common.Invert.ModularShift.Arithmetic

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

def finalDifference (p : Inputs) : Limbs :=
  ⟨v108c5f p, (v108c9c p).1, (v108cd3 p).1, (v108d0d p).1⟩

theorem final_difference_eq (p : Inputs) :
    subRaw (quotientLow p) (limbs modulusWords) =
      (finalDifference p, v108d25 p) := by
  simp only [subRaw,
    subWord,
    borrow,
    quotientLow, finalDifference, v108c5f, v108c65, v108c6b, v108c6e,
    v108c71, v108c74, v108c77, v108c88, v108c95, v108c98, v108c9c,
    v108ca2, v108ca8, v108cab, v108cae, v108cb1, v108cb4,
    v108cbf, v108ccc, v108ccf, v108cd3, v108cd9, v108cdf,
    v108ce2, v108ce5, v108ce8, v108ceb, v108cf6, v108d06,
    v108d09, v108d0d, v108d13, v108d19, v108d1c, v108d1f, v108d22, v108d25,
    addSpec, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem final_borrow_one (p : Inputs) (hbound : (quotientLow p).toNat < (limbs modulusWords).toNat) :
    v108d25 p = 1 := by
  have h := subRaw_toNat
    (quotientLow p) (limbs modulusWords)
  rw [final_difference_eq] at h
  dsimp only at h
  have hn : (v108d25 p).toNat = 1 := by omega
  exact BitVec.eq_of_toNat_eq hn

theorem resultWords_eq (p : Inputs) (hbound : (quotientLow p).toNat < (limbs modulusWords).toNat)
    (hhigh : quotientHigh p = 0) :
    resultWords p = words (quotientLow p) := by
  change v108d33 p = 0 at hhigh
  have hb := final_borrow_one p hbound
  have hflag : v108d4b p = 1 := by
    simp only [v108d4b, setWidth_mergeGPR8, v108d36, hb, hhigh]
    rfl
  have hmask : v108d8a p = -1 := by
    simp only [v108d8a, setWidth_mergeGPR8, hflag]
    rfl
  simp only [resultWords, words, quotientLow,
    v108d90, v108d8d, v108d87, v108da5, v108da2, v108d9c,
    v108dba, v108db7, v108db1, v108dcf, v108dcc, v108dc6,
    show v108d9f p = v108d8a p from rfl,
    show v108db4 p = v108d8a p from rfl,
    show v108dc9 p = v108d8a p from rfl, hmask]
  change #v[(BitVec.allOnes 64 &&& _) ^^^ _, (BitVec.allOnes 64 &&& _) ^^^ _,
    (BitVec.allOnes 64 &&& _) ^^^ _, (BitVec.allOnes 64 &&& _) ^^^ _] = _
  simp only [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end K256.Proofs.Common.Invert.ModularShift.Arithmetic
