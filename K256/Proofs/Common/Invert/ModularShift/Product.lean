import K256.Proofs.Common.Invert.ModularShift.Model
import K256.Proofs.Common.Invert.ModularShift.Correction

namespace K256.Proofs.Common.Invert.ModularShift.Arithmetic

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

def wideLow (p : Inputs) : Limbs :=
  let a := p.magnitude
  ⟨a[0], a[1], a[2], a[3]⟩

def wideHigh (p : Inputs) : BitVec 64 := (p.magnitude)[4]

def productLow (p : Inputs) : Limbs :=
  ⟨(v1089ec p).1, (v108a24 p).1, (v108a2c p).1, (v108a2f p).1⟩

def productHigh (p : Inputs) : BitVec 64 := (v108a32 p).1

def differenceLow (p : Inputs) : Limbs :=
  ⟨v108a39 p, (v108a7e p).1, (v108aae p).1, (v108ade p).1⟩

def differenceHigh (p : Inputs) : BitVec 64 := (v108b1c p).1

theorem product_eq (p : Inputs) :
    K256.Proofs.Common.Invert.ModularShift.productWide (limbs modulusWords) (v1089d3 p) =
      (productLow p, productHigh p) := by
  rfl

theorem difference_eq (p : Inputs) :
    K256.Proofs.Common.Invert.ModularShift.subWide (wideLow p) (productLow p) (wideHigh p)
      (productHigh p) =
      (differenceLow p, differenceHigh p, v108b25 p) := by
  simp only [K256.Proofs.Common.Invert.ModularShift.subWide, wideLow, productLow, wideHigh,
    productHigh,
    differenceLow, differenceHigh,
    v108a39, v108a3c, v108a42, v108a45, v108a4d, v108a50, v108a5e,
    v108a6f, v108a77, v108a7a, v108a7e, v108a81, v108a87, v108a8a,
    v108a8d, v108a90, v108a93, v108a9f, v108aa7, v108aaa, v108aae,
    v108ab1, v108ab7, v108aba, v108abd, v108ac0, v108ac3, v108acf,
    v108ad7, v108ada, v108ade, v108ae1, v108ae7, v108aea, v108af0,
    v108af3, v108af6, v108b01, v108b09, v108b0c, v108b12, v108b15,
    v108b18, v108b1c, v108b1f, v108b22, v108b25,
    subRaw,
    subWord,
    borrow,
    addSpec, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem product_value (p : Inputs) :
    K256.Proofs.Common.Invert.ModularShift.wideValue (productLow p) (productHigh p) =
      (limbs modulusWords).toNat * (v1089d3 p).toNat := by
  have h := K256.Proofs.Common.Invert.ModularShift.productWide_value (limbs modulusWords)
    (v1089d3 p)
  rwa [product_eq] at h

set_option exponentiation.threshold 320 in
theorem difference_value (p : Inputs) :
    (v108b25 p).toNat ≤ 1 ∧
      K256.Proofs.Common.Invert.ModularShift.wideValue (differenceLow p) (differenceHigh p) +
        (limbs modulusWords).toNat * (v1089d3 p).toNat =
      K256.Proofs.Common.Invert.ModularShift.wideValue (wideLow p) (wideHigh p) + 2^320 *
        (v108b25 p).toNat := by
  have h := K256.Proofs.Common.Invert.ModularShift.subWide_value (wideLow p) (productLow p)
    (wideHigh p) (productHigh p)
  rwa [difference_eq, product_value] at h

theorem wide_low_word (p : Inputs) :
    BitVec.ofNat 64 (K256.Proofs.Common.Invert.ModularShift.wideValue (wideLow p) (wideHigh
      p)) =
      (p.magnitude)[0] := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (p.magnitude[0]).isLt
  simp only [K256.Proofs.Common.Invert.ModularShift.wideValue, wideLow, wideHigh, Limbs.toNat,
    BitVec.toNat_ofNat]
  omega

theorem correction_eq (p : Inputs) :
    K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.correctionWord
      (K256.Proofs.Common.Invert.ModularShift.wideValue (wideLow p) (wideHigh p))
        p.shift.toNat = v1089d3 p := by
  simp only [K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.correctionWord, wide_low_word,
    v1089d3, v1089d0, v1089cc]

theorem correctedWords_eq (p : Inputs)
 :
    K256.Proofs.Common.Invert.ModularShift.correctedWords (wideLow p) (wideHigh p)
      p.shift.toNat =
      (differenceLow p, differenceHigh p, v108b25 p) := by
  simp only [prime, K256.Proofs.Common.Invert.ModularShift.correctedWords,
    K256.Proofs.Common.Invert.ModularShift.correctionProduct, correction_eq p,
    product_eq, difference_eq]

end K256.Proofs.Common.Invert.ModularShift.Arithmetic
