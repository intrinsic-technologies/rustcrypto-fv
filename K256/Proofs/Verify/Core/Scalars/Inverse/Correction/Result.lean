import K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Model
import K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Division

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Arithmetic

open Common.Invert.LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open Common.Invert.ModularShift (limbs words productWide productWide_value subWide subWide_value wideValue wideValue_lt limbs_toNat_lt)
open X86Proofs

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
    productWide (limbs p.params.modulusWords) (v1089d3 p) =
      (productLow p, productHigh p) := by
  rfl

theorem difference_eq (p : Inputs) :
    subWide (wideLow p) (productLow p) (wideHigh p)
      (productHigh p) =
      (differenceLow p, differenceHigh p, v108b25 p) := by
  simp only [subWide, wideLow, productLow, wideHigh,
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

theorem wide_low_word (p : Inputs) :
    BitVec.ofNat 64 (wideValue (wideLow p) (wideHigh
      p)) =
      (p.magnitude)[0] := by
  apply BitVec.eq_of_toNat_eq
  have h0 := (p.magnitude[0]).isLt
  simp only [wideValue, wideLow, wideHigh, Limbs.toNat,
    BitVec.toNat_ofNat]
  omega

theorem correction_eq (p : Inputs) :
    p.params.correctionWord
      (wideValue (wideLow p) (wideHigh p))
        p.shift.toNat = v1089d3 p := by
  simp only [Parameters.correctionWord, wide_low_word,
    v1089d3, v1089d0, v1089cc]

theorem correctedWords_eq (p : Inputs) :
    correctedWords p.params (wideLow p) (wideHigh p)
      p.shift.toNat =
      (differenceLow p, differenceHigh p, v108b25 p) := by
  simp only [correctedWords,
    correctionProduct, correction_eq p,
    product_eq, difference_eq]

def magnitudeLow (p : Inputs) : Limbs :=
  ⟨v108c34 p, v108be2 p, v108bd6 p, v108bca p⟩

def magnitudeHigh (p : Inputs) : BitVec 64 := v108c00 p

private theorem zero_sub_cf (x : BitVec 64) :
    (subSpec (0#64) x).2.CF = decide (x ≠ 0#64) := by
  simp [subSpec, Nat.pos_iff_ne_zero]
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq h
  · intro h
    rw [h]
    rfl

private theorem neg1_eq (p : Inputs) :
    Common.Invert.ModularShift.AbsoluteShift.neg1 (differenceLow p) = v108b44 p :=
      by
  simp only [Common.Invert.ModularShift.AbsoluteShift.neg1, differenceLow,
    v108b44, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]
  rw [zero_sub_cf]

private theorem neg2_eq (p : Inputs) :
    Common.Invert.ModularShift.AbsoluteShift.neg2 (differenceLow p) = v108b4c p :=
      by
  simp only [Common.Invert.ModularShift.AbsoluteShift.neg2]
  rw [neg1_eq]
  simp only [differenceLow,
    v108b4c, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]

private theorem neg3_eq (p : Inputs) :
    Common.Invert.ModularShift.AbsoluteShift.neg3 (differenceLow p) = v108b4f p :=
      by
  simp only [Common.Invert.ModularShift.AbsoluteShift.neg3]
  rw [neg2_eq]
  simp only [differenceLow,
    v108b4f, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]

private theorem select_bool (c : Bool) (a b : BitVec 64) :
    (-(((if c then 1 else 0 : BitVec 8).setWidth 32).setWidth 64) &&& (a ^^^ b)) ^^^ b =
      if c then a else b := by
  cases c
  · simp
  · change (BitVec.allOnes 64 &&& (a ^^^ b)) ^^^ b = a
    rw [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem carry_cast (c : Bool) :
    (((((if !c then 1 else 0 : BitVec 8).setWidth 32).setWidth 64).setWidth 32 &&& 1).setWidth 64) =
      (if c = false then 1 else 0 : BitVec 64) := by
  cases c <;> rfl

theorem magnitudeLow_eq (p : Inputs) :
    magnitudeLow p = if v108b25 p = 0 then differenceLow p
      else Common.Invert.ModularShift.AbsoluteShift.negLow (differenceLow p) := by
  simp only [magnitudeLow, v108c34, v108c31, v108c15, v108c12,
    v108be2, v108bdf, v108bdc, v108bd9,
    v108bd6, v108bd3, v108bd0, v108bcd,
    v108bca, v108bc7, v108bc4, v108bc1, select_bool,
    Common.Invert.ModularShift.AbsoluteShift.negLow, neg1_eq, neg2_eq, neg3_eq]
  by_cases hz : v108b25 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceLow, v108b3b]

theorem magnitudeHigh_eq (p : Inputs) :
    magnitudeHigh p = if v108b25 p = 0 then differenceHigh p
      else Common.Invert.ModularShift.AbsoluteShift.negHigh (differenceLow p)
        (differenceHigh p) := by
  simp only [magnitudeHigh, v108c00, v108bfd, v108bfa, v108bf1, select_bool,
    v108bee, v108beb, v108be5, addSpec, carry_cast,
    Common.Invert.ModularShift.AbsoluteShift.negHigh, neg3_eq]
  by_cases hz : v108b25 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceHigh]

theorem magnitudeLow_retained (p : Inputs) :
    Correction.magnitudeLow p.params (wideLow p) (wideHigh p)
      p.shift.toNat = magnitudeLow p := by
  rw [Correction.magnitudeLow, correctedWords_eq p, magnitudeLow_eq]

theorem magnitudeHigh_retained (p : Inputs) :
    Correction.magnitudeHigh p.params (wideLow p) (wideHigh
      p) p.shift.toNat = magnitudeHigh p := by
  rw [Correction.magnitudeHigh, correctedWords_eq p, magnitudeHigh_eq]

def quotientLow (p : Inputs) : Limbs :=
  ⟨v108c54 p, v108c51 p, v108c37 p, v108cfb p⟩

def quotientHigh (p : Inputs) : BitVec 64 := v108d33 p

private theorem limbs_ext {a b : Limbs} (h0 : a.l0 = b.l0) (h1 : a.l1 = b.l1)
    (h2 : a.l2 = b.l2) (h3 : a.l3 = b.l3) : a = b := by
  cases a
  cases b
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

theorem quotient_limbs (p : Inputs) (hi : p.shift.toNat ≤ 64)
    (hbound : wideValue (magnitudeLow p) (magnitudeHigh
      p) / 2^p.shift.toNat < 2^256) :
    (quotientLow p).toNat =
      wideValue (magnitudeLow p) (magnitudeHigh p) /
        2^p.shift.toNat ∧
    quotientHigh p = 0 := by
  obtain ⟨out, hvalue, h0, h1, h2, h3, h4⟩ :=
    Common.Invert.ModularShift.AbsoluteShift.shifted_magnitude (magnitudeLow p)
      (magnitudeHigh p) p.shift.toNat hi hbound
  have he : quotientLow p = out := by
    apply limbs_ext
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  exact ⟨he ▸ hvalue, h4⟩

theorem quotient_value (p : Inputs) (hi : p.shift.toNat ≤ 62)
    (hbound : wideValue (wideLow p) (wideHigh p) <
      2^p.shift.toNat * (limbs p.params.modulusWords).toNat) :
    (quotientLow p).toNat < (limbs p.params.modulusWords).toNat ∧
    quotientHigh p = 0 ∧
    (if decide (v108b25 p ≠ 0) then -((quotientLow p).toNat : Int)
      else ((quotientLow p).toNat : Int)) =
      correctedValue p.params (wideLow p) (wideHigh p)
        p.shift.toNat / (2 : Int)^p.shift.toNat := by
  have h := quotient_bound_signed p.params
    (wideLow p) (wideHigh p) p.shift.toNat hi hbound
  dsimp only at h
  rw [magnitudeLow_retained p, magnitudeHigh_retained p] at h
  have hq := quotient_limbs p (by omega) (Nat.lt_trans h.1
    (limbs_toNat_lt _))
  rw [← hq.1] at h
  refine ⟨h.1, hq.2, ?_⟩
  simpa only [Correction.correctionNegative,
    correctedWords_eq p] using h.2

def finalDifference (p : Inputs) : Limbs :=
  ⟨v108c5f p, (v108c9c p).1, (v108cd3 p).1, (v108d0d p).1⟩

theorem final_difference_eq (p : Inputs) :
    subRaw (quotientLow p) (limbs p.params.modulusWords) =
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

theorem final_borrow_one (p : Inputs) (hbound : (quotientLow p).toNat < (limbs p.params.modulusWords).toNat) :
    v108d25 p = 1 := by
  have h := subRaw_toNat
    (quotientLow p) (limbs p.params.modulusWords)
  rw [final_difference_eq] at h
  dsimp only at h
  have hn : (v108d25 p).toNat = 1 := by omega
  exact BitVec.eq_of_toNat_eq hn

theorem resultWords_eq (p : Inputs) (hbound : (quotientLow p).toNat < (limbs p.params.modulusWords).toNat)
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

def resultNegative (p : Inputs) (negative : Bool) := negative != decide (v108b25 p ≠ 0)

theorem result_correct (p : Inputs) (negative : Bool) (x : Int)
    (sign : p.sign = if negative then 1 else 0)
    (input : x = if negative then -(wideValue (wideLow p) (wideHigh p) : Int)
      else (wideValue (wideLow p) (wideHigh p) : Int))
    (hi : p.shift.toNat ≤ 62) (bound : x.natAbs < 2^p.shift.toNat * (limbs p.params.modulusWords).toNat) :
    let y := if resultNegative p negative then -((limbs (resultWords p)).toNat : Int)
      else ((limbs (resultWords p)).toNat : Int)
    resultSign p = (if resultNegative p negative then 1 else 0) ∧ y.natAbs < (limbs p.params.modulusWords).toNat ∧
      ((2 : Int)^p.shift.toNat * y) % (limbs p.params.modulusWords).toNat = x % (limbs p.params.modulusWords).toNat := by
  have mag : x.natAbs = wideValue (wideLow p) (wideHigh p) := by
    rw [input]
    cases negative <;> simp
  have q := quotient_value p hi (mag ▸ bound)
  have h := signed_quotient_result p.params hi input q.2.2 bound
  refine ⟨?_, ?_⟩
  · simp only [resultSign, v108d40, setWidth_mergeGPR8, sign, resultNegative]
    cases negative <;> by_cases h : v108b25 p = 0#64 <;> simp [h]
  · rw [resultWords_eq p q.1 q.2.1]
    exact h

end K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Arithmetic
