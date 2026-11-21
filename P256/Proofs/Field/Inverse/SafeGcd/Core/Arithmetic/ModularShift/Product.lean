import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Support
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.StageState
import P256.Proofs.Field.Schoolbook.WordSpecs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open ModularShift
open P256.Proofs.Field.Inverse.SafeGcd

abbrev limbs (a : Vector (BitVec 64) 4) : Limbs := ⟨a[0], a[1], a[2], a[3]⟩
abbrev words (a : Limbs) : Vector (BitVec 64) 4 := #v[a.l0, a.l1, a.l2, a.l3]

def wideLow (p : Inputs) : Limbs :=
  let a := LinearCombination.resultWords p.linear
  ⟨a[0], a[1], a[2], a[3]⟩

def wideHigh (p : Inputs) : BitVec 64 := (LinearCombination.resultWords p.linear)[4]

def productLow (p : Inputs) : Limbs :=
  ⟨(v1b15dc p).1, (v1b1614 p).1, (v1b161c p).1, (v1b161f p).1⟩

def productHigh (p : Inputs) : BitVec 64 := (v1b1622 p).1

def differenceLow (p : Inputs) : Limbs :=
  ⟨v1b1629 p, (v1b166e p).1, (v1b169e p).1, (v1b16ce p).1⟩

def differenceHigh (p : Inputs) : BitVec 64 := (v1b170c p).1

private theorem adc_low (a b : BitVec 64) (c : Bool) :
    (Common.Instructions.Carry.adcSpec a b (BitVec.ofBool c)).1 =
      (X86Proofs.adcSpec c a b).1 := by
  simp only [Common.Instructions.Carry.adcSpec, BitVec.toNat_ofBool,
    ofInt_add_add_toNat, X86Proofs.adcSpec]

private theorem adc_cf (a b : BitVec 64) (c : Bool) :
    (Common.Instructions.Carry.adcSpec a b (BitVec.ofBool c)).2.CF =
      (X86Proofs.adcSpec c a b).2.CF := by
  simp only [Common.Instructions.Carry.adcSpec, BitVec.toNat_ofBool,
    ofInt_add_add_toNat, X86Proofs.adcSpec, ne_eq, natCast_eq_add_add]

theorem product_eq (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.productWide (limbs p.modulus) (v1b15c3 p) =
      (productLow p, productHigh p) := by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.productWide, productLow, productHigh,
    v1b15dc, v1b15ed, v1b15ff, v1b1611, v1b1614, v1b161c, v1b161f, v1b1622,
    adc_low, adc_cf, mulResult_fst, Support.mulResult_snd]

theorem difference_eq (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.subWide (wideLow p) (productLow p) (wideHigh p)
      (productHigh p) =
      (differenceLow p, differenceHigh p, v1b1715 p) := by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.subWide, wideLow, productLow, wideHigh,
    productHigh,
    differenceLow, differenceHigh,
    v1b1629, v1b162c, v1b1632, v1b1635, v1b163d, v1b1640, v1b164e,
    v1b165f, v1b1667, v1b166a, v1b166e, v1b1671, v1b1677, v1b167a,
    v1b167d, v1b1680, v1b1683, v1b168f, v1b1697, v1b169a, v1b169e,
    v1b16a1, v1b16a7, v1b16aa, v1b16ad, v1b16b0, v1b16b3, v1b16bf,
    v1b16c7, v1b16ca, v1b16ce, v1b16d1, v1b16d7, v1b16da, v1b16e0,
    v1b16e3, v1b16e6, v1b16f1, v1b16f9, v1b16fc, v1b1702, v1b1705,
    v1b1708, v1b170c, v1b170f, v1b1712, v1b1715,
    P256.Proofs.Field.Subtract.subRaw,
    P256.Proofs.Field.Subtract.subWord,
    P256.Proofs.Field.Subtract.borrow,
    addSpec, BitVec.reduceSetWidth, BitVec.zero_sub]

theorem product_value (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (productLow p) (productHigh p) =
      (limbs p.modulus).toNat * (v1b15c3 p).toNat := by
  have h := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.productWide_value (limbs p.modulus)
    (v1b15c3 p)
  rwa [product_eq] at h

set_option exponentiation.threshold 320 in
theorem difference_value (p : Inputs) :
    (v1b1715 p).toNat ≤ 1 ∧
      P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (differenceLow p) (differenceHigh p) +
        (limbs p.modulus).toNat * (v1b15c3 p).toNat =
      P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) + 2^320 *
        (v1b1715 p).toNat := by
  have h := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.subWide_value (wideLow p) (productLow p)
    (wideHigh p) (productHigh p)
  rwa [difference_eq, product_value] at h

theorem wide_low_word (p : Inputs) :
    BitVec.ofNat 64 (P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh
      p)) =
      (LinearCombination.resultWords p.linear)[0] := by
  apply BitVec.eq_of_toNat_eq
  have h0 := ((LinearCombination.resultWords p.linear)[0]).isLt
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue, wideLow, wideHigh, Limbs.toNat,
    BitVec.toNat_ofNat]
  omega

theorem correction_eq [parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hinv : p.inverse = parameters.inverse) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctionWord
      (P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p))
        p.shift.toNat = v1b15c3 p := by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctionWord, wide_low_word, ← hinv,
    v1b15c3, v1b15c0, v1b15bc]

theorem correctedWords_eq [parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hmod : parameters.modulus = limbs p.modulus)
    (hinv : p.inverse = parameters.inverse) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctedWords (wideLow p) (wideHigh p)
      p.shift.toNat =
      (differenceLow p, differenceHigh p, v1b1715 p) := by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctedWords,
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctionProduct, correction_eq p hinv, hmod,
    product_eq, difference_eq]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic
