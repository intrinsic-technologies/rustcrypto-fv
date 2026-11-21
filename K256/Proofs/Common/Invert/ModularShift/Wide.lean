import K256.Proofs.Common.Invert.ModularShift.Limbs

namespace K256.Proofs.Common.Invert.ModularShift

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

theorem correctionWord_divisible (magnitude shift : Nat) (hs : shift ≤ 62) :
    (2 : Int)^shift ∣ (magnitude : Int) - prime.toNat *
      ((correctionWord magnitude shift).toNat : Int) := by
  rw [correctionWord_value magnitude shift (by omega)]
  exact K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.corrected_divisible (inverse_mod_two_pow (by omega))

def wideValue (low : Limbs) (high : BitVec 64) : Nat :=
  low.toNat + 2^256 * high.toNat

theorem wideValue_lt (low : Limbs) (high : BitVec 64) :
    wideValue low high < 2^320 := by
  have hl := limbs_toNat_lt low
  have hh := high.isLt
  dsimp only [wideValue]
  omega
def productWide (a : Limbs) (k : BitVec 64) : Limbs × BitVec 64 :=
  let p0 := mulResult a.l0 k
  let p1 := mulResult a.l1 k
  let p2 := mulResult a.l2 k
  let p3 := mulResult a.l3 k
  let r1 := addSpec p1.1 p0.2
  let r2 := adcSpec r1.2.CF p2.1 p1.2
  let r3 := adcSpec r2.2.CF p3.1 p2.2
  (⟨p0.1,r1.1,r2.1,r3.1⟩, (adcSpec r3.2.CF p3.2 0).1)

set_option exponentiation.threshold 320 in
theorem productWide_value (a : Limbs) (k : BitVec 64) :
    wideValue (productWide a k).1 (productWide a k).2 = a.toNat*k.toNat := by
  have h := LinearCombination.product_limbs k a.l0 a.l1 a.l2 a.l3
  have comm (b : BitVec 64) : mulResult k b = mulResult b k := by
    simp only [mulResult, Nat.mul_comm k.toNat]
  simp only [LinearCombination.packFive, LinearCombination.packFour, Vector.getElem_mk,
    Array.reduceGetElem, comm] at h
  have pack : a.l0.toNat + 2^64*a.l1.toNat + 2^128*a.l2.toNat + 2^192*a.l3.toNat = a.toNat := by
    simp only [Limbs.toNat]
    omega
  rw [pack] at h
  rw [Nat.mul_comm a.toNat k.toNat]
  simp only [wideValue, productWide, Limbs.toNat] at ⊢
  unfold Limbs.toNat at h
  omega

def subWide (a b : Limbs) (ah bh : BitVec 64) :
    Limbs × BitVec 64 × BitVec 64 :=
  let low := subRaw a b
  let high := subWord ah bh low.2
  (low.1, high, borrow ah bh high)

theorem subWide_value (a b : Limbs) (ah bh : BitVec 64) :
    (subWide a b ah bh).2.2.toNat ≤ 1 ∧
    wideValue (subWide a b ah bh).1 (subWide a b ah bh).2.1 + wideValue b bh =
      wideValue a ah + 2^320 * (subWide a b ah bh).2.2.toNat := by
  have hl := subRaw_toNat a b
  have hh := subWord_borrow ah bh (subRaw a b).2 (eq_zero_or_one hl.1)
  refine ⟨hh.1, ?_⟩
  dsimp only [subWide,wideValue]
  omega

end K256.Proofs.Common.Invert.ModularShift
