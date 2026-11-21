import K256.Proofs.Common.Invert.ModularShift.Product
import K256.Proofs.Common.Invert.ModularShift.Magnitude

namespace K256.Proofs.Common.Invert.ModularShift.Arithmetic

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

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
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg1 (differenceLow p) = v108b44 p :=
      by
  simp only [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg1, differenceLow,
    v108b44, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]
  rw [zero_sub_cf]

private theorem neg2_eq (p : Inputs) :
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg2 (differenceLow p) = v108b4c p :=
      by
  simp only [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg2]
  rw [neg1_eq]
  simp only [differenceLow,
    v108b4c, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]

private theorem neg3_eq (p : Inputs) :
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg3 (differenceLow p) = v108b4f p :=
      by
  simp only [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.neg3]
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
      else K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.negLow (differenceLow p) := by
  simp only [magnitudeLow, v108c34, v108c31, v108c15, v108c12,
    v108be2, v108bdf, v108bdc, v108bd9,
    v108bd6, v108bd3, v108bd0, v108bcd,
    v108bca, v108bc7, v108bc4, v108bc1, select_bool,
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.negLow, neg1_eq, neg2_eq, neg3_eq]
  by_cases hz : v108b25 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceLow, v108b3b]

theorem magnitudeHigh_eq (p : Inputs) :
    magnitudeHigh p = if v108b25 p = 0 then differenceHigh p
      else K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.negHigh (differenceLow p)
        (differenceHigh p) := by
  simp only [magnitudeHigh, v108c00, v108bfd, v108bfa, v108bf1, select_bool,
    v108bee, v108beb, v108be5, addSpec, carry_cast,
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.negHigh, neg3_eq]
  by_cases hz : v108b25 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceHigh]

end K256.Proofs.Common.Invert.ModularShift.Arithmetic
