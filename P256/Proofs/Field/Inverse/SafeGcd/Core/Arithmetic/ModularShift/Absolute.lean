import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Product
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.AbsoluteShift.Arithmetic

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open ModularShift
open P256.Proofs.Field.Inverse.SafeGcd

def magnitudeLow (p : Inputs) : Limbs :=
  ⟨v1b1824 p, v1b17d2 p, v1b17c6 p, v1b17ba p⟩

def magnitudeHigh (p : Inputs) : BitVec 64 := v1b17f0 p

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
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg1 (differenceLow p) = v1b1734 p :=
      by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg1, differenceLow,
    v1b1734, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]
  rw [zero_sub_cf]

private theorem neg2_eq (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg2 (differenceLow p) = v1b173c p :=
      by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg2]
  rw [neg1_eq]
  simp only [differenceLow,
    v1b173c, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]

private theorem neg3_eq (p : Inputs) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg3 (differenceLow p) = v1b173f p :=
      by
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.neg3]
  rw [neg2_eq]
  simp only [differenceLow,
    v1b173f, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat]

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
    magnitudeLow p = if v1b1715 p = 0 then differenceLow p
      else P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.negLow (differenceLow p) := by
  simp only [magnitudeLow, v1b1824, v1b1821, v1b1805, v1b1802,
    v1b17d2, v1b17cf, v1b17cc, v1b17c9,
    v1b17c6, v1b17c3, v1b17c0, v1b17bd,
    v1b17ba, v1b17b7, v1b17b4, v1b17b1, select_bool,
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.negLow, neg1_eq, neg2_eq, neg3_eq]
  by_cases hz : v1b1715 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceLow, v1b172b]

theorem magnitudeHigh_eq (p : Inputs) :
    magnitudeHigh p = if v1b1715 p = 0 then differenceHigh p
      else P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.negHigh (differenceLow p)
        (differenceHigh p) := by
  simp only [magnitudeHigh, v1b17f0, v1b17ed, v1b17ea, v1b17e1, select_bool,
    v1b17de, v1b17db, v1b17d5, addSpec, carry_cast,
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.negHigh, neg3_eq]
  by_cases hz : v1b1715 p = 0 <;>
    simp only [hz, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_false, ite_true, differenceHigh]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic
