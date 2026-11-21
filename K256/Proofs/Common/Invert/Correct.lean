import K256.Proofs.Common.Invert.ModularShift.Limbs
import K256.Proofs.Generate.Generator.Affine.Invert.Contract

namespace K256.Proofs.Common.Invert.Correct

open K256.Proofs.Generate.Generator.Affine.Invert
open ModularShift

def magnitudeOr (v : Vector (BitVec 64) 4) : BitVec 64 :=
  v[1] ||| v[0] ||| v[2] ||| v[3]

def signBit (flag sign : BitVec 8) : BitVec 8 := (flag ^^^ sign) &&& 1

def signMask (v : Vector (BitVec 64) 4) (flag sign : BitVec 8) : BitVec 64 :=
  if magnitudeOr v = 0 then 0 else -(signBit flag sign).setWidth 64

def correctedWords (q v : Vector (BitVec 64) 4) (flag sign : BitVec 8) :
    Vector (BitVec 64) 4 :=
  let diff := words (subRaw (limbs q) (limbs v)).1
  Vector.ofFn fun i => ((signMask v flag sign &&& (diff[i] ^^^ v[i])) ^^^ v[i])

theorem limbs_value (v : Vector (BitVec 64) 4) : (limbs v).toNat = value v := by
  simp only [LinearCombination.Limbs.toNat, value, Nat.mul_add]
  omega

private theorem difference_value (q v : Vector (BitVec 64) 4) (h : value v < value q) :
    value (words (subRaw (limbs q) (limbs v)).1) = value q - value v := by
  rw [← limbs_value, ← limbs_value q, ← limbs_value v]
  have hraw := subRaw_toNat (limbs q) (limbs v)
  have hlt := limbs_toNat_lt (subRaw (limbs q) (limbs v)).1
  have he (l : Limbs) : (limbs (words l)).toNat = l.toNat := by cases l; rfl
  rw [he]
  rw [← limbs_value q, ← limbs_value v] at h
  omega

private theorem magnitudeOr_eq_zero (v : Vector (BitVec 64) 4) :
    magnitudeOr v = 0 ↔ value v = 0 := by
  change (v[1] ||| v[0] ||| v[2] ||| v[3]) = 0#64 ↔ value v = 0
  simp only [BitVec.or_eq_zero_iff, value]
  constructor
  · rintro ⟨⟨⟨h1, h0⟩, h2⟩, h3⟩
    rw [h0, h1, h2, h3]
    decide
  · intro h
    exact ⟨⟨⟨BitVec.eq_of_toNat_eq (by change _ = 0; omega),
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩,
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩,
      BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩

private theorem selectedWord (a b : BitVec 64) (mask : BitVec 64) (h : mask = 0 ∨ mask = -1) :
    ((mask &&& (b ^^^ a)) ^^^ a) = if mask = 0 then a else b := by
  rcases h with rfl|rfl
  · simp
  · rw [ite_eq_right (by decide), show (-1 : BitVec 64) = BitVec.allOnes 64 by decide,
      BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem correctedWords_eq (q v : Vector (BitVec 64) 4) (flag sign : BitVec 8)
    (h : signBit flag sign = 0 ∨ signBit flag sign = 1) :
    correctedWords q v flag sign =
      if value v = 0 ∨ signBit flag sign = 0 then v else words (subRaw (limbs q) (limbs v)).1 := by
  by_cases hz : value v = 0
  · simp only [correctedWords, signMask, magnitudeOr_eq_zero, hz, true_or, ite_true]
    apply Vector.ext
    intro i hi
    simp
  rcases h with hs|hs
  · simp only [correctedWords, signMask, magnitudeOr_eq_zero, hz, hs, ite_false, or_true, ite_true]
    apply Vector.ext
    intro i hi
    simp
  · simp only [correctedWords, signMask, magnitudeOr_eq_zero, hz, hs, ite_false, false_or]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, show ¬ (1 : BitVec 8) = 0 by decide, ite_false]
    exact (selectedWord _ _ (-1) (Or.inr rfl)).trans (ite_eq_right (by decide))

theorem correctedWords_value (q v : Vector (BitVec 64) 4) (flag : BitVec 8) (inputNeg neg : Bool)
    (flagBit : flag &&& 1 = (if neg then 1 else 0))
    (h : value v < value q) :
    let x : Int := if inputNeg then -(value v : Int) else value v
    value (correctedWords q v flag (if inputNeg then 1 else 0)) =
      ((if neg then -x else x) % (value q : Int)).toNat := by
  have signEq : signBit flag (if inputNeg then 1 else 0) =
      (if neg != inputNeg then 1 else 0) := by
    unfold signBit
    have masked (a b : BitVec 8) :
        (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases (1 : BitVec 8).getLsbD i <;> rfl
    rw [masked, flagBit]
    cases inputNeg <;> cases neg <;> rfl
  have bits : signBit flag (if inputNeg then 1 else 0) = 0 ∨
      signBit flag (if inputNeg then 1 else 0) = 1 := by rw [signEq]; split <;> simp
  rw [correctedWords_eq _ _ _ _ bits, signEq]
  dsimp only
  have hpos : (value v : Int) % (value q : Int) = value v := Int.emod_eq_of_lt (by omega) (by omega)
  have hneg (hn : value v ≠ 0) :
      (-(value v : Int)) % (value q : Int) = (value q : Int) - value v :=
    (Int.sub_emod_left _ _).symm.trans
      (Int.emod_eq_of_lt (a := (value q : Int) - value v) (by omega) (by omega))
  by_cases hz : value v = 0
  · cases inputNeg <;> cases neg <;> simp [hz]
  have diff := difference_value q v h
  cases inputNeg <;> cases neg <;>
    simp [hz, hpos, hneg hz, diff] <;> omega

end K256.Proofs.Common.Invert.Correct
