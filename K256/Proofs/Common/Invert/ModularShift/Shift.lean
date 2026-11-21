import K256.Proofs.Common.Invert.ModularShift.Limbs

namespace K256.Proofs.Common.Invert.ModularShift

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

theorem extract_shiftRight_limb {n offset shift : Nat} (x : BitVec n) (hs : shift ≤ 64) :
    (x.extractLsb' offset 64 >>> shift) |||
      (x.extractLsb' (offset+64) 64 <<< (64-shift)) =
      (x >>> shift).extractLsb' offset 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_extractLsb']
  by_cases h : shift + i < 64
  · have hn : i < 64-shift := by omega
    simp only [h,hi,hn,decide_true,Bool.not_true,Bool.false_and,Bool.and_false,
      Bool.true_and,Bool.or_false]
    congr 1
    omega
  · have hn : ¬ i < 64-shift := by omega
    have hr : i-(64-shift)<64 := by omega
    simp only [h,hi,hn,hr,decide_true,decide_false,Bool.not_false,Bool.true_and,
      Bool.false_and,Bool.false_or]
    congr 1
    omega

set_option exponentiation.threshold 320 in
theorem shift_limb {magnitude shift j : Nat} (hm : magnitude < 2^320) (hs : shift ≤ 64) :
    (BitVec.ofNat 64 (magnitude / 2^(64*j)) >>> shift) |||
      (BitVec.ofNat 64 (magnitude / 2^(64*(j+1))) <<< (64-shift)) =
      BitVec.ofNat 64 ((magnitude / 2^shift) / 2^(64*j)) := by
  have h := extract_shiftRight_limb (offset := 64*j) (BitVec.ofNat 320 magnitude) hs
  have digits (k : Nat) : (BitVec.ofNat 320 magnitude).extractLsb' k 64 =
      BitVec.ofNat 64 (magnitude / 2^k) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hm]
  rw [digits,digits] at h
  have offset : 64*j+64 = 64*(j+1) := by omega
  rw [offset] at h
  exact h.trans (by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hm])

theorem signed_magnitude_div {magnitude shift : Nat} (negative : Bool)
    (divisible : (2 : Int)^shift ∣ if negative then -(magnitude : Int) else (magnitude : Int)) :
    (if negative then -(magnitude : Int) else (magnitude : Int)) / (2 : Int)^shift =
      if negative then -((magnitude / 2^shift : Nat) : Int) else ((magnitude / 2^shift : Nat) : Int) := by
  have cast : ((2^shift : Nat) : Int)=(2 : Int)^shift := by simp
  cases negative
  · simpa only [Bool.false_eq_true,ite_false,←cast] using (Int.natCast_ediv magnitude (2^shift)).symm
  · simp only [ite_true] at divisible ⊢
    rw [Int.neg_ediv_of_dvd (Int.dvd_neg.mp divisible),←cast,←Int.natCast_ediv]

end K256.Proofs.Common.Invert.ModularShift
