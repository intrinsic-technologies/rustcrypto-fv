import Sha2.Proofs.Common.SHA512.Mathematics.Model
import Init.Data.BitVec.Bitblast

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Proofs.NIST

theorem choice_eq_xor_and (x y z : UInt64) :
    choice x y z = z ^^^ (x &&& (y ^^^ z)) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) =
    z.toBitVec ^^^ (x.toBitVec &&& (y.toBitVec ^^^ z.toBitVec))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem choice_eq_and_xor (x y z : UInt64) :
    choice x y z = ((y ^^^ z) &&& x) ^^^ z := by
  rw [choice_eq_xor_and, UInt64.and_comm (y ^^^ z) x, UInt64.xor_comm]

theorem majority_eq_xor_and (x y z : UInt64) :
    majority x y z = (x &&& y) ^^^ (z &&& (x ^^^ y)) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    (x.toBitVec &&& y.toBitVec) ^^^ (z.toBitVec &&& (x.toBitVec ^^^ y.toBitVec))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem majority_eq_and_xor (x y z : UInt64) :
    majority x y z = ((y ^^^ z) &&& x) ^^^ (y &&& z) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    ((y.toBitVec ^^^ z.toBitVec) &&& x.toBitVec) ^^^ (y.toBitVec &&& z.toBitVec)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem majority_eq_or_and (x y z : UInt64) :
    majority x y z = (x &&& y) ||| ((x ||| y) &&& z) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    (x.toBitVec &&& y.toBitVec) ||| ((x.toBitVec ||| y.toBitVec) &&& z.toBitVec)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem choice_eq_add_and (x y z : UInt64) :
    choice x y z = (x &&& y) + (~~~x &&& z) := by
  apply UInt64.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) =
    (x.toBitVec &&& y.toBitVec) + (~~~x.toBitVec &&& z.toBitVec)
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_or, hi, decide_true, Bool.true_and]
    cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
      cases z.toBitVec.getLsbD i <;> rfl
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero,
      hi, decide_true, Bool.true_and]
    cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
      cases z.toBitVec.getLsbD i <;> rfl

theorem choice_toBitVec (x y z : UInt64) :
    (choice x y z).toBitVec =
      (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) := rfl

theorem majority_toBitVec (x y z : UInt64) :
    (majority x y z).toBitVec = (x.toBitVec &&& y.toBitVec) ^^^
      (x.toBitVec &&& z.toBitVec) ^^^ (y.toBitVec &&& z.toBitVec) := rfl

theorem shiftRight_ofNat_toBitVec (x : UInt64) (n : Nat) :
    (x >>> UInt64.ofNat n).toBitVec = x.toBitVec >>> (n % 64) := by
  simp only [UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat', BitVec.ushiftRight_eq',
    BitVec.toNat_umod, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mod_mod_of_dvd n (by decide)

theorem shiftLeft_ofNat_toBitVec (x : UInt64) (n : Nat) :
    (x <<< UInt64.ofNat n).toBitVec = x.toBitVec <<< (n % 64) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat', BitVec.shiftLeft_eq',
    BitVec.toNat_umod, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mod_mod_of_dvd n (by decide)

theorem rotateRight_toBitVec (x : UInt64) (n : Nat) :
    (SHA512.rotateRight x n).toBitVec = x.toBitVec.rotateRight n := by
  simp only [SHA512.rotateRight, UInt64.toBitVec_or, shiftRight_ofNat_toBitVec,
    shiftLeft_ofNat_toBitVec, Nat.mod_mod, BitVec.rotateRight_def]
  by_cases hn : n % 64 = 0
  · simp only [hn, Nat.sub_zero, Nat.mod_self, BitVec.shiftLeft_zero,
      BitVec.ushiftRight_zero, BitVec.or_self,
      BitVec.shiftLeft_eq_zero (by decide : 64 ≤ 64), BitVec.or_zero]
  · rw [Nat.mod_eq_of_lt (show 64 - n % 64 < 64 by omega)]

theorem rotateRight_toBitVec_rotateLeft (x : UInt64) (n : Nat) :
    (SHA512.rotateRight x n).toBitVec = x.toBitVec.rotateLeft (64 - n % 64) := by
  rw [rotateRight_toBitVec, BitVec.rotateRight_def, BitVec.rotateLeft_def]
  by_cases hn : n % 64 = 0
  · simp only [hn, Nat.sub_zero, Nat.mod_self, BitVec.shiftLeft_zero,
      BitVec.ushiftRight_zero, BitVec.shiftLeft_eq_zero (by decide : 64 ≤ 64),
      BitVec.ushiftRight_eq_zero (by decide : 64 ≤ 64), BitVec.or_zero]
  · rw [Nat.mod_eq_of_lt (show 64 - n % 64 < 64 by omega),
      Nat.sub_sub_self (Nat.le_of_lt (Nat.mod_lt n (by decide : 0 < 64)))]
    exact BitVec.or_comm _ _

theorem smallSigma0_toBitVec (x : UInt64) :
    (smallSigma0 x).toBitVec = x.toBitVec.rotateRight 1 ^^^
      x.toBitVec.rotateRight 8 ^^^ (x.toBitVec >>> 7) := by
  simp only [smallSigma0, UInt64.toBitVec_xor, rotateRight_toBitVec]
  rfl

theorem smallSigma1_toBitVec (x : UInt64) :
    (smallSigma1 x).toBitVec = x.toBitVec.rotateRight 19 ^^^
      x.toBitVec.rotateRight 61 ^^^ (x.toBitVec >>> 6) := by
  simp only [smallSigma1, UInt64.toBitVec_xor, rotateRight_toBitVec]
  rfl

theorem bigSigma0_toBitVec (x : UInt64) :
    (bigSigma0 x).toBitVec = x.toBitVec.rotateRight 28 ^^^
      x.toBitVec.rotateRight 34 ^^^ x.toBitVec.rotateRight 39 := by
  simp only [bigSigma0, UInt64.toBitVec_xor, rotateRight_toBitVec]

theorem bigSigma1_toBitVec (x : UInt64) :
    (bigSigma1 x).toBitVec = x.toBitVec.rotateRight 14 ^^^
      x.toBitVec.rotateRight 18 ^^^ x.toBitVec.rotateRight 41 := by
  simp only [bigSigma1, UInt64.toBitVec_xor, rotateRight_toBitVec]

theorem smallSigma0_toBitVec_rotateLeft (x : UInt64) :
    (smallSigma0 x).toBitVec = x.toBitVec.rotateLeft 63 ^^^
      x.toBitVec.rotateLeft 56 ^^^ (x.toBitVec >>> 7) := by
  simp only [smallSigma0, UInt64.toBitVec_xor, rotateRight_toBitVec_rotateLeft]
  rfl

theorem smallSigma1_toBitVec_rotateLeft (x : UInt64) :
    (smallSigma1 x).toBitVec = x.toBitVec.rotateLeft 45 ^^^
      x.toBitVec.rotateLeft 3 ^^^ (x.toBitVec >>> 6) := by
  simp only [smallSigma1, UInt64.toBitVec_xor, rotateRight_toBitVec_rotateLeft]
  rfl

theorem bigSigma0_toBitVec_rotateLeft (x : UInt64) :
    (bigSigma0 x).toBitVec = x.toBitVec.rotateLeft 36 ^^^
      x.toBitVec.rotateLeft 30 ^^^ x.toBitVec.rotateLeft 25 := by
  simp only [bigSigma0, UInt64.toBitVec_xor, rotateRight_toBitVec_rotateLeft]

theorem bigSigma1_toBitVec_rotateLeft (x : UInt64) :
    (bigSigma1 x).toBitVec = x.toBitVec.rotateLeft 50 ^^^
      x.toBitVec.rotateLeft 46 ^^^ x.toBitVec.rotateLeft 23 := by
  simp only [bigSigma1, UInt64.toBitVec_xor, rotateRight_toBitVec_rotateLeft]

end Sha2.Proofs.Common.SHA512
