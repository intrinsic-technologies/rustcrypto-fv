import Hkdf.Proofs.Common.SHA256.Mathematics.Model
import Init.Data.BitVec.Bitblast

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Proofs.NIST

theorem choice_eq_xor_and (x y z : UInt32) :
    choice x y z = z ^^^ (x &&& (y ^^^ z)) := by
  apply UInt32.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) =
    z.toBitVec ^^^ (x.toBitVec &&& (y.toBitVec ^^^ z.toBitVec))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hi, decide_true, Bool.true_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem choice_eq_and_xor (x y z : UInt32) :
    choice x y z = ((y ^^^ z) &&& x) ^^^ z := by
  rw [choice_eq_xor_and, UInt32.and_comm (y ^^^ z) x, UInt32.xor_comm]

theorem majority_eq_xor_and (x y z : UInt32) :
    majority x y z = (x &&& y) ^^^ (z &&& (x ^^^ y)) := by
  apply UInt32.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    (x.toBitVec &&& y.toBitVec) ^^^ (z.toBitVec &&& (x.toBitVec ^^^ y.toBitVec))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem majority_eq_and_xor (x y z : UInt32) :
    majority x y z = ((y ^^^ z) &&& x) ^^^ (y &&& z) := by
  apply UInt32.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    ((y.toBitVec ^^^ z.toBitVec) &&& x.toBitVec) ^^^ (y.toBitVec &&& z.toBitVec)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem majority_eq_or_and (x y z : UInt32) :
    majority x y z = (x &&& y) ||| ((x ||| y) &&& z) := by
  apply UInt32.eq_of_toBitVec_eq
  change (x.toBitVec &&& y.toBitVec) ^^^ (x.toBitVec &&& z.toBitVec) ^^^
    (y.toBitVec &&& z.toBitVec) =
    (x.toBitVec &&& y.toBitVec) ||| ((x.toBitVec ||| y.toBitVec) &&& z.toBitVec)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;>
    cases z.toBitVec.getLsbD i <;> rfl

theorem choice_eq_add_and (x y z : UInt32) :
    choice x y z = (x &&& y) + (~~~x &&& z) := by
  apply UInt32.eq_of_toBitVec_eq
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

theorem choice_toBitVec (x y z : UInt32) :
    (choice x y z).toBitVec =
      (x.toBitVec &&& y.toBitVec) ^^^ (~~~x.toBitVec &&& z.toBitVec) := rfl

theorem majority_toBitVec (x y z : UInt32) :
    (majority x y z).toBitVec = (x.toBitVec &&& y.toBitVec) ^^^
      (x.toBitVec &&& z.toBitVec) ^^^ (y.toBitVec &&& z.toBitVec) := rfl

theorem shiftRight_ofNat_toBitVec (x : UInt32) (n : Nat) :
    (x >>> UInt32.ofNat n).toBitVec = x.toBitVec >>> (n % 32) := by
  simp only [UInt32.toBitVec_shiftRight, UInt32.toBitVec_ofNat', BitVec.ushiftRight_eq',
    BitVec.toNat_umod, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mod_mod_of_dvd n (by decide)

theorem shiftLeft_ofNat_toBitVec (x : UInt32) (n : Nat) :
    (x <<< UInt32.ofNat n).toBitVec = x.toBitVec <<< (n % 32) := by
  simp only [UInt32.toBitVec_shiftLeft, UInt32.toBitVec_ofNat', BitVec.shiftLeft_eq',
    BitVec.toNat_umod, BitVec.toNat_ofNat]
  congr 1
  exact Nat.mod_mod_of_dvd n (by decide)

theorem rotateRight_toBitVec (x : UInt32) (n : Nat) :
    (SHA256.rotateRight x n).toBitVec = x.toBitVec.rotateRight n := by
  simp only [SHA256.rotateRight, UInt32.toBitVec_or, shiftRight_ofNat_toBitVec,
    shiftLeft_ofNat_toBitVec, Nat.mod_mod, BitVec.rotateRight_def]
  by_cases hn : n % 32 = 0
  · simp only [hn, Nat.sub_zero, Nat.mod_self, BitVec.shiftLeft_zero,
      BitVec.ushiftRight_zero, BitVec.or_self,
      BitVec.shiftLeft_eq_zero (by decide : 32 ≤ 32), BitVec.or_zero]
  · rw [Nat.mod_eq_of_lt (show 32 - n % 32 < 32 by omega)]

theorem rotateRight_toBitVec_rotateLeft (x : UInt32) (n : Nat) :
    (SHA256.rotateRight x n).toBitVec = x.toBitVec.rotateLeft (32 - n % 32) := by
  rw [rotateRight_toBitVec, BitVec.rotateRight_def, BitVec.rotateLeft_def]
  by_cases hn : n % 32 = 0
  · simp only [hn, Nat.sub_zero, Nat.mod_self, BitVec.shiftLeft_zero,
      BitVec.ushiftRight_zero, BitVec.shiftLeft_eq_zero (by decide : 32 ≤ 32),
      BitVec.ushiftRight_eq_zero (by decide : 32 ≤ 32), BitVec.or_zero]
  · rw [Nat.mod_eq_of_lt (show 32 - n % 32 < 32 by omega),
      Nat.sub_sub_self (Nat.le_of_lt (Nat.mod_lt n (by decide : 0 < 32)))]
    exact BitVec.or_comm _ _

theorem smallSigma0_toBitVec (x : UInt32) :
    (smallSigma0 x).toBitVec = x.toBitVec.rotateRight 7 ^^^
      x.toBitVec.rotateRight 18 ^^^ (x.toBitVec >>> 3) := by
  simp only [smallSigma0, UInt32.toBitVec_xor, rotateRight_toBitVec]
  rfl

theorem smallSigma1_toBitVec (x : UInt32) :
    (smallSigma1 x).toBitVec = x.toBitVec.rotateRight 17 ^^^
      x.toBitVec.rotateRight 19 ^^^ (x.toBitVec >>> 10) := by
  simp only [smallSigma1, UInt32.toBitVec_xor, rotateRight_toBitVec]
  rfl

theorem bigSigma0_toBitVec (x : UInt32) :
    (bigSigma0 x).toBitVec = x.toBitVec.rotateRight 2 ^^^
      x.toBitVec.rotateRight 13 ^^^ x.toBitVec.rotateRight 22 := by
  simp only [bigSigma0, UInt32.toBitVec_xor, rotateRight_toBitVec]

theorem bigSigma1_toBitVec (x : UInt32) :
    (bigSigma1 x).toBitVec = x.toBitVec.rotateRight 6 ^^^
      x.toBitVec.rotateRight 11 ^^^ x.toBitVec.rotateRight 25 := by
  simp only [bigSigma1, UInt32.toBitVec_xor, rotateRight_toBitVec]

theorem smallSigma0_toBitVec_rotateLeft (x : UInt32) :
    (smallSigma0 x).toBitVec = x.toBitVec.rotateLeft 25 ^^^
      x.toBitVec.rotateLeft 14 ^^^ (x.toBitVec >>> 3) := by
  simp only [smallSigma0, UInt32.toBitVec_xor, rotateRight_toBitVec_rotateLeft]
  rfl

theorem smallSigma1_toBitVec_rotateLeft (x : UInt32) :
    (smallSigma1 x).toBitVec = x.toBitVec.rotateLeft 15 ^^^
      x.toBitVec.rotateLeft 13 ^^^ (x.toBitVec >>> 10) := by
  simp only [smallSigma1, UInt32.toBitVec_xor, rotateRight_toBitVec_rotateLeft]
  rfl

theorem bigSigma0_toBitVec_rotateLeft (x : UInt32) :
    (bigSigma0 x).toBitVec = x.toBitVec.rotateLeft 30 ^^^
      x.toBitVec.rotateLeft 19 ^^^ x.toBitVec.rotateLeft 10 := by
  simp only [bigSigma0, UInt32.toBitVec_xor, rotateRight_toBitVec_rotateLeft]

theorem bigSigma1_toBitVec_rotateLeft (x : UInt32) :
    (bigSigma1 x).toBitVec = x.toBitVec.rotateLeft 26 ^^^
      x.toBitVec.rotateLeft 21 ^^^ x.toBitVec.rotateLeft 7 := by
  simp only [bigSigma1, UInt32.toBitVec_xor, rotateRight_toBitVec_rotateLeft]

end Hkdf.Proofs.Common.SHA256
