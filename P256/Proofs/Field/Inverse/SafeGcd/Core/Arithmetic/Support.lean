import P256.Proofs.Field.Inverse.SafeGcd.Correction.Arithmetic
import P256.Proofs.Field.Schoolbook.Arithmetic
import P256.Proofs.Common.Instructions.Mul.Spec
import X86Proofs.Instructions.Mul.Operation

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Support
open X86Proofs
open P256.Proofs.Field.Inverse.SafeGcd.Correction
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Schoolbook

theorem packed_limbs (w : Vector (BitVec 64) 4) :
    packFour (w.map BitVec.toNat) = (limbs w).toNat := by
  simp only [packFour, Vector.getElem_map, limbs, Limbs.toNat, Field.Montgomery.wordBase]
  omega

theorem byte_merge (v : BitVec 8) (x : BitVec 64) : (mergeGPR 8 v x).setWidth 8 = v := by
  simp only [setWidth_mergeGPR8]

theorem mulResult_snd (a b : BitVec 64) :
    (mulResult a b).2 = Common.Instructions.mulHigh64 a b := by
  apply BitVec.eq_of_toNat_eq
  have h : a.toNat * b.toNat < 2^128 := by
    change a.toNat * b.toNat < 2^64 * 2^64
    exact Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
  simp [mulResult, Common.Instructions.mulHigh64, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]

theorem signed_residue (a m : Nat) (q : BitVec 8) (h : a < m) :
    (if a = 0 ∨ q = 0 then a else m-a) =
      ((if q = 0 then (a : Int) else -(a : Int)) % (m : Int)).toNat := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hq : q = 0
  · simp only [hq, or_true, ↓reduceIte]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rfl
  · simp only [ha, hq, or_false, ↓reduceIte]
    rw [Int.neg_emod_eq_sub_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

theorem correctedWords_signed (p : Inputs)
    (hb : (limbs p.magnitude).toNat < (limbs p.modulus).toNat) :
    packFour ((correctedWords p).map BitVec.toNat) =
      ((if signBit p = 0 then ((limbs p.magnitude).toNat : Int)
        else -((limbs p.magnitude).toNat : Int)) % ((limbs p.modulus).toNat : Int)).toNat := by
  rw [packed_limbs, Correction.correctedWords_value p hb]
  exact signed_residue _ _ _ hb

end P256.Proofs.Field.Inverse.SafeGcd.Core.Support
