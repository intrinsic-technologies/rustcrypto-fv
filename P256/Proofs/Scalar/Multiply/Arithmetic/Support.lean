import P256.Proofs.Scalar.Multiply.Model
import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Field.Schoolbook.Arithmetic
import P256.Proofs.Field.Add.Arithmetic
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Support
import P256.Proofs.SecretKeyFromBytes.Compare

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Support
open X86Proofs
open P256.Proofs.Field.Montgomery.Reduction
export P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
export P256.Proofs.Field.Montgomery.Reduction (adc carry)
export P256.Proofs.Field.Add (addRaw addRaw_toNat)
export P256.Proofs.Field.Montgomery (wordBase)
export P256.Proofs.Field.Schoolbook (packFour mulWord_bound)
theorem mul64_toNat_add_high (a b : BitVec 64) :
    (a*b).toNat + wordBase * (P256.Proofs.Common.Instructions.mulHigh64 a b).toNat = a.toNat*b.toNat :=
  P256.Proofs.Field.Montgomery.product64_value a b

theorem adcSpec_low (c : Bool) (a b : BitVec 64) :
    (adcSpec c a b).1 = a + b + BitVec.ofNat 64 c.toNat := rfl


theorem addSpec_low (a b : BitVec 64) : (addSpec a b).1 = a + b := rfl


theorem boolByte_eq (c : Bool) : (if c then (1 : BitVec 8) else 0) = BitVec.ofNat 8 c.toNat := by
  cases c <;> rfl


theorem boolByte_carry (c : Bool) :
    (addSpec (BitVec.ofNat 8 c.toNat) 255).2.CF = c := by
  cases c <;> decide +kernel


theorem setWidth_mergeGPR {n k : Nat} (v : BitVec n) (x : BitVec 64)
    (hn : n ≤ 64) (hk : k ≤ n) : (mergeGPR n v x).setWidth k = v.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and, mergeGPR]
  split
  · simp [show j < 64 by omega]
  · rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
    simp [show j < n by omega]


theorem addSpec_carry (a b : BitVec 64) : (addSpec a b).2.CF = carry a b false := by
  simp only [addSpec, carry, Bool.toNat_false, Nat.add_zero]
  rw [decide_eq_decide]
  have h := (a + b).isLt
  by_cases ha : a.toNat + b.toNat < 2^64
  · rw [BitVec.toNat_add, Nat.mod_eq_of_lt ha]
    omega
  · omega


theorem adcSpec_carry (c : Bool) (a b : BitVec 64) : (adcSpec c a b).2.CF = carry a b c := by
  simp only [adcSpec, carry]
  rw [decide_eq_decide]
  have h := (a + b + BitVec.ofNat 64 c.toNat).isLt
  have hc : c.toNat < 2^64 := by cases c <;> decide
  by_cases ha : a.toNat + b.toNat + c.toNat < 2^64
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hc, Nat.mod_add_mod, Nat.mod_eq_of_lt ha]
    omega
  · omega

end P256.Proofs.Scalar.Multiply.Arithmetic.Support
