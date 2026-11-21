import Std.Tactic
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shift.Values
import P256.Proofs.Field.Subtract.Arithmetic
import P256.Proofs.Common.Instructions.Carry.Arithmetic
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.Parameters
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Correction

set_option autoImplicit false

open P256.Proofs.Field.Subtract (borrow subRaw subRaw_toNat subWord subWord_borrow)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

open P256.Spec

theorem shift_mask {width shift : Nat} (x : BitVec width) (hs : shift ≤ width) :
    (x <<< (width-shift)) >>> (width-shift) = (x.setWidth shift).setWidth width := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i < shift
  · have hn : width-shift+i < width := by omega
    simp only [h,hi,hn,decide_true,Bool.true_and,
      show ¬ width-shift+i < width-shift by omega,decide_false,Bool.not_false]
    congr 1
    omega
  · have hn : ¬ width-shift+i < width := by omega
    simp [h,hi,hn]

variable [parameters : Parameters]

def correctionWord (magnitude : Nat) (shift : Nat) : BitVec 64 :=
  ((parameters.inverse * BitVec.ofNat 64 magnitude) <<< (64-shift)) >>> (64-shift)

theorem correctionWord_eq (magnitude shift : Nat) (hs : shift ≤ 64) :
    correctionWord magnitude shift =
      (BitVec.ofNat shift (magnitude * parameters.inverse.toNat)).setWidth 64 := by
  rw [correctionWord, shift_mask _ hs]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mul_mod_mod, Nat.mul_comm parameters.inverse.toNat magnitude,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs)]

theorem correctionWord_value (magnitude shift : Nat) (hs : shift ≤ 64) :
    ((correctionWord magnitude shift).toNat : Int) =
      ((magnitude : Int) * parameters.inverse.toNat) % (2 : Int)^shift := by
  rw [correctionWord_eq magnitude shift hs, BitVec.toNat_setWidth]
  have hn : (BitVec.ofNat shift (magnitude * parameters.inverse.toNat)).toNat < 2^64 :=
    Nat.lt_of_lt_of_le (BitVec.isLt _) (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat]
  simp only [Int.natCast_emod, Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]

theorem corrected_divisible (magnitude shift : Nat) (hs : shift ≤ 62) :
    (2 : Int)^shift ∣ (magnitude : Int) - parameters.modulus.toNat *
      ((correctionWord magnitude shift).toNat : Int) := by
  rw [correctionWord_value magnitude shift (by omega)]
  exact P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Correction.corrected_divisible (inverse_mod_two_pow (by omega))

def wideValue (low : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (high : BitVec 64) : Nat :=
  low.toNat + 2^256 * high.toNat

omit parameters in
theorem wideValue_lt (low : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (high : BitVec 64) :
    wideValue low high < 2^320 := by
  have hl := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt low
  have hh := high.isLt
  dsimp only [wideValue]
  omega

def productWide (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (k : BitVec 64) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs × BitVec 64 :=
  let r1 := X86Proofs.addSpec (a.l1*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l0 k)
  let r2 := P256.Proofs.Common.Instructions.Carry.adcSpec (a.l2*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l1 k)
    (BitVec.ofBool r1.2.CF)
  let r3 := P256.Proofs.Common.Instructions.Carry.adcSpec (a.l3*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l2 k)
    (BitVec.ofBool r2.2.CF)
  (⟨a.l0*k,r1.1,r2.1,r3.1⟩,
    (P256.Proofs.Common.Instructions.Carry.adcSpec (P256.Proofs.Common.Instructions.mulHigh64 a.l3 k) 0
      (BitVec.ofBool r3.2.CF)).1)

omit parameters in
theorem product_word_value (a k : BitVec 64) :
    (a*k).toNat + 2^64*(P256.Proofs.Common.Instructions.mulHigh64 a k).toNat = a.toNat*k.toNat := by
  have h : a.toNat * k.toNat < 2^64 * 2^64 :=
    Nat.mul_lt_mul_of_lt_of_lt a.isLt k.isLt
  have hh : a.toNat * k.toNat / 2^64 < 2^64 :=
    (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  simp only [BitVec.toNat_mul, P256.Proofs.Common.Instructions.mulHigh64,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh]
  exact Nat.mod_add_div _ _

set_option exponentiation.threshold 320 in
omit parameters in
theorem productWide_value (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (k : BitVec 64) :
    wideValue (productWide a k).1 (productWide a k).2 = a.toNat*k.toNat := by
  have p0 := product_word_value a.l0 k
  have p1 := product_word_value a.l1 k
  have p2 := product_word_value a.l2 k
  have p3 := product_word_value a.l3 k
  have h1 := P256.Proofs.Common.Instructions.Carry.addSpec_toNat_add_carry
    (a.l1*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l0 k)
  have h2 := P256.Proofs.Common.Instructions.Carry.adcSpec_toNat_add_carry
    (a.l2*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l1 k)
    (BitVec.ofBool (X86Proofs.addSpec (a.l1*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l0 k)).2.CF)
  have h3 := P256.Proofs.Common.Instructions.Carry.adcSpec_toNat_add_carry
    (a.l3*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l2 k)
    (BitVec.ofBool (P256.Proofs.Common.Instructions.Carry.adcSpec
      (a.l2*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l1 k)
      (BitVec.ofBool (X86Proofs.addSpec (a.l1*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l0 k)).2.CF)).2.CF)
  have h4 := P256.Proofs.Common.Instructions.Carry.adcSpec_toNat_add_carry
    (P256.Proofs.Common.Instructions.mulHigh64 a.l3 k) 0
    (BitVec.ofBool (P256.Proofs.Common.Instructions.Carry.adcSpec
      (a.l3*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l2 k)
      (BitVec.ofBool (P256.Proofs.Common.Instructions.Carry.adcSpec
        (a.l2*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l1 k)
        (BitVec.ofBool (X86Proofs.addSpec (a.l1*k) (P256.Proofs.Common.Instructions.mulHigh64 a.l0 k)).2.CF)).2.CF)).2.CF)
  simp only [BitVec.toNat_ofBool] at h2 h3 h4
  have bound : a.toNat*k.toNat < 2^320 := by
    have ha := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt a
    have hk := k.isLt
    have h := Nat.mul_lt_mul_of_lt_of_lt ha hk
    exact h
  simp only [productWide,wideValue,P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat,Nat.add_mul,Nat.mul_assoc] at bound ⊢
  conv at h4 => rhs; lhs; rhs; change 0
  omega

def subWide (a b : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah bh : BitVec 64) :
    P256.Proofs.SecretKeyFromBytes.Scalar.Limbs × BitVec 64 × BitVec 64 :=
  let low := subRaw a b
  let high := subWord ah bh low.2
  (low.1, high, borrow ah bh high)

omit parameters in
theorem subWide_value (a b : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah bh : BitVec 64) :
    (subWide a b ah bh).2.2.toNat ≤ 1 ∧
    wideValue (subWide a b ah bh).1 (subWide a b ah bh).2.1 + wideValue b bh =
      wideValue a ah + 2^320 * (subWide a b ah bh).2.2.toNat := by
  have hl := subRaw_toNat a b
  have hh := subWord_borrow ah bh (subRaw a b).2 (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one hl.1)
  refine ⟨hh.1, ?_⟩
  dsimp only [subWide,wideValue]
  omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
