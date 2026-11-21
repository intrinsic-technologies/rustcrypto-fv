import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.Parameters
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.AbsoluteShift.Arithmetic

set_option autoImplicit false
namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift

variable [parameters : Parameters]
open P256.Spec

theorem quotient_bound_signed (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat)
    (hi : shift ≤ 62) (bound : wideValue a ah < 2^shift*parameters.modulus.toNat) :
    let m := wideValue (magnitudeLow a ah shift) (magnitudeHigh a ah shift)
    m / 2^shift < parameters.modulus.toNat ∧
    (if correctionNegative a ah shift then -((m / 2^shift : Nat) : Int)
      else ((m / 2^shift : Nat) : Int)) = correctedValue a ah shift / (2 : Int)^shift := by
  have signed := magnitude_signed a ah shift
  have divisible := corrected_divisible (wideValue a ah) shift hi
  change (2 : Int)^shift ∣ correctedValue a ah shift at divisible
  have quotient := Shift.signed_magnitude_div (correctionNegative a ah shift)
    (magnitude := wideValue (magnitudeLow a ah shift) (magnitudeHigh a ah shift))
    (by rw [signed]; exact divisible)
  rw [signed] at quotient
  have boundInt : (wideValue a ah : Int) < (2 : Int)^shift*(parameters.modulus.toNat : Int) := by
    exact_mod_cast bound
  have correction := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Correction.modular_correction
    (modulus := (parameters.modulus.toNat : Int)) (by exact_mod_cast parameters.positive)
    (Int.pow_pos (by decide : (0 : Int) < 2)) (inverse_mod_two_pow (by omega : shift ≤ 64))
    (Int.natCast_nonneg (wideValue a ah)) boundInt
  have corrected : correctedValue a ah shift = (wideValue a ah : Int) -
      parameters.modulus.toNat * (((wideValue a ah : Int)*parameters.inverse.toNat) % (2 : Int)^shift) := by
    rw [correctedValue,correctionWord_value _ _ (by omega)]
  dsimp only at correction ⊢
  rw [← corrected,quotient] at correction
  refine ⟨?_,quotient.symm⟩
  cases hn : correctionNegative a ah shift <;>
    simp only [hn,Bool.false_eq_true,ite_false,ite_true] at correction <;> omega

set_option exponentiation.threshold 320 in
omit parameters in
theorem shifted_magnitude (low : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (high : BitVec 64) (shift : Nat)
    (hi : shift ≤ 64) (qbound : wideValue low high / 2^shift < 2^256) :
    ∃ out : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs,
      out.toNat = wideValue low high / 2^shift ∧
      ((low.l0 >>> shift) ||| (low.l1 <<< (64-shift))) = out.l0 ∧
      ((low.l1 >>> shift) ||| (low.l2 <<< (64-shift))) = out.l1 ∧
      ((low.l2 >>> shift) ||| (low.l3 <<< (64-shift))) = out.l2 ∧
      ((low.l3 >>> shift) ||| (high <<< (64-shift))) = out.l3 ∧
      high >>> shift = 0 := by
  let m := wideValue low high
  let q := m / 2^shift
  let out : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs := ⟨BitVec.ofNat 64 q, BitVec.ofNat 64 (q / 2^64),
    BitVec.ofNat 64 (q / 2^128), BitVec.ofNat 64 (q / 2^192)⟩
  have d0 : BitVec.ofNat 64 m = low.l0 := by
    have h0 := low.l0.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,m,wideValue,P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
    omega
  have d1 : BitVec.ofNat 64 (m / 2^64) = low.l1 := by
    have h0 := low.l0.isLt
    have h1 := low.l1.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,m,wideValue,P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
    omega
  have d2 : BitVec.ofNat 64 (m / 2^128) = low.l2 := by
    have h0 := low.l0.isLt
    have h1 := low.l1.isLt
    have h2 := low.l2.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,m,wideValue,P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
    omega
  have d3 : BitVec.ofNat 64 (m / 2^192) = low.l3 := by
    have h0 := low.l0.isLt
    have h1 := low.l1.isLt
    have h2 := low.l2.isLt
    have h3 := low.l3.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,m,wideValue,P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
    omega
  have d4 : BitVec.ofNat 64 (m / 2^256) = high := by
    have hl := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt low
    have hh := high.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,m,wideValue]
    omega
  have shifted (j : Nat) :
      (BitVec.ofNat 64 (m / 2^(64*j)) >>> shift) |||
        (BitVec.ofNat 64 (m / 2^(64*(j+1))) <<< (64-shift)) =
        BitVec.ofNat 64 (q / 2^(64*j)) :=
    Shift.shift_limb (j := j) (wideValue_lt low high) hi
  refine ⟨out,?_,?_,?_,?_,?_,?_⟩
  · have pack (v : Nat) (hv : v < 2^256) :
        (⟨BitVec.ofNat 64 v, BitVec.ofNat 64 (v / 2^64),
          BitVec.ofNat 64 (v / 2^128), BitVec.ofNat 64 (v / 2^192)⟩ : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs).toNat = v := by
      simp only [P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat,BitVec.toNat_ofNat]
      omega
    exact pack q qbound
  · simpa only [Nat.reduceMul,Nat.reduceAdd,Nat.pow_zero,Nat.div_one,d0,d1] using shifted 0
  · simpa only [Nat.reduceMul,Nat.reduceAdd,d1,d2] using shifted 1
  · simpa only [Nat.reduceMul,Nat.reduceAdd,d2,d3] using shifted 2
  · simpa only [Nat.reduceMul,Nat.reduceAdd,d3,d4] using shifted 3
  · have bound := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mp qbound
    have highBound : high.toNat < 2^shift := by
      dsimp only [wideValue] at bound
      omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt highBound,show (0 : BitVec 64).toNat = 0 from rfl]

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift
