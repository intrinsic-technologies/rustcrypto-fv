import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.Parameters
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.StageState

set_option autoImplicit false

open P256.Proofs.Common.Instructions.Carry (sbbSpec sbbSpec_toNat_add_borrow subSpec_toNat_add_borrow)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift

variable [parameters : Parameters]

open P256.Spec X86Proofs

def neg1 (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) :=
  sbbSpec 0 a.l1 (BitVec.ofBool (subSpec 0 a.l0).2.CF)

def neg2 (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) :=
  sbbSpec 0 a.l2 (BitVec.ofBool (neg1 a).2.CF)

def neg3 (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) :=
  sbbSpec 0 a.l3 (BitVec.ofBool (neg2 a).2.CF)

def negLow (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs :=
  ⟨-a.l0, (neg1 a).1, (neg2 a).1, (neg3 a).1⟩

def negHigh (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) : BitVec 64 :=
  ~~~ah + (if (neg3 a).2.CF = false then 1 else 0)

set_option exponentiation.threshold 320 in
omit parameters in
theorem negLow_value (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) :
    (negLow a).toNat + a.toNat = 2^256 * (neg3 a).2.CF.toNat := by
  have h0 := subSpec_toNat_add_borrow (0 : BitVec 64) a.l0
  have h1 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a.l1 (BitVec.ofBool (subSpec 0 a.l0).2.CF)
  have h2 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a.l2 (BitVec.ofBool (neg1 a).2.CF)
  have h3 := sbbSpec_toNat_add_borrow (0 : BitVec 64) a.l3 (BitVec.ofBool (neg2 a).2.CF)
  change (-a.l0).toNat + a.l0.toNat = 0 + 2^64 * (subSpec 0 a.l0).2.CF.toNat at h0
  change (neg1 a).1.toNat + a.l1.toNat + (BitVec.ofBool (subSpec 0 a.l0).2.CF).toNat = 0 + 2^64 * (neg1 a).2.CF.toNat at h1
  change (neg2 a).1.toNat + a.l2.toNat + (BitVec.ofBool (neg1 a).2.CF).toNat = 0 + 2^64 * (neg2 a).2.CF.toNat at h2
  change (neg3 a).1.toNat + a.l3.toNat + (BitVec.ofBool (neg2 a).2.CF).toNat = 0 + 2^64 * (neg3 a).2.CF.toNat at h3
  simp only [BitVec.toNat_ofBool, Nat.zero_add] at h1 h2 h3
  simp only [negLow, P256.Proofs.SecretKeyFromBytes.Scalar.Limbs.toNat]
  omega

set_option exponentiation.threshold 320 in
omit parameters in
theorem negWide_value (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) :
    wideValue (negLow a) (negHigh a ah) = (2^320 - wideValue a ah) % 2^320 := by
  have hl := negLow_value a
  have ha := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt a
  have hn := P256.Proofs.SecretKeyFromBytes.Scalar.limbs_toNat_lt (negLow a)
  have hh := ah.isLt
  have hb := wideValue_lt a ah
  unfold negHigh wideValue
  rw [BitVec.toNat_add, BitVec.toNat_not]
  change (negLow a).toNat + 2^256 *
    ((2^64-1-ah.toNat + (if (neg3 a).2.CF = false then 1 else 0 : BitVec 64).toNat) % 2^64) = _
  cases hc : (neg3 a).2.CF <;> simp only [hc, Bool.true_eq_false,
    ite_true, ite_false, show (0 : BitVec 64).toNat = 0 from rfl, show (1 : BitVec 64).toNat = 1 from rfl, Bool.toNat_false,
    Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hl ⊢
  all_goals dsimp only [wideValue] at hb ⊢
  all_goals omega

def magnitudeLow (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs :=
  let r := correctedWords a ah shift
  if r.2.2 = 0 then r.1 else negLow r.1

def magnitudeHigh (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) : BitVec 64 :=
  let r := correctedWords a ah shift
  if r.2.2 = 0 then r.2.1 else negHigh r.1 r.2.1

def correctionNegative (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) : Bool :=
  decide ((correctedWords a ah shift).2.2 ≠ 0)

theorem correctionProduct_value (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) :
    wideValue (correctionProduct a ah shift).1 (correctionProduct a ah shift).2 =
      parameters.modulus.toNat * (correctionWord (wideValue a ah) shift).toNat := by
  exact productWide_value _ _

set_option exponentiation.threshold 320 in
theorem magnitude_signed (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) :
    (if correctionNegative a ah shift then
      -(wideValue (magnitudeLow a ah shift) (magnitudeHigh a ah shift) : Int)
     else (wideValue (magnitudeLow a ah shift) (magnitudeHigh a ah shift) : Int)) =
      correctedValue a ah shift := by
  have h := subWide_value a (correctionProduct a ah shift).1 ah (correctionProduct a ah shift).2
  change (correctedWords a ah shift).2.2.toNat ≤ 1 ∧
    wideValue (correctedWords a ah shift).1 (correctedWords a ah shift).2.1 +
      wideValue (correctionProduct a ah shift).1 (correctionProduct a ah shift).2 =
      wideValue a ah + 2^320 * (correctedWords a ah shift).2.2.toNat at h
  have ha := wideValue_lt a ah
  have hp := wideValue_lt (correctionProduct a ah shift).1 (correctionProduct a ah shift).2
  have hr := wideValue_lt (correctedWords a ah shift).1 (correctedWords a ah shift).2.1
  have product := correctionProduct_value a ah shift
  rcases P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one h.1 with hz | ho
  · simp only [correctionNegative, magnitudeLow, magnitudeHigh, hz, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ite_false, ite_true]
    rw [hz] at h
    change _ ∧ _ + _ = _ + 2^320 * 0 at h
    unfold correctedValue
    omega
  · simp only [correctionNegative, magnitudeLow, magnitudeHigh, ho,
      show (1 : BitVec 64) ≠ 0 by decide, show decide ((1 : BitVec 64) ≠ 0) = true by decide, ite_true, ite_false, negWide_value]
    rw [ho] at h
    change _ ∧ _ + _ = _ + 2^320 * 1 at h
    unfold correctedValue
    omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift
