import P256.Proofs.Scalar.Multiply.Arithmetic.Support
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.QuotientArithmetic
import P256.Proofs.Field.Subtract.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Remainder

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs)
open P256.Proofs.Field.Subtract

def subtractFive (a p : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
  let lower := subRaw ⟨a[0], a[1], a[2], a[3]⟩ ⟨p[0], p[1], p[2], p[3]⟩
  #v[lower.1.l0, lower.1.l1, lower.1.l2, lower.1.l3, subWord a[4] p[4] lower.2]

theorem quotientValue_lt (a : Vector (BitVec 64) 5) : quotientValue a < 2^320 := by
  have h0 := a[0].isLt
  have h1 := a[1].isLt
  have h2 := a[2].isLt
  have h3 := a[3].isLt
  have h4 := a[4].isLt
  dsimp only [quotientValue]
  omega

theorem subtractFive_value (a p : Vector (BitVec 64) 5) :
    ∃ b : Nat, quotientValue (subtractFive a p) + quotientValue p =
      quotientValue a + 2^320*b := by
  let al : Limbs := ⟨a[0], a[1], a[2], a[3]⟩
  let pl : Limbs := ⟨p[0], p[1], p[2], p[3]⟩
  have lower := subRaw_toNat al pl
  have upper := subWord_borrow a[4] p[4] (subRaw al pl).2
    (P256.Proofs.SecretKeyFromBytes.Scalar.eq_zero_or_one lower.1)
  refine ⟨(borrow a[4] p[4] (subWord a[4] p[4] (subRaw al pl).2)).toNat, ?_⟩
  have lowerValue := lower.2
  simp only [Limbs.toNat] at lowerValue
  dsimp only [al, pl] at lowerValue
  change (subRaw al pl).1.l0.toNat + 2^64*(subRaw al pl).1.l1.toNat +
    2^128*(subRaw al pl).1.l2.toNat + 2^192*(subRaw al pl).1.l3.toNat +
    2^256*(subWord a[4] p[4] (subRaw al pl).2).toNat + quotientValue p = _
  dsimp only [quotientValue, al, pl] at upper ⊢
  omega

set_option exponentiation.threshold 512 in
theorem subtractFive_barrett {a p : Vector (BitVec 64) 5} {x : Nat}
    (bound : x < 2^512) (input : quotientValue a = x % 2^320)
    (product : quotientValue p = (barrettQuotient x * P256.Spec.Operations.domain.n) % 2^320) :
    quotientValue (subtractFive a p) = barrettRemainder x := by
  obtain ⟨b, difference⟩ := subtractFive_value a p
  have resultBound := quotientValue_lt (subtractFive a p)
  have remainderBound := barrettRemainder_lt bound
  have below := barrettQuotient_le x
  have xd := Nat.mod_add_div x (2^320)
  have pd := Nat.mod_add_div (barrettQuotient x * P256.Spec.Operations.domain.n) (2^320)
  rw [input, product] at difference
  dsimp only [barrettRemainder, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Remainder
