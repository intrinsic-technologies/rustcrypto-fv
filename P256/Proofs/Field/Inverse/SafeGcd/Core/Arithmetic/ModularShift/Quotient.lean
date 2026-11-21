import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Absolute
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.AbsoluteShift.Quotient

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic

open X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)
open P256.Proofs.Field.Schoolbook (packFour packFive)
open P256.Proofs.Field.Inverse.SafeGcd.Core
open ModularShift
open P256.Proofs.Field.Inverse.SafeGcd

theorem magnitudeLow_retained [parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hmod : parameters.modulus = limbs p.modulus)
    (hinv : p.inverse = parameters.inverse) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.magnitudeLow (wideLow p) (wideHigh p)
      p.shift.toNat = magnitudeLow p := by
  rw [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.magnitudeLow, correctedWords_eq p
    hmod hinv, magnitudeLow_eq]

theorem magnitudeHigh_retained [parameters :
  P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hmod : parameters.modulus = limbs p.modulus)
    (hinv : p.inverse = parameters.inverse) :
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.magnitudeHigh (wideLow p) (wideHigh
      p) p.shift.toNat = magnitudeHigh p := by
  rw [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.magnitudeHigh, correctedWords_eq p
    hmod hinv, magnitudeHigh_eq]

def quotientLow (p : Inputs) : Limbs :=
  ⟨v1b1844 p, v1b1841 p, v1b1827 p, v1b18eb p⟩

def quotientHigh (p : Inputs) : BitVec 64 := v1b1923 p

private theorem limbs_ext {a b : Limbs} (h0 : a.l0 = b.l0) (h1 : a.l1 = b.l1)
    (h2 : a.l2 = b.l2) (h3 : a.l3 = b.l3) : a = b := by
  cases a
  cases b
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

theorem quotient_limbs (p : Inputs) (hi : p.shift.toNat ≤ 64)
    (hbound : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (magnitudeLow p) (magnitudeHigh
      p) / 2^p.shift.toNat < 2^256) :
    (quotientLow p).toNat =
      P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (magnitudeLow p) (magnitudeHigh p) /
        2^p.shift.toNat ∧
    quotientHigh p = 0 := by
  obtain ⟨out, hvalue, h0, h1, h2, h3, h4⟩ :=
    P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.shifted_magnitude (magnitudeLow p)
      (magnitudeHigh p) p.shift.toNat hi hbound
  have he : quotientLow p = out := by
    apply limbs_ext
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  exact ⟨he ▸ hvalue, h4⟩

theorem quotient_value [parameters : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Parameters]
    (p : Inputs) (hmod : parameters.modulus = limbs p.modulus)
    (hinv : p.inverse = parameters.inverse) (hi : p.shift.toNat ≤ 62)
    (hbound : P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.wideValue (wideLow p) (wideHigh p) <
      2^p.shift.toNat * parameters.modulus.toNat) :
    (quotientLow p).toNat < parameters.modulus.toNat ∧
    quotientHigh p = 0 ∧
    (if decide (v1b1715 p ≠ 0) then -((quotientLow p).toNat : Int)
      else ((quotientLow p).toNat : Int)) =
      P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.correctedValue (wideLow p) (wideHigh p)
        p.shift.toNat / (2 : Int)^p.shift.toNat := by
  have h := P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.quotient_bound_signed
    (wideLow p) (wideHigh p) p.shift.toNat hi hbound
  dsimp only at h
  rw [magnitudeLow_retained p hmod hinv, magnitudeHigh_retained p hmod hinv] at h
  have hq := quotient_limbs p (by omega) (Nat.lt_trans h.1
    (P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.modulus_bound))
  rw [← hq.1] at h
  refine ⟨h.1, hq.2, ?_⟩
  simpa only [P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.AbsoluteShift.correctionNegative,
    correctedWords_eq p hmod hinv] using h.2

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift.Arithmetic
