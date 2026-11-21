import K256.Proofs.Common.Invert.ModularShift.Absolute
import K256.Proofs.Common.Invert.ModularShift.Division

namespace K256.Proofs.Common.Invert.ModularShift.Arithmetic

open LinearCombination (Limbs subRaw subWord borrow subRaw_toNat subWord_borrow eq_zero_or_one)
open X86Proofs K256.Proofs.Generate.Generator.Affine.Invert
open SafeGcd (correctionWord correctionWord_value inverse_mod_two_pow)

theorem magnitudeLow_retained (p : Inputs)
 :
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.magnitudeLow (wideLow p) (wideHigh p)
      p.shift.toNat = magnitudeLow p := by
  rw [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.magnitudeLow, correctedWords_eq p, magnitudeLow_eq]

theorem magnitudeHigh_retained (p : Inputs)
 :
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.magnitudeHigh (wideLow p) (wideHigh
      p) p.shift.toNat = magnitudeHigh p := by
  rw [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.magnitudeHigh, correctedWords_eq p, magnitudeHigh_eq]

def quotientLow (p : Inputs) : Limbs :=
  ⟨v108c54 p, v108c51 p, v108c37 p, v108cfb p⟩

def quotientHigh (p : Inputs) : BitVec 64 := v108d33 p

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
    (hbound : K256.Proofs.Common.Invert.ModularShift.wideValue (magnitudeLow p) (magnitudeHigh
      p) / 2^p.shift.toNat < 2^256) :
    (quotientLow p).toNat =
      K256.Proofs.Common.Invert.ModularShift.wideValue (magnitudeLow p) (magnitudeHigh p) /
        2^p.shift.toNat ∧
    quotientHigh p = 0 := by
  obtain ⟨out, hvalue, h0, h1, h2, h3, h4⟩ :=
    K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.shifted_magnitude (magnitudeLow p)
      (magnitudeHigh p) p.shift.toNat hi hbound
  have he : quotientLow p = out := by
    apply limbs_ext
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  exact ⟨he ▸ hvalue, h4⟩

theorem quotient_value (p : Inputs)
 (hi : p.shift.toNat ≤ 62)
    (hbound : K256.Proofs.Common.Invert.ModularShift.wideValue (wideLow p) (wideHigh p) <
      2^p.shift.toNat * prime.toNat) :
    (quotientLow p).toNat < prime.toNat ∧
    quotientHigh p = 0 ∧
    (if decide (v108b25 p ≠ 0) then -((quotientLow p).toNat : Int)
      else ((quotientLow p).toNat : Int)) =
      K256.Proofs.Common.Invert.ModularShift.correctedValue (wideLow p) (wideHigh p)
        p.shift.toNat / (2 : Int)^p.shift.toNat := by
  have h := K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.quotient_bound_signed
    (wideLow p) (wideHigh p) p.shift.toNat hi hbound
  dsimp only at h
  rw [magnitudeLow_retained p, magnitudeHigh_retained p] at h
  have hq := quotient_limbs p (by omega) (Nat.lt_trans h.1
    (K256.Proofs.Common.Invert.ModularShift.modulus_bound))
  rw [← hq.1] at h
  refine ⟨h.1, hq.2, ?_⟩
  simpa only [K256.Proofs.Common.Invert.ModularShift.AbsoluteShift.correctionNegative,
    correctedWords_eq p] using h.2

end K256.Proofs.Common.Invert.ModularShift.Arithmetic
