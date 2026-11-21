import P256.Proofs.Projective.Algebra.RCB.Complete
import P256.Proofs.Projective.Algebra.RCB.Double
import P256.Proofs.Projective.Algebra.RCB.Nonzero

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

variable {R : Type} [Field R] [DecidableEq R]

theorem add_affine_nonzero (b x y u v : R)
    (noRoot : ∀ t : R, t * t * t - 3 * t + b ≠ 0)
    (h8 : (8 : R) ≠ 0)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b) :
    nonzero (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩) := by
  by_cases hxu : x = u
  · subst u
    have hy : y ≠ 0 := by
      intro h
      apply noRoot x
      grind only
    have hc : onCurve b (⟨x, y, 1⟩ : Coordinates R) := by
      simpa only [onCurve, Semiring.mul_one] using hl
    have hn : nonzero (⟨x, y, 1⟩ : Coordinates R) := Or.inr (Or.inl hy)
    have hdn := double_nonzero b _ hc hn h8 (fun _ => hy)
    have hv : v = y ∨ v = -y := by grind only
    rcases hv with hv | hv
    · subst v
      rw [← double_eq_add b _ hc]
      exact hdn
    · subst v
      change nonzero (add b ⟨x, y, 1⟩ (negate ⟨x, y, 1⟩))
      rw [add_negate]
      apply Or.inr ∘ Or.inl
      simp only [scale, Semiring.mul_one]
      exact y_ne_zero b noRoot _ (double_onCurve b _ hc) hdn
  · exact add_distinct_nonzero b x y u v noRoot hl hr hxu

theorem add_distinct_toAffine (b x y u v : R)
    (noRoot : ∀ t : R, t * t * t - 3 * t + b ≠ 0)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b)
    (hxu : x ≠ u) :
    toAffine (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩) =
      Affine.add (-3) (.affine x y) (.affine u v) := by
  have hn := add_distinct_nonzero b x y u v noRoot hl hr hxu
  have hp := add_distinct_proportional b x y u v hl hr hxu
  have hx := hp.1
  have hy := hp.2
  have hz : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).z ≠ 0 := by
    intro hz
    rcases hn with hn | hn | hn
    · apply hn
      rw [hx, hz, Semiring.zero_mul]
    · apply hn
      rw [hy, hz, Semiring.zero_mul]
    · exact hn hz
  have hi := Field.mul_inv_cancel hz
  simp only [toAffine, hz, ite_false, Affine.add, hxu, false_and, Field.div_eq_mul_inv]
  congr 1
  · rw [hx]
    simp only [Field.div_eq_mul_inv] at *
    clear noRoot hl hr hn hp hy
    grind only
  · rw [hy]
    simp only [Field.div_eq_mul_inv] at *
    clear noRoot hl hr hn hp hx
    grind only

theorem add_affine_toAffine (b x y u v : R)
    (noRoot : ∀ t : R, t * t * t - 3 * t + b ≠ 0)
    (h8 : (8 : R) ≠ 0)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b) :
    toAffine (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩) =
      Affine.add (-3) (.affine x y) (.affine u v) := by
  by_cases hxu : x = u
  · subst u
    by_cases hyv : y + v = 0
    · have hv : v = -y := by grind only
      subst v
      change toAffine (add b ⟨x, y, 1⟩ (negate ⟨x, y, 1⟩)) = _
      rw [add_negate]
      simp [toAffine, scale, Affine.add, hyv, Semiring.mul_zero]
    · have hv : v = y := by grind only
      subst v
      have hy : y ≠ 0 := by
        intro h
        apply noRoot x
        grind only
      have hc : onCurve b (⟨x, y, 1⟩ : Coordinates R) := by
        simpa only [onCurve, Semiring.mul_one] using hl
      rw [← double_eq_add b _ hc]
      exact double_affine b x y hl hy h8
  · exact add_distinct_toAffine b x y u v noRoot hl hr hxu

end P256.Proofs.Projective.RCB
