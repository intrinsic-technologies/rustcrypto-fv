import P256.Proofs.Projective.Algebra.RCB.Affine

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB
open Lean.Grind
variable {R : Type}

theorem double_onCurve [CommRing R] (b : R) (point : Coordinates R) (h : onCurve b point) :
    onCurve b (double b point) := by
  rw [double_eq_add b point h]
  exact add_onCurve b point point h h

variable [Field R]

theorem double_nonzero (b : R) (point : Coordinates R)
    (hc : onCurve b point) (hn : nonzero point)
    (h8 : (8 : R) ≠ 0) (hy : point.z ≠ 0 → point.y ≠ 0) :
    nonzero (double b point) := by
  by_cases hz : point.z = 0
  · have hx := onCurve_x_of_z_zero b point hc hz
    have hpy := nonzero_y_of_z_zero b point hc hn hz
    apply Or.inr ∘ Or.inl
    dsimp only [double]
    rw [hz, hx]
    grind only
  · apply Or.inr ∘ Or.inr
    have hpy := hy hz
    dsimp only [double]
    grind only

theorem double_affine (b x y : R) [DecidableEq R]
    (hc : y * y + 3 * x = x * x * x + b)
    (hy : y ≠ 0) (h8 : (8 : R) ≠ 0) :
    toAffine (double b ⟨x, y, 1⟩) =
      Affine.add (-3) (.affine x y) (.affine x y) := by
  have h2 : (2 : R) ≠ 0 := by grind only
  have hyy : y + y ≠ 0 := by grind only
  have hden : 4 * (2 * (y * 1) * (y * y)) ≠ 0 := by grind only
  have hden1 := Field.mul_inv_cancel hden
  have htwo1 := Field.mul_inv_cancel (show 2 * y ≠ 0 by grind only)
  simp only [toAffine, double, hden, Affine.add,
    hyy, and_false, Field.div_eq_mul_inv, ↓reduceIte]
  congr 1 <;> grind only

end P256.Proofs.Projective.RCB
