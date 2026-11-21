import Init.Grind.Ring.Field

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

open Lean.Grind

theorem square_eq_square_cases {F : Type} [Field F] (y₁ y₂ : F)
    (h : y₁ * y₁ = y₂ * y₂) : y₁ = y₂ ∨ y₁ + y₂ = 0 := by
  have hz : (y₁ - y₂) * (y₁ + y₂) = 0 := by grind
  rcases Field.of_mul_eq_zero hz with hdiff | hsum
  · left
    grind
  · exact Or.inr hsum

theorem tangent_onCurve {F : Type} [Field F] (a b x y slope : F)
    (hcurve : y * y = x * x * x + a * x + b)
    (hslope : slope * (2 * y) = 3 * x * x + a) :
    let x₃ := slope * slope - x - x
    let y₃ := slope * (x - x₃) - y
    y₃ * y₃ = x₃ * x₃ * x₃ + a * x₃ + b := by
  dsimp only
  grind

theorem chord_slope_condition {F : Type} [Field F] (a b x₁ y₁ x₂ y₂ slope : F)
    (hcurve₁ : y₁ * y₁ = x₁ * x₁ * x₁ + a * x₁ + b)
    (hcurve₂ : y₂ * y₂ = x₂ * x₂ * x₂ + a * x₂ + b)
    (hx : x₂ - x₁ ≠ 0) (hslope : slope * (x₂ - x₁) = y₂ - y₁) :
    slope * slope * (x₂ - x₁) + 2 * slope * y₁ =
      x₂ * x₂ + x₂ * x₁ + x₁ * x₁ + a := by
  have hproduct : (x₂ - x₁) *
      (slope * slope * (x₂ - x₁) + 2 * slope * y₁ -
        (x₂ * x₂ + x₂ * x₁ + x₁ * x₁ + a)) = 0 := by grind
  have hquotient := (Field.of_mul_eq_zero hproduct).resolve_left hx
  grind

theorem chord_onCurve {F : Type} [Field F] (a b x₁ y₁ x₂ y₂ slope : F)
    (hcurve₁ : y₁ * y₁ = x₁ * x₁ * x₁ + a * x₁ + b)
    (hcurve₂ : y₂ * y₂ = x₂ * x₂ * x₂ + a * x₂ + b)
    (hx : x₂ - x₁ ≠ 0) (hslope : slope * (x₂ - x₁) = y₂ - y₁) :
    let x₃ := slope * slope - x₁ - x₂
    let y₃ := slope * (x₁ - x₃) - y₁
    y₃ * y₃ = x₃ * x₃ * x₃ + a * x₃ + b := by
  have hquotient := chord_slope_condition a b x₁ y₁ x₂ y₂ slope
    hcurve₁ hcurve₂ hx hslope
  dsimp only
  grind

end P256.Proofs.Projective.Affine
