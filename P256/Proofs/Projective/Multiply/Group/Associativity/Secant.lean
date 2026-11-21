import P256.Proofs.Projective.Multiply.Group.Associativity.Geometry
import P256.Proofs.Projective.Multiply.Group.Associativity.Algebra

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

open Lean.Grind

variable {F : Type} [Field F] [DecidableEq F]

theorem add_assoc_secants_right (a b x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (hp : onCurve a b (.affine x₁ y₁)) (hq : onCurve a b (.affine x₂ y₂))
    (hr : onCurve a b (.affine x₃ y₃)) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (hleft : add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) ≠ .infinity)
    (hR : ((y₃ - y₂) / (x₃ - x₂)) ^ 2 - x₂ - x₃ ≠ x₁) :
    add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₂ y₂) (.affine x₃ y₃)) := by
  let l := (y₂ - y₁) / (x₂ - x₁)
  have hsum : add a (.affine x₁ y₁) (.affine x₂ y₂) =
      .affine (l * l - x₁ - x₂) (l * (x₁ - (l * l - x₁ - x₂)) - y₁) := by
    simp only [add, h₁₂, false_and, ite_false, l]
  by_cases hL : l * l - x₁ - x₂ = x₃
  · have hcurve := add_onCurve a b (.affine x₁ y₁) (.affine x₂ y₂) hp hq
    rw [hsum, hL] at hcurve hleft
    have hy := same_x_of_add_ne_infinity a b x₃ _ y₃ hcurve hr hleft
    have he : add a (.affine x₁ y₁) (.affine x₂ y₂) = .affine x₃ y₃ := by rw [hsum, hL, hy]
    exact add_assoc_secant_double_left a b x₁ y₁ x₂ y₂ x₃ y₃ hp hq h₁₂ h₂₃ he
      (affine_double_den a b x₃ y₃ h2 hnozero hr) hR
  · apply add_assoc_secant a b x₁ y₁ x₂ y₂ x₃ y₃ hp hq hr h₁₂ h₂₃ _ hR
    simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hL

theorem add_assoc_secants_finite (a b x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (hp : onCurve a b (.affine x₁ y₁)) (hq : onCurve a b (.affine x₂ y₂))
    (hr : onCurve a b (.affine x₃ y₃)) (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (hleft : add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) ≠ .infinity)
    (hright : add a (.affine x₁ y₁) (add a (.affine x₂ y₂) (.affine x₃ y₃)) ≠ .infinity) :
    add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₂ y₂) (.affine x₃ y₃)) := by
  let l := (y₂ - y₁) / (x₂ - x₁)
  let m := (y₃ - y₂) / (x₃ - x₂)
  have hsumL : add a (.affine x₁ y₁) (.affine x₂ y₂) =
      .affine (l * l - x₁ - x₂) (l * (x₁ - (l * l - x₁ - x₂)) - y₁) := by
    simp only [add, h₁₂, false_and, ite_false, l]
  have hsumR : add a (.affine x₂ y₂) (.affine x₃ y₃) =
      .affine (m * m - x₂ - x₃) (m * (x₂ - (m * m - x₂ - x₃)) - y₂) := by
    simp only [add, h₂₃, false_and, ite_false, m]
  by_cases hR : m * m - x₂ - x₃ = x₁
  · have hcurveR := add_onCurve a b (.affine x₂ y₂) (.affine x₃ y₃) hq hr
    rw [hsumR, hR] at hcurveR hright
    have hyR := same_x_of_add_ne_infinity a b x₁ y₁ _ hp hcurveR hright
    have heR : add a (.affine x₂ y₂) (.affine x₃ y₃) = .affine x₁ y₁ := by
      rw [hsumR, hR, hyR]
    have hL : l * l - x₁ - x₂ ≠ x₃ := by
      intro hx
      have hcurveL := add_onCurve a b (.affine x₁ y₁) (.affine x₂ y₂) hp hq
      rw [hsumL, hx] at hcurveL hleft
      have hyL := same_x_of_add_ne_infinity a b x₃ _ y₃ hcurveL hr hleft
      have heL : add a (.affine x₁ y₁) (.affine x₂ y₂) = .affine x₃ y₃ := by
        rw [hsumL, hx, hyL]
      exact add_exchange_impossible a b h2 hnozero _ _ _ hp hq hr
        (by intro h; cases h) heL heR
    apply assoc_reverse a b _ _ _ hp hq hr
    apply add_assoc_secants_right a b x₃ y₃ x₂ y₂ x₁ y₁ h2 hnozero hr hq hp
      (Ne.symm h₂₃) (Ne.symm h₁₂)
    · rw [add_comm a b (.affine x₃ y₃) (.affine x₂ y₂) hr hq,
        add_comm a b (add a (.affine x₂ y₂) (.affine x₃ y₃)) (.affine x₁ y₁)
          (add_onCurve a b _ _ hq hr) hp, heR]
      exact fun h => affine_double_den a b x₁ y₁ h2 hnozero hp (by
        have he := (add_eq_infinity_iff a (.affine x₁ y₁) (.affine x₁ y₁)).mp h
        have hy := (Point.affine.inj he).2
        grind only)
    · rw [← secant_x_swap x₁ y₁ x₂ y₂]
      simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hL
  · apply add_assoc_secants_right a b x₁ y₁ x₂ y₂ x₃ y₃ h2 hnozero hp hq hr h₁₂ h₂₃ hleft
    simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hR

end P256.Proofs.Projective.Affine
