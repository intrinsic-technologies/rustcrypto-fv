import P256.Proofs.Projective.Multiply.Group.Associativity.Double
import P256.Proofs.Projective.Multiply.Group.Associativity.Secant

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

open Lean.Grind

variable {F : Type} [Field F] [DecidableEq F]

theorem add_assoc (a b : F) (h2 : (2 : F) ≠ 0)
    (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hq : onCurve a b q) (hr : onCurve a b r) :
    add a (add a p q) r = add a p (add a q r) := by
  by_cases hpq : add a p q = .infinity
  · exact add_assoc_zero_left a b h2 hnozero p q r hp hr hpq
  by_cases hqr : add a q r = .infinity
  · apply assoc_reverse a b p q r hp hq hr
    apply add_assoc_zero_left a b h2 hnozero r q p hr hp
    rwa [add_comm a b r q hr hq]
  by_cases hleft : add a (add a p q) r = .infinity
  · exact add_assoc_zero_sum_left a b h2 hnozero p q r hp hq hleft
  by_cases hright : add a p (add a q r) = .infinity
  · apply assoc_reverse a b p q r hp hq hr
    apply add_assoc_zero_sum_left a b h2 hnozero r q p hr hq
    rwa [add_comm a b r q hr hq,
      add_comm a b (add a q r) p (add_onCurve a b q r hq hr) hp]
  cases p with
  | infinity => rfl
  | affine x₁ y₁ =>
    cases q with
    | infinity => simp only [add_infinity, infinity_add]
    | affine x₂ y₂ =>
      cases r with
      | infinity => simp only [add_infinity]
      | affine x₃ y₃ =>
        by_cases hx₁₂ : x₁ = x₂
        · subst x₂
          have hy₁₂ := same_x_of_add_ne_infinity a b x₁ y₁ y₂ hp hq hpq
          subst y₂
          by_cases hx₁₃ : x₁ = x₃
          · subst x₃
            have hy₁₃ := same_x_of_add_ne_infinity a b x₁ y₁ y₃ hp hr hqr
            subst y₃
            exact add_comm a b _ _ (add_onCurve a b _ _ hp hp) hp
          · exact add_assoc_double_finite a b x₁ y₁ x₃ y₃ h2 hnozero hp hr hx₁₃ hleft hright
        · by_cases hx₂₃ : x₂ = x₃
          · subst x₃
            have hy₂₃ := same_x_of_add_ne_infinity a b x₂ y₂ y₃ hq hr hqr
            subst y₃
            apply assoc_reverse a b _ _ _ hp hq hq
            apply add_assoc_double_finite a b x₂ y₂ x₁ y₁ h2 hnozero hq hp (Ne.symm hx₁₂)
            · rwa [add_comm a b _ _ (add_onCurve a b _ _ hq hq) hp]
            · rwa [add_comm a b (.affine x₂ y₂) (.affine x₁ y₁) hq hp,
                add_comm a b (.affine x₂ y₂) _ hq (add_onCurve a b _ _ hp hq)]
          · exact add_assoc_secants_finite a b x₁ y₁ x₂ y₂ x₃ y₃
              h2 hnozero hp hq hr hx₁₂ hx₂₃ hleft hright

end P256.Proofs.Projective.Affine
