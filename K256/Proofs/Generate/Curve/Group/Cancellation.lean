import K256.Proofs.Generate.Curve.Group.PointLaws

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group.Affine

open Lean.Grind

theorem reverse_add {F : Type} [Field F] [DecidableEq F]
    (a x₁ y₁ x₂ y₂ slope : F) (hy : 2 * y₁ ≠ 0)
    (hslope : slope * (x₂ - x₁) = y₂ - y₁)
    (hquad : slope * slope * (x₂ - x₁) + 2 * slope * y₁ =
      x₂ * x₂ + x₂ * x₁ + x₁ * x₁ + a) :
    let x₃ := slope * slope - x₁ - x₂
    let y₃ := slope * (x₁ - x₃) - y₁
    add a (.affine x₁ (-y₁)) (.affine x₃ y₃) = .affine x₂ y₂ := by
  dsimp only
  have hnot : ¬(x₁ = slope * slope - x₁ - x₂ ∧
      -y₁ + (slope * (x₁ - (slope * slope - x₁ - x₂)) - y₁) = 0) := by
    intro hz
    apply hy
    grind
  have hreverse :
      (if x₁ = slope * slope - x₁ - x₂ then (3 * x₁ * x₁ + a) / (2 * -y₁)
        else ((slope * (x₁ - (slope * slope - x₁ - x₂)) - y₁) - -y₁) /
          ((slope * slope - x₁ - x₂) - x₁)) = -slope := by
    split
    · rename_i hx
      have hden : 2 * -y₁ ≠ 0 := by grind
      have hc := Field.div_mul_cancel (x := 3 * x₁ * x₁ + a) hden
      have hz : ((3 * x₁ * x₁ + a) / (2 * -y₁) + slope) * (2 * -y₁) = 0 := by grind
      have hq := (Field.of_mul_eq_zero hz).resolve_right hden
      grind
    · rename_i hx
      have hden : ((slope * slope - x₁ - x₂) - x₁) ≠ 0 := by grind
      have hc := Field.div_mul_cancel
        (x := (slope * (x₁ - (slope * slope - x₁ - x₂)) - y₁) - -y₁) hden
      have hz : (((slope * (x₁ - (slope * slope - x₁ - x₂)) - y₁) - -y₁) /
          ((slope * slope - x₁ - x₂) - x₁) + slope) *
          ((slope * slope - x₁ - x₂) - x₁) = 0 := by grind
      have hq := (Field.of_mul_eq_zero hz).resolve_right hden
      grind
  simp only [add, hnot, ite_false, hreverse]
  congr 1 <;> grind

theorem neg_add_cancel_left {F : Type} [Field F] [DecidableEq F] (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q : Point F) (hp : onCurve a b p) (hq : onCurve a b q) :
    add a (neg p) (add a p q) = q := by
  cases p with
  | infinity => rfl
  | affine x₁ y₁ =>
    cases q with
    | infinity => exact neg_add_cancel a (.affine x₁ y₁)
    | affine x₂ y₂ =>
      have hy₁ : y₁ ≠ 0 := by
        intro hz
        have := hnozero x₁
        simp only [onCurve] at hp
        grind
      have hden : 2 * y₁ ≠ 0 := by
        intro hz
        exact (Field.of_mul_eq_zero hz).elim h2 hy₁
      by_cases hzero : x₁ = x₂ ∧ y₁ + y₂ = 0
      · have hsum : add a (.affine x₁ y₁) (.affine x₂ y₂) = .infinity := by
          exact ite_eq_left hzero
        rw [hsum]
        simp only [neg, add]
        congr 1 <;> grind
      · by_cases hx : x₁ = x₂
        · subst x₂
          have hy : y₁ = y₂ := (square_eq_square_cases y₁ y₂ (hp.trans hq.symm)).resolve_right
            (fun hsum => hzero ⟨rfl, hsum⟩)
          subst y₂
          have hsum : add a (.affine x₁ y₁) (.affine x₁ y₁) =
              .affine (((3*x₁*x₁+a)/(2*y₁))*((3*x₁*x₁+a)/(2*y₁))-x₁-x₁)
                (((3*x₁*x₁+a)/(2*y₁))*(x₁-(((3*x₁*x₁+a)/(2*y₁))*
                  ((3*x₁*x₁+a)/(2*y₁))-x₁-x₁))-y₁) := by
            have hsum : y₁ + y₁ ≠ 0 := fun h => hzero ⟨rfl, h⟩
            simp only [add, true_and, hsum, ite_false, ite_true]
          rw [hsum]
          apply reverse_add a x₁ y₁ x₁ y₁ _ hden
          · grind
          · have hc := Field.div_mul_cancel (x := 3 * x₁ * x₁ + a) hden
            grind
        · have hden' : x₂ - x₁ ≠ 0 := by grind
          have hsum : add a (.affine x₁ y₁) (.affine x₂ y₂) =
              .affine (((y₂-y₁)/(x₂-x₁))*((y₂-y₁)/(x₂-x₁))-x₁-x₂)
                (((y₂-y₁)/(x₂-x₁))*(x₁-(((y₂-y₁)/(x₂-x₁))*
                  ((y₂-y₁)/(x₂-x₁))-x₁-x₂))-y₁) := by
            simp only [add, hx, false_and, ite_false]
          rw [hsum]
          apply reverse_add a x₁ y₁ x₂ y₂ _ hden
          · exact Field.div_mul_cancel hden'
          · exact chord_slope_condition a b x₁ y₁ x₂ y₂ _ hp hq hden'
              (Field.div_mul_cancel hden')

theorem add_neg_cancel_left {F : Type} [Field F] [DecidableEq F] (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q : Point F) (hp : onCurve a b p) (hq : onCurve a b q) :
    add a p (add a (neg p) q) = q := by
  have h := neg_add_cancel_left a b h2 hnozero (neg p) q (neg_onCurve a b p hp) hq
  simpa only [neg_neg] using h

theorem add_left_cancel {F : Type} [Field F] [DecidableEq F] (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hq : onCurve a b q) (hr : onCurve a b r)
    (h : add a p q = add a p r) : q = r := by
  have h' := congrArg (add a (neg p)) h
  simpa only [neg_add_cancel_left a b h2 hnozero p q hp hq,
    neg_add_cancel_left a b h2 hnozero p r hp hr] using h'

theorem add_right_cancel {F : Type} [Field F] [DecidableEq F] (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hq : onCurve a b q) (hr : onCurve a b r)
    (h : add a q p = add a r p) : q = r := by
  apply add_left_cancel a b h2 hnozero p q r hp hq hr
  rw [add_comm a b p q hp hq, add_comm a b p r hp hr]
  exact h

end K256.Proofs.Generate.Curve.Group.Affine
