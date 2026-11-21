import K256.Proofs.Generate.Curve.Group.Affine
import K256.Proofs.Generate.Curve.Group.Polynomial

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group.Affine

open Lean.Grind

theorem add_onCurve {F : Type} [Field F] [DecidableEq F] (a b : F)
    (p q : Point F) (hp : onCurve a b p) (hq : onCurve a b q) :
    onCurve a b (add a p q) := by
  cases p with
  | infinity => exact hq
  | affine x₁ y₁ =>
    cases q with
    | infinity => exact hp
    | affine x₂ y₂ =>
      simp only [onCurve] at hp hq
      simp only [add]
      split
      · trivial
      · rename_i hnot
        by_cases hx : x₁ = x₂
        · subst x₂
          have hy : y₁ = y₂ := (square_eq_square_cases y₁ y₂ (hp.trans hq.symm)).resolve_right
            (fun hsum => hnot ⟨rfl, hsum⟩)
          subst y₂
          have hden : 2 * y₁ ≠ 0 := by
            intro hz
            apply hnot
            exact ⟨rfl, by grind⟩
          simp only [ite_true, onCurve]
          exact tangent_onCurve a b x₁ y₁ _ hp (Field.div_mul_cancel hden)
        · simp only [hx, ite_false, onCurve]
          have hden : x₂ - x₁ ≠ 0 := by
            intro hz
            apply hx
            grind
          exact chord_onCurve a b x₁ y₁ x₂ y₂ _ hp hq hden (Field.div_mul_cancel hden)

theorem neg_onCurve {F : Type} [Field F] (a b : F) (p : Point F)
    (hp : onCurve a b p) : onCurve a b (neg p) := by
  cases p with
  | infinity => trivial
  | affine x y =>
    simp only [onCurve, neg] at *
    grind

theorem neg_neg {F : Type} [Field F] (p : Point F) : neg (neg p) = p := by
  cases p with
  | infinity => rfl
  | affine x y => simp only [neg, AddCommGroup.neg_neg]

theorem add_neg_cancel {F : Type} [Field F] [DecidableEq F] (a : F) (p : Point F) :
    add a p (neg p) = .infinity := by
  cases p with
  | infinity => rfl
  | affine x y =>
    simp only [neg, add]
    rw [ite_eq_left ⟨True.intro, by grind⟩]

theorem neg_add_cancel {F : Type} [Field F] [DecidableEq F] (a : F) (p : Point F) :
    add a (neg p) p = .infinity := by
  cases p with
  | infinity => rfl
  | affine x y =>
    simp only [neg, add]
    rw [ite_eq_left ⟨True.intro, by grind⟩]

theorem add_comm {F : Type} [Field F] [DecidableEq F] (a b : F)
    (p q : Point F) (hp : onCurve a b p) (hq : onCurve a b q) :
    add a p q = add a q p := by
  cases p with
  | infinity => exact (add_infinity a q).symm
  | affine x₁ y₁ =>
    cases q with
    | infinity => rfl
    | affine x₂ y₂ =>
      by_cases hx : x₁ = x₂
      · subst x₂
        by_cases hy : y₁ + y₂ = 0
        · have hy' : y₂ + y₁ = 0 := by grind
          simp [add, hy, hy']
        · have hsame : y₁ = y₂ :=
            (square_eq_square_cases y₁ y₂ (hp.trans hq.symm)).resolve_right hy
          subst y₂
          rfl
      · have hden : x₂ - x₁ ≠ 0 := by grind
        have hslope := Field.div_mul_cancel (x := y₂ - y₁) hden
        have hreverse : (y₂ - y₁) / (x₂ - x₁) = (y₁ - y₂) / (x₁ - x₂) := by
          have hdx : x₁ - x₂ = -(x₂ - x₁) := by grind
          simp only [Field.div_eq_mul_inv, hdx, Field.inv_neg]
          grind
        simp only [add, hx, Ne.symm hx, false_and, ite_false, ← hreverse]
        congr 1 <;> grind

end K256.Proofs.Generate.Curve.Group.Affine
