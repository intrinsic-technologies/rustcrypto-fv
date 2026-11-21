import P256.Proofs.Projective.Multiply.Group.Neg
import P256.Proofs.Projective.Multiply.Group.PointLaws

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

open Lean.Grind

variable {F : Type} [Field F] [DecidableEq F]

theorem add_assoc_secant (a b x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hp : onCurve a b (.affine x₁ y₁))
    (hq : onCurve a b (.affine x₂ y₂))
    (hr : onCurve a b (.affine x₃ y₃))
    (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (hleft : ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - x₁ - x₂ ≠ x₃)
    (hright : ((y₃ - y₂) / (x₃ - x₂)) ^ 2 - x₂ - x₃ ≠ x₁) :
    add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₂ y₂) (.affine x₃ y₃)) := by
  let l := (y₂ - y₁) / (x₂ - x₁)
  let m := (y₃ - y₂) / (x₃ - x₂)
  have hl : l * (x₂ - x₁) = y₂ - y₁ := Field.div_mul_cancel (by grind)
  have hm : m * (x₃ - x₂) = y₃ - y₂ := Field.div_mul_cancel (by grind)
  have hL : l * l - x₁ - x₂ ≠ x₃ := by
    simpa only [l, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hleft
  have hR : m * m - x₂ - x₃ ≠ x₁ := by
    simpa only [m, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hright
  simp only [add, h₁₂, h₂₃, false_and, ite_false]
  dsimp only [l, m] at hL hR
  simp only [hL, Ne.symm hR, false_and, ite_false]
  let s := (y₃ - (l * (x₁ - (l * l - x₁ - x₂)) - y₁)) /
    (x₃ - (l * l - x₁ - x₂))
  let t := ((m * (x₂ - (m * m - x₂ - x₃)) - y₂) - y₁) /
    ((m * m - x₂ - x₃) - x₁)
  have hs : s * (x₃ - (l * l - x₁ - x₂)) =
      y₃ - (l * (x₁ - (l * l - x₁ - x₂)) - y₁) :=
    Field.div_mul_cancel (by grind)
  have ht : t * ((m * m - x₂ - x₃) - x₁) =
      (m * (x₂ - (m * m - x₂ - x₃)) - y₂) - y₁ :=
    Field.div_mul_cancel (by grind)
  change Point.affine (s * s - (l * l - x₁ - x₂) - x₃)
      (s * ((l * l - x₁ - x₂) - (s * s - (l * l - x₁ - x₂) - x₃)) -
        (l * (x₁ - (l * l - x₁ - x₂)) - y₁)) =
    Point.affine (t * t - x₁ - (m * m - x₂ - x₃))
      (t * (x₁ - (t * t - x₁ - (m * m - x₂ - x₃))) - y₁)
  simp only [onCurve] at hp hq hr
  change l * l - x₁ - x₂ ≠ x₃ at hL
  change m * m - x₂ - x₃ ≠ x₁ at hR
  clear hleft hright
  clear_value s t l m
  congr 1 <;> grind only

theorem add_assoc_double_secant (a b x₁ y₁ x₃ y₃ : F)
    (hp : onCurve a b (.affine x₁ y₁)) (hr : onCurve a b (.affine x₃ y₃))
    (hdouble : 2 * y₁ ≠ 0) (h₁₃ : x₁ ≠ x₃)
    (hleft : ((3 * x₁ * x₁ + a) / (2 * y₁)) ^ 2 - x₁ - x₁ ≠ x₃)
    (hright : ((y₃ - y₁) / (x₃ - x₁)) ^ 2 - x₁ - x₃ ≠ x₁) :
    add a (add a (.affine x₁ y₁) (.affine x₁ y₁)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₁ y₁) (.affine x₃ y₃)) := by
  let l := (3 * x₁ * x₁ + a) / (2 * y₁)
  let m := (y₃ - y₁) / (x₃ - x₁)
  have hl : l * (2 * y₁) = 3 * x₁ * x₁ + a := Field.div_mul_cancel hdouble
  have hm : m * (x₃ - x₁) = y₃ - y₁ := Field.div_mul_cancel (by grind)
  have hny : y₁ + y₁ ≠ 0 := by grind only
  have hL : l * l - x₁ - x₁ ≠ x₃ := by
    simpa only [l, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hleft
  have hR : m * m - x₁ - x₃ ≠ x₁ := by
    simpa only [m, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hright
  simp only [add, hny, h₁₃, false_and, true_and, ite_false, ite_true]
  dsimp only [l, m] at hL hR
  simp only [hL, Ne.symm hR, false_and, ite_false]
  let s := (y₃ - (l * (x₁ - (l * l - x₁ - x₁)) - y₁)) /
    (x₃ - (l * l - x₁ - x₁))
  let t := ((m * (x₁ - (m * m - x₁ - x₃)) - y₁) - y₁) /
    ((m * m - x₁ - x₃) - x₁)
  have hs : s * (x₃ - (l * l - x₁ - x₁)) =
      y₃ - (l * (x₁ - (l * l - x₁ - x₁)) - y₁) := Field.div_mul_cancel (by grind)
  have ht : t * ((m * m - x₁ - x₃) - x₁) =
      (m * (x₁ - (m * m - x₁ - x₃)) - y₁) - y₁ := Field.div_mul_cancel (by grind)
  change Point.affine (s * s - (l * l - x₁ - x₁) - x₃)
      (s * ((l * l - x₁ - x₁) - (s * s - (l * l - x₁ - x₁) - x₃)) -
        (l * (x₁ - (l * l - x₁ - x₁)) - y₁)) =
    Point.affine (t * t - x₁ - (m * m - x₁ - x₃))
      (t * (x₁ - (t * t - x₁ - (m * m - x₁ - x₃))) - y₁)
  simp only [onCurve] at hp hr
  change l * l - x₁ - x₁ ≠ x₃ at hL
  change m * m - x₁ - x₃ ≠ x₁ at hR
  clear hleft hright hny
  clear_value s t l m
  congr 1 <;> grind only

theorem add_assoc_secant_double_left (a b x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hp : onCurve a b (.affine x₁ y₁)) (hq : onCurve a b (.affine x₂ y₂))
    (h₁₂ : x₁ ≠ x₂) (h₂₃ : x₂ ≠ x₃)
    (hleft : add a (.affine x₁ y₁) (.affine x₂ y₂) = .affine x₃ y₃)
    (hdouble : 2 * y₃ ≠ 0)
    (hright : ((y₃ - y₂) / (x₃ - x₂)) ^ 2 - x₂ - x₃ ≠ x₁) :
    add a (add a (.affine x₁ y₁) (.affine x₂ y₂)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₂ y₂) (.affine x₃ y₃)) := by
  let l := (y₂ - y₁) / (x₂ - x₁)
  let m := (y₃ - y₂) / (x₃ - x₂)
  have hl : l * (x₂ - x₁) = y₂ - y₁ := Field.div_mul_cancel (by grind)
  have hm : m * (x₃ - x₂) = y₃ - y₂ := Field.div_mul_cancel (by grind)
  have hny : y₃ + y₃ ≠ 0 := by grind only
  have hR : m * m - x₂ - x₃ ≠ x₁ := by
    simpa only [m, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hright
  rw [hleft]
  have hxy : l * l - x₁ - x₂ = x₃ ∧ l * (x₁ - (l * l - x₁ - x₂)) - y₁ = y₃ := by
    simpa only [add, h₁₂, false_and, ite_false, Point.affine.injEq] using hleft
  clear hleft
  simp only [add, hny, h₂₃, false_and, true_and, ite_false, ite_true]
  dsimp only [m] at hR
  simp only [Ne.symm hR, false_and, ite_false]
  let s := (3 * x₃ * x₃ + a) / (2 * y₃)
  let t := ((m * (x₂ - (m * m - x₂ - x₃)) - y₂) - y₁) /
    ((m * m - x₂ - x₃) - x₁)
  have hs : s * (2 * y₃) = 3 * x₃ * x₃ + a := Field.div_mul_cancel hdouble
  have ht : t * ((m * m - x₂ - x₃) - x₁) =
      (m * (x₂ - (m * m - x₂ - x₃)) - y₂) - y₁ := Field.div_mul_cancel (by grind)
  change Point.affine (s * s - x₃ - x₃) (s * (x₃ - (s * s - x₃ - x₃)) - y₃) =
    Point.affine (t * t - x₁ - (m * m - x₂ - x₃))
      (t * (x₁ - (t * t - x₁ - (m * m - x₂ - x₃))) - y₁)
  simp only [onCurve] at hp hq
  change m * m - x₂ - x₃ ≠ x₁ at hR
  clear hright hny
  clear_value s t l m
  congr 1 <;> grind only

theorem add_assoc_double_double_left (a x₁ y₁ x₃ y₃ : F)
    (h₁₃ : x₁ ≠ x₃)
    (hleft : add a (.affine x₁ y₁) (.affine x₁ y₁) = .affine x₃ y₃)
    (hdouble₁ : 2 * y₁ ≠ 0) (hdouble₃ : 2 * y₃ ≠ 0)
    (hright : ((y₃ - y₁) / (x₃ - x₁)) ^ 2 - x₁ - x₃ ≠ x₁) :
    add a (add a (.affine x₁ y₁) (.affine x₁ y₁)) (.affine x₃ y₃) =
      add a (.affine x₁ y₁) (add a (.affine x₁ y₁) (.affine x₃ y₃)) := by
  let l := (3 * x₁ * x₁ + a) / (2 * y₁)
  let m := (y₃ - y₁) / (x₃ - x₁)
  have hl : l * (2 * y₁) = 3 * x₁ * x₁ + a := Field.div_mul_cancel hdouble₁
  have hm : m * (x₃ - x₁) = y₃ - y₁ := Field.div_mul_cancel (by grind)
  have hn₁ : y₁ + y₁ ≠ 0 := by grind only
  have hn₃ : y₃ + y₃ ≠ 0 := by grind only
  have hR : m * m - x₁ - x₃ ≠ x₁ := by
    simpa only [m, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hright
  rw [hleft]
  have hxy : l * l - x₁ - x₁ = x₃ ∧ l * (x₁ - (l * l - x₁ - x₁)) - y₁ = y₃ := by
    simpa only [add, hn₁, true_and, ite_false, ite_true, Point.affine.injEq] using hleft
  clear hleft
  simp only [add, hn₃, h₁₃, false_and, true_and, ite_false, ite_true]
  dsimp only [m] at hR
  simp only [Ne.symm hR, false_and, ite_false]
  let s := (3 * x₃ * x₃ + a) / (2 * y₃)
  let t := ((m * (x₁ - (m * m - x₁ - x₃)) - y₁) - y₁) /
    ((m * m - x₁ - x₃) - x₁)
  have hs : s * (2 * y₃) = 3 * x₃ * x₃ + a := Field.div_mul_cancel hdouble₃
  have ht : t * ((m * m - x₁ - x₃) - x₁) =
      (m * (x₁ - (m * m - x₁ - x₃)) - y₁) - y₁ := Field.div_mul_cancel (by grind)
  change Point.affine (s * s - x₃ - x₃) (s * (x₃ - (s * s - x₃ - x₃)) - y₃) =
    Point.affine (t * t - x₁ - (m * m - x₁ - x₃))
      (t * (x₁ - (t * t - x₁ - (m * m - x₁ - x₃))) - y₁)
  change m * m - x₁ - x₃ ≠ x₁ at hR
  clear hright hn₁ hn₃
  clear_value s t l m
  congr 1 <;> grind only

end P256.Proofs.Projective.Affine
