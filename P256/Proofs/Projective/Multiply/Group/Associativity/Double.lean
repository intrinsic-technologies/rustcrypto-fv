import P256.Proofs.Projective.Multiply.Group.Associativity.Geometry
import P256.Proofs.Projective.Multiply.Group.Associativity.Algebra

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

open Lean.Grind

variable {F : Type} [Field F] [DecidableEq F]

theorem add_assoc_double_finite (a b x y u v : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (hp : onCurve a b (.affine x y)) (hr : onCurve a b (.affine u v))
    (hx : x ≠ u)
    (hleft : add a (add a (.affine x y) (.affine x y)) (.affine u v) ≠ .infinity)
    (hright : add a (.affine x y) (add a (.affine x y) (.affine u v)) ≠ .infinity) :
    add a (add a (.affine x y) (.affine x y)) (.affine u v) =
      add a (.affine x y) (add a (.affine x y) (.affine u v)) := by
  let l := (3 * x * x + a) / (2 * y)
  let m := (v - y) / (u - x)
  have hd := affine_double_den a b x y h2 hnozero hp
  have hdu := affine_double_den a b u v h2 hnozero hr
  have hny : y + y ≠ 0 := by grind only
  have hdouble : add a (.affine x y) (.affine x y) =
      .affine (l * l - x - x) (l * (x - (l * l - x - x)) - y) := by
    simp only [add, hny, true_and, ite_true, ite_false, l]
  have hsecant : add a (.affine x y) (.affine u v) =
      .affine (m * m - x - u) (m * (x - (m * m - x - u)) - y) := by
    simp only [add, hx, false_and, ite_false, m]
  have hR : m * m - x - u ≠ x := second_sum_x_ne a b x y _ _ h2 hnozero
    (.affine u v) hp hr (by intro h; cases h) hsecant (hsecant ▸ hright)
  have hRp : ((v - y) / (u - x)) ^ 2 - x - u ≠ x := by
    simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hR
  by_cases hL : l * l - x - x = u
  · have hcurve := add_onCurve a b (.affine x y) (.affine x y) hp hp
    rw [hdouble, hL] at hcurve hleft
    have hy : l * (x - u) - y = v :=
      same_x_of_add_ne_infinity a b u _ v hcurve hr hleft
    have he : add a (.affine x y) (.affine x y) = .affine u v := by rw [hdouble, hL, hy]
    exact add_assoc_double_double_left a x y u v hx he hd hdu hRp
  · apply add_assoc_double_secant a b x y u v hp hr hd hx _ hRp
    simpa only [Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul] using hL

end P256.Proofs.Projective.Affine
