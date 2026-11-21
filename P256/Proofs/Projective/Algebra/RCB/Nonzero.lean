import P256.Proofs.Projective.Algebra.RCB.Affine

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

theorem y_ne_zero {R : Type} [Field R] [DecidableEq R] (b : R)
    (noRoot : ∀ x : R, x * x * x - 3 * x + b ≠ 0)
    (point : Coordinates R) (hc : onCurve b point) (hn : nonzero point) : point.y ≠ 0 := by
  by_cases hz : point.z = 0
  · exact nonzero_y_of_z_zero b point hc hn hz
  · intro hy
    have he := (onCurve_toAffine b point hz).mp hc
    simp only [toAffine, hz, ite_false, Affine.onCurve, Field.div_eq_mul_inv] at he
    apply noRoot (point.x / point.z)
    simp only [Field.div_eq_mul_inv]
    grind only


end P256.Proofs.Projective.RCB
