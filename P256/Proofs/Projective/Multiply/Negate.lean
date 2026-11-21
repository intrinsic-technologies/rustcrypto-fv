import P256.Proofs.Projective.Multiply.Coordinates
import P256.Proofs.Projective.Multiply.Group.Neg

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

variable {R : Type} [Field R]

theorem negate_onCurve (b : R) (point : Coordinates R) (h : onCurve b point) :
    onCurve b (negate point) := by
  dsimp only [onCurve, negate] at *
  grind only

theorem negate_nonzero (point : Coordinates R) (h : nonzero point) :
    nonzero (negate point) := by
  dsimp only [nonzero, negate] at *
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by intro hn; apply h; grind only))
  · exact Or.inr (Or.inr h)

variable [DecidableEq R]

theorem toAffine_negate (point : Coordinates R) :
    toAffine (negate point) = Affine.neg (toAffine point) := by
  by_cases hz : point.z = 0
  · simp [toAffine, negate, hz, Affine.neg]
  · simp only [toAffine, negate, hz, ite_false, Affine.neg]
    congr 1
    simp only [Field.div_eq_mul_inv]
    grind only

end P256.Proofs.Projective.RCB
