import P256.Proofs.Projective.Algebra.RCB.Ring
import P256.Proofs.Projective.Algebra.RCB.Point

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

variable {R : Type} [Field R] [DecidableEq R]

def toAffine (point : Coordinates R) : Affine.Point R :=
  if point.z = 0 then .infinity else .affine (point.x / point.z) (point.y / point.z)

theorem toAffine_eq_infinity_iff (point : Coordinates R) :
    toAffine point = .infinity ↔ point.z = 0 := by
  simp only [toAffine]
  split <;> simp_all

theorem toAffine_scale (point : Coordinates R) (s : R) (hs : s ≠ 0) :
    toAffine (scale s point) = toAffine point := by
  have hs1 := Field.mul_inv_cancel hs
  by_cases hz : point.z = 0
  · simp [toAffine, scale, hz, Semiring.mul_zero]
  · have hsz : s * point.z ≠ 0 := by
      intro h
      rcases Field.of_mul_eq_zero h with h | h <;> contradiction
    simp only [toAffine, scale, hz, hsz, ite_false]
    congr 1 <;> simp only [Field.div_eq_mul_inv, Field.inv_mul] <;> grind only

omit [DecidableEq R] in
theorem normalize (point : Coordinates R) (hz : point.z ≠ 0) :
    point = scale point.z ⟨point.x / point.z, point.y / point.z, 1⟩ := by
  have hz1 := Field.mul_inv_cancel hz
  apply Coordinates.ext <;> dsimp only [scale] <;>
    simp only [Field.div_eq_mul_inv, Semiring.mul_one] <;> grind only

theorem onCurve_toAffine (b : R) (point : Coordinates R) (hz : point.z ≠ 0) :
    onCurve b point ↔ Affine.onCurve (-3) b (toAffine point) := by
  have hz1 := Field.mul_inv_cancel hz
  simp only [toAffine, hz, ite_false, Affine.onCurve, onCurve, Field.div_eq_mul_inv]
  constructor <;> intro h <;> grind only

omit [DecidableEq R] in
theorem onCurve_x_of_z_zero (b : R) (point : Coordinates R)
    (h : onCurve b point) (hz : point.z = 0) : point.x = 0 := by
  have hx : point.x * point.x * point.x = 0 := by
    dsimp only [onCurve] at h
    grind only
  rcases Field.of_mul_eq_zero hx with hx | hx
  · rcases Field.of_mul_eq_zero hx with hx | hx <;> exact hx
  · exact hx

omit [DecidableEq R] in
theorem nonzero_y_of_z_zero (b : R) (point : Coordinates R)
    (h : onCurve b point) (hn : nonzero point) (hz : point.z = 0) : point.y ≠ 0 := by
  have hx := onCurve_x_of_z_zero b point h hz
  rcases hn with hn | hn | hn <;> simp_all

end P256.Proofs.Projective.RCB
