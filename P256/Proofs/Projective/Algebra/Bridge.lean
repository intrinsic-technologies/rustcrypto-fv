import P256.Proofs.Projective.Algebra.Coordinates

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

theorem encode_toAffine (point : Projective) (hc : point.canonical) :
    encodePoint point.toAffine = RCB.toAffine point.coordinates := by
  have hz : (point.z : Fp) = 0 ↔ point.z = 0 :=
    IsCharP.natCast_eq_zero_iff_of_lt domain.p hc.2.2
  by_cases hzero : point.z = 0
  · simp [toAffine, RCB.toAffine, coordinates, encodePoint, hzero, Semiring.natCast_zero]
  · simp only [toAffine, hzero, ite_false, RCB.toAffine, coordinates, hz,
      encodePoint, cast_mod, Semiring.natCast_mul, cast_inverse, Field.div_eq_mul_inv]

theorem decode_toAffine (point : Projective) (hc : point.canonical) :
    decodePoint (RCB.toAffine point.coordinates) = point.toAffine := by
  rw [← encode_toAffine point hc]
  by_cases hz : point.z = 0
  · simp [toAffine, hz, encodePoint, decodePoint]
  · simp only [toAffine, hz, ite_false, encodePoint, decodePoint,
      Curve.Point.affine.injEq]
    exact ⟨Nat.mod_mod _ _, Nat.mod_mod _ _⟩

theorem toAffine_onCurve (point : Projective) (h : point.valid) :
    Curve.onCurve domain point.toAffine = true := by
  have hv := (valid_iff point).mp h
  rw [← decode_toAffine point hv.1]
  apply decode_onCurve
  rw [coefficient_a]
  by_cases hz : point.coordinates.z = 0
  · simp [RCB.toAffine, hz, Affine.onCurve]
  · exact (RCB.onCurve_toAffine _ point.coordinates hz).mp hv.2.2

end P256.Proofs.Projective
