import P256.Proofs.Projective.Multiply.Algebra
import P256.Proofs.Projective.Multiply.Group.Scalar
import P256.Proofs.Projective.Multiply.Group.PointLaws

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ScalarMul

open P256.Spec.Operations (domain)
open Algebra
open Standards.SECG.ECC Group

theorem add_negate_toAffine (point : Projective) (h : point.valid) :
    Curve.add domain point.toAffine point.negate.toAffine = .infinity := by
  have hp := Projective.toAffine_onCurve point h
  have hn := Projective.toAffine_onCurve point.negate (Projective.negate_valid point h)
  rw [← decode_encode_add _ _ hp hn, encode_add _ _ hp hn,
    Projective.encode_toAffine_negate point h.1, Affine.add_neg_cancel]
  rfl

theorem add_multiple_toAffine (laws : CurveAddLaws domain)
    (base : Curve.Point) (hb : Curve.onCurve domain base = true)
    (left right : Projective) (hl : left.valid) (hr : right.valid) (m n : Nat)
    (hleft : left.toAffine = multiple domain base m)
    (hright : right.toAffine = multiple domain base n) :
    (left.add right).toAffine = multiple domain base (m + n) := by
  rw [Projective.add_toAffine left right hl hr, P256.Spec.Points.add, hleft, hright,
    ← multiple_add domain laws base hb]

theorem add_negate_multiple_toAffine (laws : CurveAddLaws domain)
    (base : Curve.Point) (hb : Curve.onCurve domain base = true)
    (left right : Projective) (hl : left.valid) (hr : right.valid) (m n : Nat) (hle : n ≤ m)
    (hleft : left.toAffine = multiple domain base m)
    (hright : right.toAffine = multiple domain base n) :
    (left.add right.negate).toAffine = multiple domain base (m - n) := by
  have hsub := multiple_onCurve domain laws base hb (m - n)
  have hn := Projective.toAffine_onCurve right hr
  have hneg := Projective.toAffine_onCurve right.negate (Projective.negate_valid right hr)
  rw [Projective.add_toAffine left right.negate hl (Projective.negate_valid right hr),
    P256.Spec.Points.add, hleft]
  have hm : multiple domain base m =
      Curve.add domain (multiple domain base (m - n)) right.toAffine := by
    rw [hright, ← multiple_add domain laws base hb, Nat.sub_add_cancel hle]
  rw [hm, laws.assoc _ _ _ hsub hn hneg, add_negate_toAffine right hr]
  cases multiple domain base (m - n) <;> rfl

theorem double_multiple_toAffine (laws : CurveAddLaws domain)
    (base : Curve.Point) (hb : Curve.onCurve domain base = true)
    (point : Projective) (hpoint : point.valid) (n : Nat)
    (heq : point.toAffine = multiple domain base n) :
    point.double.toAffine = multiple domain base (2 * n) := by
  rw [Projective.double_toAffine point hpoint, heq,
    ← multiple_add domain laws base hb, Nat.two_mul]

end P256.Proofs.Projective.Multiply.ScalarMul
