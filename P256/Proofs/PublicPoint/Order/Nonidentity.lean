import P256.Proofs.Projective.Multiply.Group.Scalar
import P256.Proofs.PublicPoint.Order.Period

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Order

open Standards.SECG.ECC P256.Proofs.Projective.Multiply.Group

theorem scalarMul_ne_infinity_of_prime_order (domain : Curve.Domain)
    (laws : CurveAddLaws domain) (point : Curve.Point)
    (honCurve : Curve.onCurve domain point = true) (hne : point ≠ .infinity)
    (hprime : P256.Proofs.Projective.Algebra.FieldArithmetic.IsPrime domain.n)
    (horder : Curve.scalarMul domain domain.n point = .infinity)
    (d : Nat) (hpos : 0 < d) (hlt : d < domain.n) :
    Curve.scalarMul domain d point ≠ .infinity := by
  rw [scalarMul_eq_multiple domain laws point honCurve]
  apply nonzero_of_prime_period (multiple domain point) .infinity domain.n hprime
  · rw [← scalarMul_eq_multiple domain laws point honCurve]
    exact horder
  · simpa only [multiple, Curve.add] using hne
  · intro m hm k
    rw [multiple_add domain laws point honCurve, hm]
    rfl
  · exact hpos
  · exact hlt

end P256.Proofs.PublicPoint.Order
