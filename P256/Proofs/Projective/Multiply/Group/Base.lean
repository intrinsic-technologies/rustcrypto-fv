import P256.Spec.Points

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Group

open Standards.SECG.ECC

structure CurveAddLaws (domain : Curve.Domain) : Prop where
  closed : ∀ p q, Curve.onCurve domain p = true → Curve.onCurve domain q = true →
    Curve.onCurve domain (Curve.add domain p q) = true
  assoc : ∀ p q r, Curve.onCurve domain p = true → Curve.onCurve domain q = true →
    Curve.onCurve domain r = true →
    Curve.add domain (Curve.add domain p q) r = Curve.add domain p (Curve.add domain q r)

def multiple (domain : Curve.Domain) (point : Curve.Point) : Nat → Curve.Point
  | 0 => .infinity
  | n + 1 => Curve.add domain (multiple domain point n) point

end P256.Proofs.Projective.Multiply.Group
