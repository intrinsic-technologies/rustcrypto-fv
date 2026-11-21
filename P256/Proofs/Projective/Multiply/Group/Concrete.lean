import P256.Proofs.Projective.Algebra
import P256.Proofs.Projective.Multiply.Group.PointLaws

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Group

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

theorem p256_add_closed (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) :
    Curve.onCurve domain (Curve.add domain p q) = true := by
  rw [← decode_encode_add p q hp hq, encode_add p q hp hq]
  apply decode_onCurve
  exact Affine.add_onCurve _ _ _ _ (encode_onCurve p hp) (encode_onCurve q hq)

theorem p256_cubic_ne_zero (x : Fp) :
    x * x * x + (domain.a : Fp) * x + (domain.b : Fp) ≠ 0 := by
  rw [coefficient_a]
  intro h
  apply cubic_ne_zero x
  grind only

theorem p256_two_ne_zero : (2 : Fp) ≠ 0 := by decide +kernel

end P256.Proofs.Projective.Multiply.Group
