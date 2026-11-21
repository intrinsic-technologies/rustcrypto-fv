import P256.Proofs.Projective.Multiply.Group.Base
import P256.Proofs.Projective.Multiply.Group.Concrete
import P256.Proofs.Projective.Multiply.Group.Associativity

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Group

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Algebra

theorem p256_add_laws : CurveAddLaws domain := by
  refine ⟨p256_add_closed, ?_⟩
  intro p q r hp hq hr
  have hpq := p256_add_closed p q hp hq
  have hqr := p256_add_closed q r hq hr
  have hleft := p256_add_closed (Curve.add domain p q) r hpq hr
  have hright := p256_add_closed p (Curve.add domain q r) hp hqr
  have he : encodePoint (Curve.add domain (Curve.add domain p q) r) =
      encodePoint (Curve.add domain p (Curve.add domain q r)) := by
    rw [encode_add _ r hpq hr, encode_add p _ hp hqr,
      encode_add p q hp hq, encode_add q r hq hr]
    exact Affine.add_assoc _ _ p256_two_ne_zero p256_cubic_ne_zero _ _ _
      (encode_onCurve p hp) (encode_onCurve q hq) (encode_onCurve r hr)
  exact (decode_encode _ hleft).symm.trans ((congrArg decodePoint he).trans (decode_encode _ hright))

end P256.Proofs.Projective.Multiply.Group
