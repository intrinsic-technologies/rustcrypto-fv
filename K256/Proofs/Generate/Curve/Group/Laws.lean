import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Generate.Curve.Group.Base
import K256.Proofs.Generate.Curve.Group.Concrete
import K256.Proofs.Generate.Curve.Group.Associativity

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem secp256k1_add_laws : CurveAddLaws domain := by
  refine ⟨secp256k1_add_closed, ?_⟩
  intro p q r hp hq hr
  have hpq := secp256k1_add_closed p q hp hq
  have hqr := secp256k1_add_closed q r hq hr
  have hleft := secp256k1_add_closed (Curve.add domain p q) r hpq hr
  have hright := secp256k1_add_closed p (Curve.add domain q r) hp hqr
  have he : encodePoint (Curve.add domain (Curve.add domain p q) r) =
      encodePoint (Curve.add domain p (Curve.add domain q r)) := by
    rw [encode_add _ r hpq hr, encode_add p _ hp hqr,
      encode_add p q hp hq, encode_add q r hq hr]
    exact Affine.add_assoc _ _ secp256k1_two_ne_zero secp256k1_cubic_ne_zero _ _ _
      (encode_onCurve p hp) (encode_onCurve q hq) (encode_onCurve r hr)
  exact (decode_encode _ hleft).symm.trans ((congrArg decodePoint he).trans (decode_encode _ hright))

end K256.Proofs.Generate.Curve.Group
