import P256.Spec.Points

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Order

open Standards.SECG.ECC P256.Spec.Operations

theorem generator_onCurve : Curve.onCurve domain domain.G = true := by
  decide +kernel

theorem scalarMul_order : Curve.scalarMul domain domain.n domain.G = .infinity := by
  decide +kernel

end P256.Proofs.PublicPoint.Order
