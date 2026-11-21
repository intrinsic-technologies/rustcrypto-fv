import P256.Proofs.ProjectiveWrapper.Model
import P256.Proofs.Projective.Multiply.Correct
import P256.Spec.Ecdh

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open Standards.SECG.ECC P256.Spec.Operations

theorem model_sharedX {point : Curve.Point} {d : Nat}
    (curve : Curve.onCurve domain point = true) (bound : d < 2^256) :
    P256.Spec.Points.xBytes
      (Projective.Multiply.model (ProjectiveWrapper.Decode.projective point) d).toAffine =
      P256.Spec.Ecdh.sharedX d point := by
  have valid := ProjectiveWrapper.projective_valid point curve
  rw [(Projective.Multiply.model_correct _ valid d bound).2,
    ProjectiveWrapper.projective_toAffine point valid.1]
  rfl

end P256.Proofs.Ecdh
