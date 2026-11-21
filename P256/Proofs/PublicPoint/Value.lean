import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface
import P256.Proofs.Projective.Multiply.Correct

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open P256.Spec P256.Spec.Operations
open Projective.Multiply Projective.Multiply.Machine

theorem basePoint_valid : Basepoint.basePoint.valid := by
  unfold Projective.valid Projective.canonical
  decide +kernel

theorem basePoint_toAffine : Basepoint.basePoint.toAffine = domain.G := by decide +kernel

theorem model_toAffine (d : Nat) (bound : d < 2^256) :
    (model Basepoint.basePoint d).toAffine = Points.mul d domain.G := by
  rw [(model_correct Basepoint.basePoint basePoint_valid d bound).2, basePoint_toAffine]

end P256.Proofs.PublicPoint
