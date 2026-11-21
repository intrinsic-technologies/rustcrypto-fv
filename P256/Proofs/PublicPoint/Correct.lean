import P256.Proofs.PublicPoint.Composition
import P256.Proofs.PublicPoint.Normalize
import P256.Proofs.Projective.Multiply.Machine.Basepoint

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open Prelude X86 X86.Machine

theorem public_point_correct (bindings : Bindings) : Contract bindings :=
  public_point_correct_of_stages bindings
    (Projective.Multiply.Machine.Basepoint.basepoint_correct bindings)
    (fun _ _ _ _ pre state => Normalize.normalize pre state)

end P256.Proofs.PublicPoint
