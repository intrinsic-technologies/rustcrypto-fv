import P256.Proofs.PublicPoint.Order.Generator
import P256.Proofs.PublicPoint.Order.Nonidentity
import P256.Proofs.Projective.Multiply.Group.Laws
import P256.Proofs.Scalar.Primality

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open Standards.SECG.ECC P256.Spec P256.Spec.Operations
open Projective.Multiply.Group

theorem publicPoint_ne_infinity (d : Nat) (positive : 0 < d) (bound : d < domain.n) :
    Points.mul d domain.G ≠ .infinity :=
  Order.scalarMul_ne_infinity_of_prime_order domain p256_add_laws domain.G
    Order.generator_onCurve (by decide) Scalar.prime_order Order.scalarMul_order d positive bound

end P256.Proofs.PublicPoint
