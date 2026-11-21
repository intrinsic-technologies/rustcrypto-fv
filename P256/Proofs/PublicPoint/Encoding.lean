import P256.Proofs.PublicPoint.Order
import P256.Proofs.Sec1.Model
import P256.Proofs.Sec1Serialize.Interface

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open P256.Spec P256.Spec.Operations

theorem encodedPoint_publicPoint (d : Nat) (positive : 0 < d) (bound : d < domain.n) :
    Sec1Serialize.encodedPoint (Points.mul d domain.G) = Keys.uncompressed (Keys.publicPoint d) := by
  have nonzero := publicPoint_ne_infinity d positive bound
  change Sec1Serialize.encodedPoint (Points.mul d domain.G) =
    Keys.uncompressed (Points.mul d domain.G)
  cases hpoint : Points.mul d domain.G with
  | infinity => exact (nonzero hpoint).elim
  | affine x y => rfl

theorem publicPoint_encoding_size (d : Nat) (positive : 0 < d) (bound : d < domain.n) :
    (Keys.uncompressed (Keys.publicPoint d)).size = 65 := by
  have nonzero := publicPoint_ne_infinity d positive bound
  change (Keys.uncompressed (Points.mul d domain.G)).size = 65
  cases hpoint : Points.mul d domain.G with
  | infinity => exact (nonzero hpoint).elim
  | affine x y => exact Sec1.uncompressed_affine_size x y

theorem publicKeyOfSecret_encoding (input : ByteArray)
    (positive : 0 < Arith.uint input) (bound : Arith.uint input < domain.n) :
    Sec1Serialize.encodedPoint (Points.mul (Arith.uint input) domain.G) =
      Keys.publicKeyOfSecret #[input] :=
  encodedPoint_publicPoint (Arith.uint input) positive bound

theorem publicKeyOfSecret_size (input : ByteArray)
    (positive : 0 < Arith.uint input) (bound : Arith.uint input < domain.n) :
    (Keys.publicKeyOfSecret #[input]).size = 65 :=
  publicPoint_encoding_size (Arith.uint input) positive bound

end P256.Proofs.PublicPoint
