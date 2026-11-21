import P256.Proofs.Projective.Algebra.RCB.Point

set_option autoImplicit false

namespace P256.Proofs.Projective.Affine

def neg {F : Type} [Lean.Grind.Field F] : Point F → Point F
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

end P256.Proofs.Projective.Affine
