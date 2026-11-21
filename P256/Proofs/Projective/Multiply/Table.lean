import P256.Proofs.Projective.Multiply.Operations

set_option autoImplicit false

namespace P256.Proofs.Projective

def tableEntry (point : Projective) : Nat → Projective
  | 0 => point
  | i + 1 => point.add (tableEntry point i)

def table (point : Projective) (index : Fin 8) : Projective :=
  tableEntry point index.val

end P256.Proofs.Projective
