import P256.Proofs.Projective.Multiply.Lookup.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ProjectiveLoop

open ProjectiveLookup

def double4 (point : Projective) : Projective :=
  point.double.double.double.double

def accumulator (table : Fin 8 → Projective) (digits : Nat → BitVec 8) : Nat → Projective
  | 0 => Projective.identity.add (signedLookup table (digits 64))
  | n + 1 => (double4 (accumulator table digits n)).add (signedLookup table (digits (63 - n)))

def linearCombination (table : Fin 8 → Projective) (digits : Nat → BitVec 8) : Projective :=
  accumulator table digits 64

end P256.Proofs.Projective.Multiply.ProjectiveLoop
