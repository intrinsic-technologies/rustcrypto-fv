import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Field.Montgomery (wordBase)

def limbsToNat (a b c d : Nat) : Nat :=
  a + wordBase * (b + wordBase * (c + wordBase * d))

end P256.Proofs.Sec1.SquareRoot.Montgomery
