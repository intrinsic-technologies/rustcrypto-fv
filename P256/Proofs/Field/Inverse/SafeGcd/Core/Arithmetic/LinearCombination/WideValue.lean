import P256.Proofs.Field.Schoolbook.Arithmetic

set_option autoImplicit false

open P256.Proofs.Field.Schoolbook (packFive)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination

def wideValue (a : Vector (BitVec 64) 5) : Nat := packFive (a.map BitVec.toNat)

def signedWideValue (a : Vector (BitVec 64) 5) (negative : Bool) : Int :=
  if negative then -(wideValue a : Int) else (wideValue a : Int)

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination
