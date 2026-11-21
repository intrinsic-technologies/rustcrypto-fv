import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.ModularShift.Generic.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift

variable [parameters : Parameters]

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def correctionProduct (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) :=
  productWide parameters.modulus (correctionWord (wideValue a ah) shift)

def correctedWords (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) :=
  subWide a (correctionProduct a ah shift).1 ah (correctionProduct a ah shift).2

def correctedValue (a : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs) (ah : BitVec 64) (shift : Nat) : Int :=
  (wideValue a ah : Int) - parameters.modulus.toNat * (correctionWord (wideValue a ah) shift).toNat

end P256.Proofs.Field.Inverse.SafeGcd.Core.ModularShift
