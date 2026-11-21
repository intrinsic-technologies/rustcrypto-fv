import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearCombination.Model

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift

structure Inputs where
  linear : LinearCombination.Inputs
  shift : BitVec 32

def shiftedWords (p : Inputs) : Vector (BitVec 64) 4 :=
  Vector.ofFn fun i =>
    ((LinearCombination.resultWords p.linear)[i.val] >>> p.shift.toNat) |||
    ((LinearCombination.resultWords p.linear)[i.val + 1] <<< (64 - p.shift.toNat))

def resultSign (p : Inputs) : BitVec 8 := LinearCombination.resultSign p.linear

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
