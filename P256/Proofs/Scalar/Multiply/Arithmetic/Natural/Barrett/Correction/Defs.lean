import P256.Proofs.Scalar.Multiply.Arithmetic.Reduction
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.QuotientArithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open P256.Proofs.Scalar.Multiply.Arithmetic.Support (Limbs adc carry)
open P256.Proofs.SecretKeyFromBytes.Scalar (orderBorrow)

def correctionBorrow (a : Limbs) (top : BitVec 64) : BitVec 64 :=
  (~~~top &&& ((-orderBorrow a).sshiftRight 63 + top)) >>> 63

def correctionResult (r : Limbs) (q : BitVec 64) : Limbs :=
  let m := -q
  let n0 := 0xf3b9cac2fc632551 &&& m
  let n1 := 0xbce6faada7179e84 &&& m
  let n3 := 0xffffffff00000000 &&& m
  let c0 := carry n0 r.l0 false
  let c1 := carry n1 r.l1 c0
  let c2 := carry m r.l2 c1
  ⟨n0 + r.l0, adc n1 r.l1 c0, adc (r.l2-q) 0 c1, adc n3 r.l3 c2⟩

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
