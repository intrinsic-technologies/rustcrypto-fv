import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Field.Montgomery.Words
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Representation

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat_add_carry addSpec_toNat_add_carry)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open X86Proofs

export P256.Proofs.Field.Montgomery
  (wordBase add64 adc64 product64 add64_value adc64_value product64_value)

theorem product64_high_lt (a b : BitVec 64) :
    (product64 a b).2.toNat < wordBase - 1 := by
  exact (P256.Proofs.Field.Schoolbook.mulHigh64_toNat a b).symm ▸
    P256.Proofs.Field.Schoolbook.mulWord_high_lt a.isLt b.isLt

def startCarry (q hi : BitVec 64) (carry : Bool) : BitVec 64 × BitVec 64 :=
  let m0 := product64 q 0xffffffffffffffff
  let m1 := product64 q 0xffffffff
  let x := adc64 m1.1 hi carry
  let y := adc64 m1.2 0 x.2
  let z := add64 m0.2 x.1
  let w := adc64 y.1 0 z.2
  let k := add64 m0.1 q
  let n := adc64 z.1 0 k.2
  let o := adc64 w.1 0 n.2
  (n.1, o.1)

def middleCarry (a b q modulus old c0 c1 : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 :=
  let x := product64 a b
  let m := product64 q modulus
  let l := add64 x.1 old
  let h := adc64 m.1 x.2 l.2
  let j := adc64 m.2 0 h.2
  let k := add64 h.1 c1
  let n := adc64 j.1 0 k.2
  let o := add64 l.1 c0
  let r := adc64 k.1 0 o.2
  let s := adc64 n.1 0 r.2
  (o.1, r.1, s.1)

end P256.Proofs.Sec1.SquareRoot.Montgomery
