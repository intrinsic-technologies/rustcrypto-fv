import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstTop
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open X86Proofs

theorem firstCarry_words (q hi : BitVec 64) :
    let m0 := product64 q 0xffffffffffffffff
    let m1 := product64 q 0xffffffff
    let x := add64 m1.1 hi
    let y := adc64 m1.2 0 x.2
    let z := add64 x.1 m0.2
    let w := adc64 y.1 0 z.2
    let k := add64 m0.1 q
    let n := adc64 z.1 0 k.2
    let o := adc64 w.1 0 n.2
    (n.1, o.1) = startCarry q hi false := by
  simp only [startCarry, adc64_false]
  rw [add64_comm (product64 q 0xffffffffffffffff).2]

theorem firstMiddle_words (a b q p c0 c1 : BitVec 64) :
    let x := product64 a b
    let m := product64 q p
    let h := add64 m.1 x.2
    let j := adc64 m.2 0 h.2
    let k := add64 h.1 c1
    let n := adc64 j.1 0 k.2
    let o := add64 c0 x.1
    let r := adc64 k.1 0 o.2
    let s := adc64 n.1 0 r.2
    (o.1, r.1, s.1) = middleCarry a b q p 0 c0 c1 := by
  simp only [middleCarry, add64_zero, adc64_false]
  rw [add64_comm c0]

end P256.Proofs.Sec1.SquareRoot.Montgomery
