import P256.Proofs.Field.Montgomery.Words

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second

open P256.Proofs.Field.Montgomery

structure Words where
  low : BitVec 64
  middle : BitVec 64
  high : BitVec 64
  top : BitVec 64
  extra : BitVec 64
  carry : Bool

def round (a b c d e f : BitVec 64) : Words :=
  let p0 := product64 a 0xffffffffffffffff
  let p1 := product64 a 0xffffffff
  let x := add64 p1.1 b
  let xh := adc64 p1.2 0 x.2
  let z := add64 p0.1 a
  let y := adc64 x.1 p0.2 z.2
  let yh := adc64 xh.1 0 y.2
  let m := add64 c yh.1
  let mh := adc64 0 0 m.2
  let p3 := product64 a 0xffffffff00000001
  let h := add64 d e
  let eh := adc64 f 0 h.2
  let u := add64 h.1 p3.1
  let uh := adc64 p3.2 0 u.2
  let w := add64 u.1 mh.1
  let wh := adc64 uh.1 0 w.2
  ⟨y.1, m.1, w.1, wh.1, eh.1, eh.2⟩

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
