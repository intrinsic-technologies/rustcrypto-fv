import P256.Proofs.Field.Montgomery.Words

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Proofs.Field.Montgomery
open X86Proofs

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

def wordsValue (v : Vector (BitVec 64) 4) : Nat :=
  v[0].toNat + wordBase*v[1].toNat + wordBase^2*v[2].toNat + wordBase^3*v[3].toNat

def lowerWordsValue (v : Vector (BitVec 64) 4) : Nat :=
  v[0].toNat + wordBase*v[1].toNat + wordBase^2*v[2].toNat

structure CoreWords where
  first : BitVec 64
  second : BitVec 64
  low : BitVec 64
  high : BitVec 64

def CoreWords.value (t : CoreWords) : Nat :=
  t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.low.toNat + wordBase^3*t.high.toNat

def coreWords (old0 old1 old2 a : BitVec 64) (b : Vector (BitVec 64) 4) : CoreWords :=
  let x := product64 a b[0]
  let q := add64 x.1 old0
  let c := startCarry q.1 x.2 q.2
  let m := middleCarry a b[1] q.1 0 old1 c.1 c.2
  let n := middleCarry a b[2] q.1 0xffffffff00000001 old2 m.2.1 m.2.2
  ⟨m.1, n.1, n.2.1, n.2.2⟩

structure FinalTop where
  low : BitVec 64
  mid : BitVec 64
  high : BitVec 64
  highBeforeCarry : BitVec 64
  carry : Bool

structure FinalWords where
  first : BitVec 64
  second : BitVec 64
  top : FinalTop

def FinalWords.value (t : FinalWords) : Nat :=
  t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.top.low.toNat +
    wordBase^3*t.top.mid.toNat + wordBase^4*t.top.high.toNat


end P256.Proofs.Sec1.SquareRoot.SquareFour
