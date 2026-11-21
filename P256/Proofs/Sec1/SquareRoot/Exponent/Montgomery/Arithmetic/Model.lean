import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Top

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

def wordsValue (v : Vector (BitVec 64) 4) : Nat :=
  P256.Proofs.Sec1.SquareRoot.Montgomery.limbsToNat v[0].toNat v[1].toNat v[2].toNat v[3].toNat

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

structure InterleavedWords where
  first : BitVec 64
  second : BitVec 64
  top : TopWords

def InterleavedWords.value (t : InterleavedWords) : Nat :=
  t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.top.value

def firstRow (a next : BitVec 64) (b : Vector (BitVec 64) 4) : InterleavedWords :=
  let c := coreWords 0 0 0 a b
  ⟨c.first, c.second, firstTop c.low c.high a b[3] next⟩

def nextRow (t : InterleavedWords) (a next : BitVec 64) (b : Vector (BitVec 64) 4) : InterleavedWords :=
  let c := coreWords t.first t.second t.top.low a b
  ⟨c.first, c.second, mergeTop c.low c.high t.top.mid t.top.high t.top.carry next b[3]⟩

structure FinalWords where
  first : BitVec 64
  second : BitVec 64
  top : FinalTop

def FinalWords.value (t : FinalWords) : Nat :=
  t.first.toNat + wordBase*t.second.toNat + wordBase^2*t.top.low.toNat +
    wordBase^3*t.top.mid.toNat + wordBase^4*t.top.high.toNat

def lastRow (t : InterleavedWords) (a : BitVec 64) (b : Vector (BitVec 64) 4) : FinalWords :=
  let c := coreWords t.first t.second t.top.low a b
  ⟨c.first, c.second, finishTop c.low c.high t.top.mid t.top.high t.top.carry⟩

def multiplyWords (a b : Vector (BitVec 64) 4) : FinalWords :=
  let t0 := firstRow a[0] a[1] b
  let t1 := nextRow t0 a[1] a[2] b
  let t2 := nextRow t1 a[2] a[3] b
  lastRow t2 a[3] b

end P256.Proofs.Sec1.SquareRoot.Montgomery
