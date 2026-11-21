import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shared.Batch.Model

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Batch

abbrev Words := Shared.Batch.Words

def positiveBit (d : BitVec 64) : BitVec 64 :=
  ((0x8000000000000000 - (d ^^^ 0x8000000000000000)) &&&
    (d ^^^ 0x8000000000000000)) >>> 63

def oddByte (p : Words) : BitVec 8 := p.g.setWidth 8 &&& 1

def swapByte (p : Words) : BitVec 8 := (positiveBit p.delta).setWidth 8 &&& p.g.setWidth 8

def select (c : BitVec 8) (a b : BitVec 64) : BitVec 64 :=
  ((-c.setWidth 64) &&& (b ^^^ a)) ^^^ a

def maskedF (p : Words) : BitVec 64 := (-((oddByte p).setWidth 64)) &&& p.f

def next (p : Words) : Words where
  delta := select (swapByte p) (p.delta + 2) (2 - p.delta)
  f := select (swapByte p) p.f p.g
  g := (select (swapByte p) (p.g + maskedF p) (p.g - maskedF p)).sshiftRight 1
  u := select (swapByte p) p.u p.q + select (swapByte p) p.u p.q
  v := select (swapByte p) p.v p.r + select (swapByte p) p.v p.r
  q := p.q + ((-(oddByte p).setWidth 64) &&& select ((positiveBit p.delta).setWidth 8) p.u (-p.u))
  r := p.r + ((-(oddByte p).setWidth 64) &&& select ((positiveBit p.delta).setWidth 8) p.v (-p.v))

def run : Nat → Words → Words
  | 0, p => p
  | n+1, p => run n (next p)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Batch
