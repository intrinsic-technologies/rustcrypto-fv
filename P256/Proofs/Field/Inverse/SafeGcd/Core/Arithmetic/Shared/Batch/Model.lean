import Std.Tactic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch

structure Words where
  delta : BitVec 64
  f : BitVec 64
  g : BitVec 64
  u : BitVec 64
  v : BitVec 64
  q : BitVec 64
  r : BitVec 64

def even (p : Words) : Bool := p.g.setWidth 8 &&& 1 == 0

def positive (p : Words) : Bool := decide (0 < p.delta.toInt)

def swap (p : Words) : Bool := !even p && positive p

def numerator (p : Words) : BitVec 64 :=
  if even p then p.g else if positive p then p.g - p.f else p.g + p.f

def next (p : Words) : Words where
  delta := if swap p then 2 - p.delta else p.delta + 2
  f := if swap p then p.g else p.f
  g := (numerator p).sshiftRight 1
  u := if swap p then p.q + p.q else p.u + p.u
  v := if swap p then p.r + p.r else p.v + p.v
  q := if even p then p.q else if positive p then p.q - p.u else p.q + p.u
  r := if even p then p.r else if positive p then p.r - p.v else p.r + p.v

def run : Nat → Words → Words
  | 0, p => p
  | n+1, p => run n (next p)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
