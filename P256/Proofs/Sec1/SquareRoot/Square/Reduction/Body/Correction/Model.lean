import P256.Proofs.Field.Montgomery.Arithmetic
import P256.Proofs.SecretKeyFromBytes.Arithmetic

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

def modulus : Limbs := ⟨0xffffffffffffffff, 0xffffffff, 0, 0xffffffff00000001⟩

def borrow (a p r : BitVec 64) : BitVec 64 :=
  (((~~~a ||| p) &&& r) ||| (p &&& ~~~a)) >>> 63

def subWord (a p b : BitVec 64) : BitVec 64 :=
  (-b).sshiftRight 63 + (a - p)

def subRaw (a p : Limbs) : Limbs × BitVec 64 :=
  let r0 := a.l0 - p.l0
  let b0 := borrow a.l0 p.l0 r0
  let r1 := subWord a.l1 p.l1 b0
  let b1 := borrow a.l1 p.l1 r1
  let r2 := subWord a.l2 p.l2 b1
  let b2 := borrow a.l2 p.l2 r2
  let r3 := subWord a.l3 p.l3 b2
  let b3 := borrow a.l3 p.l3 r3
  (⟨r0, r1, r2, r3⟩, b3)

def selectWord (a r q : BitVec 64) : BitVec 64 := (-q &&& (a ^^^ r)) ^^^ r

def selectLimbs (a r : Limbs) (q : BitVec 64) : Limbs :=
  ⟨selectWord a.l0 r.l0 q, selectWord a.l1 r.l1 q,
    selectWord a.l2 r.l2 q, selectWord a.l3 r.l3 q⟩

def selector (high borrow : BitVec 64) : BitVec 64 :=
  (if high = 0 then (1 : BitVec 64) else 0) &&& -borrow

def reduce (a : Limbs) (high : BitVec 64) : Limbs :=
  let r := subRaw a modulus
  selectLimbs a r.1 (selector high r.2)

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction
