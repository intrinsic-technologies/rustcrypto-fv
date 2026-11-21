import K256.Proofs.Common.Field.Repr
import X86Proofs.Instructions.Or.Generated.RR.Triple

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field X86Proofs

def mask52 : Word := 0xfffffffffffff
def mask48 : Word := 0xffffffffffff

def first (a : Limbs) : Word := a[4] >>> 48 * 4294968273 + a[0]
def carry (t x : Word) : Word := t >>> 52 + x
def top (t x : Word) : Word := t >>> 52 + (x &&& 281474976710655)

def flagOf (t0 t1 t2 t3 t4 : Word) : Word :=
  BitVec.setWidth 64
    (((if ¬(t0 &&& 4503599627370495).toNat < 4503595332402222 ∧
          ¬(t0 &&& 4503599627370495) = 4503595332402222 then (1 : BitVec 8) else 0) &&&
      (if (orFlags (t2 &&& (t1 &&& 4503599627370495) &&& t3 ^^^ 4503599627370495 |||
          t4 ^^^ 281474976710655)).ZF.getD false = true then (1 : BitVec 8) else 0)) |||
      BitVec.setWidth 8 (t4 >>> 48))

def normOf (r t0 t1 t2 t3 t4 : Word) : Limbs :=
  let m := mask52 &&& -BitVec.setWidth 64 (BitVec.setWidth 8 r)
  let s0 := 0x1000003d1 + (t0 &&& mask52)
  let s1 := (s0 >>> 52) + (t1 &&& mask52)
  let s2 := (s1 >>> 52) + (t2 &&& mask52)
  let s3 := (s2 >>> 52) + (t3 &&& mask52)
  let s4 := ((s3 >>> 52) + t4) &&& mask48
  #v[(s0 ^^^ t0) &&& m ^^^ (t0 &&& mask52),
    (s1 ^^^ t1) &&& m ^^^ (t1 &&& mask52),
    (s2 ^^^ t2) &&& m ^^^ (t2 &&& mask52),
    (s3 ^^^ t3) &&& m ^^^ (t3 &&& mask52),
    (s4 ^^^ t4) &&& -BitVec.setWidth 64 (BitVec.setWidth 8 r) ^^^ t4]

def normalize (a : Limbs) : Limbs :=
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  let t4 := top t3 a[4]
  normOf (flagOf t0 t1 t2 t3 t4) t0 t1 t2 t3 t4

def foldedValue (t0 t1 t2 t3 t4 : Word) : Nat :=
  ((((t4.toNat * 2^52 + t3.toNat % 2^52) * 2^52 + t2.toNat % 2^52) * 2^52 +
    t1.toNat % 2^52) * 2^52 + t0.toNat % 2^52)

def Widths (a : Limbs) : Prop :=
  ∀ i : Fin 5, a[i].toNat < 2^(if i.val = 4 then 48 else 52)

end K256.Proofs.Sec1.Serialize.Normalize
