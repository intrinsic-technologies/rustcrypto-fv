import K256.Proofs.Common.Field.Repr
import K256.Proofs.Common.Field.WordOps

namespace K256.Proofs.Common.Field
open X86Proofs

def squareLimbs (a : Limbs) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let x5 : BitVec 64 := a[1]
  let x6 : BitVec 64 := a[4]
  let x7 : BitVec 64 := a[0]
  let x8 : BitVec 64 := a[2]
  let x9 : BitVec 64 := a[3]
  let x10 : BitVec 64 := x8 * x6
  let x11 : BitVec 64 := x9 * x6
  let x12 : BitVec 64 := x8 * x8
  let x13 : BitVec 64 := x7 * x7
  let x14 : BitVec 64 := x9 * x5
  let x15 : BitVec 64 := x8 * x5
  let x16 : BitVec 64 := x9 * x7
  let x17 : BitVec 64 := x6 * x7
  let x18 : BitVec 64 := x6 * x5
  let x19 : BitVec 64 := x7 + x7
  let x20 : BitVec 64 := x6 * x6
  let x21 : BitVec 64 := x9 * x8
  let x22 : BitVec 64 := x9 * x9
  let x23 : BitVec 64 := x5 * x5
  let x24 : BitVec 64 := 4503599627370493 &&& x20
  let x25 : BitVec 64 := x18 + x21
  let x26 : BitVec 64 := x14 + x17
  let x27 : BitVec 64 := x10 + x10
  let x28 : BitVec 64 := x19 * x5
  let x29 : BitVec 64 := x15 + x16
  let x30 : BitVec 64 := x19 * x8
  let x31 : BitVec 64 := x11 + x11
  let x32 : BitVec 64 := shldResult 12 (mulResult x6 x6).snd x20
  let x33 : BitVec 64 := x24 * 68719492368
  let x34 : BitVec 64 := x27 + x22
  let x35 : BitVec 64 := x25 + x25
  let x36 : BitVec 64 := x26 + x26
  let x37 : BitVec 64 := x30 + x23
  let x38 : BitVec 64 := x29 + x29
  let x39 : BitVec 64 := x33 + x38
  let x40 : BitVec 64 := x32 * 68719492368
  let x41 : BitVec 64 := x36 + x12
  let x42 : BitVec 64 := 4503599627370494 &&& x39
  let x43 : BitVec 64 := x41 + x40
  let x44 : BitVec 64 := shldResult 12 ((mulResult x24 68719492368).snd + shldResult 1 ((mulResult x8 x5).snd + (mulResult x9 x7).snd + BitVec.ofNat 64 (addSpec x15 x16).snd.CF.toNat) x29 + BitVec.ofNat 64 (addSpec x33 x38).snd.CF.toNat) x39
  let x45 : BitVec 64 := x43 + x44
  let x46 : BitVec 64 := shldResult 12 (shldResult 1 ((mulResult x6 x7).snd + (mulResult x9 x5).snd + BitVec.ofNat 64 (addSpec x14 x17).snd.CF.toNat) x26 + (mulResult x8 x8).snd + BitVec.ofNat 64 (addSpec x36 x12).snd.CF.toNat + (mulResult x32 68719492368).snd + BitVec.ofNat 64 (addSpec x41 x40).snd.CF.toNat + BitVec.ofNat 64 (addSpec x43 x44).snd.CF.toNat) x45
  let x47 : BitVec 64 := x35 + x46
  let x48 : BitVec 64 := x47 <<< 4 &&& (72057594037927920 : BitVec 64) ||| BitVec.setWidth 64 (BitVec.setWidth 32 (x45 >>> 48) &&& 15)
  let x49 : BitVec 64 := shldResult 12 (shldResult 1 ((mulResult x9 x8).snd + (mulResult x6 x5).snd + BitVec.ofNat 64 (addSpec x18 x21).snd.CF.toNat) x25 + BitVec.ofNat 64 (addSpec x35 x46).snd.CF.toNat) x47
  let x50 : BitVec 64 := x34 + x49
  let x51 : BitVec 64 := x48 * 4294968273
  let x52 : BitVec 64 := x51 + x13
  let x53 : BitVec 64 := x50 &&& 4503599627370495
  let x54 : BitVec 64 := x53 * 68719492368
  let x55 : BitVec 64 := x54 + x28
  let x56 : BitVec 64 := shldResult 12 ((mulResult x9 x9).snd + shldResult 1 (mulResult x8 x6).snd x10 + BitVec.ofNat 64 (addSpec x27 x22).snd.CF.toNat + BitVec.ofNat 64 (addSpec x34 x49).snd.CF.toNat) x50
  let x57 : BitVec 64 := x31 + x56
  let x58 : BitVec 64 := shldResult 12 ((mulResult x48 4294968273).snd + (mulResult x7 x7).snd + BitVec.ofNat 64 (addSpec x51 x13).snd.CF.toNat) x52
  let x59 : BitVec 64 := x55 + x58
  let x60 : BitVec 64 := x57 &&& 4503599627370495
  let x61 : BitVec 64 := x60 * 68719492368
  let x62 : BitVec 64 := x37 + x61
  let x63 : BitVec 64 := shldResult 12 (shldResult 1 (mulResult x9 x6).snd x11 + BitVec.ofNat 64 (addSpec x31 x56).snd.CF.toNat) x57
  let x64 : BitVec 64 := shldResult 12 ((mulResult x53 68719492368).snd + ((mulResult x19 x5).snd + x7 >>> 63 * x5) + BitVec.ofNat 64 (addSpec x54 x28).snd.CF.toNat + BitVec.ofNat 64 (addSpec x55 x58).snd.CF.toNat) x59
  let x65 : BitVec 64 := x63 * 68719492368
  let x66 : BitVec 64 := x62 + x64
  let x67 : BitVec 64 := x42 + x65
  let x68 : BitVec 64 := shldResult 12 ((mulResult x19 x8).snd + x7 >>> 63 * x8 + (mulResult x5 x5).snd + BitVec.ofNat 64 (addSpec x30 x23).snd.CF.toNat + (mulResult x60 68719492368).snd + BitVec.ofNat 64 (addSpec x37 x61).snd.CF.toNat + BitVec.ofNat 64 (addSpec x62 x64).snd.CF.toNat) x66
  let x69 : BitVec 64 := x67 + x68
  (x52 &&& 4503599627370495,
    x59 &&& 4503599627370495,
    x66 &&& 4503599627370495,
    4503599627370495 &&& x69,
    (281474976710655 &&& x45) + shldResult 12 ((mulResult x63 68719492368).snd + BitVec.ofNat 64 (addSpec x42 x65).snd.CF.toNat + BitVec.ofNat 64 (addSpec x67 x68).snd.CF.toNat) x69)

def squareWords (a : Limbs) : Limbs :=
  let r := squareLimbs a
  #v[r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2]

end K256.Proofs.Common.Field
