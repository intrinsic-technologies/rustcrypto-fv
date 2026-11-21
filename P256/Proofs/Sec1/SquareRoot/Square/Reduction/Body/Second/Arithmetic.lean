import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second

open P256.Proofs.Field.Montgomery

attribute [local irreducible] add64 adc64 product64

set_option maxHeartbeats 800000 in
theorem round_value (a b c d e f : BitVec 64) :
    let r := round a b c d e f
    r.low.toNat + 2^64*r.middle.toNat + 2^128*r.high.toNat +
      2^192*r.top.toNat + 2^192*r.extra.toNat + 2^256*r.carry.toNat =
    reduceStep (a.toNat + 2^64*b.toNat + 2^128*c.toNat + 2^192*d.toNat) +
      2^128*e.toNat + 2^192*f.toNat := by
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
  have hp0 := product64_value a 0xffffffffffffffff
  change p0.1.toNat + wordBase*p0.2.toNat = a.toNat * 18446744073709551615 at hp0
  have hp1 := product64_value a 0xffffffff
  change p1.1.toNat + wordBase*p1.2.toNat = a.toNat * 4294967295 at hp1
  have hx := add64_value p1.1 b
  change x.1.toNat + wordBase*x.2.toNat = p1.1.toNat + b.toNat at hx
  have hxh := adc64_value p1.2 0 x.2
  change xh.1.toNat + wordBase*xh.2.toNat = p1.2.toNat + 0 + x.2.toNat at hxh
  have hz := add64_value p0.1 a
  change z.1.toNat + wordBase*z.2.toNat = p0.1.toNat + a.toNat at hz
  have hy := adc64_value x.1 p0.2 z.2
  change y.1.toNat + wordBase*y.2.toNat = x.1.toNat + p0.2.toNat + z.2.toNat at hy
  have hyh := adc64_value xh.1 0 y.2
  change yh.1.toNat + wordBase*yh.2.toNat = xh.1.toNat + 0 + y.2.toNat at hyh
  have hm := add64_value c yh.1
  change m.1.toNat + wordBase*m.2.toNat = c.toNat + yh.1.toNat at hm
  have hmh := adc64_value 0 0 m.2
  change mh.1.toNat + wordBase*mh.2.toNat = 0 + 0 + m.2.toNat at hmh
  have hp3 := product64_value a 0xffffffff00000001
  change p3.1.toNat + wordBase*p3.2.toNat = a.toNat * 18446744069414584321 at hp3
  have hh := add64_value d e
  change h.1.toNat + wordBase*h.2.toNat = d.toNat + e.toNat at hh
  have heh := adc64_value f 0 h.2
  change eh.1.toNat + wordBase*eh.2.toNat = f.toNat + 0 + h.2.toNat at heh
  have hu := add64_value h.1 p3.1
  change u.1.toNat + wordBase*u.2.toNat = h.1.toNat + p3.1.toNat at hu
  have huh := adc64_value p3.2 0 u.2
  change uh.1.toNat + wordBase*uh.2.toNat = p3.2.toNat + 0 + u.2.toNat at huh
  have hw := add64_value u.1 mh.1
  change w.1.toNat + wordBase*w.2.toNat = u.1.toNat + mh.1.toNat at hw
  have hwh := adc64_value uh.1 0 w.2
  change wh.1.toNat + wordBase*wh.2.toNat = uh.1.toNat + 0 + w.2.toNat at hwh
  have hz0 : z.1 = 0 := by
    dsimp only [z, p0]
    simp only [add64, product64, X86Proofs.addSpec]
    change a * (-1 : BitVec 64) + a = 0
    rw [BitVec.mul_neg]
    change -(a * 1#64) + a = 0
    rw [BitVec.mul_one]
    exact BitVec.add_left_neg a
  rw [hz0] at hz
  have ha := a.isLt
  have hred := reduceStep_limbs_sparse a.toNat b.toNat c.toNat d.toNat ha
  have hinput : a.toNat + 2^64*b.toNat + 2^128*c.toNat + 2^192*d.toNat =
      a.toNat + wordBase*(b.toNat + wordBase*(c.toNat + wordBase*d.toNat)) := by
    dsimp only [wordBase]
    omega
  dsimp only
  rw [hinput, hred]
  change y.1.toNat + 2^64*m.1.toNat + 2^128*w.1.toNat +
    2^192*wh.1.toNat + 2^192*eh.1.toNat + 2^256*eh.2.toNat = _
  clear_value p0 p1 x xh z y yh m mh p3 h eh u uh w wh
  clear hz0 hred hinput
  dsimp only [wordBase, BitVec.toNat_ofNat] at *
  have hp1hi : p1.2.toNat < 2^32 := by omega
  have hp3hi : p3.2.toNat < 18446744069414584321 := by omega
  have hxh0 : xh.2.toNat = 0 := by
    have := Bool.toNat_le x.2
    omega
  have hyh0 : yh.2.toNat = 0 := by
    have := Bool.toNat_le x.2
    have := Bool.toNat_le y.2
    omega
  have hmh0 : mh.2.toNat = 0 := by
    have := Bool.toNat_le m.2
    omega
  have huh0 : uh.2.toNat = 0 := by
    have := Bool.toNat_le u.2
    omega
  have hwh0 : wh.2.toNat = 0 := by
    have := Bool.toNat_le u.2
    have := Bool.toNat_le w.2
    omega
  omega

set_option exponentiation.threshold 512 in
theorem round_value_lift (a b c d : BitVec 64) (v : Nat)
    (h : a.toNat + 2^64*b.toNat + 2^128*c.toNat + 2^192*d.toNat +
      2^192*(v / 2^256) = reduceStep v) :
    let r := round a b c d (BitVec.ofNat 64 (v / 2^256)) (BitVec.ofNat 64 (v / 2^320))
    r.low.toNat + 2^64*r.middle.toNat + 2^128*r.high.toNat +
      2^192*r.top.toNat + 2^192*r.extra.toNat + 2^256*r.carry.toNat +
      2^256*(v / 2^384) = reduceStep (reduceStep v) := by
  have hv := round_value a b c d (BitVec.ofNat 64 (v / 2^256))
    (BitVec.ofNat 64 (v / 2^320))
  have hs := reduceStep_add_wordMultiple
    (a.toNat + 2^64*b.toNat + 2^128*c.toNat + 2^192*d.toNat) (2^128*(v / 2^256))
  have he : wordBase*(2^128*(v / 2^256)) = 2^192*(v / 2^256) := by
    dsimp only [wordBase]
    omega
  rw [he, h] at hs
  rw [hs]
  dsimp only at hv ⊢
  rw [hv]
  simp only [BitVec.toNat_ofNat]
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
