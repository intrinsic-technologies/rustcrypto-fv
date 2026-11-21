import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.HighArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Field.Montgomery
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

attribute [local irreducible] add64 adc64 product64

theorem negProduct_add (a : BitVec 64) :
    (add64 (product64 a 0xffffffffffffffff).1 a).1 = 0 := by
  simp only [add64, product64, X86Proofs.addSpec]
  change a * (-1 : BitVec 64) + a = 0
  rw [BitVec.mul_neg]
  change -(a * 1#64) + a = 0
  rw [BitVec.mul_one]
  exact BitVec.add_left_neg a

def thirdLow (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := product64 a 0xffffffffffffffff
  let p1 := product64 a 0xffffffff
  let x := add64 p1.1 b
  let h := adc64 p1.2 0 x.2
  let z := add64 p0.1 a
  let y := adc64 x.1 p0.2 z.2
  let k := adc64 h.1 0 y.2
  (y.1, k.1)

theorem thirdLow_value (a b : BitVec 64) :
    (thirdLow a b).1.toNat + wordBase*(thirdLow a b).2.toNat =
      b.toNat + a.toNat*2^32 := by
  dsimp only [thirdLow]
  generalize eq_p0 : product64 a 0xffffffffffffffff = p0
  generalize eq_p1 : product64 a 0xffffffff = p1
  generalize eq_x : add64 p1.1 b = x
  generalize eq_h : adc64 p1.2 0 x.2 = h
  generalize eq_z : add64 p0.1 a = z
  generalize eq_y : adc64 x.1 p0.2 z.2 = y
  generalize eq_k : adc64 h.1 0 y.2 = k
  have hp0 := product64_value a 0xffffffffffffffff
  rw [eq_p0] at hp0
  have hp1 := product64_value a 0xffffffff
  rw [eq_p1] at hp1
  have hx := add64_value p1.1 b
  rw [eq_x] at hx
  have hh := adc64_value p1.2 0 x.2
  rw [eq_h] at hh
  have hz := add64_value p0.1 a
  rw [eq_z] at hz
  have hy := adc64_value x.1 p0.2 z.2
  rw [eq_y] at hy
  have hk := adc64_value h.1 0 y.2
  rw [eq_k] at hk
  have hz0 : z.1 = 0 := by
    rw [← eq_z, ← eq_p0]
    exact negProduct_add a
  rw [hz0] at hz
  clear eq_p0 eq_p1 eq_x eq_h eq_z eq_y eq_k hz0
  change p0.1.toNat + wordBase*p0.2.toNat = a.toNat*18446744073709551615 at hp0
  change p1.1.toNat + wordBase*p1.2.toNat = a.toNat*4294967295 at hp1
  change h.1.toNat + wordBase*h.2.toNat = p1.2.toNat+0+x.2.toNat at hh
  change k.1.toNat + wordBase*k.2.toNat = h.1.toNat+0+y.2.toNat at hk
  dsimp only [wordBase] at *
  have ha := a.isLt
  have hmhi : p1.2.toNat < 2^32 := by
    clear hp0 hx hh hz hy hk
    omega
  have hhc : h.2.toNat = 0 := by
    clear hp0 hp1 hx hz hy hk
    have := Bool.toNat_le x.2
    omega
  have hkc : k.2.toNat = 0 := by
    clear hp0 hp1 hx hz hy
    have := Bool.toNat_le x.2
    have := Bool.toNat_le y.2
    omega
  omega

def thirdWords (a : Limbs) (extra carry : BitVec 64) : Limbs × Bool :=
  let low := thirdLow a.l0 a.l1
  let middle := add64 low.2 a.l2
  let high := highWords a.l0 a.l3 extra carry middle.2
  (⟨low.1, middle.1, high.1, high.2.1⟩, high.2.2)

theorem thirdWords_value (a : Limbs) (extra carry : BitVec 64) :
    (thirdWords a extra carry).1.toNat + 2^256*(thirdWords a extra carry).2.toNat =
      reduceStep (a.toNat + 2^192*extra.toNat + 2^256*carry.toNat) := by
  dsimp only [thirdWords]
  generalize eq_low : thirdLow a.l0 a.l1 = low
  generalize eq_middle : add64 low.2 a.l2 = middle
  generalize eq_high : highWords a.l0 a.l3 extra carry middle.2 = high
  have hl := thirdLow_value a.l0 a.l1
  rw [eq_low] at hl
  have hm := add64_value low.2 a.l2
  rw [eq_middle] at hm
  have hh := highWords_value a.l0 a.l3 extra carry middle.2
  rw [eq_high] at hh
  have hred := reduceStep_limbs_sparse a.l0.toNat a.l1.toNat a.l2.toNat a.l3.toNat a.l0.isLt
  change reduceStep a.toNat = _ at hred
  have split : a.toNat + 2^192*extra.toNat + 2^256*carry.toNat =
      a.toNat + wordBase*(2^128*extra.toNat + 2^192*carry.toNat) := by
    dsimp only [wordBase]
    omega
  rw [split, reduceStep_add_wordMultiple, hred]
  clear eq_low eq_middle eq_high hred split
  dsimp only [Limbs.toNat, wordBase] at *
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
