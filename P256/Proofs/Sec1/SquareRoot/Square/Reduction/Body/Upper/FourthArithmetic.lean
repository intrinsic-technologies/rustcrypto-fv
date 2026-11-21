import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper.ThirdArithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper

open P256.Proofs.Field.Montgomery
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

attribute [local irreducible] add64 adc64 product64

def fourthLow (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := product64 a 0xffffffffffffffff
  let p1 := product64 0xffffffff a
  let z := add64 p0.1 a
  let y := adc64 p0.2 b z.2
  let x := add64 y.1 p1.1
  let k := adc64 (BitVec.ofNat 64 y.2.toNat) p1.2 x.2
  (x.1, k.1)

theorem fourthLow_value (a b : BitVec 64) :
    (fourthLow a b).1.toNat + wordBase*(fourthLow a b).2.toNat =
      b.toNat + a.toNat*2^32 := by
  dsimp only [fourthLow]
  generalize eq_p0 : product64 a 0xffffffffffffffff = p0
  generalize eq_p1 : product64 0xffffffff a = p1
  generalize eq_z : add64 p0.1 a = z
  generalize eq_y : adc64 p0.2 b z.2 = y
  generalize eq_x : add64 y.1 p1.1 = x
  generalize eq_k : adc64 (BitVec.ofNat 64 y.2.toNat) p1.2 x.2 = k
  have hp0 := product64_value a 0xffffffffffffffff
  rw [eq_p0] at hp0
  have hp1 := product64_value 0xffffffff a
  rw [eq_p1] at hp1
  have hz := add64_value p0.1 a
  rw [eq_z] at hz
  have hy := adc64_value p0.2 b z.2
  rw [eq_y] at hy
  have hx := add64_value y.1 p1.1
  rw [eq_x] at hx
  have hk := adc64_value (BitVec.ofNat 64 y.2.toNat) p1.2 x.2
  rw [eq_k] at hk
  have hz0 : z.1 = 0 := by
    rw [← eq_z, ← eq_p0]
    exact negProduct_add a
  rw [hz0] at hz
  clear eq_p0 eq_p1 eq_z eq_y eq_x eq_k hz0
  change p0.1.toNat + wordBase*p0.2.toNat = a.toNat*18446744073709551615 at hp0
  change p1.1.toNat + wordBase*p1.2.toNat = 4294967295*a.toNat at hp1
  simp only [wordBase, BitVec.toNat_ofNat] at *
  have ha := a.isLt
  have hmhi : p1.2.toNat < 2^32 := by
    clear hp0 hz hy hx hk
    omega
  have hkc : k.2.toNat = 0 := by
    clear hp0 hp1 hz hy hx
    have := Bool.toNat_le y.2
    have := Bool.toNat_le x.2
    omega
  have := Bool.toNat_le y.2
  omega

theorem fourthLow_eq_thirdLow (a b : BitVec 64) : fourthLow a b = thirdLow a b := by
  have h := fourthLow_value a b
  have k := thirdLow_value a b
  have h0 := (fourthLow a b).1.isLt
  have k0 := (thirdLow a b).1.isLt
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq <;> dsimp only [wordBase] at * <;> omega

def fourthWords (a : Limbs) (extra carry input7 : BitVec 64) : Limbs × BitVec 64 :=
  let low := fourthLow a.l0 a.l1
  let middle := add64 low.2 a.l2
  let high := highWords a.l0 a.l3 extra carry middle.2
  let last := add64 high.2.1 input7
  let lasthi := adc64 (BitVec.ofNat 64 high.2.2.toNat) 0 last.2
  (⟨low.1, middle.1, high.1, last.1⟩, lasthi.1)

theorem add_top_value (a b : BitVec 64) (c : Bool) :
    (add64 a b).1.toNat + wordBase*(adc64 (BitVec.ofNat 64 c.toNat) 0 (add64 a b).2).1.toNat =
      a.toNat + b.toNat + wordBase*c.toNat := by
  generalize eq_last : add64 a b = last
  generalize eq_lasthi : adc64 (BitVec.ofNat 64 c.toNat) 0 last.2 = lasthi
  have hl := add64_value a b
  rw [eq_last] at hl
  have hh := adc64_value (BitVec.ofNat 64 c.toNat) 0 last.2
  rw [eq_lasthi] at hh
  change lasthi.1.toNat + wordBase*lasthi.2.toNat = c.toNat%wordBase+0+last.2.toNat at hh
  clear eq_last eq_lasthi
  have := Bool.toNat_le c
  have := Bool.toNat_le last.2
  dsimp only [wordBase] at *
  have hzero : lasthi.2.toNat = 0 := by omega
  omega

theorem fourthWords_value (a : Limbs) (extra carry input7 : BitVec 64) :
    (fourthWords a extra carry input7).1.toNat + 2^256*(fourthWords a extra carry input7).2.toNat =
      reduceStep (a.toNat + 2^192*extra.toNat + 2^256*carry.toNat) + 2^192*input7.toNat := by
  have h := thirdWords_value a extra carry
  dsimp only [fourthWords]
  rw [fourthLow_eq_thirdLow]
  dsimp only [thirdWords] at h
  generalize eq_low : thirdLow a.l0 a.l1 = low at *
  generalize eq_middle : add64 low.2 a.l2 = middle at *
  generalize eq_high : highWords a.l0 a.l3 extra carry middle.2 = high at *
  have htop := add_top_value high.2.1 input7 high.2.2
  generalize eq_last : add64 high.2.1 input7 = last at *
  generalize eq_lasthi : adc64 (BitVec.ofNat 64 high.2.2.toNat) 0 last.2 = lasthi at *
  clear eq_low eq_middle eq_high eq_last eq_lasthi
  dsimp only [Limbs.toNat, wordBase] at *
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Upper
