import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.QuotientArithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Scalar.Multiply.Arithmetic.Support (mul64_toNat_add_high mulWord_bound)

def multiplyAddFirst (a b c : BitVec 64) : BitVec 64 × BitVec 64 :=
  let low := addSpec (a*b) c
  (low.1, (adcSpec (mulHigh64 a b) 0 (BitVec.ofBool low.2.CF)).1)

theorem multiplyAddFirst_value (a b c : BitVec 64) :
    (multiplyAddFirst a b c).1.toNat + 2^64 * (multiplyAddFirst a b c).2.toNat =
      a.toNat*b.toNat + c.toNat := by
  let lo := addSpec (a*b) c
  let hi := adcSpec (mulHigh64 a b) 0 (BitVec.ofBool lo.2.CF)
  have hm := mul64_toNat_add_high a b
  have hp := mulWord_bound a.isLt b.isLt
  have hl := addSpec_toNat_add_carry (a*b) c
  have hh := adcSpec_toNat_add_carry (mulHigh64 a b) 0 (BitVec.ofBool lo.2.CF)
  change lo.1.toNat + 2^64*lo.2.CF.toNat = _ at hl
  change hi.1.toNat + 2^64*hi.2.CF.toNat = _ at hh
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at hh
  change lo.1.toNat + 2^64*hi.1.toNat = _
  have cb := c.isLt
  have lob := lo.1.isLt
  have hib := hi.1.isLt
  clear_value lo hi
  dsimp only [P256.Proofs.Scalar.Multiply.Arithmetic.Support.wordBase] at hm hp
  omega

attribute [irreducible] multiplyAddFirst

structure QuotientPartial where
  lower : BitVec 64
  middle : BitVec 64
  upper : BitVec 64
  upperCarry : BitVec 64
  top : BitVec 64
  topAdd : BitVec 64
  carry : Bool

def QuotientPartial.value (r : QuotientPartial) : Nat :=
  r.lower.toNat + 2^64*r.middle.toNat + 2^128*(r.upper.toNat+r.upperCarry.toNat) +
    2^192*(r.top.toNat+r.topAdd.toNat) + 2^256*r.carry.toNat

def QuotientPartial.upperSum (r : QuotientPartial) := addSpec r.upper r.upperCarry

def QuotientPartial.topSum (r : QuotientPartial) :=
  adcSpec r.top r.topAdd (BitVec.ofBool r.upperSum.2.CF)

structure QuotientPartialStep (r : QuotientPartial) (a : BitVec 64) where
  low : BitVec 64 × StatusFlags
  middle : BitVec 64 × BitVec 64
  high : BitVec 64 × BitVec 64
  top : BitVec 64 × BitVec 64
  sum : BitVec 64 × StatusFlags
  low_eq : addSpec (a * 0x012ffd85eedf9bfe) (r.lower &&& 0xfffffffffffffffe) = low
  middle_eq : multiplyAdd a 0x43190552df1a6c21 r.middle
    (mulHigh64 a 0x012ffd85eedf9bfe) low.2.CF = middle
  high_eq : multiplyAdd a 0xfffffffeffffffff r.upperSum.1 middle.2 false = high
  top_eq : multiplyAddFirst a 0xffffffff r.topSum.1 = top
  sum_eq : adcSpec (BitVec.ofNat 64 r.carry.toNat) a (BitVec.ofBool r.topSum.2.CF) = sum

def QuotientPartialStep.result {r : QuotientPartial} {a : BitVec 64}
    (step : QuotientPartialStep r a) : QuotientPartial :=
  ⟨step.middle.1, step.high.1, step.top.1, step.high.2, step.top.2, step.sum.1, step.sum.2.CF⟩

attribute [local irreducible] addSpec P256.Proofs.Common.Instructions.Carry.adcSpec mulHigh64

theorem QuotientPartialStep.value {r : QuotientPartial} {a : BitVec 64}
    (step : QuotientPartialStep r a) :
    step.result.value = (r.value + a.toNat * barrettMu) / 2^64 := by
  obtain ⟨lo, mid, hi, top, sum, hldef, hmdef, hhdef, htdef, hsdef⟩ := step
  have hp := mul64_toNat_add_high a 0x012ffd85eedf9bfe
  change (a * 0x012ffd85eedf9bfe).toNat + 2^64*(mulHigh64 a 0x012ffd85eedf9bfe).toNat =
    a.toNat * 85565669623438334 at hp
  have aa := a.isLt
  have cb := lo.2.CF.toNat_le
  have bound : (mulHigh64 a 0x012ffd85eedf9bfe).toNat + lo.2.CF.toNat < 2^64 := by omega
  have hm := multiplyAdd_value a 0x43190552df1a6c21 r.middle
    (mulHigh64 a 0x012ffd85eedf9bfe) lo.2.CF bound
  have hh := multiplyAdd_value a 0xfffffffeffffffff r.upperSum.1 mid.2 false
    (by change mid.2.toNat < 2^64; exact mid.2.isLt)
  have ht := multiplyAddFirst_value a 0xffffffff r.topSum.1
  rw [hmdef] at hm
  rw [hhdef] at hh
  rw [htdef] at ht
  change mid.1.toNat + 2^64*mid.2.toNat = a.toNat*4834901528447446049 +
    r.middle.toNat + (mulHigh64 a 0x012ffd85eedf9bfe).toNat + lo.2.CF.toNat at hm
  change hi.1.toNat + 2^64*hi.2.toNat = a.toNat*18446744069414584319 +
    r.upperSum.1.toNat + mid.2.toNat + 0 at hh
  change top.1.toNat + 2^64*top.2.toNat = a.toNat*4294967295 + r.topSum.1.toNat at ht
  have hl := addSpec_toNat_add_carry (a * 0x012ffd85eedf9bfe) r.lower
  have mask := clearLowBit_add_carry (a * 0x012ffd85eedf9bfe) r.lower (muLow_even a)
  rw [hldef] at mask
  rw [← mask] at hl
  have hu := addSpec_toNat_add_carry r.upper r.upperCarry
  have hv := adcSpec_toNat_add_carry r.top r.topAdd (BitVec.ofBool r.upperSum.2.CF)
  have hs := adcSpec_toNat_add_carry (BitVec.ofNat 64 r.carry.toNat) a (BitVec.ofBool r.topSum.2.CF)
  change r.upperSum.1.toNat + 2^64*r.upperSum.2.CF.toNat = _ at hu
  change r.topSum.1.toNat + 2^64*r.topSum.2.CF.toNat = _ at hv
  rw [hsdef] at hs
  simp only [BitVec.toNat_ofBool, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt r.carry.toNat_le (by decide : 1 < 2^64))] at hv hs
  have lb := (addSpec (a * 0x012ffd85eedf9bfe) r.lower).1.isLt
  change mid.1.toNat + 2^64*hi.1.toNat + 2^128*(top.1.toNat+hi.2.toNat) +
    2^192*(top.2.toNat+sum.1.toNat) + 2^256*sum.2.CF.toNat = _
  clear hldef hmdef hhdef htdef hsdef
  dsimp only [QuotientPartial.value, barrettMu]
  omega

def QuotientPartial.result (r : QuotientPartial) : Vector (BitVec 64) 5 :=
  #v[r.lower, r.middle, r.upperSum.1, r.topSum.1,
    (adcSpec (BitVec.ofNat 64 r.carry.toNat) 0 (BitVec.ofBool r.topSum.2.CF)).1]

theorem QuotientPartial.result_value (r : QuotientPartial) :
    quotientValue r.result = r.value := by
  let last := adcSpec (BitVec.ofNat 64 r.carry.toNat) 0 (BitVec.ofBool r.topSum.2.CF)
  have hu := addSpec_toNat_add_carry r.upper r.upperCarry
  have hv := adcSpec_toNat_add_carry r.top r.topAdd (BitVec.ofBool r.upperSum.2.CF)
  have hl := adcSpec_toNat_add_carry (BitVec.ofNat 64 r.carry.toNat) 0 (BitVec.ofBool r.topSum.2.CF)
  change r.upperSum.1.toNat + 2^64*r.upperSum.2.CF.toNat = _ at hu
  change r.topSum.1.toNat + 2^64*r.topSum.2.CF.toNat = _ at hv
  change last.1.toNat + 2^64*last.2.CF.toNat = _ at hl
  simp only [BitVec.toNat_ofBool, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt r.carry.toNat_le (by decide : 1 < 2^64)),
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at hl hv
  have cb := r.carry.toNat_le
  have vb := r.topSum.2.CF.toNat_le
  have lb := last.1.isLt
  change r.lower.toNat + 2^64*r.middle.toNat + 2^128*r.upperSum.1.toNat +
    2^192*r.topSum.1.toNat + 2^256*last.1.toNat = _
  clear_value last
  dsimp only [QuotientPartial.value]
  omega

def quotientPartialOfFirst (row : Vector (BitVec 64) 4 × Bool) : QuotientPartial :=
  ⟨row.1[0], row.1[1], row.1[2], 0, row.1[3], 0, row.2⟩

theorem quotientPartialOfFirst_value (row : Vector (BitVec 64) 4 × Bool) :
    (quotientPartialOfFirst row).value = quotientFirstValue row := rfl

def quotientPartialInitial (a : BitVec 64) : QuotientPartial :=
  quotientPartialOfFirst (quotientFirstRow a)

theorem quotientPartialInitial_value (a : BitVec 64) :
    (quotientPartialInitial a).value = a.toNat * barrettMu / 2^64 := by
  unfold quotientPartialInitial
  rw [quotientPartialOfFirst_value, quotientFirstRow_value]

attribute [local irreducible] QuotientPartial.value QuotientPartialStep.result quotientPartialInitial quotientValue

set_option exponentiation.threshold 512 in
theorem quotientPartialRows_value (a : Vector (BitVec 64) 5)
    (s1 : QuotientPartialStep (quotientPartialInitial a[0]) a[1])
    (s2 : QuotientPartialStep s1.result a[2])
    (s3 : QuotientPartialStep s2.result a[3])
    (s4 : QuotientPartialStep s3.result a[4]) :
    s4.result.value = quotientValue a * barrettMu / 2^320 := by
  have h0 := quotientPartialInitial_value a[0]
  have h1 := s1.value
  have h2 := s2.value
  have h3 := s3.value
  have h4 := s4.value
  rw [h4, h3, h2, h1, h0]
  simp only [quotientValue, barrettMu, Nat.add_mul, Nat.mul_assoc]
  omega

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
