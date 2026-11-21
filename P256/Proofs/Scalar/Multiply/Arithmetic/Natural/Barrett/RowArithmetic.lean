import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Arithmetic
import P256.Proofs.Scalar.Multiply.Arithmetic.Support

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Scalar.Multiply.Arithmetic.Support (mul64_toNat_add_high mulWord_bound)

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open X86Proofs

theorem clearLowBit_toNat (x : BitVec 64) :
    (x &&& 0xfffffffffffffffe).toNat = x.toNat / 2 * 2 := by
  have h := BitVec.shiftLeft_ushiftRight (x := x) (n := 1)
  change x >>> 1 <<< 1 = x &&& 0xfffffffffffffffe at h
  rw [← h, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  change (x.toNat / 2 * 2) % 2^64 = x.toNat / 2 * 2
  apply Nat.mod_eq_of_lt
  have := x.isLt
  omega

theorem clearLowBit_add_carry (x y : BitVec 64) (even : x.toNat % 2 = 0) :
    (addSpec x (y &&& 0xfffffffffffffffe)).2.CF = (addSpec x y).2.CF := by
  have h := clearLowBit_toNat y
  have ex := addSpec_toNat_add_carry x (y &&& 0xfffffffffffffffe)
  have ey := addSpec_toNat_add_carry x y
  have hx := (addSpec x (y &&& 0xfffffffffffffffe)).1.isLt
  have hy := (addSpec x y).1.isLt
  have hcx := (addSpec x (y &&& 0xfffffffffffffffe)).2.CF.toNat_le
  have hcy := (addSpec x y).2.CF.toNat_le
  have eq : (addSpec x (y &&& 0xfffffffffffffffe)).2.CF.toNat =
      (addSpec x y).2.CF.toNat := by omega
  cases h1 : (addSpec x (y &&& 0xfffffffffffffffe)).2.CF <;>
    cases h2 : (addSpec x y).2.CF <;> simp_all

theorem muLow_even (a : BitVec 64) :
    (a * 0x012ffd85eedf9bfe).toNat % 2 = 0 := by
  rw [BitVec.toNat_mul]
  change a.toNat * 85565669623438334 % 18446744073709551616 % 2 = 0
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 18446744073709551616)]
  omega

def multiplyAdd (a b c d : BitVec 64) (carry : Bool) : BitVec 64 × BitVec 64 :=
  let l1 := addSpec (a*b) c
  let h1 := adcSpec (mulHigh64 a b) 0 (BitVec.ofBool l1.2.CF)
  let l2 := adcSpec l1.1 d (BitVec.ofBool carry)
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  (l2.1, h2.1)

theorem multiplyAdd_value (a b c d : BitVec 64) (carry : Bool)
    (bound : d.toNat + carry.toNat < 2^64) :
    (multiplyAdd a b c d carry).1.toNat + 2^64*(multiplyAdd a b c d carry).2.toNat =
      a.toNat*b.toNat + c.toNat + d.toNat + carry.toNat := by
  let l1 := addSpec (a*b) c
  let h1 := adcSpec (mulHigh64 a b) 0 (BitVec.ofBool l1.2.CF)
  let l2 := adcSpec l1.1 d (BitVec.ofBool carry)
  let h2 := adcSpec h1.1 0 (BitVec.ofBool l2.2.CF)
  have hm := mul64_toNat_add_high a b
  have hp := mulWord_bound a.isLt b.isLt
  have e1 := addSpec_toNat_add_carry (a*b) c
  have e2 := adcSpec_toNat_add_carry (mulHigh64 a b) 0 (BitVec.ofBool l1.2.CF)
  have e3 := adcSpec_toNat_add_carry l1.1 d (BitVec.ofBool carry)
  have e4 := adcSpec_toNat_add_carry h1.1 0 (BitVec.ofBool l2.2.CF)
  change l1.1.toNat + 2^64*l1.2.CF.toNat = _ at e1
  change h1.1.toNat + 2^64*h1.2.CF.toNat = _ at e2
  change l2.1.toNat + 2^64*l2.2.CF.toNat = _ at e3
  change h2.1.toNat + 2^64*h2.2.CF.toNat = _ at e4
  simp only [BitVec.toNat_ofBool, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e2 e3 e4
  change l2.1.toNat + 2^64*h2.1.toNat = _
  have cb := c.isLt
  have lb := l1.1.isLt
  have hb := h1.1.isLt
  have l2b := l2.1.isLt
  have h2b := h2.1.isLt
  clear_value l1 h1 l2 h2
  dsimp only [P256.Proofs.Scalar.Multiply.Arithmetic.Support.wordBase] at hm hp
  omega

attribute [irreducible] multiplyAdd
attribute [local irreducible] addSpec P256.Proofs.Common.Instructions.Carry.adcSpec mulHigh64

structure QuotientRow (r : Vector (BitVec 64) 5) (a : BitVec 64) where
  low : BitVec 64 × StatusFlags
  middle : BitVec 64 × BitVec 64
  high : BitVec 64 × BitVec 64
  top : BitVec 64 × BitVec 64
  sum0 : BitVec 64 × StatusFlags
  sum1 : BitVec 64 × StatusFlags
  sum2 : BitVec 64 × StatusFlags
  low_eq : addSpec (a * 0x012ffd85eedf9bfe) (r[0] &&& 0xfffffffffffffffe) = low
  middle_eq : multiplyAdd a 0x43190552df1a6c21 r[1] (mulHigh64 a 0x012ffd85eedf9bfe) low.2.CF = middle
  high_eq : multiplyAdd a 0xfffffffeffffffff r[2] middle.2 false = high
  top_eq : multiplyAdd a 0xffffffff r[3] high.2 false = top
  sum0_eq : addSpec a r[4] = sum0
  sum1_eq : addSpec sum0.1 top.2 = sum1
  sum2_eq : adcSpec (BitVec.ofNat 64 sum0.2.CF.toNat) 0 (BitVec.ofBool sum1.2.CF) = sum2

def QuotientRow.result {r : Vector (BitVec 64) 5} {a : BitVec 64} (row : QuotientRow r a) :
    Vector (BitVec 64) 5 :=
  #v[row.middle.1, row.high.1, row.top.1, row.sum1.1, row.sum2.1]

def quotientValue (r : Vector (BitVec 64) 5) : Nat :=
  r[0].toNat + 2^64*r[1].toNat + 2^128*r[2].toNat + 2^192*r[3].toNat + 2^256*r[4].toNat

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
