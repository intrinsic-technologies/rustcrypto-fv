import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Proofs.Field.Montgomery
open X86Proofs

theorem startCarry_value (q hi : BitVec 64) (carry : Bool) :
    (startCarry q hi carry).1.toNat + wordBase * (startCarry q hi carry).2.toNat =
      hi.toNat + carry.toNat + q.toNat * 2 ^ 32 := by
  let m0 := product64 q 0xffffffffffffffff
  let m1 := product64 q 0xffffffff
  let x := adc64 m1.1 hi carry
  let y := adc64 m1.2 0 x.2
  let z := add64 m0.2 x.1
  let w := adc64 y.1 0 z.2
  let k := add64 m0.1 q
  let n := adc64 z.1 0 k.2
  let o := adc64 w.1 0 n.2
  have hm0 := product64_value q 0xffffffffffffffff
  have hm1 := product64_value q 0xffffffff
  have hx := adc64_value m1.1 hi carry
  have hy := adc64_value m1.2 0 x.2
  have hz := add64_value m0.2 x.1
  have hw := adc64_value y.1 0 z.2
  have hk := add64_value m0.1 q
  have hn := adc64_value z.1 0 k.2
  have ho := adc64_value w.1 0 n.2
  change m0.1.toNat + 18446744073709551616*m0.2.toNat = _ at hm0
  change m1.1.toNat + 18446744073709551616*m1.2.toNat = _ at hm1
  change x.1.toNat + 18446744073709551616*x.2.toNat = _ at hx
  change y.1.toNat + 18446744073709551616*y.2.toNat = _ at hy
  change z.1.toNat + 18446744073709551616*z.2.toNat = _ at hz
  change w.1.toNat + 18446744073709551616*w.2.toNat = _ at hw
  change k.1.toNat + 18446744073709551616*k.2.toNat = _ at hk
  change n.1.toNat + 18446744073709551616*n.2.toNat = _ at hn
  change o.1.toNat + 18446744073709551616*o.2.toNat = _ at ho
  have hq := q.isLt
  have hhi := hi.isLt
  have hc := Bool.toNat_le carry
  have hklt := k.1.isLt
  change n.1.toNat + 18446744073709551616*o.1.toNat = _
  change m0.1.toNat + 18446744073709551616*m0.2.toNat = q.toNat * 18446744073709551615 at hm0
  change m1.1.toNat + 18446744073709551616*m1.2.toNat = q.toNat * 4294967295 at hm1
  change y.1.toNat + 18446744073709551616*y.2.toNat = m1.2.toNat + 0 + x.2.toNat at hy
  change w.1.toNat + 18446744073709551616*w.2.toNat = y.1.toNat + 0 + z.2.toNat at hw
  change n.1.toNat + 18446744073709551616*n.2.toNat = z.1.toNat + 0 + k.2.toNat at hn
  change o.1.toNat + 18446744073709551616*o.2.toNat = w.1.toNat + 0 + n.2.toNat at ho
  clear_value m0 m1 x y z w k n o
  have cancel : m0.2.toNat + k.2.toNat = q.toNat := by
    clear hm1 hx hy hz hw hn ho hhi hc
    omega
  have total : n.1.toNat + 18446744073709551616*o.1.toNat +
      340282366920938463463374607431768211456*(y.2.toNat+w.2.toNat+o.2.toNat) =
      hi.toNat+carry.toNat+q.toNat*4294967296 := by
    clear hm0 hk hq hhi hc hklt
    omega
  clear hm0 hm1 hx hy hz hw hk hn ho cancel hklt
  omega

theorem middleCarry_value (a b q modulus old c0 c1 : BitVec 64) :
    let r := middleCarry a b q modulus old c0 c1
    r.1.toNat + wordBase*r.2.1.toNat + wordBase^2*r.2.2.toNat =
      a.toNat*b.toNat + old.toNat + c0.toNat + wordBase*c1.toNat +
        wordBase*(q.toNat*modulus.toNat) := by
  let x := product64 a b
  let m := product64 q modulus
  let l := add64 x.1 old
  let h := adc64 m.1 x.2 l.2
  let j := adc64 m.2 0 h.2
  let k := add64 h.1 c1
  let n := adc64 j.1 0 k.2
  let o := add64 l.1 c0
  let r := adc64 k.1 0 o.2
  let s := adc64 n.1 0 r.2
  have hx := product64_value a b
  have hm := product64_value q modulus
  have hl := add64_value x.1 old
  have hh := adc64_value m.1 x.2 l.2
  have hj := adc64_value m.2 0 h.2
  have hk := add64_value h.1 c1
  have hn := adc64_value j.1 0 k.2
  have ho := add64_value l.1 c0
  have hr := adc64_value k.1 0 o.2
  have hs := adc64_value n.1 0 r.2
  change x.1.toNat + 18446744073709551616*x.2.toNat = _ at hx
  change m.1.toNat + 18446744073709551616*m.2.toNat = _ at hm
  change l.1.toNat + 18446744073709551616*l.2.toNat = _ at hl
  change h.1.toNat + 18446744073709551616*h.2.toNat = _ at hh
  change j.1.toNat + 18446744073709551616*j.2.toNat = _ at hj
  change k.1.toNat + 18446744073709551616*k.2.toNat = _ at hk
  change n.1.toNat + 18446744073709551616*n.2.toNat = _ at hn
  change o.1.toNat + 18446744073709551616*o.2.toNat = _ at ho
  change r.1.toNat + 18446744073709551616*r.2.toNat = _ at hr
  change s.1.toNat + 18446744073709551616*s.2.toNat = _ at hs
  have hxp := Nat.mul_le_mul (Nat.le_pred_of_lt a.isLt) (Nat.le_pred_of_lt b.isLt)
  change a.toNat*b.toNat ≤ 18446744073709551615*18446744073709551615 at hxp
  have hmp := Nat.mul_le_mul (Nat.le_pred_of_lt q.isLt) (Nat.le_pred_of_lt modulus.isLt)
  change q.toNat*modulus.toNat ≤ 18446744073709551615*18446744073709551615 at hmp
  have hold := old.isLt
  have hc0 := c0.isLt
  have hc1 := c1.isLt
  change o.1.toNat + 18446744073709551616*r.1.toNat + 18446744073709551616^2*s.1.toNat =
    a.toNat*b.toNat + old.toNat + c0.toNat + 18446744073709551616*c1.toNat +
      18446744073709551616*(q.toNat*modulus.toNat)
  change j.1.toNat + 18446744073709551616*j.2.toNat = m.2.toNat + 0 + h.2.toNat at hj
  change n.1.toNat + 18446744073709551616*n.2.toNat = j.1.toNat + 0 + k.2.toNat at hn
  change r.1.toNat + 18446744073709551616*r.2.toNat = k.1.toNat + 0 + o.2.toNat at hr
  change s.1.toNat + 18446744073709551616*s.2.toNat = n.1.toNat + 0 + r.2.toNat at hs
  clear_value x m l h j k n o r s
  have total : o.1.toNat + 18446744073709551616*r.1.toNat +
      340282366920938463463374607431768211456*s.1.toNat +
      6277101735386680763835789423207666416102355444464034512896*(j.2.toNat+n.2.toNat+s.2.toNat) =
      a.toNat*b.toNat+old.toNat+c0.toNat+18446744073709551616*c1.toNat+
        18446744073709551616*(q.toNat*modulus.toNat) := by
    clear hxp hmp hold hc0 hc1
    omega
  clear hx hm hl hh hj hk hn ho hr hs
  omega


end P256.Proofs.Sec1.SquareRoot.SquareFour
