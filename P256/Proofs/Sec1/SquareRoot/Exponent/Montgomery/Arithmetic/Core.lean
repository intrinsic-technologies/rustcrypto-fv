import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Model
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.CarryValues

set_option autoImplicit false

open P256.Proofs.Field.Montgomery (p reduceStep)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

theorem reduceStep_of_scaled (r t q : Nat) (hq : q < wordBase)
    (h : r * wordBase = t + q * p) : r = reduceStep t := by
  rw [P256.Proofs.Field.Montgomery.reduceStep_eq]
  change r * 18446744073709551616 = t + q *
    115792089210356248762697446949407573530086143415290314195533631308867097853951 at h
  change q < 18446744073709551616 at hq
  change r = t / 18446744073709551616 + (t % 18446744073709551616) *
    6277101733925179126845168871924920046849447032244165148672
  omega

theorem coreWords_value (old0 old1 old2 a : BitVec 64) (b : Vector (BitVec 64) 4) :
    (coreWords old0 old1 old2 a b).value = reduceStep
      (old0.toNat + wordBase*old1.toNat + wordBase^2*old2.toNat + a.toNat*lowerWordsValue b) := by
  have expanded : a.toNat*lowerWordsValue b =
      a.toNat*b[0].toNat + 18446744073709551616*(a.toNat*b[1].toNat) +
        340282366920938463463374607431768211456*(a.toNat*b[2].toNat) := by
    unfold lowerWordsValue wordBase
    grind only
  let x := product64 a b[0]
  let q := add64 x.1 old0
  let c := startCarry q.1 x.2 q.2
  let m := middleCarry a b[1] q.1 0 old1 c.1 c.2
  let n := middleCarry a b[2] q.1 0xffffffff00000001 old2 m.2.1 m.2.2
  have hx := product64_value a b[0]
  have hq := add64_value x.1 old0
  have hc := startCarry_value q.1 x.2 q.2
  have hm := middleCarry_value a b[1] q.1 0 old1 c.1 c.2
  have hn := middleCarry_value a b[2] q.1 0xffffffff00000001 old2 m.2.1 m.2.2
  change x.1.toNat + 18446744073709551616*x.2.toNat = a.toNat*b[0].toNat at hx
  change q.1.toNat + 18446744073709551616*q.2.toNat = x.1.toNat + old0.toNat at hq
  change c.1.toNat + 18446744073709551616*c.2.toNat = x.2.toNat + q.2.toNat + q.1.toNat*4294967296 at hc
  change m.1.toNat + 18446744073709551616*m.2.1.toNat +
    340282366920938463463374607431768211456*m.2.2.toNat =
      a.toNat*b[1].toNat+old1.toNat+c.1.toNat+18446744073709551616*c.2.toNat+18446744073709551616*(q.1.toNat*0) at hm
  change n.1.toNat + 18446744073709551616*n.2.1.toNat +
    340282366920938463463374607431768211456*n.2.2.toNat =
      a.toNat*b[2].toNat+old2.toNat+m.2.1.toNat+18446744073709551616*m.2.2.toNat+
        18446744073709551616*(q.1.toNat*18446744069414584321) at hn
  apply reduceStep_of_scaled _ _ q.1.toNat q.1.isLt
  change (m.1.toNat + 18446744073709551616*n.1.toNat +
    340282366920938463463374607431768211456*n.2.1.toNat +
    6277101735386680763835789423207666416102355444464034512896*n.2.2.toNat)*18446744073709551616 =
      old0.toNat + 18446744073709551616*old1.toNat + 340282366920938463463374607431768211456*old2.toNat +
        a.toNat*lowerWordsValue b + q.1.toNat*115792089210356248762697446949407573530086143415290314195533631308867097853951
  clear_value x q c m n
  omega

end P256.Proofs.Sec1.SquareRoot.Montgomery
