import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.CarryValues
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Core
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Identities
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Model
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Recurrence
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Rows
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Top
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Words

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

theorem multiplyWords_limbs (a b : Vector (BitVec 64) 4) :
    let r := multiplyWords a b
    P256.Proofs.Sec1.SquareRoot.Montgomery.limbsToNat r.first.toNat r.second.toNat r.top.low.toNat r.top.mid.toNat +
      2^256*r.top.high.toNat = P256.Proofs.Field.Montgomery.reduceFour (wordsValue a*wordsValue b) := by
  rw [← multiplyWords_value]
  change P256.Proofs.Sec1.SquareRoot.Montgomery.limbsToNat (multiplyWords a b).first.toNat (multiplyWords a b).second.toNat
      (multiplyWords a b).top.low.toNat (multiplyWords a b).top.mid.toNat +
    2^256*(multiplyWords a b).top.high.toNat = (multiplyWords a b).value
  generalize multiplyWords a b = r
  unfold P256.Proofs.Sec1.SquareRoot.Montgomery.limbsToNat FinalWords.value wordBase
  omega

end P256.Proofs.Sec1.SquareRoot.Montgomery
