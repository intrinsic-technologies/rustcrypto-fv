import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Arithmetic
import P256.Proofs.Scalar.Multiply.Arithmetic.Support

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec adcSpec_toNat_add_carry addSpec_toNat_add_carry)
open P256.Proofs.Scalar.Multiply.Arithmetic.Support (mul64_toNat_add_high wordBase)

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett

open X86Proofs

def quotientFirstRow (a : BitVec 64) : Vector (BitVec 64) 4 × Bool :=
  let q1 := addSpec (a * 0x43190552df1a6c21) (mulHigh64 a 0x012ffd85eedf9bfe)
  let q2 := adcSpec (a * 0xfffffffeffffffff) (mulHigh64 a 0x43190552df1a6c21) (BitVec.ofBool q1.2.CF)
  let q3 := adcSpec (a * 0xffffffff) (mulHigh64 a 0xfffffffeffffffff) (BitVec.ofBool q2.2.CF)
  let q4 := adcSpec (mulHigh64 a 0xffffffff) a (BitVec.ofBool q3.2.CF)
  (#v[q1.1, q2.1, q3.1, q4.1], q4.2.CF)

def quotientFirstValue (row : Vector (BitVec 64) 4 × Bool) : Nat :=
  row.1[0].toNat + 2^64*row.1[1].toNat + 2^128*row.1[2].toNat +
    2^192*row.1[3].toNat + 2^256*row.2.toNat

theorem quotientFirstRow_value (a : BitVec 64) :
    quotientFirstValue (quotientFirstRow a) = a.toNat * barrettMu / 2^64 := by
  let q1 := addSpec (a * 0x43190552df1a6c21) (mulHigh64 a 0x012ffd85eedf9bfe)
  let q2 := adcSpec (a * 0xfffffffeffffffff) (mulHigh64 a 0x43190552df1a6c21) (BitVec.ofBool q1.2.CF)
  let q3 := adcSpec (a * 0xffffffff) (mulHigh64 a 0xfffffffeffffffff) (BitVec.ofBool q2.2.CF)
  let q4 := adcSpec (mulHigh64 a 0xffffffff) a (BitVec.ofBool q3.2.CF)
  have h0 := mul64_toNat_add_high a 0x012ffd85eedf9bfe
  have h1 := mul64_toNat_add_high a 0x43190552df1a6c21
  have h2 := mul64_toNat_add_high a 0xfffffffeffffffff
  have h3 := mul64_toNat_add_high a 0xffffffff
  have e1 := addSpec_toNat_add_carry (a * 0x43190552df1a6c21) (mulHigh64 a 0x012ffd85eedf9bfe)
  have e2 := adcSpec_toNat_add_carry (a * 0xfffffffeffffffff) (mulHigh64 a 0x43190552df1a6c21) (BitVec.ofBool q1.2.CF)
  have e3 := adcSpec_toNat_add_carry (a * 0xffffffff) (mulHigh64 a 0xfffffffeffffffff) (BitVec.ofBool q2.2.CF)
  have e4 := adcSpec_toNat_add_carry (mulHigh64 a 0xffffffff) a (BitVec.ofBool q3.2.CF)
  change q1.1.toNat + 2^64*q1.2.CF.toNat = _ at e1
  change q2.1.toNat + 2^64*q2.2.CF.toNat = _ at e2
  change q3.1.toNat + 2^64*q3.2.CF.toNat = _ at e3
  change q4.1.toNat + 2^64*q4.2.CF.toNat = _ at e4
  simp only [BitVec.toNat_ofBool] at e2 e3 e4
  change q1.1.toNat + 2^64*q2.1.toNat + 2^128*q3.1.toNat +
    2^192*q4.1.toNat + 2^256*q4.2.CF.toNat = _
  have lowBound := (a * (0x012ffd85eedf9bfe : BitVec 64)).isLt
  clear_value q1 q2 q3 q4
  change (a * 0x12ffd85eedf9bfe).toNat + 2^64*(mulHigh64 a 0x12ffd85eedf9bfe).toNat = a.toNat * 85565669623438334 at h0
  change (a * 0x43190552df1a6c21).toNat + 2^64*(mulHigh64 a 0x43190552df1a6c21).toNat = a.toNat * 4834901528447446049 at h1
  change (a * 0xfffffffeffffffff).toNat + 2^64*(mulHigh64 a 0xfffffffeffffffff).toNat = a.toNat * 18446744069414584319 at h2
  change (a * 0xffffffff).toNat + 2^64*(mulHigh64 a 0xffffffff).toNat = a.toNat * 4294967295 at h3
  unfold barrettMu
  omega

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett
