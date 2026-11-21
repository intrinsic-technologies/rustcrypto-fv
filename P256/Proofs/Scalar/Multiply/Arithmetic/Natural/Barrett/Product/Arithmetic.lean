import P256.Proofs.Scalar.Multiply.Arithmetic.Support
import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product.WordArithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product

open P256.Spec P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Scalar.Multiply.Arithmetic.Support X86Proofs

set_option exponentiation.threshold 512 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 100000 in
theorem productWords_value (q : Vector (BitVec 64) 5) :
    quotientValue (productWords q) = (quotientValue q * P256.Spec.Operations.domain.n) % 2^320 := by
  let a := q[0]
  let b := q[1]
  let c := q[2]
  let d := q[3]
  let e := q[4]
  let v1185e6 := a * (17562291160714782033 : BitVec 64)
  let hv1185e6 := mulHigh64 a (17562291160714782033 : BitVec 64)
  let v118600 := a * (13611842547513532036 : BitVec 64)
  let hv118600 := mulHigh64 a (13611842547513532036 : BitVec 64)
  let v118615 := a * (18446744073709551615 : BitVec 64)
  let hv118615 := mulHigh64 a (18446744073709551615 : BitVec 64)
  let v118623 := b <<< 32
  let v11862a := d * (13611842547513532036 : BitVec 64)
  let v11862e := addSpec v118623 c
  let v118631 := v11862a - v11862e.1
  let v118641 := a * (18446744069414584320 : BitVec 64)
  let hv118641 := mulHigh64 a (18446744069414584320 : BitVec 64)
  let v11864a := e * (17562291160714782033 : BitVec 64)
  let v11864e := addSpec v118631 v11864a
  let v118654 := b * (17562291160714782033 : BitVec 64)
  let hv118654 := mulHigh64 b (17562291160714782033 : BitVec 64)
  let v11866a := b * (13611842547513532036 : BitVec 64)
  let hv11866a := mulHigh64 b (13611842547513532036 : BitVec 64)
  let v118670 := addSpec v118600 hv1185e6
  let v118675 := adcSpec v118615 hv118600 (BitVec.ofBool v118670.2.CF)
  let v11867a := adcSpec v118641 hv118615 (BitVec.ofBool v118675.2.CF)
  let v11867f := adcSpec v11864e.1 hv118641 (BitVec.ofBool v11867a.2.CF)
  let v118682 := addSpec v118675.1 v11866a
  let v118685 := adcSpec hv11866a (0 : BitVec 64) (BitVec.ofBool v118682.2.CF)
  let v118689 := addSpec v118670.1 v118654
  let v11868c := adcSpec v118682.1 hv118654 (BitVec.ofBool v118689.2.CF)
  let v11868f := adcSpec v118685.1 (0 : BitVec 64) (BitVec.ofBool v11868c.2.CF)
  let v11869d := b * (18446744073709551615 : BitVec 64)
  let hv11869d := mulHigh64 b (18446744073709551615 : BitVec 64)
  let v1186a6 := addSpec v11869d v11867a.1
  let v1186a9 := adcSpec hv11869d (0 : BitVec 64) (BitVec.ofBool v1186a6.2.CF)
  let v1186b0 := c * (17562291160714782033 : BitVec 64)
  let hv1186b0 := mulHigh64 c (17562291160714782033 : BitVec 64)
  let v1186c6 := c * (13611842547513532036 : BitVec 64)
  let hv1186c6 := mulHigh64 c (13611842547513532036 : BitVec 64)
  let v1186cc := addSpec v1186a6.1 v11868f.1
  let v1186cf := adcSpec v1186a9.1 v11867f.1 (BitVec.ofBool v1186cc.2.CF)
  let v1186d2 := addSpec v1186cc.1 v1186c6
  let v1186d5 := adcSpec hv1186c6 (0 : BitVec 64) (BitVec.ofBool v1186d2.2.CF)
  let v1186dc := d * (17562291160714782033 : BitVec 64)
  let hv1186dc := mulHigh64 d (17562291160714782033 : BitVec 64)
  let v1186e2 := addSpec v1186b0 v11868c.1
  let v1186e5 := adcSpec v1186d2.1 hv1186b0 (BitVec.ofBool v1186e2.2.CF)
  let v1186e8 := adcSpec v1186d5.1 v1186cf.1 (BitVec.ofBool v1186e5.2.CF)
  let v1186f3 := addSpec v1186e5.1 v1186dc
  let v1186f6 := adcSpec v1186e8.1 hv1186dc (BitVec.ofBool v1186f3.2.CF)
  change v1185e6.toNat + 18446744073709551616*v118689.1.toNat + 340282366920938463463374607431768211456*v1186e2.1.toNat + 6277101735386680763835789423207666416102355444464034512896*v1186f3.1.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*v1186f6.1.toNat =
    ((a.toNat + 18446744073709551616*b.toNat + 340282366920938463463374607431768211456*c.toNat + 6277101735386680763835789423207666416102355444464034512896*d.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*e.toNat)*115792089210356248762697446949407573529996955224135760342422259061068512044369) % 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576
  exact ProductWordCalculation.value {
    a := a
    b := b
    c := c
    d := d
    e := e
    v1185e6 := v1185e6
    hv1185e6 := hv1185e6
    v118600 := v118600
    hv118600 := hv118600
    v118615 := v118615
    hv118615 := hv118615
    v118623 := v118623
    v11862a := v11862a
    v11862e := v11862e
    v118631 := v118631
    v118641 := v118641
    hv118641 := hv118641
    v11864a := v11864a
    v11864e := v11864e
    v118654 := v118654
    hv118654 := hv118654
    v11866a := v11866a
    hv11866a := hv11866a
    v118670 := v118670
    v118675 := v118675
    v11867a := v11867a
    v11867f := v11867f
    v118682 := v118682
    v118685 := v118685
    v118689 := v118689
    v11868c := v11868c
    v11868f := v11868f
    v11869d := v11869d
    hv11869d := hv11869d
    v1186a6 := v1186a6
    v1186a9 := v1186a9
    v1186b0 := v1186b0
    hv1186b0 := hv1186b0
    v1186c6 := v1186c6
    hv1186c6 := hv1186c6
    v1186cc := v1186cc
    v1186cf := v1186cf
    v1186d2 := v1186d2
    v1186d5 := v1186d5
    v1186dc := v1186dc
    hv1186dc := hv1186dc
    v1186e2 := v1186e2
    v1186e5 := v1186e5
    v1186e8 := v1186e8
    v1186f3 := v1186f3
    v1186f6 := v1186f6
    v1185e6_eq := rfl
    hv1185e6_eq := rfl
    v118600_eq := rfl
    hv118600_eq := rfl
    v118615_eq := rfl
    hv118615_eq := rfl
    v118623_eq := rfl
    v11862a_eq := rfl
    v11862e_eq := rfl
    v118631_eq := rfl
    v118641_eq := rfl
    hv118641_eq := rfl
    v11864a_eq := rfl
    v11864e_eq := rfl
    v118654_eq := rfl
    hv118654_eq := rfl
    v11866a_eq := rfl
    hv11866a_eq := rfl
    v118670_eq := rfl
    v118675_eq := rfl
    v11867a_eq := rfl
    v11867f_eq := rfl
    v118682_eq := rfl
    v118685_eq := rfl
    v118689_eq := rfl
    v11868c_eq := rfl
    v11868f_eq := rfl
    v11869d_eq := rfl
    hv11869d_eq := rfl
    v1186a6_eq := rfl
    v1186a9_eq := rfl
    v1186b0_eq := rfl
    hv1186b0_eq := rfl
    v1186c6_eq := rfl
    hv1186c6_eq := rfl
    v1186cc_eq := rfl
    v1186cf_eq := rfl
    v1186d2_eq := rfl
    v1186d5_eq := rfl
    v1186dc_eq := rfl
    hv1186dc_eq := rfl
    v1186e2_eq := rfl
    v1186e5_eq := rfl
    v1186e8_eq := rfl
    v1186f3_eq := rfl
    v1186f6_eq := rfl
  }

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product
