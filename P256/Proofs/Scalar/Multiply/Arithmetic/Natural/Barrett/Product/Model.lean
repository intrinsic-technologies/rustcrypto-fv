import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.RowArithmetic

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product

open P256.Spec P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Scalar.Multiply.Arithmetic.Support X86Proofs

def productWords (q : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
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
  #v[v1185e6, v118689.1, v1186e2.1, v1186f3.1, v1186f6.1]

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product
