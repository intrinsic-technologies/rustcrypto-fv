import P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product.Certificate

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product

open P256.Spec P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Scalar.Multiply.Arithmetic.Support X86Proofs

theorem orderMiddle_high_bound (a lo hi : Nat) (bound : a < 18446744073709551616)
    (value : lo + 18446744073709551616*hi = a*13611842547513532036) :
    hi + 2 < 18446744073709551616 := by omega

theorem carrySmall_zero (hi carry lo overflow : Nat) (bound : hi + 1 < 18446744073709551616)
    (bit : carry ≤ 1) (value : lo + 18446744073709551616*overflow = hi + carry) :
    overflow = 0 ∧ lo ≤ hi + 1 := by omega

theorem subMod_certificate (a b r : Nat) (bound : b ≤ 18446744073709551616)
    (value : r = (18446744073709551616 - b + a) % 18446744073709551616) :
    r + 18446744073709551616*((18446744073709551616 - b + a) / 18446744073709551616) + b =
      18446744073709551616 + a := by
  have h := Nat.mod_add_div (18446744073709551616 - b + a) 18446744073709551616
  omega

structure ProductWordCalculation where
  a : BitVec 64
  b : BitVec 64
  c : BitVec 64
  d : BitVec 64
  e : BitVec 64
  v1185e6 : BitVec 64
  hv1185e6 : BitVec 64
  v118600 : BitVec 64
  hv118600 : BitVec 64
  v118615 : BitVec 64
  hv118615 : BitVec 64
  v118623 : BitVec 64
  v11862a : BitVec 64
  v11862e : BitVec 64 × X86Proofs.StatusFlags
  v118631 : BitVec 64
  v118641 : BitVec 64
  hv118641 : BitVec 64
  v11864a : BitVec 64
  v11864e : BitVec 64 × X86Proofs.StatusFlags
  v118654 : BitVec 64
  hv118654 : BitVec 64
  v11866a : BitVec 64
  hv11866a : BitVec 64
  v118670 : BitVec 64 × X86Proofs.StatusFlags
  v118675 : BitVec 64 × X86Proofs.StatusFlags
  v11867a : BitVec 64 × X86Proofs.StatusFlags
  v11867f : BitVec 64 × X86Proofs.StatusFlags
  v118682 : BitVec 64 × X86Proofs.StatusFlags
  v118685 : BitVec 64 × X86Proofs.StatusFlags
  v118689 : BitVec 64 × X86Proofs.StatusFlags
  v11868c : BitVec 64 × X86Proofs.StatusFlags
  v11868f : BitVec 64 × X86Proofs.StatusFlags
  v11869d : BitVec 64
  hv11869d : BitVec 64
  v1186a6 : BitVec 64 × X86Proofs.StatusFlags
  v1186a9 : BitVec 64 × X86Proofs.StatusFlags
  v1186b0 : BitVec 64
  hv1186b0 : BitVec 64
  v1186c6 : BitVec 64
  hv1186c6 : BitVec 64
  v1186cc : BitVec 64 × X86Proofs.StatusFlags
  v1186cf : BitVec 64 × X86Proofs.StatusFlags
  v1186d2 : BitVec 64 × X86Proofs.StatusFlags
  v1186d5 : BitVec 64 × X86Proofs.StatusFlags
  v1186dc : BitVec 64
  hv1186dc : BitVec 64
  v1186e2 : BitVec 64 × X86Proofs.StatusFlags
  v1186e5 : BitVec 64 × X86Proofs.StatusFlags
  v1186e8 : BitVec 64 × X86Proofs.StatusFlags
  v1186f3 : BitVec 64 × X86Proofs.StatusFlags
  v1186f6 : BitVec 64 × X86Proofs.StatusFlags
  v1185e6_eq : v1185e6 = a * (17562291160714782033 : BitVec 64)
  hv1185e6_eq : hv1185e6 = mulHigh64 a (17562291160714782033 : BitVec 64)
  v118600_eq : v118600 = a * (13611842547513532036 : BitVec 64)
  hv118600_eq : hv118600 = mulHigh64 a (13611842547513532036 : BitVec 64)
  v118615_eq : v118615 = a * (18446744073709551615 : BitVec 64)
  hv118615_eq : hv118615 = mulHigh64 a (18446744073709551615 : BitVec 64)
  v118623_eq : v118623 = b <<< 32
  v11862a_eq : v11862a = d * (13611842547513532036 : BitVec 64)
  v11862e_eq : v11862e = addSpec v118623 c
  v118631_eq : v118631 = v11862a - v11862e.1
  v118641_eq : v118641 = a * (18446744069414584320 : BitVec 64)
  hv118641_eq : hv118641 = mulHigh64 a (18446744069414584320 : BitVec 64)
  v11864a_eq : v11864a = e * (17562291160714782033 : BitVec 64)
  v11864e_eq : v11864e = addSpec v118631 v11864a
  v118654_eq : v118654 = b * (17562291160714782033 : BitVec 64)
  hv118654_eq : hv118654 = mulHigh64 b (17562291160714782033 : BitVec 64)
  v11866a_eq : v11866a = b * (13611842547513532036 : BitVec 64)
  hv11866a_eq : hv11866a = mulHigh64 b (13611842547513532036 : BitVec 64)
  v118670_eq : v118670 = addSpec v118600 hv1185e6
  v118675_eq : v118675 = adcSpec v118615 hv118600 (BitVec.ofBool v118670.2.CF)
  v11867a_eq : v11867a = adcSpec v118641 hv118615 (BitVec.ofBool v118675.2.CF)
  v11867f_eq : v11867f = adcSpec v11864e.1 hv118641 (BitVec.ofBool v11867a.2.CF)
  v118682_eq : v118682 = addSpec v118675.1 v11866a
  v118685_eq : v118685 = adcSpec hv11866a (0 : BitVec 64) (BitVec.ofBool v118682.2.CF)
  v118689_eq : v118689 = addSpec v118670.1 v118654
  v11868c_eq : v11868c = adcSpec v118682.1 hv118654 (BitVec.ofBool v118689.2.CF)
  v11868f_eq : v11868f = adcSpec v118685.1 (0 : BitVec 64) (BitVec.ofBool v11868c.2.CF)
  v11869d_eq : v11869d = b * (18446744073709551615 : BitVec 64)
  hv11869d_eq : hv11869d = mulHigh64 b (18446744073709551615 : BitVec 64)
  v1186a6_eq : v1186a6 = addSpec v11869d v11867a.1
  v1186a9_eq : v1186a9 = adcSpec hv11869d (0 : BitVec 64) (BitVec.ofBool v1186a6.2.CF)
  v1186b0_eq : v1186b0 = c * (17562291160714782033 : BitVec 64)
  hv1186b0_eq : hv1186b0 = mulHigh64 c (17562291160714782033 : BitVec 64)
  v1186c6_eq : v1186c6 = c * (13611842547513532036 : BitVec 64)
  hv1186c6_eq : hv1186c6 = mulHigh64 c (13611842547513532036 : BitVec 64)
  v1186cc_eq : v1186cc = addSpec v1186a6.1 v11868f.1
  v1186cf_eq : v1186cf = adcSpec v1186a9.1 v11867f.1 (BitVec.ofBool v1186cc.2.CF)
  v1186d2_eq : v1186d2 = addSpec v1186cc.1 v1186c6
  v1186d5_eq : v1186d5 = adcSpec hv1186c6 (0 : BitVec 64) (BitVec.ofBool v1186d2.2.CF)
  v1186dc_eq : v1186dc = d * (17562291160714782033 : BitVec 64)
  hv1186dc_eq : hv1186dc = mulHigh64 d (17562291160714782033 : BitVec 64)
  v1186e2_eq : v1186e2 = addSpec v1186b0 v11868c.1
  v1186e5_eq : v1186e5 = adcSpec v1186d2.1 hv1186b0 (BitVec.ofBool v1186e2.2.CF)
  v1186e8_eq : v1186e8 = adcSpec v1186d5.1 v1186cf.1 (BitVec.ofBool v1186e5.2.CF)
  v1186f3_eq : v1186f3 = addSpec v1186e5.1 v1186dc
  v1186f6_eq : v1186f6 = adcSpec v1186e8.1 hv1186dc (BitVec.ofBool v1186f3.2.CF)

attribute [local irreducible] mulHigh64 addSpec P256.Proofs.Common.Instructions.Carry.adcSpec

set_option maxRecDepth 4096 in
set_option maxHeartbeats 100000 in
theorem ProductWordCalculation.value (w : ProductWordCalculation) :
    w.v1185e6.toNat + 18446744073709551616*w.v118689.1.toNat + 340282366920938463463374607431768211456*w.v1186e2.1.toNat + 6277101735386680763835789423207666416102355444464034512896*w.v1186f3.1.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*w.v1186f6.1.toNat =
    ((w.a.toNat + 18446744073709551616*w.b.toNat + 340282366920938463463374607431768211456*w.c.toNat + 6277101735386680763835789423207666416102355444464034512896*w.d.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*w.e.toNat)*115792089210356248762697446949407573529996955224135760342422259061068512044369) % 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 := by
  rcases w with ⟨a, b, c, d, e, v1185e6, hv1185e6, v118600, hv118600, v118615, hv118615, v118623, v11862a, v11862e, v118631, v118641, hv118641, v11864a, v11864e, v118654, hv118654, v11866a, hv11866a, v118670, v118675, v11867a, v11867f, v118682, v118685, v118689, v11868c, v11868f, v11869d, hv11869d, v1186a6, v1186a9, v1186b0, hv1186b0, v1186c6, hv1186c6, v1186cc, v1186cf, v1186d2, v1186d5, v1186dc, hv1186dc, v1186e2, v1186e5, v1186e8, v1186f3, v1186f6, v1185e6_eq, hv1185e6_eq, v118600_eq, hv118600_eq, v118615_eq, hv118615_eq, v118623_eq, v11862a_eq, v11862e_eq, v118631_eq, v118641_eq, hv118641_eq, v11864a_eq, v11864e_eq, v118654_eq, hv118654_eq, v11866a_eq, hv11866a_eq, v118670_eq, v118675_eq, v11867a_eq, v11867f_eq, v118682_eq, v118685_eq, v118689_eq, v11868c_eq, v11868f_eq, v11869d_eq, hv11869d_eq, v1186a6_eq, v1186a9_eq, v1186b0_eq, hv1186b0_eq, v1186c6_eq, hv1186c6_eq, v1186cc_eq, v1186cf_eq, v1186d2_eq, v1186d5_eq, v1186dc_eq, hv1186dc_eq, v1186e2_eq, v1186e5_eq, v1186e8_eq, v1186f3_eq, v1186f6_eq⟩
  change v1185e6.toNat + 18446744073709551616*v118689.1.toNat + 340282366920938463463374607431768211456*v1186e2.1.toNat + 6277101735386680763835789423207666416102355444464034512896*v1186f3.1.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*v1186f6.1.toNat =
    ((a.toNat + 18446744073709551616*b.toNat + 340282366920938463463374607431768211456*c.toNat + 6277101735386680763835789423207666416102355444464034512896*d.toNat + 115792089237316195423570985008687907853269984665640564039457584007913129639936*e.toNat)*115792089210356248762697446949407573529996955224135760342422259061068512044369) % 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576
  have ev1185e6 : v1185e6.toNat + 18446744073709551616*hv1185e6.toNat = a.toNat*17562291160714782033 := by
    rw [ v1185e6_eq, hv1185e6_eq ]
    have h := mul64_toNat_add_high a (17562291160714782033 : BitVec 64)
    exact h
  have ev118600 : v118600.toNat + 18446744073709551616*hv118600.toNat = a.toNat*13611842547513532036 := by
    rw [ v118600_eq, hv118600_eq ]
    have h := mul64_toNat_add_high a (13611842547513532036 : BitVec 64)
    exact h
  have ev118615 : v118615.toNat + 18446744073709551616*hv118615.toNat = a.toNat*18446744073709551615 := by
    rw [ v118615_eq, hv118615_eq ]
    have h := mul64_toNat_add_high a (18446744073709551615 : BitVec 64)
    exact h
  have ev118623 : v118623.toNat = b.toNat*4294967296 % 18446744073709551616 := by
    rw [ v118623_eq ]
    have h := (BitVec.toNat_shiftLeft (x := b) (n := 32))
    rw [Nat.shiftLeft_eq] at h
    exact h
  have ev11862a : v11862a.toNat = d.toNat*13611842547513532036 % 18446744073709551616 := by
    rw [ v11862a_eq ]
    have h := BitVec.toNat_mul d (13611842547513532036 : BitVec 64)
    exact h
  have ev11862e : v11862e.1.toNat + 18446744073709551616*v11862e.2.CF.toNat = v118623.toNat + c.toNat := by
    rw [ v11862e_eq ]
    have h := addSpec_toNat_add_carry v118623 c
    exact h
  have ev118631 : v118631.toNat = ((18446744073709551616 - v11862e.1.toNat) + v11862a.toNat) % 18446744073709551616 := by
    rw [ v118631_eq ]
    have h := BitVec.toNat_sub v11862a v11862e.1
    exact h
  have ev118641 : v118641.toNat + 18446744073709551616*hv118641.toNat = a.toNat*18446744069414584320 := by
    rw [ v118641_eq, hv118641_eq ]
    have h := mul64_toNat_add_high a (18446744069414584320 : BitVec 64)
    exact h
  have ev11864a : v11864a.toNat = e.toNat*17562291160714782033 % 18446744073709551616 := by
    rw [ v11864a_eq ]
    have h := BitVec.toNat_mul e (17562291160714782033 : BitVec 64)
    exact h
  have ev11864e : v11864e.1.toNat + 18446744073709551616*v11864e.2.CF.toNat = v118631.toNat + v11864a.toNat := by
    rw [ v11864e_eq ]
    have h := addSpec_toNat_add_carry v118631 v11864a
    exact h
  have ev118654 : v118654.toNat + 18446744073709551616*hv118654.toNat = b.toNat*17562291160714782033 := by
    rw [ v118654_eq, hv118654_eq ]
    have h := mul64_toNat_add_high b (17562291160714782033 : BitVec 64)
    exact h
  have ev11866a : v11866a.toNat + 18446744073709551616*hv11866a.toNat = b.toNat*13611842547513532036 := by
    rw [ v11866a_eq, hv11866a_eq ]
    have h := mul64_toNat_add_high b (13611842547513532036 : BitVec 64)
    exact h
  have ev118670 : v118670.1.toNat + 18446744073709551616*v118670.2.CF.toNat = v118600.toNat + hv1185e6.toNat := by
    rw [ v118670_eq ]
    have h := addSpec_toNat_add_carry v118600 hv1185e6
    exact h
  have ev118675 : v118675.1.toNat + 18446744073709551616*v118675.2.CF.toNat = v118615.toNat + hv118600.toNat + v118670.2.CF.toNat := by
    rw [ v118675_eq ]
    have h := adcSpec_toNat_add_carry v118615 hv118600 (BitVec.ofBool v118670.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev11867a : v11867a.1.toNat + 18446744073709551616*v11867a.2.CF.toNat = v118641.toNat + hv118615.toNat + v118675.2.CF.toNat := by
    rw [ v11867a_eq ]
    have h := adcSpec_toNat_add_carry v118641 hv118615 (BitVec.ofBool v118675.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev11867f : v11867f.1.toNat + 18446744073709551616*v11867f.2.CF.toNat = v11864e.1.toNat + hv118641.toNat + v11867a.2.CF.toNat := by
    rw [ v11867f_eq ]
    have h := adcSpec_toNat_add_carry v11864e.1 hv118641 (BitVec.ofBool v11867a.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev118682 : v118682.1.toNat + 18446744073709551616*v118682.2.CF.toNat = v118675.1.toNat + v11866a.toNat := by
    rw [ v118682_eq ]
    have h := addSpec_toNat_add_carry v118675.1 v11866a
    exact h
  have ev118685 : v118685.1.toNat + 18446744073709551616*v118685.2.CF.toNat = hv11866a.toNat + 0 + v118682.2.CF.toNat := by
    rw [ v118685_eq ]
    have h := adcSpec_toNat_add_carry hv11866a (0 : BitVec 64) (BitVec.ofBool v118682.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev118689 : v118689.1.toNat + 18446744073709551616*v118689.2.CF.toNat = v118670.1.toNat + v118654.toNat := by
    rw [ v118689_eq ]
    have h := addSpec_toNat_add_carry v118670.1 v118654
    exact h
  have ev11868c : v11868c.1.toNat + 18446744073709551616*v11868c.2.CF.toNat = v118682.1.toNat + hv118654.toNat + v118689.2.CF.toNat := by
    rw [ v11868c_eq ]
    have h := adcSpec_toNat_add_carry v118682.1 hv118654 (BitVec.ofBool v118689.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev11868f : v11868f.1.toNat + 18446744073709551616*v11868f.2.CF.toNat = v118685.1.toNat + 0 + v11868c.2.CF.toNat := by
    rw [ v11868f_eq ]
    have h := adcSpec_toNat_add_carry v118685.1 (0 : BitVec 64) (BitVec.ofBool v11868c.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev11869d : v11869d.toNat + 18446744073709551616*hv11869d.toNat = b.toNat*18446744073709551615 := by
    rw [ v11869d_eq, hv11869d_eq ]
    have h := mul64_toNat_add_high b (18446744073709551615 : BitVec 64)
    exact h
  have ev1186a6 : v1186a6.1.toNat + 18446744073709551616*v1186a6.2.CF.toNat = v11869d.toNat + v11867a.1.toNat := by
    rw [ v1186a6_eq ]
    have h := addSpec_toNat_add_carry v11869d v11867a.1
    exact h
  have ev1186a9 : v1186a9.1.toNat + 18446744073709551616*v1186a9.2.CF.toNat = hv11869d.toNat + 0 + v1186a6.2.CF.toNat := by
    rw [ v1186a9_eq ]
    have h := adcSpec_toNat_add_carry hv11869d (0 : BitVec 64) (BitVec.ofBool v1186a6.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev1186b0 : v1186b0.toNat + 18446744073709551616*hv1186b0.toNat = c.toNat*17562291160714782033 := by
    rw [ v1186b0_eq, hv1186b0_eq ]
    have h := mul64_toNat_add_high c (17562291160714782033 : BitVec 64)
    exact h
  have ev1186c6 : v1186c6.toNat + 18446744073709551616*hv1186c6.toNat = c.toNat*13611842547513532036 := by
    rw [ v1186c6_eq, hv1186c6_eq ]
    have h := mul64_toNat_add_high c (13611842547513532036 : BitVec 64)
    exact h
  have ev1186cc : v1186cc.1.toNat + 18446744073709551616*v1186cc.2.CF.toNat = v1186a6.1.toNat + v11868f.1.toNat := by
    rw [ v1186cc_eq ]
    have h := addSpec_toNat_add_carry v1186a6.1 v11868f.1
    exact h
  have ev1186cf : v1186cf.1.toNat + 18446744073709551616*v1186cf.2.CF.toNat = v1186a9.1.toNat + v11867f.1.toNat + v1186cc.2.CF.toNat := by
    rw [ v1186cf_eq ]
    have h := adcSpec_toNat_add_carry v1186a9.1 v11867f.1 (BitVec.ofBool v1186cc.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev1186d2 : v1186d2.1.toNat + 18446744073709551616*v1186d2.2.CF.toNat = v1186cc.1.toNat + v1186c6.toNat := by
    rw [ v1186d2_eq ]
    have h := addSpec_toNat_add_carry v1186cc.1 v1186c6
    exact h
  have ev1186d5 : v1186d5.1.toNat + 18446744073709551616*v1186d5.2.CF.toNat = hv1186c6.toNat + 0 + v1186d2.2.CF.toNat := by
    rw [ v1186d5_eq ]
    have h := adcSpec_toNat_add_carry hv1186c6 (0 : BitVec 64) (BitVec.ofBool v1186d2.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev1186dc : v1186dc.toNat + 18446744073709551616*hv1186dc.toNat = d.toNat*17562291160714782033 := by
    rw [ v1186dc_eq, hv1186dc_eq ]
    have h := mul64_toNat_add_high d (17562291160714782033 : BitVec 64)
    exact h
  have ev1186e2 : v1186e2.1.toNat + 18446744073709551616*v1186e2.2.CF.toNat = v1186b0.toNat + v11868c.1.toNat := by
    rw [ v1186e2_eq ]
    have h := addSpec_toNat_add_carry v1186b0 v11868c.1
    exact h
  have ev1186e5 : v1186e5.1.toNat + 18446744073709551616*v1186e5.2.CF.toNat = v1186d2.1.toNat + hv1186b0.toNat + v1186e2.2.CF.toNat := by
    rw [ v1186e5_eq ]
    have h := adcSpec_toNat_add_carry v1186d2.1 hv1186b0 (BitVec.ofBool v1186e2.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev1186e8 : v1186e8.1.toNat + 18446744073709551616*v1186e8.2.CF.toNat = v1186d5.1.toNat + v1186cf.1.toNat + v1186e5.2.CF.toNat := by
    rw [ v1186e8_eq ]
    have h := adcSpec_toNat_add_carry v1186d5.1 v1186cf.1 (BitVec.ofBool v1186e5.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have ev1186f3 : v1186f3.1.toNat + 18446744073709551616*v1186f3.2.CF.toNat = v1186e5.1.toNat + v1186dc.toNat := by
    rw [ v1186f3_eq ]
    have h := addSpec_toNat_add_carry v1186e5.1 v1186dc
    exact h
  have ev1186f6 : v1186f6.1.toNat + 18446744073709551616*v1186f6.2.CF.toNat = v1186e8.1.toNat + hv1186dc.toNat + v1186f3.2.CF.toNat := by
    rw [ v1186f6_eq ]
    have h := adcSpec_toNat_add_carry v1186e8.1 hv1186dc (BitVec.ofBool v1186f3.2.CF)
    simp only [BitVec.toNat_ofBool] at h
    exact h
  have bv1185e6 := v1185e6.isLt
  have bhv1185e6 := hv1185e6.isLt
  have bv118600 := v118600.isLt
  have bhv118600 := hv118600.isLt
  have bv118615 := v118615.isLt
  have bhv118615 := hv118615.isLt
  have bv118623 := v118623.isLt
  have bv11862a := v11862a.isLt
  have bv11862e := v11862e.1.isLt
  have cv11862e := v11862e.2.CF.toNat_le
  have bv118631 := v118631.isLt
  have bv118641 := v118641.isLt
  have bhv118641 := hv118641.isLt
  have bv11864a := v11864a.isLt
  have bv11864e := v11864e.1.isLt
  have cv11864e := v11864e.2.CF.toNat_le
  have bv118654 := v118654.isLt
  have bhv118654 := hv118654.isLt
  have bv11866a := v11866a.isLt
  have bhv11866a := hv11866a.isLt
  have bv118670 := v118670.1.isLt
  have cv118670 := v118670.2.CF.toNat_le
  have bv118675 := v118675.1.isLt
  have cv118675 := v118675.2.CF.toNat_le
  have bv11867a := v11867a.1.isLt
  have cv11867a := v11867a.2.CF.toNat_le
  have bv11867f := v11867f.1.isLt
  have cv11867f := v11867f.2.CF.toNat_le
  have bv118682 := v118682.1.isLt
  have cv118682 := v118682.2.CF.toNat_le
  have bv118685 := v118685.1.isLt
  have cv118685 := v118685.2.CF.toNat_le
  have bv118689 := v118689.1.isLt
  have cv118689 := v118689.2.CF.toNat_le
  have bv11868c := v11868c.1.isLt
  have cv11868c := v11868c.2.CF.toNat_le
  have bv11868f := v11868f.1.isLt
  have cv11868f := v11868f.2.CF.toNat_le
  have bv11869d := v11869d.isLt
  have bhv11869d := hv11869d.isLt
  have bv1186a6 := v1186a6.1.isLt
  have cv1186a6 := v1186a6.2.CF.toNat_le
  have bv1186a9 := v1186a9.1.isLt
  have cv1186a9 := v1186a9.2.CF.toNat_le
  have bv1186b0 := v1186b0.isLt
  have bhv1186b0 := hv1186b0.isLt
  have bv1186c6 := v1186c6.isLt
  have bhv1186c6 := hv1186c6.isLt
  have bv1186cc := v1186cc.1.isLt
  have cv1186cc := v1186cc.2.CF.toNat_le
  have bv1186cf := v1186cf.1.isLt
  have cv1186cf := v1186cf.2.CF.toNat_le
  have bv1186d2 := v1186d2.1.isLt
  have cv1186d2 := v1186d2.2.CF.toNat_le
  have bv1186d5 := v1186d5.1.isLt
  have cv1186d5 := v1186d5.2.CF.toNat_le
  have bv1186dc := v1186dc.isLt
  have bhv1186dc := hv1186dc.isLt
  have bv1186e2 := v1186e2.1.isLt
  have cv1186e2 := v1186e2.2.CF.toNat_le
  have bv1186e5 := v1186e5.1.isLt
  have cv1186e5 := v1186e5.2.CF.toNat_le
  have bv1186e8 := v1186e8.1.isLt
  have cv1186e8 := v1186e8.2.CF.toNat_le
  have bv1186f3 := v1186f3.1.isLt
  have cv1186f3 := v1186f3.2.CF.toNat_le
  have bv1186f6 := v1186f6.1.isLt
  have cv1186f6 := v1186f6.2.CF.toNat_le
  have ba := a.isLt
  have bb := b.isLt
  have bc := c.isLt
  have bd := d.isLt
  have be := e.isLt
  let kv118623 := b.toNat*4294967296 / 18446744073709551616
  have dv118623 : v118623.toNat + 18446744073709551616*kv118623 = b.toNat*4294967296 := by
    simpa only [← ev118623] using (Nat.mod_add_div (b.toNat*4294967296) 18446744073709551616)
  let kv11862a := d.toNat*13611842547513532036 / 18446744073709551616
  have dv11862a : v11862a.toNat + 18446744073709551616*kv11862a = d.toNat*13611842547513532036 := by
    simpa only [← ev11862a] using (Nat.mod_add_div (d.toNat*13611842547513532036) 18446744073709551616)
  let kv11864a := e.toNat*17562291160714782033 / 18446744073709551616
  have dv11864a : v11864a.toNat + 18446744073709551616*kv11864a = e.toNat*17562291160714782033 := by
    simpa only [← ev11864a] using (Nat.mod_add_div (e.toNat*17562291160714782033) 18446744073709551616)
  let kv118631 := (18446744073709551616 - v11862e.1.toNat + v11862a.toNat) / 18446744073709551616
  have dv118631 : v118631.toNat + 18446744073709551616*kv118631 + v11862e.1.toNat = 18446744073709551616+v11862a.toNat :=
    subMod_certificate _ _ _ (Nat.le_of_lt bv11862e) ev118631
  clear_value kv118623 kv11862a kv11864a kv118631
  have highBound := orderMiddle_high_bound b.toNat v11866a.toNat hv11866a.toNat bb ev11866a
  have z1 := carrySmall_zero hv11866a.toNat v118682.2.CF.toNat v118685.1.toNat v118685.2.CF.toNat
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide : 1 ≤ 2) _) highBound) cv118682 (by simpa only [Nat.add_zero] using ev118685)
  have z2 := carrySmall_zero v118685.1.toNat v11868c.2.CF.toNat v11868f.1.toNat v11868f.2.CF.toNat
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right z1.2 1) highBound) cv11868c (by simpa only [Nat.add_zero] using ev11868f)
  clear bhv1185e6 bv118600 bhv118600 bv118615 bhv118615 bv118623 bv11862a cv11862e bv118631 bv118641 bhv118641 bv11864a bv11864e cv11864e bv118654 bhv118654 bv11866a bhv11866a bv118670 cv118670 bv118675 cv118675 bv11867a cv11867a bv11867f cv11867f bv118682 cv118682 bv118685 cv118685 cv118689 bv11868c cv11868c bv11868f cv11868f bv11869d bhv11869d bv1186a6 cv1186a6 bv1186a9 cv1186a9 bv1186b0 bhv1186b0 bv1186c6 bhv1186c6 bv1186cc cv1186cc bv1186cf cv1186cf bv1186d2 cv1186d2 bv1186d5 cv1186d5 bv1186dc bhv1186dc cv1186e2 bv1186e5 cv1186e5 bv1186e8 cv1186e8 cv1186f3 cv1186f6 ba bb bc bd be highBound
  clear ev118623 ev11862a ev11864a ev118631
  exact ProductCalculation.value {
    v1185e6 := v1185e6.toNat
    hv1185e6 := hv1185e6.toNat
    a := a.toNat
    v118600 := v118600.toNat
    hv118600 := hv118600.toNat
    v118615 := v118615.toNat
    hv118615 := hv118615.toNat
    v11862e := v11862e.1.toNat
    cv11862e := v11862e.2.CF.toNat
    v118623 := v118623.toNat
    c := c.toNat
    v118641 := v118641.toNat
    hv118641 := hv118641.toNat
    v11864e := v11864e.1.toNat
    cv11864e := v11864e.2.CF.toNat
    v118631 := v118631.toNat
    v11864a := v11864a.toNat
    v118654 := v118654.toNat
    hv118654 := hv118654.toNat
    b := b.toNat
    v11866a := v11866a.toNat
    hv11866a := hv11866a.toNat
    v118670 := v118670.1.toNat
    cv118670 := v118670.2.CF.toNat
    v118675 := v118675.1.toNat
    cv118675 := v118675.2.CF.toNat
    v11867a := v11867a.1.toNat
    cv11867a := v11867a.2.CF.toNat
    v11867f := v11867f.1.toNat
    cv11867f := v11867f.2.CF.toNat
    v118682 := v118682.1.toNat
    cv118682 := v118682.2.CF.toNat
    v118685 := v118685.1.toNat
    cv118685 := v118685.2.CF.toNat
    v118689 := v118689.1.toNat
    cv118689 := v118689.2.CF.toNat
    v11868c := v11868c.1.toNat
    cv11868c := v11868c.2.CF.toNat
    v11868f := v11868f.1.toNat
    cv11868f := v11868f.2.CF.toNat
    v11869d := v11869d.toNat
    hv11869d := hv11869d.toNat
    v1186a6 := v1186a6.1.toNat
    cv1186a6 := v1186a6.2.CF.toNat
    v1186a9 := v1186a9.1.toNat
    cv1186a9 := v1186a9.2.CF.toNat
    v1186b0 := v1186b0.toNat
    hv1186b0 := hv1186b0.toNat
    v1186c6 := v1186c6.toNat
    hv1186c6 := hv1186c6.toNat
    v1186cc := v1186cc.1.toNat
    cv1186cc := v1186cc.2.CF.toNat
    v1186cf := v1186cf.1.toNat
    cv1186cf := v1186cf.2.CF.toNat
    v1186d2 := v1186d2.1.toNat
    cv1186d2 := v1186d2.2.CF.toNat
    v1186d5 := v1186d5.1.toNat
    cv1186d5 := v1186d5.2.CF.toNat
    v1186dc := v1186dc.toNat
    hv1186dc := hv1186dc.toNat
    d := d.toNat
    v1186e2 := v1186e2.1.toNat
    cv1186e2 := v1186e2.2.CF.toNat
    v1186e5 := v1186e5.1.toNat
    cv1186e5 := v1186e5.2.CF.toNat
    v1186e8 := v1186e8.1.toNat
    cv1186e8 := v1186e8.2.CF.toNat
    v1186f3 := v1186f3.1.toNat
    cv1186f3 := v1186f3.2.CF.toNat
    v1186f6 := v1186f6.1.toNat
    cv1186f6 := v1186f6.2.CF.toNat
    kv118623 := kv118623
    v11862a := v11862a.toNat
    kv11862a := kv11862a
    kv11864a := kv11864a
    e := e.toNat
    kv118631 := kv118631
    ev1185e6 := ev1185e6
    ev118600 := ev118600
    ev118615 := ev118615
    ev11862e := ev11862e
    ev118641 := ev118641
    ev11864e := ev11864e
    ev118654 := ev118654
    ev11866a := ev11866a
    ev118670 := ev118670
    ev118675 := ev118675
    ev11867a := ev11867a
    ev11867f := ev11867f
    ev118682 := ev118682
    ev118685 := ev118685
    ev118689 := ev118689
    ev11868c := ev11868c
    ev11868f := ev11868f
    ev11869d := ev11869d
    ev1186a6 := ev1186a6
    ev1186a9 := ev1186a9
    ev1186b0 := ev1186b0
    ev1186c6 := ev1186c6
    ev1186cc := ev1186cc
    ev1186cf := ev1186cf
    ev1186d2 := ev1186d2
    ev1186d5 := ev1186d5
    ev1186dc := ev1186dc
    ev1186e2 := ev1186e2
    ev1186e5 := ev1186e5
    ev1186e8 := ev1186e8
    ev1186f3 := ev1186f3
    ev1186f6 := ev1186f6
    dv118623 := dv118623
    dv11862a := dv11862a
    dv11864a := dv11864a
    dv118631 := dv118631
    zero675 := z1.1
    zero67f := z2.1
    bv1185e6 := bv1185e6
    bv118689 := bv118689
    bv1186e2 := bv1186e2
    bv1186f3 := bv1186f3
    bv1186f6 := bv1186f6
  }


end P256.Proofs.Scalar.Multiply.Arithmetic.Natural.Barrett.Product
