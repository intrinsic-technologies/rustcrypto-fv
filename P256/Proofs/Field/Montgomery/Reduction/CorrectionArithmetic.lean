import P256.Proofs.Field.Montgomery.Reduction.RoundsArithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open P256.Proofs.SecretKeyFromBytes.Scalar

def carry (a b : BitVec 64) (c : Bool) : Bool :=
  decide (2^64 ≤ a.toNat + b.toNat + c.toNat)

def adc (a b : BitVec 64) (c : Bool) : BitVec 64 :=
  a + b + BitVec.ofNat 64 c.toNat

def subtractModulus (a : Limbs) : Limbs × BitVec 64 :=
  let r0 := a.l0 + 1
  let b0 := (~~~a.l0 ||| r0) >>> 63
  let r1 := a.l1 + (-b0).sshiftRight 63 + 0xffffffff00000001
  let b1 := (~~~a.l1 &&& r1) >>> 63
  let r2 := (-b1).sshiftRight 63 + a.l2
  let b2 := (~~~a.l2 &&& r2) >>> 63
  let r3 := a.l3 + (-b2).sshiftRight 63 + 0xffffffff
  let b3 := (~~~a.l3 ||| r3) >>> 63
  (⟨r0, r1, r2, r3⟩, b3)

def reduceSum (a : Limbs) (c : Bool) : Limbs :=
  let result := subtractModulus a
  let r0 := result.1.l0
  let r1 := result.1.l1
  let r2 := result.1.l2
  let r3 := result.1.l3
  let b3 := result.2
  let q := ((-b3).sshiftRight 63 + BitVec.ofNat 64 c.toNat) >>> 63
  let z0 := r0 - q
  let correction1 := ((-q).setWidth 32).setWidth 64
  let u1 := correction1 + r1
  let c1 := carry correction1 r1 false
  let c0 := decide (z0 < r0)
  let z1 := adc u1 0 c0
  let c2 := carry u1 0 c0
  let z2 := adc (BitVec.ofNat 64 c1.toNat) r2 c2
  let c3 := carry (BitVec.ofNat 64 c1.toNat) r2 c2
  let z3 := adc (-q &&& 0xffffffff00000001) r3 c3
  ⟨z0, z1, z2, z3⟩

def correct (r : Limbs) (q : BitVec 64) : Limbs :=
  let r0 := r.l0
  let r1 := r.l1
  let r2 := r.l2
  let r3 := r.l3
  let z0 := r0 - q
  let correction1 := ((-q).setWidth 32).setWidth 64
  let u1 := correction1 + r1
  let c1 := carry correction1 r1 false
  let c0 := decide (z0 < r0)
  let z1 := adc u1 0 c0
  let c2 := carry u1 0 c0
  let z2 := adc (BitVec.ofNat 64 c1.toNat) r2 c2
  let c3 := carry (BitVec.ofNat 64 c1.toNat) r2 c2
  let z3 := adc (0xffffffff00000001 &&& -q) r3 c3
  ⟨z0, z1, z2, z3⟩

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (adc a b c).toNat + 2^64 * (carry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := Bool.toNat_le c
  simp only [adc, carry, BitVec.toNat_add, BitVec.toNat_ofNat]
  by_cases h : 2^64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem adc_false (a b : BitVec 64) : adc a b false = a+b := by
  simp [adc]

theorem sub_one_carry (a : BitVec 64) :
    (a-1).toNat + 2^64 * (decide (a-1<a)).toNat = a.toNat + 2^64-1 := by
  have ha := a.isLt
  have he : (a-1).toNat = (2^64-1+a.toNat)%2^64 := rfl
  by_cases h : a-1<a
  · have h' : (a-1).toNat < a.toNat := h
    simp only [h, decide_true, Bool.toNat_true]
    omega
  · have h' : ¬ (a-1).toNat < a.toNat := h
    simp only [h, decide_false, Bool.toNat_false]
    omega

theorem correct_zero (r : Limbs) : correct r 0 = r := by
  have h0 := r.l0.isLt
  have h1 := r.l1.isLt
  have h2 := r.l2.isLt
  have h3 := r.l3.isLt
  simp [correct, carry, adc, Nat.not_le.mpr h1, Nat.not_le.mpr h2]

theorem correct_one_toNat (r : Limbs) :
    (correct r 1).toNat = (r.toNat + P256.Spec.Operations.domain.p) % 2^256 := by
  let c0 := decide (r.l0-1 < r.l0)
  let u1 := (0xffffffff : BitVec 64) + r.l1
  let c1 := carry (0xffffffff : BitVec 64) r.l1 false
  let c2 := carry u1 0 c0
  let c3 := carry (BitVec.ofNat 64 c1.toNat) r.l2 c2
  have h0 := sub_one_carry r.l0
  have h1 := adc_carry (0xffffffff : BitVec 64) r.l1 false
  have h2 := adc_carry u1 0 c0
  have h3 := adc_carry (BitVec.ofNat 64 c1.toNat) r.l2 c2
  have h4 := adc_carry (0xffffffff00000001 : BitVec 64) r.l3 c3
  rw [adc_false] at h1
  change u1.toNat + 2^64*c1.toNat = 4294967295 + r.l1.toNat + 0 at h1
  change (adc u1 0 c0).toNat + 2^64*c2.toNat = u1.toNat+0+c0.toNat at h2
  change (adc (BitVec.ofNat 64 c1.toNat) r.l2 c2).toNat + 2^64*c3.toNat =
    c1.toNat%2^64 + r.l2.toNat+c2.toNat at h3
  have hc1 := Bool.toNat_le c1
  have hl := limbs_toNat_lt (correct r 1)
  change (r.l0-1).toNat + 2^64*c0.toNat = _ at h0
  change (adc (0xffffffff00000001 : BitVec 64) r.l3 c3).toNat +
    2^64*(carry (0xffffffff00000001 : BitVec 64) r.l3 c3).toNat =
    18446744069414584321 + r.l3.toNat+c3.toNat at h4
  change ((r.l0-1).toNat + 2^64*((adc u1 0 c0).toNat +
    2^64*((adc (BitVec.ofNat 64 c1.toNat) r.l2 c2).toNat +
      2^64*(adc (0xffffffff00000001 : BitVec 64) r.l3 c3).toNat))) < 2^256 at hl
  change ((r.l0-1).toNat + 2^64*((adc u1 0 c0).toNat +
    2^64*((adc (BitVec.ofNat 64 c1.toNat) r.l2 c2).toNat +
      2^64*(adc (0xffffffff00000001 : BitVec 64) r.l3 c3).toNat))) = _
  simp only [Limbs.toNat, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
  omega

theorem subtractWord_borrow_and (a r : BitVec 64) (k b : Nat)
    (hk : k < 2^63) (hb : b ≤ 1)
    (hr : r.toNat = (2^64+a.toNat-k-b)%2^64) :
    ((~~~a &&& r) >>> 63).toNat ≤ 1 ∧
    r.toNat + k + b = a.toNat + 2^64 * ((~~~a &&& r) >>> 63).toNat := by
  have ha := a.isLt
  have hr' := r.isLt
  rw [shift63_toNat, BitVec.msb_and, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide, show decide (0 < 64) = true from rfl, Bool.true_and]
  by_cases h₁ : 2^63 ≤ a.toNat <;>
    by_cases h₂ : 2^63 ≤ r.toNat <;>
    simp only [show 64-1=63 from rfl, h₁, h₂, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.toNat_true, Bool.toNat_false] <;> omega

theorem subtractModulus_toNat (a : Limbs) :
    (subtractModulus a).2.toNat ≤ 1 ∧
    (subtractModulus a).1.toNat + P256.Spec.Operations.domain.p =
      a.toNat + 2^256 * (subtractModulus a).2.toNat := by
  let r0 := a.l0 + 1
  let b0 := (~~~a.l0 ||| r0) >>> 63
  let r1 := a.l1 + (-b0).sshiftRight 63 + 0xffffffff00000001
  let b1 := (~~~a.l1 &&& r1) >>> 63
  let r2 := (-b1).sshiftRight 63 + a.l2
  let b2 := (~~~a.l2 &&& r2) >>> 63
  let r3 := a.l3 + (-b2).sshiftRight 63 + 0xffffffff
  have h0nat : r0.toNat = (2^64+a.l0.toNat-(2^64-1)-0)%2^64 := by
    rw [BitVec.toNat_add]
    change (a.l0.toNat+1)%2^64 = _
    exact congrArg (fun x : Nat => x % 2^64) (by omega)
  have h0 := subtractWord_borrow_or a.l0 r0 (2^64-1) 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) h0nat
  change b0.toNat ≤ 1 ∧ _ at h0
  have h1nat := subtractWord_toNat a.l1 b0 4294967295
    (by decide +kernel) (eq_zero_or_one h0.1)
  change r1.toNat = (2^64+a.l1.toNat-4294967295-b0.toNat)%2^64 at h1nat
  have h1 := subtractWord_borrow_and a.l1 r1 4294967295 b0.toNat
    (by decide +kernel) h0.1 h1nat
  change b1.toNat ≤ 1 ∧ _ at h1
  have h2nat := subtractWord_toNat a.l2 b1 0
    (by decide +kernel) (eq_zero_or_one h1.1)
  rw [show BitVec.ofNat 64 (2^64-0) = 0#64 from by decide +kernel,
    BitVec.add_zero, BitVec.add_comm] at h2nat
  have h2 := subtractWord_borrow_and a.l2 r2 0 b1.toNat
    (by decide +kernel) h1.1 h2nat
  change b2.toNat ≤ 1 ∧ _ at h2
  have h3nat := subtractWord_toNat a.l3 b2 18446744069414584321
    (by decide +kernel) (eq_zero_or_one h2.1)
  change r3.toNat = (2^64+a.l3.toNat-18446744069414584321-b2.toNat)%2^64 at h3nat
  have h3 := subtractWord_borrow_or a.l3 r3 18446744069414584321 b2.toNat
    (by decide +kernel) (by decide +kernel) h2.1 h3nat
  refine ⟨h3.1, ?_⟩
  change r0.toNat + 2^64*(r1.toNat+2^64*(r2.toNat+2^64*r3.toNat)) +
    P256.Spec.Operations.domain.p = _
  simp only [Limbs.toNat, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
  change r0.toNat + 2^64*(r1.toNat+2^64*(r2.toNat+2^64*r3.toNat)) + _ =
    a.l0.toNat + 2^64*(a.l1.toNat+2^64*(a.l2.toNat+2^64*a.l3.toNat)) +
      2^256 * ((~~~a.l3 ||| r3) >>> 63).toNat
  clear h0nat h1nat h2nat h3nat
  dsimp only [b0, b1, b2] at h0 h1 h2 h3
  omega

theorem subtractModulus_borrow (a : Limbs) :
    (subtractModulus a).2.toNat =
      if a.toNat < P256.Spec.Operations.domain.p then 1 else 0 := by
  have h := subtractModulus_toNat a
  have hr := limbs_toNat_lt (subtractModulus a).1
  split <;> omega

theorem reduceSum_eq_correct (a : Limbs) (c : Bool) :
    reduceSum a c = correct (subtractModulus a).1
      (((-(subtractModulus a).2).sshiftRight 63 + BitVec.ofNat 64 c.toNat) >>> 63) := by
  simp only [reduceSum, correct, BitVec.and_comm]

theorem reduceSum_toNat (a : Limbs) (c : Bool)
    (h : a.toNat + 2^256 * c.toNat < 2 * P256.Spec.Operations.domain.p) :
    (reduceSum a c).toNat =
      (a.toNat + 2^256 * c.toNat) % P256.Spec.Operations.domain.p := by
  have hr := subtractModulus_toNat a
  have ha := limbs_toNat_lt a
  have hl := limbs_toNat_lt (subtractModulus a).1
  rw [reduceSum_eq_correct]
  rcases eq_zero_or_one hr.1 with hb | hb
  · rw [hb] at hr ⊢
    change (0 : Nat) ≤ 1 ∧ (subtractModulus a).1.toNat +
      P256.Spec.Operations.domain.p = a.toNat + 2^256 * 0 at hr
    cases c
    · change (correct (subtractModulus a).1 0).toNat = _
      rw [correct_zero]
      simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain, Bool.toNat_false] at hr h ⊢
      omega
    · simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain, Bool.toNat_true] at hr h
      omega
  · rw [hb] at hr ⊢
    change (1 : Nat) ≤ 1 ∧ (subtractModulus a).1.toNat +
      P256.Spec.Operations.domain.p = a.toNat + 2^256 * 1 at hr
    cases c
    · change (correct (subtractModulus a).1 1).toNat = _
      rw [correct_one_toNat]
      simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain, Bool.toNat_false] at hr h ⊢
      omega
    · change (correct (subtractModulus a).1 0).toNat = _
      rw [correct_zero]
      simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain, Bool.toNat_true] at hr h ⊢
      omega

theorem reduce_normalizedRounds (low high : Limbs)
    (h : low.toNat + 2^256*high.toNat < P256.Proofs.Field.Montgomery.p * 2^256) :
    (reduceSum (normalizedRounds low high).1 (normalizedRounds low high).2).toNat =
      P256.Proofs.Field.Montgomery.subtractP (reduceFour (low.toNat + 2^256*high.toNat)) := by
  rw [reduceSum_toNat _ _ (normalizedRounds_lt_two_mul_p low high h),
    normalizedRounds_value low high h]
  exact (P256.Proofs.Field.Montgomery.subtractP_eq_mod _
    (P256.Proofs.Field.Montgomery.reduceFour_lt_two_mul_p _ h)).symm

theorem adc64_low_add (a b : BitVec 64) (c : Bool) :
    (adc64 a b c).1 = a + (adc64 b 0 c).1 := by
  simp only [adc64, P256.Proofs.Common.Instructions.Carry.adcSpec_result]
  change a + b + (BitVec.ofBool c).setWidth 64 =
    a + (b + 0#64 + (BitVec.ofBool c).setWidth 64)
  rw [BitVec.add_zero, BitVec.add_assoc]

theorem borrow_selector_or (b : BitVec 64) (c d : Bool) (hb : b.toNat ≤ 1) :
    (adc64 (BitVec.ofNat 64 c.toNat) ((-b).sshiftRight 63) d).1 >>> 63 =
      ((-b).sshiftRight 63 + BitVec.ofNat 64 (d || c).toNat) >>> 63 := by
  rcases eq_zero_or_one hb with rfl | rfl
  all_goals cases c <;> cases d <;> decide +kernel

def rawTail (a0 a1 y h e : BitVec 64) (c0 c1 : Bool) : Limbs :=
  let x := adc64 y 0 c0
  let z := adc64 h 0 x.2
  let top := add64 z.1 e
  let b0 := (~~~a0 ||| (a0 + 1)) >>> 63
  let r1 := a1 + (-b0).sshiftRight 63 + 0xffffffff00000001
  let b1 := (~~~a1 &&& r1) >>> 63
  let r2 := (adc64 ((-b1).sshiftRight 63) y c0).1
  let b2 := (~~~x.1 &&& r2) >>> 63
  let r3 := top.1 + (-b2).sshiftRight 63 + 0xffffffff
  let b3 := (~~~top.1 ||| r3) >>> 63
  let q := (adc64 (BitVec.ofNat 64 c1.toNat) ((-b3).sshiftRight 63) top.2).1 >>> 63
  correct ⟨a0 + 1, r1, r2, r3⟩ q

theorem rawTail_eq_reduceSum (a0 a1 y h e : BitVec 64) (c0 c1 : Bool) :
    let x := adc64 y 0 c0
    let z := adc64 h 0 x.2
    let normalized := normalize ⟨a0, a1, x.1, z.1⟩ (e, c1)
    rawTail a0 a1 y h e c0 c1 = reduceSum normalized.1 normalized.2 := by
  dsimp only
  let x := adc64 y 0 c0
  let z := adc64 h 0 x.2
  let top := add64 z.1 e
  let a : Limbs := ⟨a0, a1, x.1, top.1⟩
  have hs := subtractModulus_toNat a
  have hq := borrow_selector_or (subtractModulus a).2 c1 top.2 hs.1
  rw [reduceSum_eq_correct]
  change rawTail a0 a1 y h e c0 c1 =
    correct (subtractModulus a).1
      (((-(subtractModulus a).2).sshiftRight 63 + BitVec.ofNat 64 (top.2 || c1).toNat) >>> 63)
  rw [← hq]
  have hr2 (b : BitVec 64) : (adc64 b y c0).1 = b + x.1 := adc64_low_add b y c0
  simp only [rawTail, hr2, subtractModulus, a, x, z, top]


end P256.Proofs.Field.Montgomery.Reduction
