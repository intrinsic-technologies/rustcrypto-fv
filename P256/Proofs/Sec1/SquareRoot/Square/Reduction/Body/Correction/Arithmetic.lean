import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Model

set_option autoImplicit false

open P256.Proofs.SecretKeyFromBytes.Scalar

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

theorem subWord_toNat (a p b : BitVec 64) (hb : b = 0 ∨ b = 1) :
    (subWord a p b).toNat = (2 * 2^64 + a.toNat - p.toNat - b.toNat) % 2^64 := by
  have ha := a.isLt
  have hp := p.isLt
  rcases hb with rfl | rfl
  · change ((0 : BitVec 64) + (a-p)).toNat = _
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.toNat_sub]
    change (2^64-p.toNat+a.toNat) % 2^64 =
      (2*2^64+a.toNat-p.toNat-0)%2^64
    omega
  · change ((-1 : BitVec 64) + (a-p)).toNat = _
    simp only [BitVec.toNat_add, BitVec.toNat_sub]
    change ((2^64-1) + (2^64-p.toNat+a.toNat) % 2^64)%2^64 =
      (2*2^64+a.toNat-p.toNat-1)%2^64
    omega

theorem borrow_toNat (a p r : BitVec 64) :
    (borrow a p r).toNat =
      (((!a.msb || p.msb) && r.msb) || (p.msb && !a.msb)).toNat := by
  simp only [borrow, shift63_toNat, BitVec.msb_or, BitVec.msb_and,
    BitVec.msb_not, show decide (0 < 64) = true from rfl, Bool.true_and]

theorem subWord_borrow (a p b : BitVec 64) (hb : b = 0 ∨ b = 1) :
    (borrow a p (subWord a p b)).toNat ≤ 1 ∧
    (subWord a p b).toNat + p.toNat + b.toNat =
      a.toNat + 2^64 * (borrow a p (subWord a p b)).toNat := by
  have ha := a.isLt
  have hp := p.isLt
  have hr := (subWord a p b).isLt
  have he := subWord_toNat a p b hb
  have hb' : b.toNat ≤ 1 := by
    rcases hb with rfl | rfl <;> decide +kernel
  rw [borrow_toNat]
  simp only [BitVec.msb_eq_decide, show 64-1=63 from rfl]
  by_cases h₁ : 2^63 ≤ a.toNat <;>
    by_cases h₂ : 2^63 ≤ p.toNat <;>
    by_cases h₃ : 2^63 ≤ (subWord a p b).toNat <;>
    simp only [h₁, h₂, h₃, decide_true, decide_false,
      Bool.not_false, Bool.not_true, Bool.or_false,
      Bool.or_true, Bool.and_false,
      Bool.and_true, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem subWord_zero (a p : BitVec 64) : subWord a p 0 = a-p := by
  simp [subWord]

theorem subRaw_toNat (a p : Limbs) :
    (subRaw a p).2.toNat ≤ 1 ∧
    (subRaw a p).1.toNat + p.toNat = a.toNat + 2^256 * (subRaw a p).2.toNat := by
  have h0 := subWord_borrow a.l0 p.l0 0 (Or.inl rfl)
  rw [subWord_zero, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at h0
  have h1 := subWord_borrow a.l1 p.l1 _ (eq_zero_or_one h0.1)
  have h2 := subWord_borrow a.l2 p.l2 _ (eq_zero_or_one h1.1)
  have h3 := subWord_borrow a.l3 p.l3 _ (eq_zero_or_one h2.1)
  refine ⟨h3.1, ?_⟩
  simp only [subRaw, Limbs.toNat]
  omega

theorem modulus_toNat : modulus.toNat = P256.Spec.Operations.domain.p := by
  decide +kernel

theorem selectWord_zero (a r : BitVec 64) : selectWord a r 0 = r := by
  simp [selectWord]

theorem selectWord_one (a r : BitVec 64) : selectWord a r 1 = a := by
  change (BitVec.allOnes 64 &&& (a ^^^ r)) ^^^ r = a
  rw [BitVec.allOnes_and, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem selectLimbs_zero (a r : Limbs) : selectLimbs a r 0 = r := by
  simp only [selectLimbs, selectWord_zero]

theorem selectLimbs_one (a r : Limbs) : selectLimbs a r 1 = a := by
  simp only [selectLimbs, selectWord_one]

theorem selector_zero (high : BitVec 64) : selector high 0 = 0 := by
  simp [selector]

theorem selector_one (high : BitVec 64) :
    selector high 1 = if high = 0 then 1 else 0 := by
  change (if high = 0 then (1 : BitVec 64) else 0) &&& BitVec.allOnes 64 = _
  rw [BitVec.and_allOnes]

theorem reduce_toNat (a : Limbs) (high : BitVec 64)
    (ha : a.toNat + 2^256 * high.toNat < 2 * P256.Spec.Operations.domain.p) :
    (reduce a high).toNat =
      P256.Proofs.Field.Montgomery.subtractP (a.toNat + 2^256 * high.toNat) := by
  have hr := subRaw_toNat a modulus
  rw [modulus_toNat] at hr
  have hl := limbs_toNat_lt a
  have hh : high.toNat ≤ 1 := by
    simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at ha
    omega
  rcases eq_zero_or_one hr.1 with hb | hb
  · have hhigh : high.toNat = 0 := by
      rw [hb] at hr
      simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at hr ha
      change _ ∧ (subRaw a modulus).1.toNat + _ = a.toNat + 2^256 * 0 at hr
      omega
    have hge : P256.Spec.Operations.domain.p ≤ a.toNat := by
      rw [hb] at hr
      change _ ∧ (subRaw a modulus).1.toNat + _ = a.toNat + 2^256 * 0 at hr
      omega
    simp only [reduce, hb, selector_zero, selectLimbs_zero, hhigh,
      Nat.mul_zero, Nat.add_zero, P256.Proofs.Field.Montgomery.subtractP, P256.Proofs.Field.Montgomery.p,
      Nat.not_lt.mpr hge, ite_false]
    rw [hb] at hr
    change _ ∧ (subRaw a modulus).1.toNat + _ = a.toNat + 2^256 * 0 at hr
    omega
  · have hlt : a.toNat < P256.Spec.Operations.domain.p := by
      have hrl := limbs_toNat_lt (subRaw a modulus).1
      rw [hb] at hr
      change _ ∧ (subRaw a modulus).1.toNat + _ = a.toNat + 2^256 * 1 at hr
      omega
    rw [show reduce a high = selectLimbs a (subRaw a modulus).1 (selector high (subRaw a modulus).2) from rfl,
      hb, selector_one]
    by_cases hz : high = 0
    · rw [ite_eq_left hz, selectLimbs_one]
      subst high
      change a.toNat = if a.toNat < P256.Spec.Operations.domain.p then a.toNat
        else a.toNat - P256.Spec.Operations.domain.p
      rw [ite_eq_left hlt]
    · have hhigh : high.toNat = 1 := by
        have hn : high.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
        omega
      have hge : P256.Spec.Operations.domain.p ≤ a.toNat + 2^256 * high.toNat := by
        simp only [hhigh, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain]
        omega
      rw [ite_eq_right hz, selectLimbs_zero]
      simp only [P256.Proofs.Field.Montgomery.subtractP, P256.Proofs.Field.Montgomery.p]
      rw [ite_eq_right (Nat.not_lt.mpr hge), hhigh]
      rw [hb] at hr
      change _ ∧ (subRaw a modulus).1.toNat + _ = a.toNat + 2^256 * 1 at hr
      omega

theorem selector_byte (high b : BitVec 64) (hb : b = 0 ∨ b = 1) :
    (((if high = 0 then (1 : BitVec 8) else 0) &&& (-b).setWidth 8).setWidth 64) =
      selector high b := by
  rcases hb with rfl | rfl <;> by_cases h : high = 0#64 <;>
    simp [selector, BitVec.ofNat_eq_ofNat, h]

theorem top_add_eq (d e f a h : BitVec 64)
    (top : d.toNat + e.toNat + 2^64 * f.toNat = a.toNat + 2^64 * h.toNat) :
    d + e = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add]
  have ha := a.isLt
  omega

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction
