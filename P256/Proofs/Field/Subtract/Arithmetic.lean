import P256.Proofs.Field.Montgomery.Reduction.CorrectionArithmetic
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field.Subtract

open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Field.Montgomery.Reduction

def borrow (a b r : BitVec 64) : BitVec 64 :=
  (((~~~a ||| b) &&& r) ||| (b &&& ~~~a)) >>> 63

def subWord (a b c : BitVec 64) : BitVec 64 :=
  (-c).sshiftRight 63 + (a - b)

def subRaw (a b : Limbs) : Limbs × BitVec 64 :=
  let r0 := a.l0 - b.l0
  let c0 := borrow a.l0 b.l0 r0
  let r1 := subWord a.l1 b.l1 c0
  let c1 := borrow a.l1 b.l1 r1
  let r2 := subWord a.l2 b.l2 c1
  let c2 := borrow a.l2 b.l2 r2
  let r3 := subWord a.l3 b.l3 c2
  let c3 := borrow a.l3 b.l3 r3
  (⟨r0, r1, r2, r3⟩, c3)

def subLimbs (a b : Limbs) : Limbs :=
  let r := subRaw a b
  correct r.1 ((-r.2) >>> 63)

theorem subWord_toNat (a b c : BitVec 64) (hc : c = 0 ∨ c = 1) :
    (subWord a b c).toNat = (2^64 + a.toNat - b.toNat - c.toNat) % 2^64 := by
  have ha := a.isLt
  have hb := b.isLt
  rcases hc with rfl | rfl
  · simp only [subWord, BitVec.ofNat_eq_ofNat, BitVec.neg_zero, BitVec.zero_sshiftRight, BitVec.zero_add,
      BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
    omega
  · change ((-1 : BitVec 64) + (a-b)).toNat = _
    simp only [BitVec.toNat_add, BitVec.toNat_sub]
    change ((2^64-1 + (2^64 - b.toNat + a.toNat)%2^64)%2^64) =
      (2^64+a.toNat-b.toNat-1)%2^64
    omega

theorem subWord_borrow (a b c : BitVec 64) (hc : c = 0 ∨ c = 1) :
    (borrow a b (subWord a b c)).toNat ≤ 1 ∧
      (subWord a b c).toNat + b.toNat + c.toNat =
        a.toNat + 2^64 * (borrow a b (subWord a b c)).toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hr := (subWord a b c).isLt
  have he := subWord_toNat a b c hc
  have hc' : c.toNat ≤ 1 := by rcases hc with rfl | rfl <;> decide
  simp only [borrow, shift63_toNat]
  simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not]
  simp only [BitVec.msb_eq_decide]
  by_cases h₀ : 2^63 ≤ a.toNat <;>
    by_cases h₁ : 2^63 ≤ b.toNat <;>
    by_cases h₂ : 2^63 ≤ (subWord a b c).toNat <;>
    simp only [show 64-1=63 from rfl, show decide (0 < 64) = true from rfl,
      h₀, h₁, h₂, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, Bool.false_and,
      Bool.true_and, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem subWord_zero (a b : BitVec 64) : subWord a b 0 = a-b := by simp [subWord]

theorem subRaw_toNat (a b : Limbs) :
    (subRaw a b).2.toNat ≤ 1 ∧
      (subRaw a b).1.toNat + b.toNat = a.toNat + 2^256 * (subRaw a b).2.toNat := by
  have h0 := subWord_borrow a.l0 b.l0 0 (Or.inl rfl)
  rw [subWord_zero, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at h0
  have h1 := subWord_borrow a.l1 b.l1 _ (eq_zero_or_one h0.1)
  have h2 := subWord_borrow a.l2 b.l2 _ (eq_zero_or_one h1.1)
  have h3 := subWord_borrow a.l3 b.l3 _ (eq_zero_or_one h2.1)
  refine ⟨h3.1, ?_⟩
  simp only [subRaw, Limbs.toNat]
  omega

theorem subLimbs_toNat (a b : Limbs)
    (ha : a.toNat < P256.Spec.Operations.domain.p)
    (hb : b.toNat < P256.Spec.Operations.domain.p) :
    (subLimbs a b).toNat = (a.toNat + P256.Spec.Operations.domain.p - b.toNat) %
      P256.Spec.Operations.domain.p := by
  have hr := subRaw_toNat a b
  have hl := limbs_toNat_lt (subRaw a b).1
  rcases eq_zero_or_one hr.1 with hc | hc
  · rw [hc] at hr
    change (correct (subRaw a b).1 ((-(subRaw a b).2) >>> 63)).toNat = _
    rw [hc]
    change (correct (subRaw a b).1 0).toNat = _
    rw [correct_zero]
    have he : (subRaw a b).1.toNat + b.toNat = a.toNat := by simpa using hr.2
    simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at ha hb ⊢
    omega
  · rw [hc] at hr
    change (correct (subRaw a b).1 ((-(subRaw a b).2) >>> 63)).toNat = _
    rw [hc]
    change (correct (subRaw a b).1 1).toNat = _
    rw [correct_one_toNat]
    have he : (subRaw a b).1.toNat + b.toNat = a.toNat + 2^256 := by simpa using hr.2
    simp only [P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at ha hb ⊢
    omega

theorem mod_neg_mul (p x k : Nat) (hp : 0 < p) (hx : x ≤ p) :
    (p-x*k%p)%p = ((p-x)%p)*k%p := by
  have h0 := Nat.mod_lt (x*k) hp
  have h1 := Nat.mod_lt ((p-x)*k) hp
  have hs : (x*k%p + (p-x)*k%p)%p = 0 := by
    rw [← Nat.add_mod, ← Nat.add_mul, Nat.add_sub_of_le hx, Nat.mul_mod_right]
  rw [Nat.mod_mul_mod]
  rw [Nat.add_mod_eq_ite] at hs
  simp only [Nat.mod_mod] at hs
  split at hs
  · have hxpos : 0 < x*k%p := by omega
    rw [Nat.mod_eq_of_lt (by omega : p-x*k%p<p)]
    omega
  · have hx0 : x*k%p=0 := by omega
    rw [hx0, Nat.sub_zero, Nat.mod_self]
    omega

theorem subLimbs_montgomery (a b : Limbs) (x y : Nat)
    (hy : y < P256.Spec.Operations.domain.p)
    (ha : a.toNat = x * 2^256 % P256.Spec.Operations.domain.p)
    (hb : b.toNat = y * 2^256 % P256.Spec.Operations.domain.p) :
    (subLimbs a b).toNat = ((x + P256.Spec.Operations.domain.p - y) %
      P256.Spec.Operations.domain.p) * 2^256 % P256.Spec.Operations.domain.p := by
  have hp := Montgomery.p_pos
  rw [subLimbs_toNat a b (ha ▸ Nat.mod_lt _ hp) (hb ▸ Nat.mod_lt _ hp), ha, hb]
  rw [Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt (y * 2^256) hp)),
    Nat.add_sub_assoc (Nat.le_of_lt hy), Nat.mod_mul_mod, Nat.add_mul,
    Nat.add_mod, Nat.mod_mod, mod_neg_mul _ y _ hp (Nat.le_of_lt hy), Nat.mod_mul_mod,
    ← Nat.add_mod]

end P256.Proofs.Field.Subtract
