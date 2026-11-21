import X86Proofs.Instructions.Sbb.Operation

namespace K256.Proofs.Common.Invert.LinearCombination

open X86Proofs

structure Limbs where
  l0 : BitVec 64
  l1 : BitVec 64
  l2 : BitVec 64
  l3 : BitVec 64

def Limbs.toNat (a : Limbs) : Nat :=
  a.l0.toNat + 2^64 * (a.l1.toNat + 2^64 * (a.l2.toNat + 2^64 * a.l3.toNat))

theorem shift63_toNat (a : BitVec 64) : (a >>> 63).toNat = a.msb.toNat := by
  have ha := a.isLt
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  by_cases h : 2^63 ≤ a.toNat <;>
    simp only [show 64-1=63 from rfl, h, decide_true, decide_false,
      Bool.toNat_true, Bool.toNat_false] <;> omega

theorem eq_zero_or_one {b : BitVec 64} (hb : b.toNat ≤ 1) : b = 0 ∨ b = 1 := by
  by_cases h : b.toNat = 0
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · right
    apply BitVec.eq_of_toNat_eq
    change b.toNat = 1
    omega
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

def packFour (w : Vector Nat 4) : Nat :=
  w[0] + 2^64*w[1] + 2^128*w[2] + 2^192*w[3]

def packFive (w : Vector Nat 5) : Nat :=
  w[0] + 2^64*w[1] + 2^128*w[2] + 2^192*w[3] + 2^256*w[4]

theorem sbb_borrow (x y : BitVec 64) (c : Bool) :
    (sbbSpec c x y).1.toNat + y.toNat + c.toNat = x.toNat + 2^64*(sbbSpec c x y).2.CF.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [sbbSpec, ← ofInt_sub_add_toNat, BitVec.toNat_ofInt]
  have hc : c.toNat ≤ 1 := by cases c <;> decide
  by_cases h : x.toNat < y.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] <;> omega

theorem sub_borrow (x y : BitVec 64) :
    (subSpec x y).1.toNat + y.toNat = x.toNat + 2^64*(subSpec x y).2.CF.toNat := by
  simpa [sbbSpec, subSpec] using sbb_borrow x y false

def wideValue (a : Vector (BitVec 64) 5) : Nat := packFive (a.map BitVec.toNat)

def signedWideValue (a : Vector (BitVec 64) 5) (negative : Bool) : Int :=
  if negative then -(wideValue a : Int) else (wideValue a : Int)
def negateWide (a : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 :=
  let v0 := subSpec 0 a[0]
  let v1 := sbbSpec v0.2.CF 0 a[1]
  let v2 := sbbSpec v1.2.CF 0 a[2]
  let v3 := sbbSpec v2.2.CF 0 a[3]
  let carry : BitVec 8 := if !v3.2.CF then 1 else 0
  #v[-a[0],v1.1,v2.1,v3.1,~~~a[4] + carry.setWidth 64]

def subtractWide (a b : Vector (BitVec 64) 5) : Vector (BitVec 64) 5 × BitVec 64 :=
  let r := subRaw ⟨a[0],a[1],a[2],a[3]⟩ ⟨b[0],b[1],b[2],b[3]⟩
  let r4 := subWord a[4] b[4] r.2
  (#v[r.1.l0,r.1.l1,r.1.l2,r.1.l3,r4],borrow a[4] b[4] r4)

theorem wideValue_eq (a : Vector (BitVec 64) 5) :
    wideValue a = a[0].toNat + 2^64*a[1].toNat + 2^128*a[2].toNat +
      2^192*a[3].toNat + 2^256*a[4].toNat := by
  simp [wideValue,packFive]

theorem wideValue_lt (a : Vector (BitVec 64) 5) : wideValue a < 2^320 := by
  rw [wideValue_eq]
  have h0 := a[0].isLt
  have h1 := a[1].isLt
  have h2 := a[2].isLt
  have h3 := a[3].isLt
  have h4 := a[4].isLt
  omega

theorem subtractWide_value (a b : Vector (BitVec 64) 5) :
    (subtractWide a b).2.toNat ≤ 1 ∧
    wideValue (subtractWide a b).1 + wideValue b =
      wideValue a + 2^320 * (subtractWide a b).2.toNat := by
  have h := subRaw_toNat ⟨a[0],a[1],a[2],a[3]⟩ ⟨b[0],b[1],b[2],b[3]⟩
  have h4 := subWord_borrow a[4] b[4] _ (eq_zero_or_one h.1)
  refine ⟨h4.1, ?_⟩
  simp only [subtractWide,wideValue_eq,Vector.getElem_mk,List.getElem_toArray,
    List.getElem_cons_succ,List.getElem_cons_zero]
  simp only [Limbs.toNat] at h
  omega

set_option maxHeartbeats 800000 in
theorem negateWide_value (a : Vector (BitVec 64) 5) :
    wideValue (negateWide a) + wideValue a = if wideValue a = 0 then 0 else 2^320 := by
  let v0 := subSpec (0 : BitVec 64) a[0]
  let v1 := sbbSpec v0.2.CF (0 : BitVec 64) a[1]
  let v2 := sbbSpec v1.2.CF (0 : BitVec 64) a[2]
  let v3 := sbbSpec v2.2.CF (0 : BitVec 64) a[3]
  have h0 := sub_borrow (0 : BitVec 64) a[0]
  have h1 := sbb_borrow (0 : BitVec 64) a[1] v0.2.CF
  have h2 := sbb_borrow (0 : BitVec 64) a[2] v1.2.CF
  have h3 := sbb_borrow (0 : BitVec 64) a[3] v2.2.CF
  change (-a[0]).toNat + a[0].toNat = 0 + 2^64*v0.2.CF.toNat at h0
  change v1.1.toNat + a[1].toNat + v0.2.CF.toNat = 0 + 2^64*v1.2.CF.toNat at h1
  change v2.1.toNat + a[2].toNat + v1.2.CF.toNat = 0 + 2^64*v2.2.CF.toNat at h2
  change v3.1.toNat + a[3].toNat + v2.2.CF.toNat = 0 + 2^64*v3.2.CF.toNat at h3
  simp only [Nat.zero_add] at h0 h1 h2 h3
  have ha := wideValue_lt a
  have hn := wideValue_lt (negateWide a)
  have ht := a[4].isLt
  have hexpand : wideValue (negateWide a) = (-a[0]).toNat + 2^64*v1.1.toNat +
      2^128*v2.1.toNat + 2^192*v3.1.toNat +
      2^256*((~~~a[4] + ((if !v3.2.CF then 1 else 0) : BitVec 8).setWidth 64).toNat) := by
    simp only [negateWide,wideValue_eq,Vector.getElem_mk,List.getElem_toArray,
      List.getElem_cons_succ,List.getElem_cons_zero]
    rfl
  rw [hexpand] at hn
  rw [hexpand,wideValue_eq]
  rw [wideValue_eq] at ha
  simp only [BitVec.toNat_add,BitVec.toNat_not,BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
  cases hc : v3.2.CF <;> simp only [hc,Bool.not_false,Bool.not_true,
    Bool.toNat_false,Bool.toNat_true,Bool.false_eq_true,ite_false,ite_true,
    show (0 : BitVec 8).toNat = 0 from rfl,show (1 : BitVec 8).toNat = 1 from rfl] at * <;>
    split <;> omega

end K256.Proofs.Common.Invert.LinearCombination
