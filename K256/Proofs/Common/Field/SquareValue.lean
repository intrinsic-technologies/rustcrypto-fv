import K256.Proofs.Common.Field.Repr
import K256.Proofs.Common.Field.WordOps
import K256.Proofs.Common.Field.Square

namespace K256.Proofs.Common.Field
open X86Proofs

namespace SquareValue

abbrev cf (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (addSpec a b).snd.CF.toNat

theorem cf_toNat (a b : BitVec 64) : (cf a b).toNat = (a.toNat + b.toNat) / 2^64 := by
  have h := addSpec_CF_toNat a b
  have hb : (addSpec a b).snd.CF.toNat < 2 := by cases (addSpec a b).snd.CF <;> decide
  simp only [cf, BitVec.toNat_ofNat]
  omega

theorem pair_mul (x y : BitVec 64) : pairNat (x * y) (mulResult x y).snd = x.toNat * y.toNat := by
  have := mulResult_toNat_add x y
  have e : (mulResult x y).1 = x * y := by
    apply BitVec.eq_of_toNat_eq
    simp only [mulResult, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_mul,
      Nat.shiftRight_zero]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [← e]; exact this

theorem pair_add (lo1 hi1 lo2 hi2 : BitVec 64) (h : pairNat lo1 hi1 + pairNat lo2 hi2 < 2^128) :
    pairNat (lo1 + lo2) (hi1 + hi2 + cf lo1 lo2) = pairNat lo1 hi1 + pairNat lo2 hi2 := by
  unfold pairNat at *
  have hc := cf_toNat lo1 lo2
  simp only [BitVec.toNat_add] at *
  omega

theorem pair_add_swap (lo1 hi1 lo2 hi2 : BitVec 64) (h : pairNat lo1 hi1 + pairNat lo2 hi2 < 2^128) :
    pairNat (lo1 + lo2) (hi2 + hi1 + cf lo1 lo2) = pairNat lo1 hi1 + pairNat lo2 hi2 := by
  unfold pairNat at *
  have hc := cf_toNat lo1 lo2
  simp only [BitVec.toNat_add] at *
  omega

theorem pair_addw (lo hi w : BitVec 64) (h : pairNat lo hi + w.toNat < 2^128) :
    pairNat (lo + w) (hi + cf lo w) = pairNat lo hi + w.toNat := by
  unfold pairNat at *
  have hc := cf_toNat lo w
  simp only [BitVec.toNat_add] at *
  omega

theorem pair_waddp (w lo hi : BitVec 64) (h : w.toNat + pairNat lo hi < 2^128) :
    pairNat (w + lo) (hi + cf w lo) = w.toNat + pairNat lo hi := by
  unfold pairNat at *
  have hc := cf_toNat w lo
  simp only [BitVec.toNat_add] at *
  omega

theorem pair_dbl (lo hi : BitVec 64) (h : 2 * pairNat lo hi < 2^128) :
    pairNat (lo + lo) (shldResult 1 hi lo) = 2 * pairNat lo hi := by
  have hs := shldResult_pairNat 1 hi lo (by decide) (by decide)
  unfold pairNat at *
  simp only [BitVec.toNat_add] at *
  omega

theorem pair_dmul (x y : BitVec 64) (hx : x.toNat < 2^63) :
    pairNat ((x + x) * y) ((mulResult (x + x) y).snd + x >>> 63 * y) = 2 * x.toNat * y.toNat := by
  have hz : x >>> 63 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    show x.toNat / 2^63 = 0
    omega
  have hxx : (x + x).toNat = 2 * x.toNat := by simp only [BitVec.toNat_add]; omega
  have h0 : (mulResult (x + x) y).snd + (0 : BitVec 64) * y = (mulResult (x + x) y).snd := by
    simp
  rw [hz, h0, pair_mul, hxx]

theorem shr52 (lo hi : BitVec 64) (h : pairNat lo hi < 2^116) :
    (shldResult 12 hi lo).toNat = pairNat lo hi / 2^52 := by
  rw [shldResult_pairNat 12 hi lo (by decide) (by decide)]
  apply Nat.mod_eq_of_lt
  have : pairNat lo hi / 2^52 < 2^64 := by omega
  exact this

theorem lo_toNat (lo hi : BitVec 64) : lo.toNat = pairNat lo hi % 2^64 := by
  unfold pairNat; omega

theorem mask52 (x : BitVec 64) : (x &&& 4503599627370495).toNat = x.toNat % 2^52 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 52

theorem mask52' (x : BitVec 64) : (4503599627370495 &&& x).toNat = x.toNat % 2^52 := by
  rw [BitVec.and_comm]; exact mask52 x

theorem mask48' (x : BitVec 64) : (281474976710655 &&& x).toNat = x.toNat % 2^48 := by
  rw [BitVec.toNat_and, Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 48

theorem hole (x c m M : BitVec 64) (hm : x &&& m = 0) (hM : c ||| m = M) :
    c &&& x = x &&& M := by
  have hz : x &&& c ||| (0 : BitVec 64) = x &&& c := by simp
  rw [← hM, BitVec.and_or_distrib_left, hm, hz, BitVec.and_comm]

theorem mask52_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    (4503599627370494 &&& x).toNat = x.toNat % 2^52 := by
  have h1 : x &&& 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 1
    simp only [Nat.reducePow, Nat.reduceSub] at this
    show x.toNat &&& 1 = 0
    omega
  rw [hole x 4503599627370494 1 4503599627370495 h1 (by decide), mask52]

theorem mask52_sq (x : BitVec 64) (h : x.toNat % 4 < 2) :
    (4503599627370493 &&& x).toNat = x.toNat % 2^52 := by
  have h1 : x &&& 2 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 2
    have h2 : x.toNat &&& 2 = (x.toNat &&& 3) &&& 2 := by
      rw [Nat.and_assoc]; rfl
    show x.toNat &&& 2 = 0
    rw [h2]
    simp only [Nat.reducePow, Nat.reduceSub] at this
    rw [this]
    have : x.toNat % 4 = 0 ∨ x.toNat % 4 = 1 := by omega
    rcases this with h' | h' <;> rw [h'] <;> decide
  rw [hole x 4503599627370493 2 4503599627370495 h1 (by decide), mask52]

theorem sq_mod4 (x : BitVec 64) : (x * x).toNat % 4 < 2 := by
  rw [BitVec.toNat_mul, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2^64), Nat.mul_mod]
  have : x.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 4 = r at *
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with h | h | h | h <;> subst h <;> decide

theorem u0_toNat (x47 x45 : BitVec 64) :
    (x47 <<< 4 &&& (72057594037927920 : BitVec 64) |||
      BitVec.setWidth 64 (BitVec.setWidth 32 (x45 >>> 48) &&& 15)).toNat =
      x47.toNat % 2^52 * 16 + x45.toNat / 2^48 % 16 := by
  have hs : (x47 <<< 4).toNat = x47.toNat * 16 % 2^64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have h15 : x47 <<< 4 &&& 15 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod (x47 <<< 4).toNat 4
    simp only [Nat.reducePow, Nat.reduceSub] at this
    show (x47 <<< 4).toNat &&& 15 = 0
    omega
  have hA : (x47 <<< 4 &&& (72057594037927920 : BitVec 64)).toNat = x47.toNat % 2^52 * 16 := by
    rw [BitVec.and_comm, hole _ 72057594037927920 15 72057594037927935 h15 (by decide),
      BitVec.toNat_and]
    have := Nat.and_two_pow_sub_one_eq_mod (x47 <<< 4).toNat 56
    simp only [Nat.reducePow, Nat.reduceSub] at this
    show (x47 <<< 4).toNat &&& 72057594037927935 = _
    omega
  have hB : (BitVec.setWidth 64 (BitVec.setWidth 32 (x45 >>> 48) &&& 15)).toNat =
      x45.toNat / 2^48 % 16 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
    have := Nat.and_two_pow_sub_one_eq_mod ((x45.toNat >>> 48) % 2^32) 4
    simp only [Nat.reducePow, Nat.reduceSub] at this
    show ((x45.toNat >>> 48) % 4294967296 &&& 15) % 18446744073709551616 = _
    rw [this, Nat.shiftRight_eq_div_pow]
    omega
  rw [BitVec.toNat_or, hA, hB]
  have hb : x45.toNat / 2^48 % 16 < 2^4 := Nat.mod_lt _ (by decide)
  rw [show x47.toNat % 2^52 * 16 = 2^4 * (x47.toNat % 2^52) from Nat.mul_comm _ _,
    ← Nat.two_pow_add_eq_or_of_lt hb]


abbrev P : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

instance : NeZero P := ⟨by decide⟩

open Fin.NatCast

theorem castLit (n : Nat) :
    ((no_index (OfNat.ofNat n : Nat)) : Fin P) = (OfNat.ofNat n : Fin P) :=
  Lean.Grind.Semiring.natCast_eq_ofNat n

theorem solve (x y r : Fin P) (h : x = y + r) : r = x - y := by grind

set_option maxRecDepth 20000 in
theorem chain_fin (a0 a1 a2 a3 a4 c1 l q1 t3 q2 t4f t4 tx q3 u p1 r0 q4 w4 p2 r1 q5 w5 p3 r2 p4 r3 : Fin P)
    (e0 : l = a4 * a4 - c1 * 2^52)
    (e1 : t3 = 2 * (a1 * a2 + a0 * a3) + l * 0x1000003D10 - q1 * 2^52)
    (e2 : t4f = 2 * (a1 * a3 + a0 * a4) + a2 * a2 + c1 * 0x1000003D10 + q1 - q2 * 2^52)
    (e2' : t4 = t4f - tx * 2^48)
    (e3 : u = 2 * (a1 * a4 + a2 * a3) + q2 - q3 * 2^52)
    (e4 : r0 = a0 * a0 + (u * 16 + tx) * 0x1000003D1 - p1 * 2^52)
    (e5 : w4 = 2 * a2 * a4 + a3 * a3 + q3 - q4 * 2^52)
    (e6 : r1 = w4 * 0x1000003D10 + 2 * a0 * a1 + p1 - p2 * 2^52)
    (e7 : w5 = 2 * a3 * a4 + q4 - q5 * 2^52)
    (e8 : r2 = 2 * a0 * a2 + a1 * a1 + w5 * 0x1000003D10 + p2 - p3 * 2^52)
    (e9 : r3 = t3 + q5 * 0x1000003D10 + p3 - p4 * 2^52) :
    r0 + r1 * 2^52 + r2 * 2^104 + r3 * 2^156 + (t4 + p4) * 2^208 =
      (a0 + a1 * 2^52 + a2 * 2^104 + a3 * 2^156 + a4 * 2^208) ^ 2 := by
  subst e9 e8 e7 e6 e5 e4 e3 e2' e2 e1 e0
  grind

set_option maxRecDepth 20000 in
theorem chain_mod (a0 a1 a2 a3 a4 c1 l q1 t3 q2 t4f t4 tx q3 u p1 r0 q4 w4 p2 r1 q5 w5 p3 r2 p4 r3 : Nat)
    (e0 : a4 * a4 = c1 * 2^52 + l)
    (e1 : 2 * (a1 * a2 + a0 * a3) + l * 0x1000003D10 = q1 * 2^52 + t3)
    (e2 : 2 * (a1 * a3 + a0 * a4) + a2 * a2 + c1 * 0x1000003D10 + q1 = q2 * 2^52 + t4f)
    (e2' : t4f = tx * 2^48 + t4)
    (e3 : 2 * (a1 * a4 + a2 * a3) + q2 = q3 * 2^52 + u)
    (e4 : a0 * a0 + (u * 16 + tx) * 0x1000003D1 = p1 * 2^52 + r0)
    (e5 : 2 * a2 * a4 + a3 * a3 + q3 = q4 * 2^52 + w4)
    (e6 : w4 * 0x1000003D10 + 2 * a0 * a1 + p1 = p2 * 2^52 + r1)
    (e7 : 2 * a3 * a4 + q4 = q5 * 2^52 + w5)
    (e8 : 2 * a0 * a2 + a1 * a1 + w5 * 0x1000003D10 + p2 = p3 * 2^52 + r2)
    (e9 : t3 + q5 * 0x1000003D10 + p3 = p4 * 2^52 + r3) :
    (r0 + r1 * 2^52 + r2 * 2^104 + r3 * 2^156 + (t4 + p4) * 2^208) % P =
      (a0 + a1 * 2^52 + a2 * 2^104 + a3 * 2^156 + a4 * 2^208) ^ 2 % P := by
  have key : ((r0 + r1 * 2^52 + r2 * 2^104 + r3 * 2^156 + (t4 + p4) * 2^208 : Nat) : Fin P) =
      (((a0 + a1 * 2^52 + a2 * 2^104 + a3 * 2^156 + a4 * 2^208) ^ 2 : Nat) : Fin P) := by
    have f0 := congrArg (Nat.cast : Nat → Fin P) e0
    have f1 := congrArg (Nat.cast : Nat → Fin P) e1
    have f2 := congrArg (Nat.cast : Nat → Fin P) e2
    have f2' := congrArg (Nat.cast : Nat → Fin P) e2'
    have f3 := congrArg (Nat.cast : Nat → Fin P) e3
    have f4 := congrArg (Nat.cast : Nat → Fin P) e4
    have f5 := congrArg (Nat.cast : Nat → Fin P) e5
    have f6 := congrArg (Nat.cast : Nat → Fin P) e6
    have f7 := congrArg (Nat.cast : Nat → Fin P) e7
    have f8 := congrArg (Nat.cast : Nat → Fin P) e8
    have f9 := congrArg (Nat.cast : Nat → Fin P) e9
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul,
      Lean.Grind.Semiring.natCast_pow, castLit] at f0 f1 f2 f2' f3 f4 f5 f6 f7 f8 f9 ⊢
    clear e0 e1 e2 e2' e3 e4 e5 e6 e7 e8 e9
    exact chain_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (solve _ _ _ f0) (solve _ _ _ f1) (solve _ _ _ f2) (solve _ _ _ f2') (solve _ _ _ f3)
      (solve _ _ _ f4) (solve _ _ _ f5) (solve _ _ _ f6) (solve _ _ _ f7) (solve _ _ _ f8)
      (solve _ _ _ f9)
  have v := congrArg Fin.val key
  rw [← Fin.val_ofNat P, ← Fin.val_ofNat P]
  exact v

theorem mul_lt {a b m n : Nat} (ha : a < 2^m) (hb : b < 2^n) : a * b < 2^(m+n) := by
  rw [Nat.pow_add]; exact Nat.mul_lt_mul'' ha hb

set_option maxHeartbeats 4000000 in
theorem squareLimbs_chain (a : Limbs)
    (h0 : a[0].toNat < 2^56) (h1 : a[1].toNat < 2^56) (h2 : a[2].toNat < 2^56)
    (h3 : a[3].toNat < 2^56) (h4 : a[4].toNat < 2^52) :
    ∃ c1 l q1 t3 q2 t4f t4 tx q3 u p1 r0 q4 w4 p2 r1 q5 w5 p3 r2 p4 r3 : Nat,
      a[4].toNat * a[4].toNat = c1 * 2^52 + l ∧
      2 * (a[1].toNat * a[2].toNat + a[0].toNat * a[3].toNat) + l * 0x1000003D10 = q1 * 2^52 + t3 ∧
      2 * (a[1].toNat * a[3].toNat + a[0].toNat * a[4].toNat) + a[2].toNat * a[2].toNat +
        c1 * 0x1000003D10 + q1 = q2 * 2^52 + t4f ∧
      t4f = tx * 2^48 + t4 ∧
      2 * (a[1].toNat * a[4].toNat + a[2].toNat * a[3].toNat) + q2 = q3 * 2^52 + u ∧
      a[0].toNat * a[0].toNat + (u * 16 + tx) * 0x1000003D1 = p1 * 2^52 + r0 ∧
      2 * a[2].toNat * a[4].toNat + a[3].toNat * a[3].toNat + q3 = q4 * 2^52 + w4 ∧
      w4 * 0x1000003D10 + 2 * a[0].toNat * a[1].toNat + p1 = p2 * 2^52 + r1 ∧
      2 * a[3].toNat * a[4].toNat + q4 = q5 * 2^52 + w5 ∧
      2 * a[0].toNat * a[2].toNat + a[1].toNat * a[1].toNat + w5 * 0x1000003D10 + p2 =
        p3 * 2^52 + r2 ∧
      t3 + q5 * 0x1000003D10 + p3 = p4 * 2^52 + r3 ∧
      (squareLimbs a).1.toNat = r0 ∧
      (squareLimbs a).2.1.toNat = r1 ∧
      (squareLimbs a).2.2.1.toNat = r2 ∧
      (squareLimbs a).2.2.2.1.toNat = r3 ∧
      (squareLimbs a).2.2.2.2.toNat = t4 + p4 ∧
      r0 < 2^52 ∧ r1 < 2^52 ∧ r2 < 2^52 ∧ r3 < 2^52 ∧ t4 < 2^48 ∧ p4 < 2^44 := by
  generalize hs : squareLimbs a = s
  unfold squareLimbs at hs
  extract_lets x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48
    x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 at hs
  subst hs
  rw [show a[0] = x7 from rfl, show a[1] = x5 from rfl, show a[2] = x8 from rfl,
    show a[3] = x9 from rfl, show a[4] = x6 from rfl]
  have g0 : x7.toNat < 2^56 := h0
  have g1 : x5.toNat < 2^56 := h1
  have g2 : x8.toNat < 2^56 := h2
  have g3 : x9.toNat < 2^56 := h3
  have g4 : x6.toNat < 2^52 := h4
  have m10 : pairNat x10 (mulResult x8 x6).snd = x8.toNat * x6.toNat := pair_mul _ _
  have m11 : pairNat x11 (mulResult x9 x6).snd = x9.toNat * x6.toNat := pair_mul _ _
  have m12 : pairNat x12 (mulResult x8 x8).snd = x8.toNat * x8.toNat := pair_mul _ _
  have m13 : pairNat x13 (mulResult x7 x7).snd = x7.toNat * x7.toNat := pair_mul _ _
  have m14 : pairNat x14 (mulResult x9 x5).snd = x9.toNat * x5.toNat := pair_mul _ _
  have m15 : pairNat x15 (mulResult x8 x5).snd = x8.toNat * x5.toNat := pair_mul _ _
  have m16 : pairNat x16 (mulResult x9 x7).snd = x9.toNat * x7.toNat := pair_mul _ _
  have m17 : pairNat x17 (mulResult x6 x7).snd = x6.toNat * x7.toNat := pair_mul _ _
  have m18 : pairNat x18 (mulResult x6 x5).snd = x6.toNat * x5.toNat := pair_mul _ _
  have m20 : pairNat x20 (mulResult x6 x6).snd = x6.toNat * x6.toNat := pair_mul _ _
  have m21 : pairNat x21 (mulResult x9 x8).snd = x9.toNat * x8.toNat := pair_mul _ _
  have m22 : pairNat x22 (mulResult x9 x9).snd = x9.toNat * x9.toNat := pair_mul _ _
  have m23 : pairNat x23 (mulResult x5 x5).snd = x5.toNat * x5.toNat := pair_mul _ _
  have m28 : pairNat x28 ((mulResult x19 x5).snd + x7 >>> 63 * x5) =
      2 * x7.toNat * x5.toNat := pair_dmul _ _ (by omega)
  have m30 : pairNat x30 ((mulResult x19 x8).snd + x7 >>> 63 * x8) =
      2 * x7.toNat * x8.toNat := pair_dmul _ _ (by omega)
  have b10 : x8.toNat * x6.toNat < 2^108 := by
    have := mul_lt g2 g4; exact this
  have b11 : x9.toNat * x6.toNat < 2^108 := by
    have := mul_lt g3 g4; exact this
  have b12 : x8.toNat * x8.toNat < 2^112 := by
    have := mul_lt g2 g2; exact this
  have b13 : x7.toNat * x7.toNat < 2^112 := by
    have := mul_lt g0 g0; exact this
  have b14 : x9.toNat * x5.toNat < 2^112 := by
    have := mul_lt g3 g1; exact this
  have b15 : x8.toNat * x5.toNat < 2^112 := by
    have := mul_lt g2 g1; exact this
  have b16 : x9.toNat * x7.toNat < 2^112 := by
    have := mul_lt g3 g0; exact this
  have b17 : x6.toNat * x7.toNat < 2^108 := by
    have := mul_lt g4 g0; exact this
  have b18 : x6.toNat * x5.toNat < 2^108 := by
    have := mul_lt g4 g1; exact this
  have b20 : x6.toNat * x6.toNat < 2^104 := by
    have := mul_lt g4 g4; exact this
  have b21 : x9.toNat * x8.toNat < 2^112 := by
    have := mul_lt g3 g2; exact this
  have b22 : x9.toNat * x9.toNat < 2^112 := by
    have := mul_lt g3 g3; exact this
  have b23 : x5.toNat * x5.toNat < 2^112 := by
    have := mul_lt g1 g1; exact this
  have b28 : 2 * x7.toNat * x5.toNat < 2^113 := by
    rw [Nat.mul_assoc]; have : x7.toNat * x5.toNat < 2^112 := mul_lt g0 g1; omega
  have b30 : 2 * x7.toNat * x8.toNat < 2^113 := by
    rw [Nat.mul_assoc]; have : x7.toNat * x8.toNat < 2^112 := mul_lt g0 g2; omega
  have hl : x24.toNat = x6.toNat * x6.toNat % 2^52 := by
    rw [show x24 = 4503599627370493 &&& x20 from rfl, mask52_sq _ (sq_mod4 x6),
      lo_toNat x20 _, m20]
    omega
  have hc1 : x32.toNat = x6.toNat * x6.toNat / 2^52 := by
    rw [show x32 = shldResult 12 (mulResult x6 x6).snd x20 from rfl, shr52 _ _ (by omega), m20]
  obtain ⟨H29, eH29⟩ : ∃ h : BitVec 64, h = (mulResult x8 x5).snd + (mulResult x9 x7).snd + cf x15 x16 := ⟨_, rfl⟩
  have p29 : pairNat x29 H29 = x8.toNat * x5.toNat + x9.toNat * x7.toNat := by
    have := pair_add x15 (mulResult x8 x5).snd x16 (mulResult x9 x7).snd (by rw [m15, m16]; omega)
    rw [m15, m16] at this; subst_vars; exact this
  have m33 : pairNat x33 (mulResult x24 68719492368).snd = x24.toNat * 68719492368 := pair_mul _ _
  obtain ⟨H38, eH38⟩ : ∃ h : BitVec 64, h = shldResult 1 H29 x29 := ⟨_, rfl⟩
  have p38 : pairNat x38 H38 = 2 * (x8.toNat * x5.toNat + x9.toNat * x7.toNat) := by
    have := pair_dbl x29 H29 (by rw [p29]; omega)
    rw [p29] at this; subst_vars; exact this
  obtain ⟨H39, eH39⟩ : ∃ h : BitVec 64, h = (mulResult x24 68719492368).snd + H38 + cf x33 x38 := ⟨_, rfl⟩
  have p39 : pairNat x39 H39 = x24.toNat * 68719492368 + 2 * (x8.toNat * x5.toNat + x9.toNat * x7.toNat) := by
    have := pair_add x33 (mulResult x24 68719492368).snd x38 H38 (by rw [m33, p38]; omega)
    rw [m33, p38] at this; subst_vars; exact this
  have hq1 : x44.toNat = pairNat x39 H39 / 2^52 := by
    have := shr52 x39 H39 (by rw [p39]; omega)
    subst_vars; exact this
  have lo39 := lo_toNat x39 H39
  have ht3 : x42.toNat = x39.toNat % 2^52 :=
    mask52_even x39 (by rw [p39] at lo39; omega)
  obtain ⟨H26, eH26⟩ : ∃ h : BitVec 64, h = (mulResult x6 x7).snd + (mulResult x9 x5).snd + cf x14 x17 := ⟨_, rfl⟩
  have p26 : pairNat x26 H26 = x9.toNat * x5.toNat + x6.toNat * x7.toNat := by
    have := pair_add_swap x14 (mulResult x9 x5).snd x17 (mulResult x6 x7).snd (by rw [m14, m17]; omega)
    rw [m14, m17] at this; subst_vars; exact this
  obtain ⟨H36, eH36⟩ : ∃ h : BitVec 64, h = shldResult 1 H26 x26 := ⟨_, rfl⟩
  have p36 : pairNat x36 H36 = 2 * (x9.toNat * x5.toNat + x6.toNat * x7.toNat) := by
    have := pair_dbl x26 H26 (by rw [p26]; omega)
    rw [p26] at this; subst_vars; exact this
  obtain ⟨H41, eH41⟩ : ∃ h : BitVec 64, h = H36 + (mulResult x8 x8).snd + cf x36 x12 := ⟨_, rfl⟩
  have p41 : pairNat x41 H41 = 2 * (x9.toNat * x5.toNat + x6.toNat * x7.toNat) + x8.toNat * x8.toNat := by
    have := pair_add x36 H36 x12 (mulResult x8 x8).snd (by rw [p36, m12]; omega)
    rw [p36, m12] at this; subst_vars; exact this
  have m40 : pairNat x40 (mulResult x32 68719492368).snd = x32.toNat * 68719492368 := pair_mul _ _
  obtain ⟨H43, eH43⟩ : ∃ h : BitVec 64, h = H41 + (mulResult x32 68719492368).snd + cf x41 x40 := ⟨_, rfl⟩
  have p43 : pairNat x43 H43 = 2 * (x9.toNat * x5.toNat + x6.toNat * x7.toNat) + x8.toNat * x8.toNat + x32.toNat * 68719492368 := by
    have := pair_add x41 H41 x40 (mulResult x32 68719492368).snd (by rw [p41, m40]; omega)
    rw [p41, m40] at this; subst_vars; exact this
  obtain ⟨H45, eH45⟩ : ∃ h : BitVec 64, h = H43 + cf x43 x44 := ⟨_, rfl⟩
  have p45 : pairNat x45 H45 = 2 * (x9.toNat * x5.toNat + x6.toNat * x7.toNat) + x8.toNat * x8.toNat + x32.toNat * 68719492368 + x44.toNat := by
    have := pair_addw x43 H43 x44 (by rw [p43]; omega)
    rw [p43] at this; subst_vars; exact this
  have hq2 : x46.toNat = pairNat x45 H45 / 2^52 := by
    have := shr52 x45 H45 (by rw [p45]; omega)
    subst_vars; exact this
  have lo45 := lo_toNat x45 H45
  obtain ⟨H25, eH25⟩ : ∃ h : BitVec 64, h = (mulResult x9 x8).snd + (mulResult x6 x5).snd + cf x18 x21 := ⟨_, rfl⟩
  have p25 : pairNat x25 H25 = x6.toNat * x5.toNat + x9.toNat * x8.toNat := by
    have := pair_add_swap x18 (mulResult x6 x5).snd x21 (mulResult x9 x8).snd (by rw [m18, m21]; omega)
    rw [m18, m21] at this; subst_vars; exact this
  obtain ⟨H35, eH35⟩ : ∃ h : BitVec 64, h = shldResult 1 H25 x25 := ⟨_, rfl⟩
  have p35 : pairNat x35 H35 = 2 * (x6.toNat * x5.toNat + x9.toNat * x8.toNat) := by
    have := pair_dbl x25 H25 (by rw [p25]; omega)
    rw [p25] at this; subst_vars; exact this
  obtain ⟨H47, eH47⟩ : ∃ h : BitVec 64, h = H35 + cf x35 x46 := ⟨_, rfl⟩
  have p47 : pairNat x47 H47 = 2 * (x6.toNat * x5.toNat + x9.toNat * x8.toNat) + x46.toNat := by
    have := pair_addw x35 H35 x46 (by rw [p35]; omega)
    rw [p35] at this; subst_vars; exact this
  have hq3 : x49.toNat = pairNat x47 H47 / 2^52 := by
    have := shr52 x47 H47 (by rw [p47]; omega)
    subst_vars; exact this
  have lo47 := lo_toNat x47 H47
  have hu0 : x48.toNat = x47.toNat % 2^52 * 16 + x45.toNat / 2^48 % 16 := u0_toNat x47 x45
  have bu0 : x48.toNat < 2^56 := by omega
  have m51 : pairNat x51 (mulResult x48 4294968273).snd = x48.toNat * 4294968273 := pair_mul _ _
  obtain ⟨H52, eH52⟩ : ∃ h : BitVec 64, h = (mulResult x48 4294968273).snd + (mulResult x7 x7).snd + cf x51 x13 := ⟨_, rfl⟩
  have p52 : pairNat x52 H52 = x48.toNat * 4294968273 + x7.toNat * x7.toNat := by
    have := pair_add x51 (mulResult x48 4294968273).snd x13 (mulResult x7 x7).snd (by rw [m51, m13]; omega)
    rw [m51, m13] at this; subst_vars; exact this
  have hp1 : x58.toNat = pairNat x52 H52 / 2^52 := by
    have := shr52 x52 H52 (by rw [p52]; omega)
    subst_vars; exact this
  have lo52 := lo_toNat x52 H52
  obtain ⟨H27, eH27⟩ : ∃ h : BitVec 64, h = shldResult 1 (mulResult x8 x6).snd x10 := ⟨_, rfl⟩
  have p27 : pairNat x27 H27 = 2 * (x8.toNat * x6.toNat) := by
    have := pair_dbl x10 (mulResult x8 x6).snd (by rw [m10]; omega)
    rw [m10] at this; subst_vars; exact this
  obtain ⟨H34, eH34⟩ : ∃ h : BitVec 64, h = (mulResult x9 x9).snd + H27 + cf x27 x22 := ⟨_, rfl⟩
  have p34 : pairNat x34 H34 = 2 * (x8.toNat * x6.toNat) + x9.toNat * x9.toNat := by
    have := pair_add_swap x27 H27 x22 (mulResult x9 x9).snd (by rw [p27, m22]; omega)
    rw [p27, m22] at this; subst_vars; exact this
  obtain ⟨H50, eH50⟩ : ∃ h : BitVec 64, h = H34 + cf x34 x49 := ⟨_, rfl⟩
  have p50 : pairNat x50 H50 = 2 * (x8.toNat * x6.toNat) + x9.toNat * x9.toNat + x49.toNat := by
    have := pair_addw x34 H34 x49 (by rw [p34]; omega)
    rw [p34] at this; subst_vars; exact this
  have hq4 : x56.toNat = pairNat x50 H50 / 2^52 := by
    have := shr52 x50 H50 (by rw [p50]; omega)
    subst_vars; exact this
  have lo50 := lo_toNat x50 H50
  have hw4 : x53.toNat = x50.toNat % 2^52 := mask52 x50
  have m54 : pairNat x54 (mulResult x53 68719492368).snd = x53.toNat * 68719492368 := pair_mul _ _
  obtain ⟨H28, eH28⟩ : ∃ h : BitVec 64, h = (mulResult x19 x5).snd + x7 >>> 63 * x5 := ⟨_, rfl⟩
  obtain ⟨H55, eH55⟩ : ∃ h : BitVec 64, h = (mulResult x53 68719492368).snd + H28 + cf x54 x28 := ⟨_, rfl⟩
  have m28' : pairNat x28 H28 = 2 * x7.toNat * x5.toNat := by subst_vars; exact m28
  have p55 : pairNat x55 H55 = x53.toNat * 68719492368 + 2 * x7.toNat * x5.toNat := by
    have := pair_add x54 (mulResult x53 68719492368).snd x28 H28 (by rw [m54, m28']; omega)
    rw [m54, m28'] at this; subst_vars; exact this
  obtain ⟨H59, eH59⟩ : ∃ h : BitVec 64, h = H55 + cf x55 x58 := ⟨_, rfl⟩
  have p59 : pairNat x59 H59 = x53.toNat * 68719492368 + 2 * x7.toNat * x5.toNat + x58.toNat := by
    have := pair_addw x55 H55 x58 (by rw [p55]; omega)
    rw [p55] at this; subst_vars; exact this
  have hp2 : x64.toNat = pairNat x59 H59 / 2^52 := by
    have := shr52 x59 H59 (by rw [p59]; omega)
    subst_vars; exact this
  have lo59 := lo_toNat x59 H59
  obtain ⟨H31, eH31⟩ : ∃ h : BitVec 64, h = shldResult 1 (mulResult x9 x6).snd x11 := ⟨_, rfl⟩
  have p31 : pairNat x31 H31 = 2 * (x9.toNat * x6.toNat) := by
    have := pair_dbl x11 (mulResult x9 x6).snd (by rw [m11]; omega)
    rw [m11] at this; subst_vars; exact this
  obtain ⟨H57, eH57⟩ : ∃ h : BitVec 64, h = H31 + cf x31 x56 := ⟨_, rfl⟩
  have p57 : pairNat x57 H57 = 2 * (x9.toNat * x6.toNat) + x56.toNat := by
    have := pair_addw x31 H31 x56 (by rw [p31]; omega)
    rw [p31] at this; subst_vars; exact this
  have hq5 : x63.toNat = pairNat x57 H57 / 2^52 := by
    have := shr52 x57 H57 (by rw [p57]; omega)
    subst_vars; exact this
  have lo57 := lo_toNat x57 H57
  have hw5 : x60.toNat = x57.toNat % 2^52 := mask52 x57
  obtain ⟨H30, eH30⟩ : ∃ h : BitVec 64, h = (mulResult x19 x8).snd + x7 >>> 63 * x8 := ⟨_, rfl⟩
  have m30' : pairNat x30 H30 = 2 * x7.toNat * x8.toNat := by subst_vars; exact m30
  obtain ⟨H37, eH37⟩ : ∃ h : BitVec 64, h = H30 + (mulResult x5 x5).snd + cf x30 x23 := ⟨_, rfl⟩
  have p37 : pairNat x37 H37 = 2 * x7.toNat * x8.toNat + x5.toNat * x5.toNat := by
    have := pair_add x30 H30 x23 (mulResult x5 x5).snd (by rw [m30', m23]; omega)
    rw [m30', m23] at this; subst_vars; exact this
  have m61 : pairNat x61 (mulResult x60 68719492368).snd = x60.toNat * 68719492368 := pair_mul _ _
  obtain ⟨H62, eH62⟩ : ∃ h : BitVec 64, h = H37 + (mulResult x60 68719492368).snd + cf x37 x61 := ⟨_, rfl⟩
  have p62 : pairNat x62 H62 = 2 * x7.toNat * x8.toNat + x5.toNat * x5.toNat + x60.toNat * 68719492368 := by
    have := pair_add x37 H37 x61 (mulResult x60 68719492368).snd (by rw [p37, m61]; omega)
    rw [p37, m61] at this; subst_vars; exact this
  obtain ⟨H66, eH66⟩ : ∃ h : BitVec 64, h = H62 + cf x62 x64 := ⟨_, rfl⟩
  have p66 : pairNat x66 H66 = 2 * x7.toNat * x8.toNat + x5.toNat * x5.toNat + x60.toNat * 68719492368 + x64.toNat := by
    have := pair_addw x62 H62 x64 (by rw [p62]; omega)
    rw [p62] at this; subst_vars; exact this
  have hp3 : x68.toNat = pairNat x66 H66 / 2^52 := by
    have := shr52 x66 H66 (by rw [p66]; omega)
    subst_vars; exact this
  have lo66 := lo_toNat x66 H66
  have m65 : pairNat x65 (mulResult x63 68719492368).snd = x63.toNat * 68719492368 := pair_mul _ _
  obtain ⟨H67, eH67⟩ : ∃ h : BitVec 64, h = (mulResult x63 68719492368).snd + cf x42 x65 := ⟨_, rfl⟩
  have p67 : pairNat x67 H67 = x42.toNat + x63.toNat * 68719492368 := by
    have := pair_waddp x42 x65 (mulResult x63 68719492368).snd (by rw [m65]; omega)
    rw [m65] at this; subst_vars; exact this
  obtain ⟨H69, eH69⟩ : ∃ h : BitVec 64, h = H67 + cf x67 x68 := ⟨_, rfl⟩
  have p69 : pairNat x69 H69 = x42.toNat + x63.toNat * 68719492368 + x68.toNat := by
    have := pair_addw x67 H67 x68 (by rw [p67]; omega)
    rw [p67] at this; subst_vars; exact this
  have hp4 : (shldResult 12 H69 x69).toNat = pairNat x69 H69 / 2^52 :=
    shr52 x69 H69 (by rw [p69]; omega)
  have lo69 := lo_toNat x69 H69
  have hr4 : ((281474976710655 &&& x45) + shldResult 12 H69 x69).toNat =
      x45.toNat % 2^48 + (shldResult 12 H69 x69).toNat := by
    rw [BitVec.toNat_add, mask48']
    omega
  have hf : ((281474976710655 &&& x45) + shldResult 12
      ((mulResult x63 68719492368).snd + cf x42 x65 + cf x67 x68) x69).toNat =
      x45.toNat % 2^48 + (shldResult 12 H69 x69).toNat := by
    subst_vars; exact hr4
  have c1 : x5.toNat * x8.toNat = x8.toNat * x5.toNat := Nat.mul_comm _ _
  have c2 : x7.toNat * x9.toNat = x9.toNat * x7.toNat := Nat.mul_comm _ _
  have c3 : x5.toNat * x9.toNat = x9.toNat * x5.toNat := Nat.mul_comm _ _
  have c4 : x7.toNat * x6.toNat = x6.toNat * x7.toNat := Nat.mul_comm _ _
  have c5 : x5.toNat * x6.toNat = x6.toNat * x5.toNat := Nat.mul_comm _ _
  have c6 : x8.toNat * x9.toNat = x9.toNat * x8.toNat := Nat.mul_comm _ _
  have c7 : 2 * x8.toNat * x6.toNat = 2 * (x8.toNat * x6.toNat) := Nat.mul_assoc _ _ _
  have c8 : 2 * x9.toNat * x6.toNat = 2 * (x9.toNat * x6.toNat) := Nat.mul_assoc _ _ _
  refine ⟨x32.toNat, x24.toNat, x44.toNat, x42.toNat, x46.toNat, x45.toNat % 2^52,
    x45.toNat % 2^48, x45.toNat / 2^48 % 16, x49.toNat, x47.toNat % 2^52, x58.toNat,
    x52.toNat % 2^52, x56.toNat, x53.toNat, x64.toNat, x59.toNat % 2^52, x63.toNat, x60.toNat,
    x68.toNat, x66.toNat % 2^52, (shldResult 12 H69 x69).toNat, x69.toNat % 2^52,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, mask52 x52, mask52 x59, mask52 x66, mask52' x69,
    hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem modulus_eq : modulus = P := by
  unfold modulus Standards.SECG.DomainParameters.Secp256k1.domain; rfl

theorem foldl5 (f : Nat → Nat) :
    (List.range 5).foldl (fun z i => z + f i) 0 = 0 + f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem limbValue_eq (a : Limbs) : limbValue a = a[0]!.toNat + a[1]!.toNat * 2^52 +
    a[2]!.toNat * 2^104 + a[3]!.toNat * 2^156 + a[4]!.toNat * 2^208 := by
  have h : limbValue a = 0 + a[0]!.toNat * radix^0 + a[1]!.toNat * radix^1 +
      a[2]!.toNat * radix^2 + a[3]!.toNat * radix^3 + a[4]!.toNat * radix^4 :=
    foldl5 (fun i => (a[i]!).toNat * radix ^ i)
  have r2 : radix^2 = 2^104 := by unfold radix; rw [← Nat.pow_mul]
  have r3 : radix^3 = 2^156 := by unfold radix; rw [← Nat.pow_mul]
  have r4 : radix^4 = 2^208 := by unfold radix; rw [← Nat.pow_mul]
  rw [h, r2, r3, r4, Nat.pow_one, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  rfl

end SquareValue

open SquareValue in
theorem squareWords_repr (a : Limbs) (x : Fin modulus) (h : FieldRepr a x 8) :
    FieldRepr (squareWords a) (x * x) 1 := by
  have b0 : a[0]!.toNat ≤ 2 * 8 * (2^52 - 1) := h.1 ⟨0, by decide⟩
  have b1 : a[1]!.toNat ≤ 2 * 8 * (2^52 - 1) := h.1 ⟨1, by decide⟩
  have b2 : a[2]!.toNat ≤ 2 * 8 * (2^52 - 1) := h.1 ⟨2, by decide⟩
  have b3 : a[3]!.toNat ≤ 2 * 8 * (2^52 - 1) := h.1 ⟨3, by decide⟩
  have b4 : a[4]!.toNat ≤ 2 * 8 * (2^48 - 1) := h.1 ⟨4, by decide⟩
  have hv := h.2
  rw [limbValue_eq] at hv
  simp only [getElem!_pos, Nat.reduceLT] at b0 b1 b2 b3 b4 hv
  obtain ⟨c1, l, q1, t3, q2, t4f, t4, tx, q3, u, p1, r0, q4, w4, p2, r1, q5, w5, p3, r2, p4, r3,
    e0, e1, e2, e2', e3, e4, e5, e6, e7, e8, e9, o0, o1, o2, o3, o4, k0, k1, k2, k3, k4, k5⟩ :=
    squareLimbs_chain a (by omega) (by omega) (by omega) (by omega) (by omega)
  have hm := chain_mod _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    e0 e1 e2 e2' e3 e4 e5 e6 e7 e8 e9
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨i, hi⟩ := i
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · show ((squareWords a)[0]!).toNat ≤ 2 * 1 * (2 ^ 52 - 1)
      simp only [squareWords]; simp; omega
    · show ((squareWords a)[1]!).toNat ≤ 2 * 1 * (2 ^ 52 - 1)
      simp only [squareWords]; simp; omega
    · show ((squareWords a)[2]!).toNat ≤ 2 * 1 * (2 ^ 52 - 1)
      simp only [squareWords]; simp; omega
    · show ((squareWords a)[3]!).toNat ≤ 2 * 1 * (2 ^ 52 - 1)
      simp only [squareWords]; simp; omega
    · show ((squareWords a)[4]!).toNat ≤ 2 * 1 * (2 ^ 48 - 1)
      simp only [squareWords]; simp; omega
  · rw [limbValue_eq]
    simp only [squareWords]
    simp
    rw [o0, o1, o2, o3, o4, Fin.val_mul, ← hv, modulus_eq, hm, ← Nat.mul_mod, Nat.pow_two]

end K256.Proofs.Common.Field
