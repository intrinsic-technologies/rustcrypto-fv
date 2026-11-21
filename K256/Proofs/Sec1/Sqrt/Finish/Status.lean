import K256.Proofs.Sec1.Serialize.Normalize.Fold
import K256.Proofs.Common.Field.Square

namespace K256.Proofs.Sec1.Sqrt.Finish

open K256.Proofs.Common.Field
open K256.Proofs.Sec1.Serialize.Normalize

def difference (rhs sq : Limbs) : Limbs :=
  #v[0x3ffffbfffff0bc + (rhs[0] - sq[0]), 0x3ffffffffffffc + rhs[1] - sq[1],
    0x3ffffffffffffc + rhs[2] - sq[2], 0x3ffffffffffffc + rhs[3] - sq[3],
    0x3fffffffffffc + (rhs[4] - sq[4])]

def zeroStatus (d : Limbs) : Word :=
  let t0 := first d
  let t1 := carry t0 d[1]
  let t2 := carry t1 d[2]
  let t3 := carry t2 d[3]
  let t4 := top t3 d[4]
  let m : Word := 4503599627370495
  let isZero := (((t1 ||| t0) ||| t2) ||| t3) &&& m ||| t4
  let isP := (((t0 ^^^ 4294968272) &&& t1) &&& t2) &&& t3 &&& ((0xf000000000000 : Word) ^^^ t4)
  ((if isZero = 0 then (1 : BitVec 8) else 0) |||
    (if isP = m then (1 : BitVec 8) else 0)).setWidth 64

def comparisonStatus (a rhs : Limbs) : Word := zeroStatus (difference rhs (squareWords a))

private theorem andMask (a b m : Word) :
    a &&& b &&& m = m ↔ a &&& m = m ∧ b &&& m = m := by
  have dist : a &&& b &&& m = (a &&& m) &&& (b &&& m) := by
    calc
      a &&& b &&& m = a &&& b &&& (m &&& m) := by rw [BitVec.and_self]
      _ = _ := by ac_rfl
  rw [dist]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at hn
    have hl : m.toNat ≤ (a &&& m).toNat := hn ▸ Nat.and_le_left
    have hr : m.toNat ≤ (b &&& m).toNat := hn ▸ Nat.and_le_right
    exact ⟨BitVec.eq_of_toNat_eq (Nat.le_antisymm Nat.and_le_right hl),
      BitVec.eq_of_toNat_eq (Nat.le_antisymm Nat.and_le_right hr)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, BitVec.and_self]

private theorem xorMask (a b m : Word) :
    (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases m.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem pTest (a b c d e : Word) (he : e.toNat < 2 ^ 49) :
    (((a ^^^ 4294968272) &&& b) &&& c) &&& d &&& ((0xf000000000000 : Word) ^^^ e)
        = 4503599627370495 ↔ foldedValue a b c d e = modulus := by
  let m : Word := 4503599627370495
  let k : Word := 4294968272
  let f : Word := 0xf000000000000
  let r := (((a ^^^ k) &&& b) &&& c) &&& d &&& (f ^^^ e)
  change r = m ↔ _
  have mask : r &&& m = r := by
    have hs : (f ^^^ e) &&& m = f ^^^ e := by
      rw [xorMask, show f &&& m = f by decide +kernel]
      congr 1
      apply BitVec.eq_of_toNat_eq
      change (e &&& 4503599627370495).toNat = _
      rw [SquareValue.mask52, Nat.mod_eq_of_lt (by omega)]
    change _ &&& _ &&& m = _
    rw [BitVec.and_assoc, hs]
  have eMask : e &&& m = e := by
    apply BitVec.eq_of_toNat_eq
    change (e &&& 4503599627370495).toNat = _
    rw [SquareValue.mask52, Nat.mod_eq_of_lt (by omega)]
  rw [← mask]
  dsimp only [r]
  simp only [andMask]
  rw [xorMask, xorMask, show k &&& m = k by decide +kernel,
    show f &&& m = f by decide +kernel, eMask]
  have ha : (a &&& m) ^^^ k = m ↔ a &&& m = 4503595332402223 := by
    rw [show m = (4503595332402223 : Word) ^^^ k by decide +kernel, BitVec.xor_left_inj]
  have he' : f ^^^ e = m ↔ e = 281474976710655 := by
    rw [show m = f ^^^ (281474976710655 : Word) by decide +kernel, BitVec.xor_right_inj]
  rw [ha, he']
  simp only [m, BitVec.toNat_eq, SquareValue.mask52]
  change ((((a.toNat % 2 ^ 52 = 4503595332402223 ∧ b.toNat % 2 ^ 52 = 4503599627370495) ∧
    c.toNat % 2 ^ 52 = 4503599627370495) ∧ d.toNat % 2 ^ 52 = 4503599627370495) ∧
    e.toNat = 281474976710655) ↔ _
  rw [show modulus = 2 ^ 256 - 4294968273 by decide +kernel]
  unfold foldedValue
  omega

private theorem zeroTest (a b c d e : Word) :
    (((b ||| a) ||| c) ||| d) &&& 4503599627370495 ||| e = 0 ↔
      foldedValue a b c d e = 0 := by
  change (((b ||| a) ||| c) ||| d) &&& 4503599627370495 ||| e = 0#64 ↔ _
  simp only [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff]
  simp only [BitVec.toNat_eq, SquareValue.mask52, foldedValue]
  change ((((b.toNat % 2 ^ 52 = 0 ∧ a.toNat % 2 ^ 52 = 0) ∧ c.toNat % 2 ^ 52 = 0) ∧
    d.toNat % 2 ^ 52 = 0) ∧ e.toNat = 0) ↔ _
  omega

theorem zeroStatus_correct (d : Limbs) (x : Fin modulus) (m : Nat)
    (hd : FieldRepr d x m) (hm : m ≤ 2047) :
    zeroStatus d = if x.val = 0 then 1 else 0 := by
  let t0 := first d
  let t1 := carry t0 d[1]
  let t2 := carry t1 d[2]
  let t3 := carry t2 d[3]
  let t4 := top t3 d[4]
  let v := foldedValue t0 t1 t2 t3 t4
  obtain ⟨ht, hv, hx⟩ := firstPass_correct d x m hd hm
  change t4.toNat < 2 ^ 49 at ht
  change v < 2 * modulus at hv
  change v % modulus = x.val at hx
  have hp : 0 < modulus := by decide +kernel
  unfold zeroStatus
  change (((if (((t1 ||| t0) ||| t2) ||| t3) &&& 4503599627370495 ||| t4 = 0 then
      (1 : BitVec 8) else 0) |||
    (if (((t0 ^^^ 4294968272) &&& t1) &&& t2) &&& t3 &&& ((0xf000000000000 : Word) ^^^ t4)
      = 4503599627370495 then (1 : BitVec 8) else 0)).setWidth 64) = _
  simp only [zeroTest, pTest t0 t1 t2 t3 t4 ht]
  change (((if v = 0 then (1 : BitVec 8) else 0) |||
      (if v = modulus then (1 : BitVec 8) else 0)).setWidth 64) = _
  have h : x.val = 0 ↔ v = 0 ∨ v = modulus := by
    rw [← hx]
    by_cases hlo : v < modulus
    · rw [Nat.mod_eq_of_lt hlo]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega : v - modulus < modulus)]
      omega
  by_cases hzero : v = 0 <;> by_cases hmod : v = modulus <;>
    simp only [h, hzero, hmod, or_self, true_or, or_true, ite_true, ite_false] <;> rfl

private theorem addSub_toNat (k a b : Word) (hadd : k.toNat + a.toNat < 2 ^ 64)
    (hsub : b.toNat ≤ k.toNat + a.toNat) :
    (k + a - b).toNat = k.toNat + a.toNat - b.toNat := by
  have ha : (k + a).toNat = k.toNat + a.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hadd]
  rw [BitVec.toNat_sub_of_le (by rwa [BitVec.le_def, ha]), ha]

private theorem differenceValue (a b : Limbs) (x y : Fin modulus) (m : Nat)
    (ha : FieldRepr a x m) (hb : FieldRepr b y 1) (hm : m ≤ 2045) :
    FieldRepr (difference a b) (x - y) (m + 2) := by
  have bound0 (i : Fin 5) := ha.1 i
  have bound1 (i : Fin 5) := hb.1 i
  have e0 : (difference a b)[0].toNat = 18014381329608892 + a[0].toNat - b[0].toNat := by
    have a0 := bound0 0
    have b0 := bound1 0
    change a[0].toNat ≤ 2 * m * (2 ^ 52 - 1) at a0
    change b[0].toNat ≤ 2 * 1 * (2 ^ 52 - 1) at b0
    change ((18014381329608892 : Word) + (a[0] - b[0])).toNat = _
    rw [show (18014381329608892 : Word) + (a[0] - b[0]) =
      (18014381329608892 : Word) + a[0] - b[0] by bv_omega]
    exact addSub_toNat _ _ _ (by change 18014381329608892 + _ < _; omega)
      (by change _ ≤ 18014381329608892 + _; omega)
  have e1 : (difference a b)[1].toNat = 18014398509481980 + a[1].toNat - b[1].toNat := by
    have ai := bound0 1
    have bi := bound1 1
    change a[1].toNat ≤ 2 * m * (2 ^ 52 - 1) at ai
    change b[1].toNat ≤ 2 * 1 * (2 ^ 52 - 1) at bi
    exact addSub_toNat _ _ _ (by change 18014398509481980 + _ < _; omega)
      (by change _ ≤ 18014398509481980 + _; omega)
  have e2 : (difference a b)[2].toNat = 18014398509481980 + a[2].toNat - b[2].toNat := by
    have ai := bound0 2
    have bi := bound1 2
    change a[2].toNat ≤ 2 * m * (2 ^ 52 - 1) at ai
    change b[2].toNat ≤ 2 * 1 * (2 ^ 52 - 1) at bi
    exact addSub_toNat _ _ _ (by change 18014398509481980 + _ < _; omega)
      (by change _ ≤ 18014398509481980 + _; omega)
  have e3 : (difference a b)[3].toNat = 18014398509481980 + a[3].toNat - b[3].toNat := by
    have ai := bound0 3
    have bi := bound1 3
    change a[3].toNat ≤ 2 * m * (2 ^ 52 - 1) at ai
    change b[3].toNat ≤ 2 * 1 * (2 ^ 52 - 1) at bi
    exact addSub_toNat _ _ _ (by change 18014398509481980 + _ < _; omega)
      (by change _ ≤ 18014398509481980 + _; omega)
  have e4 : (difference a b)[4].toNat = 1125899906842620 + a[4].toNat - b[4].toNat := by
    have a4 := bound0 4
    have b4 := bound1 4
    change a[4].toNat ≤ 2 * m * (2 ^ 48 - 1) at a4
    change b[4].toNat ≤ 2 * 1 * (2 ^ 48 - 1) at b4
    change ((1125899906842620 : Word) + (a[4] - b[4])).toNat = _
    rw [show (1125899906842620 : Word) + (a[4] - b[4]) =
      (1125899906842620 : Word) + a[4] - b[4] by bv_omega]
    exact addSub_toNat _ _ _ (by change 1125899906842620 + _ < _; omega)
      (by change _ ≤ 1125899906842620 + _; omega)
  constructor
  · intro ⟨i, hi⟩
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    · change (difference a b)[0].toNat ≤ 2 * (m + 2) * (2 ^ 52 - 1)
      have hz : a[0].toNat ≤ 2 * m * (2 ^ 52 - 1) := bound0 0
      rw [e0]
      omega
    · change (difference a b)[1].toNat ≤ 2 * (m + 2) * (2 ^ 52 - 1)
      have hz : a[1].toNat ≤ 2 * m * (2 ^ 52 - 1) := bound0 1
      rw [e1]
      omega
    · change (difference a b)[2].toNat ≤ 2 * (m + 2) * (2 ^ 52 - 1)
      have hz : a[2].toNat ≤ 2 * m * (2 ^ 52 - 1) := bound0 2
      rw [e2]
      omega
    · change (difference a b)[3].toNat ≤ 2 * (m + 2) * (2 ^ 52 - 1)
      have hz : a[3].toNat ≤ 2 * m * (2 ^ 52 - 1) := bound0 3
      rw [e3]
      omega
    · change (difference a b)[4].toNat ≤ 2 * (m + 2) * (2 ^ 48 - 1)
      have hz : a[4].toNat ≤ 2 * m * (2 ^ 48 - 1) := bound0 4
      rw [e4]
      omega
  · have hd : limbValue (difference a b) + limbValue b = limbValue a + 4 * modulus := by
      rw [SquareValue.limbValue_eq, SquareValue.limbValue_eq a, SquareValue.limbValue_eq b]
      simp only [getElem!_pos, Nat.reduceLT]
      rw [e0, e1, e2, e3, e4, show modulus = 2 ^ 256 - 4294968273 by decide +kernel]
      have q0 : b[0].toNat ≤ 2 * 1 * (2 ^ 52 - 1) := bound1 0
      have q1 : b[1].toNat ≤ 2 * 1 * (2 ^ 52 - 1) := bound1 1
      have q2 : b[2].toNat ≤ 2 * 1 * (2 ^ 52 - 1) := bound1 2
      have q3 : b[3].toNat ≤ 2 * 1 * (2 ^ 52 - 1) := bound1 3
      have q4 : b[4].toNat ≤ 2 * 1 * (2 ^ 48 - 1) := bound1 4
      omega
    have hp := congrArg (· % modulus) hd
    rw [Nat.add_mod (limbValue (difference a b)), hb.2, Nat.add_mul_mod_self_right, ha.2] at hp
    change limbValue (difference a b) % modulus = ((modulus - y.val) + x.val) % modulus
    have hl := Nat.mod_lt (limbValue (difference a b)) x.pos
    have hx := x.isLt
    have hy := y.isLt
    have cancel (p d a b : Nat) (hD : d < p) (hA : a < p) (hB : b < p)
        (h : (d + b) % p = a) : d = (p - b + a) % p := by
      by_cases h₁ : d + b < p
      · rw [Nat.mod_eq_of_lt h₁] at h
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    exact cancel modulus _ _ _ hl hx hy hp

theorem comparisonStatus_correct (a rhs : Limbs) (x y : Fin modulus) (m : Nat)
    (ha : FieldRepr a x 8) (hrhs : FieldRepr rhs y m) (hm : m ≤ 2045) :
    comparisonStatus a rhs = if x * x = y then 1 else 0 := by
  have hd := differenceValue rhs (squareWords a) y (x * x) m hrhs (squareWords_repr a x ha) hm
  rw [comparisonStatus, zeroStatus_correct _ _ _ hd (by omega)]
  have h : (y - x * x).val = 0 ↔ x * x = y := by
    change (((modulus - (x * x).val) + y.val) % modulus = 0) ↔ _
    rw [← Fin.val_inj]
    have cancel (p a b : Nat) (ha : a < p) (hb : b < p) : (p - b + a) % p = 0 ↔ b = a := by
      by_cases h₁ : a < b
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    exact cancel modulus _ _ y.isLt (x * x).isLt
  simp only [h]

end K256.Proofs.Sec1.Sqrt.Finish
