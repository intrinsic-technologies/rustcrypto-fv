import K256.Proofs.Sec1.Serialize.Normalize.Fold

namespace K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Field

def equation (cube square : Limbs) : Bool :=
  let top := 0x3fffffffffffc + (cube[4] - square[4])
  let t0 := 0x3ffffbfffff0c3 + (cube[0] - square[0]) + 0x1000003d1 * (top >>> 48)
  let t1 := 0x3ffffffffffffc + (cube[1] - square[1]) + (t0 >>> 52)
  let t2 := 0x3ffffffffffffc + (cube[2] - square[2]) + (t1 >>> 52)
  let t3 := 0x3ffffffffffffc + (cube[3] - square[3]) + (t2 >>> 52)
  let t4 := (top &&& 0xffffffffffff) + (t3 >>> 52)
  ((t0 ^^^ 0x1000003d0) &&& t1 &&& t2 &&& t3 &&& (t4 ^^^ 0xf000000000000)) == 0xfffffffffffff

open K256.Proofs.Sec1.Serialize.Normalize

private theorem biased_limb (bias c s : Word) (bound : Nat)
    (hc : c.toNat ≤ bound) (hs : s.toNat ≤ bound)
    (hl : bound ≤ bias.toNat) (hu : bias.toNat ≤ 2 * bound) (hfit : 3 * bound < 2^64) :
    (bias + (c - s)).toNat + s.toNat = bias.toNat + c.toNat ∧
      (bias + (c - s)).toNat ≤ 3 * bound := by
  have hadd : (bias + c).toNat = bias.toNat + c.toNat := BitVec.toNat_add_of_lt (by omega)
  have hsub : s ≤ bias + c := by
    rw [BitVec.le_def, hadd]
    omega
  rw [BitVec.sub_eq_add_neg, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
    BitVec.toNat_sub_of_le hsub, hadd]
  omega

private theorem low52_ones (a : Word) :
    a.setWidth 52 = BitVec.allOnes 52 ↔ a.toNat % 2^52 = 2^52 - 1 := by
  rw [BitVec.toNat_eq]
  rfl

private theorem low52_xor_ones (a mask target : Word)
    (h : (target ^^^ mask).setWidth 52 = BitVec.allOnes 52) :
    (a ^^^ mask).setWidth 52 = BitVec.allOnes 52 ↔ a.toNat % 2^52 = target.toNat % 2^52 := by
  rw [← h, BitVec.setWidth_xor, BitVec.setWidth_xor, BitVec.xor_left_inj, BitVec.toNat_eq]
  rfl

private theorem mask_eq_modulus (a b c d e : Word) (he : e.toNat < 2^49) :
    (a ^^^ 0x1000003d0) &&& b &&& c &&& d &&& (e ^^^ 0xf000000000000) = 0xfffffffffffff ↔
      foldedValue a b c d e = modulus := by
  let w := (a ^^^ 0x1000003d0) &&& b &&& c &&& d
  change w &&& (e ^^^ 0xf000000000000) = 0xfffffffffffff ↔ _
  have ha := low52_xor_ones a 0x1000003d0 4503595332402223 (by decide +kernel)
  have he' := low52_xor_ones e 0xf000000000000 281474976710655 (by decide +kernel)
  change _ ↔ a.toNat % 2^52 = 4503595332402223 at ha
  change _ ↔ e.toNat % 2^52 = 281474976710655 at he'
  rw [Nat.mod_eq_of_lt (by omega : e.toNat < 2^52)] at he'
  have hlow : (w &&& (e ^^^ 0xf000000000000)).setWidth 52 = BitVec.allOnes 52 ↔
      ((((a.toNat % 2^52 = 4503595332402223 ∧ b.toNat % 2^52 = 2^52 - 1) ∧
        c.toNat % 2^52 = 2^52 - 1) ∧ d.toNat % 2^52 = 2^52 - 1) ∧
        e.toNat = 281474976710655) := by
    simp only [w, BitVec.setWidth_and, BitVec.and_eq_allOnes_iff, low52_ones, ha, he']
  have hvalue : (w &&& (e ^^^ 0xf000000000000)).setWidth 52 = BitVec.allOnes 52 ↔
      foldedValue a b c d e = modulus := by
    rw [hlow]
    rw [show modulus = 2^256 - 4294968273 by decide +kernel, foldedValue]
    omega
  constructor
  · intro h
    apply hvalue.mp
    rw [h]
    decide +kernel
  · intro h
    have hbits := hvalue.mpr h
    have etop : e = 281474976710655 := BitVec.eq_of_toNat_eq (hlow.mp hbits).2
    rw [etop] at hbits ⊢
    have hx : (281474976710655 : Word) ^^^ 0xf000000000000 = 0xfffffffffffff := by decide +kernel
    rw [hx] at hbits ⊢
    have hw : w.setWidth 52 = BitVec.allOnes 52 := by
      rw [BitVec.setWidth_and,
        show (0xfffffffffffff : Word).setWidth 52 = BitVec.allOnes 52 by decide +kernel,
        BitVec.and_allOnes] at hbits
      exact hbits
    apply BitVec.eq_of_toNat_eq
    rw [SquareValue.mask52]
    exact (low52_ones w).mp hw

private theorem folded_eq_modulus (f x y : Nat) (hf : 0 < f)
    (hlt : f < 2 * modulus) (hy : y < modulus)
    (h : (f + y) % modulus = (x + 7) % modulus) :
    f = modulus ↔ y = (x + 7) % modulus := by
  rw [show modulus = 2^256 - 4294968273 by decide +kernel] at hlt hy h ⊢
  omega

private def biasedLimbs (cube square : Limbs) : Limbs :=
  #v[
    0x3ffffbfffff0c3 + (cube[0] - square[0]),
    0x3ffffffffffffc + (cube[1] - square[1]),
    0x3ffffffffffffc + (cube[2] - square[2]),
    0x3ffffffffffffc + (cube[3] - square[3]),
    0x3fffffffffffc + (cube[4] - square[4])]

private theorem equation_fold (a : Limbs) :
    let t0 := first a
    let t1 := carry t0 a[1]
    let t2 := carry t1 a[2]
    let t3 := carry t2 a[3]
    let t4 := top t3 a[4]
    (let s0 := a[0] + 0x1000003d1 * (a[4] >>> 48)
          let s1 := a[1] + (s0 >>> 52)
          let s2 := a[2] + (s1 >>> 52)
          let s3 := a[3] + (s2 >>> 52)
          let s4 := (a[4] &&& 0xffffffffffff) + (s3 >>> 52)
          ((s0 ^^^ 0x1000003d0) &&& s1 &&& s2 &&& s3 &&& (s4 ^^^ 0xf000000000000)) ==
            0xfffffffffffff) =
      (((t0 ^^^ 0x1000003d0) &&& t1 &&& t2 &&& t3 &&& (t4 ^^^ 0xf000000000000)) == 0xfffffffffffff) := by
  dsimp only
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  let t4 := top t3 a[4]
  have e0 : a[0] + 0x1000003d1 * (a[4] >>> 48) = t0 := by
    change _ = (a[4] >>> 48) * 4294968273 + a[0]
    rw [BitVec.add_comm a[0]]
    exact congrArg (· + a[0]) (BitVec.mul_comm _ _)
  have ecarry (x t : Word) : x + (t >>> 52) = carry t x := BitVec.add_comm _ _
  have etop : (a[4] &&& 0xffffffffffff) + (t3 >>> 52) = t4 := BitVec.add_comm _ _
  rw [e0, ecarry a[1] t0, ecarry a[2] t1, ecarry a[3] t2, etop]

private theorem biasedLimbs_repr {cube square : Limbs} {u v : Fin modulus}
    (hc : FieldRepr cube u 1) (hs : FieldRepr square v 1) :
    let a := biasedLimbs cube square
    FieldRepr a ⟨limbValue a % modulus, Nat.mod_lt _ (by decide +kernel)⟩ 3 ∧
      limbValue a + limbValue square = limbValue cube + 7 + 4 * modulus ∧
      2^52 ≤ a[3].toNat := by
  dsimp only
  let a := biasedLimbs cube square
  have hb (i : Fin 5) :
      if i.val < 4 then (cube[i.val]!).toNat ≤ 2 * (2^52 - 1) ∧
        (square[i.val]!).toNat ≤ 2 * (2^52 - 1)
      else (cube[i.val]!).toNat ≤ 2 * (2^48 - 1) ∧
        (square[i.val]!).toNat ≤ 2 * (2^48 - 1) := by
    have hci := hc.1 i
    have hsi := hs.1 i
    by_cases h : i.val < 4 <;> simp only [h, ite_true, ite_false] at * <;> exact ⟨hci, hsi⟩
  obtain ⟨e0, h0⟩ := biased_limb 0x3ffffbfffff0c3 cube[0] square[0] (2 * (2^52 - 1))
    (hb 0).1 (hb 0).2 (by decide) (by decide) (by decide)
  change a[0].toNat + square[0].toNat = 0x3ffffbfffff0c3 + cube[0].toNat at e0
  change a[0].toNat ≤ 3 * (2 * (2^52 - 1)) at h0
  obtain ⟨e1, h1⟩ := biased_limb 0x3ffffffffffffc cube[1] square[1] (2 * (2^52 - 1))
    (hb 1).1 (hb 1).2 (by decide) (by decide) (by decide)
  change a[1].toNat + square[1].toNat = 0x3ffffffffffffc + cube[1].toNat at e1
  change a[1].toNat ≤ 3 * (2 * (2^52 - 1)) at h1
  obtain ⟨e2, h2⟩ := biased_limb 0x3ffffffffffffc cube[2] square[2] (2 * (2^52 - 1))
    (hb 2).1 (hb 2).2 (by decide) (by decide) (by decide)
  change a[2].toNat + square[2].toNat = 0x3ffffffffffffc + cube[2].toNat at e2
  change a[2].toNat ≤ 3 * (2 * (2^52 - 1)) at h2
  obtain ⟨e3, h3⟩ := biased_limb 0x3ffffffffffffc cube[3] square[3] (2 * (2^52 - 1))
    (hb 3).1 (hb 3).2 (by decide) (by decide) (by decide)
  change a[3].toNat + square[3].toNat = 0x3ffffffffffffc + cube[3].toNat at e3
  change a[3].toNat ≤ 3 * (2 * (2^52 - 1)) at h3
  obtain ⟨e4, h4⟩ := biased_limb 0x3fffffffffffc cube[4] square[4] (2 * (2^48 - 1))
    (hb 4).1 (hb 4).2 (by decide) (by decide) (by decide)
  change a[4].toNat + square[4].toNat = 0x3fffffffffffc + cube[4].toNat at e4
  change a[4].toNat ≤ 3 * (2 * (2^48 - 1)) at h4
  refine ⟨⟨?_, rfl⟩, ?_, ?_⟩
  · intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp only [Fin.ext_iff]; omega
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rw [SquareValue.limbValue_eq, SquareValue.limbValue_eq, SquareValue.limbValue_eq,
      show modulus = 2^256 - 4294968273 by decide +kernel]
    change (a[0].toNat + a[1].toNat * 2^52 + a[2].toNat * 2^104 +
      a[3].toNat * 2^156 + a[4].toNat * 2^208) +
      (square[0].toNat + square[1].toNat * 2^52 + square[2].toNat * 2^104 +
      square[3].toNat * 2^156 + square[4].toNat * 2^208) =
      (cube[0].toNat + cube[1].toNat * 2^52 + cube[2].toNat * 2^104 +
      cube[3].toNat * 2^156 + cube[4].toNat * 2^208) + 7 + _
    omega
  · change 2^52 ≤ a[3].toNat
    have hs3 : square[3].toNat ≤ 2 * (2^52 - 1) := (hb 3).2
    omega

private theorem carry_ge (t a : Word) (ha : 2^52 ≤ a.toNat)
    (hb : a.toNat ≤ 2 * 3 * (2^52 - 1)) : 2^52 ≤ (carry t a).toNat := by
  have ht := t.isLt
  simp only [carry, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

private theorem top_pos (t a : Word) (h : 2^52 ≤ t.toNat) : 0 < (top t a).toNat := by
  have ht := t.isLt
  simp only [top, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and]
  change 0 < (t.toNat / 2^52 + (a.toNat &&& (2^48 - 1))) % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem folded_pos (a b c d e : Word) (he : 0 < e.toNat) :
    0 < foldedValue a b c d e := by
  unfold foldedValue
  omega

theorem equation_eq {cube square : Limbs} {u v : Fin modulus}
    (hc : FieldRepr cube u 1) (hs : FieldRepr square v 1) :
    equation cube square = decide (v.val = (u.val + 7) % modulus) := by
  let a := biasedLimbs cube square
  have hadata : FieldRepr a ⟨limbValue a % modulus, Nat.mod_lt _ (by decide +kernel)⟩ 3 ∧
      limbValue a + limbValue square = limbValue cube + 7 + 4 * modulus ∧
      2^52 ≤ a[3].toNat := biasedLimbs_repr hc hs
  obtain ⟨ha, hbalance, hpos⟩ := hadata
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  let t4 := top t3 a[4]
  let f := foldedValue t0 t1 t2 t3 t4
  have hpass : t4.toNat < 2^49 ∧ f < 2 * modulus ∧ f % modulus = limbValue a % modulus :=
    firstPass_correct _ _ _ ha (by decide)
  obtain ⟨ht4, hlt, hmod⟩ := hpass
  have ht3 : 2^52 ≤ t3.toNat := carry_ge t2 a[3] hpos (ha.1 3)
  have hf : 0 < f := folded_pos t0 t1 t2 t3 t4 (top_pos t3 a[4] ht3)
  have hres : (f + v.val) % modulus = (u.val + 7) % modulus := by
    calc
      (f + v.val) % modulus = (limbValue a + limbValue square) % modulus := by
        rw [Nat.add_mod f, Nat.add_mod (limbValue a), hmod, hs.2, Nat.mod_eq_of_lt v.isLt]
      _ = (limbValue cube + 7) % modulus := by
        rw [hbalance, Nat.add_mul_mod_self_right]
      _ = (u.val + 7) % modulus := by
        rw [Nat.add_mod (limbValue cube), Nat.add_mod u.val, hc.2, Nat.mod_eq_of_lt u.isLt]
  have hfold : equation cube square =
      (((t0 ^^^ 0x1000003d0) &&& t1 &&& t2 &&& t3 &&& (t4 ^^^ 0xf000000000000)) ==
        0xfffffffffffff) := equation_fold a
  rw [hfold]
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using
    (mask_eq_modulus t0 t1 t2 t3 t4 ht4).trans (folded_eq_modulus f u.val v.val hf hlt v.isLt hres)

end K256.Proofs.Sec1.Affine.Uncompressed
