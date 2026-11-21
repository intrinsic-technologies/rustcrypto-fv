import K256.Proofs.Common.Field.SquareValue
import K256.Proofs.Sec1.Serialize.Normalize.Words

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field

private theorem first_toNat (a : Limbs) (m : Nat) (hm : m ≤ 2047)
    (h0 : a[0].toNat ≤ 2*m*(2^52-1)) (h4 : a[4].toNat ≤ 2*m*(2^48-1)) :
    (first a).toNat = a[4].toNat / 2^48 * 4294968273 + a[0].toNat := by
  rw [first, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change ((a[4].toNat / 2^48 * 4294968273) % 2^64 + a[0].toNat) % 2^64 = _
  have hh : a[4].toNat / 2^48 ≤ 4094 := by omega
  have ha : a[0].toNat ≤ 4094 * (2^52 - 1) :=
    Nat.le_trans h0 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hm))
  have hc := Nat.mul_le_mul_right 4294968273 hh
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hc (by decide : 4094 * 4294968273 < 2^64))]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add hc ha) (by decide))

private theorem carry_toNat (t a : Word) (m : Nat) (hm : m ≤ 2047)
    (h : a.toNat ≤ 2*m*(2^52-1)) : (carry t a).toNat = t.toNat / 2^52 + a.toNat := by
  simp only [carry, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := t.isLt
  omega

private theorem top_toNat (t a : Word) : (top t a).toNat = t.toNat / 2^52 + a.toNat % 2^48 := by
  simp only [top, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_and]
  change (_ + (a.toNat &&& (2^48 - 1))) % 2^64 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := t.isLt
  omega

private theorem folded_lt (a b c d e : Word) (he : e.toNat < 2^48 + 4096) :
    foldedValue a b c d e < 2*modulus := by
  unfold foldedValue
  rw [show modulus = 2^256 - 4294968273 by decide +kernel]
  omega

private theorem fold_identity (a b c d e t0 t1 t2 t3 t4 : Nat)
    (h0 : t0 = e / 2^48 * 4294968273 + a) (h1 : t1 = t0 / 2^52 + b)
    (h2 : t2 = t1 / 2^52 + c) (h3 : t3 = t2 / 2^52 + d)
    (h4 : t4 = t3 / 2^52 + e % 2^48) :
    a + b * 2^52 + c * 2^104 + d * 2^156 + e * 2^208 =
      ((((t4 * 2^52 + t3 % 2^52) * 2^52 + t2 % 2^52) * 2^52 +
        t1 % 2^52) * 2^52 + t0 % 2^52) + e / 2^48 * modulus := by
  rw [show modulus = 2^256 - 4294968273 by decide +kernel]
  omega

theorem firstPass_correct (a : Limbs) (x : Fin modulus) (m : Nat)
    (h : FieldRepr a x m) (hm : m ≤ 2047) :
    let t0 := first a
    let t1 := carry t0 a[1]
    let t2 := carry t1 a[2]
    let t3 := carry t2 a[3]
    let t4 := top t3 a[4]
    let v := foldedValue t0 t1 t2 t3 t4
    t4.toNat < 2^49 ∧ v < 2*modulus ∧ v % modulus = x.val := by
  dsimp only
  obtain ⟨hb, hx⟩ := h
  have h0 := hb (0 : Fin 5)
  change a[0].toNat ≤ 2 * m * (2^52 - 1) at h0
  have h1 := hb (1 : Fin 5)
  change a[1].toNat ≤ 2 * m * (2^52 - 1) at h1
  have h2 := hb (2 : Fin 5)
  change a[2].toNat ≤ 2 * m * (2^52 - 1) at h2
  have h3 := hb (3 : Fin 5)
  change a[3].toNat ≤ 2 * m * (2^52 - 1) at h3
  have h4 := hb (4 : Fin 5)
  change a[4].toNat ≤ 2 * m * (2^48 - 1) at h4
  let t0 := first a
  let t1 := carry t0 a[1]
  let t2 := carry t1 a[2]
  let t3 := carry t2 a[3]
  let t4 := top t3 a[4]
  let v := foldedValue t0 t1 t2 t3 t4
  change t4.toNat < 2^49 ∧ v < 2*modulus ∧ v % modulus = x.val
  have e4 := top_toNat t3 a[4]
  have ht : t4.toNat < 2^48 + 4096 := by
    change (top t3 a[4]).toNat < _
    rw [e4]
    have hn : t3.toNat / 2^52 < 4096 := (Nat.div_lt_iff_lt_mul (by decide)).mpr t3.isLt
    have hh := Nat.mod_lt a[4].toNat (show 0 < 2^48 by decide)
    omega
  have hv := folded_lt t0 t1 t2 t3 t4 ht
  refine ⟨Nat.lt_trans ht (by decide), hv, ?_⟩
  have hid : limbValue a = v + a[4].toNat / 2^48 * modulus := by
    rw [SquareValue.limbValue_eq]
    exact fold_identity _ _ _ _ _ _ _ _ _ _ (first_toNat a m hm h0 h4)
      (carry_toNat t0 _ m hm h1) (carry_toNat t1 _ m hm h2) (carry_toNat t2 _ m hm h3) e4
  rw [hid, Nat.add_mul_mod_self_right] at hx
  exact hx

end K256.Proofs.Sec1.Serialize.Normalize
