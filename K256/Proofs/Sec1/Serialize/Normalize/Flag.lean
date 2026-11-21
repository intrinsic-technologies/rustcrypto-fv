import K256.Proofs.Sec1.Serialize.Normalize.Words
import K256.Proofs.Common.Field.SquareValue

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field

private theorem and_eq_max_iff {a b m : Nat} (ha : a ≤ m) (hb : b ≤ m) :
    a &&& b = m ↔ a = m ∧ b = m := by
  constructor
  · intro h
    have h₁ : a &&& b ≤ a := Nat.and_le_left
    have h₂ : a &&& b ≤ b := Nat.and_le_right
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    exact Nat.and_self _

private theorem middle_eq_mask (b c d : Word) :
    c &&& (b &&& 4503599627370495) &&& d = 4503599627370495 ↔
      b.toNat % 2^52 = 4503599627370495 ∧ c.toNat % 2^52 = 4503599627370495 ∧
        d.toNat % 2^52 = 4503599627370495 := by
  let m : Word := 4503599627370495
  change c &&& (b &&& m) &&& d = m ↔ _
  have hmask : c &&& (b &&& m) &&& d = ((b &&& m) &&& (c &&& m)) &&& (d &&& m) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_and]
    cases m.getLsbD i <;> simp [Bool.and_assoc, Bool.and_left_comm]
  rw [hmask, BitVec.toNat_eq]
  have hbound (x : Word) : (x &&& m).toNat ≤ m.toNat := by
    rw [SquareValue.mask52]
    have := Nat.mod_lt x.toNat (by decide : 0 < 2^52)
    change _ ≤ 4503599627370495
    omega
  rw [BitVec.toNat_and, BitVec.toNat_and]
  rw [and_eq_max_iff (Nat.le_trans Nat.and_le_left (hbound b)) (hbound d),
    and_eq_max_iff (hbound b) (hbound c)]
  simp only [m, SquareValue.mask52, and_assoc]
  rfl

private theorem reduction_comparison (a b c d e : Word) (he : e.toNat < 2^48) :
    modulus ≤ foldedValue a b c d e ↔
      4503595332402223 ≤ a.toNat % 2^52 ∧
        (b.toNat % 2^52 = 4503599627370495 ∧ c.toNat % 2^52 = 4503599627370495 ∧
          d.toNat % 2^52 = 4503599627370495) ∧ e.toNat = 281474976710655 := by
  rw [show modulus = 2^256 - 4294968273 by decide +kernel]
  unfold foldedValue
  omega

theorem flagOf_eq (a b c d e : Word) (he : e.toNat < 2^49) :
    flagOf a b c d e = if modulus ≤ foldedValue a b c d e then 1 else 0 := by
  unfold flagOf
  simp only [X86Proofs.orFlags, Option.getD_some, beq_iff_eq, SquareValue.mask52]
  have hupper :
      (c &&& (b &&& 4503599627370495) &&& d ^^^ 4503599627370495 ||| e ^^^ 281474976710655) = 0 ↔
        (b.toNat % 2^52 = 4503599627370495 ∧ c.toNat % 2^52 = 4503599627370495 ∧
          d.toNat % 2^52 = 4503599627370495) ∧ e.toNat = 281474976710655 := by
    change _ = 0#64 ↔ _
    rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff,
      middle_eq_mask, BitVec.toNat_eq (x := e)]
    rfl
  have hlow :
      (¬ a.toNat % 2^52 < 4503595332402222 ∧ ¬ a &&& (4503599627370495 : Word) = 4503595332402222) ↔
        4503595332402223 ≤ a.toNat % 2^52 := by
    rw [BitVec.toNat_eq, SquareValue.mask52]
    change (¬ _ < 4503595332402222 ∧ ¬ _ = 4503595332402222) ↔ _
    omega
  simp only [hlow, hupper]
  have hshift : (BitVec.setWidth 8 (e >>> 48)).toNat = e.toNat / 2^48 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  by_cases ht : e.toNat < 2^48
  · have hzero : BitVec.setWidth 8 (e >>> 48) = 0 :=
      BitVec.eq_of_toNat_eq (by rw [hshift]; change _ = 0; omega)
    simp only [hzero, reduction_comparison a b c d e ht]
    by_cases ha : 4503595332402223 ≤ a.toNat % 2^52 <;>
      by_cases hb : (b.toNat % 2^52 = 4503599627370495 ∧ c.toNat % 2^52 = 4503599627370495 ∧
        d.toNat % 2^52 = 4503599627370495) ∧ e.toNat = 281474976710655 <;>
      simp only [ha, hb, ite_true, ite_false, true_and, false_and] <;> rfl
  · have hone : BitVec.setWidth 8 (e >>> 48) = 1 :=
      BitVec.eq_of_toNat_eq (by rw [hshift]; change _ = 1; omega)
    have hv : modulus ≤ foldedValue a b c d e := by
      rw [show modulus = 2^256 - 4294968273 by decide +kernel, foldedValue]
      omega
    have hmid : ¬ ((b.toNat % 2^52 = 4503599627370495 ∧ c.toNat % 2^52 = 4503599627370495 ∧
        d.toNat % 2^52 = 4503599627370495) ∧ e.toNat = 281474976710655) := fun h => by omega
    rw [hone, ite_eq_left hv, ite_eq_right hmid]
    split <;> rfl

end K256.Proofs.Sec1.Serialize.Normalize
