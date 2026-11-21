import P256.Proofs.Common.Instructions.Carry.Operation

set_option autoImplicit false

namespace P256.Proofs.Common.Instructions.Carry

theorem adcSpec_toNat {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (adcSpec x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 2^n := by
  simp only [adcSpec, ← Int.natCast_add, BitVec.ofInt_natCast, BitVec.toNat_ofNat]

theorem adcSpec_cf {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (adcSpec x y c).2.CF = decide (2^n ≤ x.toNat + y.toNat + c.toNat) := by
  change decide (((adcSpec x y c).1.toNat : Int) ≠
    (x.toNat : Int) + y.toNat + c.toNat) = _
  rw [adcSpec_toNat]
  congr 1
  apply propext
  have hmod := Nat.mod_lt (x.toNat + y.toNat + c.toNat) (Nat.two_pow_pos n)
  by_cases h : x.toNat + y.toNat + c.toNat < 2^n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · omega

theorem sbbSpec_cf {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (sbbSpec x y c).2.CF = decide (x.toNat < y.toNat + c.toNat) := by
  change decide (((BitVec.ofInt n ((x.toNat : Int) - (y.toNat + c.toNat))).toNat : Int) ≠
    (x.toNat : Int) - (y.toNat + c.toNat)) = _
  rw [BitVec.toNat_ofInt]
  congr 1
  apply propext
  have hm : (0 : Int) < (2^n : Nat) := by exact_mod_cast Nat.two_pow_pos n
  have hnonneg := Int.emod_nonneg ((x.toNat : Int) - (y.toNat + c.toNat)) (by omega : ((2^n : Nat) : Int) ≠ 0)
  rw [Int.toNat_of_nonneg hnonneg]
  have hx := x.isLt
  by_cases h : y.toNat + c.toNat ≤ x.toNat
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · omega

theorem mod_add_carry {a m : Nat} (h : a < 2 * m) :
    a % m + m * (decide (m ≤ a)).toNat = a := by
  by_cases hc : m ≤ a
  · simp only [hc, decide_true, Bool.toNat_true, Nat.mul_one]
    rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp [Nat.mod_eq_of_lt (by omega : a < m), hc]

theorem adcSpec_toNat_add_carry {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (adcSpec x y c).1.toNat + 2^n * (adcSpec x y c).2.CF.toNat =
      x.toNat + y.toNat + c.toNat := by
  rw [adcSpec_toNat, adcSpec_cf]
  apply mod_add_carry
  have hx := x.isLt
  have hy := y.isLt
  have hc := c.isLt
  simp only [Nat.pow_one] at hc
  omega

theorem addSpec_toNat_add_carry {n : Nat} (x y : BitVec n) :
    (X86Proofs.addSpec x y).1.toNat + 2^n * (X86Proofs.addSpec x y).2.CF.toNat =
      x.toNat + y.toNat := by
  simp only [X86Proofs.addSpec, BitVec.toNat_add, ne_eq,
    Nat.mod_eq_iff_lt (Nat.ne_of_gt (Nat.two_pow_pos n)), Nat.not_lt]
  apply mod_add_carry
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem sbbSpec_toNat_add_borrow {n : Nat} (x y : BitVec n) (c : BitVec 1) :
    (sbbSpec x y c).1.toNat + y.toNat + c.toNat =
      x.toNat + 2^n * (sbbSpec x y c).2.CF.toNat := by
  rw [sbbSpec_cf]
  change (BitVec.ofInt n ((x.toNat : Int) - (y.toNat + c.toNat))).toNat + _ + _ = _
  rw [BitVec.toNat_ofInt]
  have hx := x.isLt
  have hy := y.isLt
  have hc := c.isLt
  simp only [Nat.pow_one] at hc
  by_cases hb : x.toNat < y.toNat + c.toNat
  · simp only [hb, decide_true, Bool.toNat_true, Nat.mul_one]
    rw [← Int.add_emod_right ((x.toNat : Int) - (y.toNat + c.toNat)) ((2^n : Nat) : Int),
      Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · simp only [hb, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

theorem subSpec_toNat_add_borrow {n : Nat} (x y : BitVec n) :
    (X86Proofs.subSpec x y).1.toNat + y.toNat =
      x.toNat + 2^n * (X86Proofs.subSpec x y).2.CF.toNat := by
  have h := sbbSpec_toNat_add_borrow x y 0
  simpa [sbbSpec_result, sbbSpec_cf, X86Proofs.subSpec] using h

end P256.Proofs.Common.Instructions.Carry
