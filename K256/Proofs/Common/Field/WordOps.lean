import X86Proofs.Instructions.Mul.Operation
import X86Proofs.Instructions.Add.Operation
import X86Proofs.Instructions.Shld.Operation

namespace K256.Proofs.Common.Field
open X86Proofs

theorem mulResult_toNat_add (a b : BitVec 64) :
    (mulResult a b).1.toNat + 2^64 * (mulResult a b).2.toNat = a.toNat * b.toNat := by
  have hlt : a.toNat * b.toNat < 2 ^ 128 := by
    have ha := a.isLt
    have hb := b.isLt
    calc a.toNat * b.toNat < 2^64 * 2^64 := Nat.mul_lt_mul'' ha hb
      _ = 2^128 := by rw [← Nat.pow_add]
  simp only [mulResult, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  generalize a.toNat * b.toNat = x at *
  omega

theorem addSpec_fst_toNat (a b : BitVec 64) :
    (addSpec a b).1.toNat = (a.toNat + b.toNat) % 2^64 := by
  simp only [addSpec, BitVec.toNat_add]

theorem addSpec_CF_toNat (a b : BitVec 64) :
    (addSpec a b).2.CF.toNat = (a.toNat + b.toNat) / 2^64 := by
  have h1 := addSpec_fst_toNat a b
  have ha := a.isLt
  have hb := b.isLt
  show (decide ((addSpec a b).1.toNat ≠ a.toNat + b.toNat)).toNat = _
  rw [h1]
  have hn : a.toNat + b.toNat < 2 * 2^64 := by omega
  generalize a.toNat + b.toNat = n at *
  by_cases h : n < 2^64
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    simp
  · have hne : n % 2^64 ≠ n := by omega
    simp only [ne_eq, hne, not_false_eq_true, decide_true, Bool.toNat_true]
    omega

theorem shldResult_toNat (k : Nat) (a b : BitVec 64) (hk0 : 0 < k) (hk : k < 64) :
    (shldResult k a b).toNat = (a.toNat * 2^k + b.toNat / 2^(64-k)) % 2^64 := by
  rw [← X86Proofs.shldResult_eq_extract (m := 64 + 64) rfl k (by omega) a b]
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hb := b.isLt
  have hlt : a.toNat * 2^64 + b.toNat < 2^(64+64) := by
    have : a.toNat * 2^64 + b.toNat < (a.toNat + 1) * 2^64 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc _ < (a.toNat + 1) * 2^64 := this
      _ ≤ 2^64 * 2^64 := Nat.mul_le_mul_right _ ha
      _ = 2^(64+64) := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt hlt]
  have e : a.toNat * 2^64 = a.toNat * 2^k * 2^(64-k) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, show k + (64 - k) = 64 by omega]
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]

def pairNat (lo hi : BitVec 64) : Nat := lo.toNat + 2^64 * hi.toNat

theorem shldResult_pairNat (k : Nat) (hi lo : BitVec 64) (hk0 : 0 < k) (hk : k < 64) :
    (shldResult k hi lo).toNat = pairNat lo hi / 2^(64-k) % 2^64 := by
  rw [shldResult_toNat k hi lo hk0 hk]
  unfold pairNat
  have e : 2^64 * hi.toNat = hi.toNat * 2^k * 2^(64-k) := by
    rw [Nat.mul_comm, Nat.mul_assoc, ← Nat.pow_add, show k + (64 - k) = 64 by omega]
  rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]

end K256.Proofs.Common.Field
