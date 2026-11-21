import Sha1.Proofs.MemoryRoutines.Contracts

namespace Sha1.Proofs.MemoryRoutines

open X86Proofs

def alignmentPrefix (destination : BitVec 64) (length : Nat) : Nat :=
  min length (((-destination.setWidth 32) &&& (7 : BitVec 32)).toNat)

theorem mask7_toNat (x : BitVec n) (h : 3 ≤ n) :
    (x &&& (7 : BitVec n)).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and]
  have h7 : (7 : BitVec n).toNat = 7 := by
    change 7 % 2 ^ n = 7
    apply Nat.mod_eq_of_lt
    have := Nat.pow_le_pow_right (by decide : 0 < 2) h
    omega
  rw [h7]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

theorem alignmentPrefix_le_length (destination : BitVec 64) (length : Nat) :
    alignmentPrefix destination length ≤ length := Nat.min_le_left _ _

theorem alignmentPrefix_lt_eight (destination : BitVec 64) (length : Nat) :
    alignmentPrefix destination length < 8 := by
  unfold alignmentPrefix
  rw [mask7_toNat _ (by decide)]
  omega

theorem alignmentPrefix_aligned (destination : BitVec 64) (length : Nat)
    (h : alignmentPrefix destination length < length) :
    (destination.toNat + alignmentPrefix destination length) % 8 = 0 := by
  unfold alignmentPrefix at *
  rw [mask7_toNat _ (by decide)] at *
  have hmin : min length ((-destination.setWidth 32).toNat % 8) =
      (-destination.setWidth 32).toNat % 8 := by omega
  rw [hmin, BitVec.toNat_neg, BitVec.toNat_setWidth]
  omega

theorem remaining_split (length head : Nat) (h : head ≤ length) :
    head + 8 * ((length - head) / 8) + (length - head) % 8 = length := by
  omega

theorem select_min_toNat (x y : BitVec 64) :
    (if decide (x.toNat < y.toNat) then x else y) =
      BitVec.ofNat 64 (min x.toNat y.toNat) := by
  by_cases h : x.toNat < y.toNat
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp [h, Nat.min_eq_right (Nat.le_of_not_lt h)]

end Sha1.Proofs.MemoryRoutines
