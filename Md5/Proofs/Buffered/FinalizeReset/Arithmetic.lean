import Md5.Proofs.RFC1321.Padding

namespace Md5.Proofs.Buffered.FinalizeReset

theorem bitLength (n : Nat) :
    (BitVec.ofNat 64 (n / 64) <<< 9) |||
      (BitVec.ofNat 64 (n % 64) <<< 3) = BitVec.ofNat 64 (n * 8) := by
  have shift (v k : Nat) : BitVec.ofNat 64 v <<< k = BitVec.ofNat 64 (v <<< k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_mul_mod]
  simp only [shift, ← BitVec.ofNat_or]
  congr 1
  rw [← Nat.shiftLeft_add_eq_or_of_lt
    (by simp only [Nat.shiftLeft_eq, Nat.reducePow]; omega : (n % 64) <<< 3 < 2^9)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  exact (RFC1321.bitLength_eq_blocks_remainder n).symm

set_option maxRecDepth 2048 in
theorem remainingBytes (n : Nat) (hn : n < 64) :
    BitVec.ofNat 64 n ^^^ 63 = BitVec.ofNat 64 (63 - n) := by
  have h : ∀ i : Fin 64, BitVec.ofNat 64 i.val ^^^ 63 =
      BitVec.ofNat 64 (63 - i.val) := by decide +kernel
  exact h ⟨n, hn⟩

theorem remainingBytes_gt_seven (n : Nat) (hn : n < 64) :
    7 < (BitVec.ofNat 64 n ^^^ 63).toNat ↔ n < 56 := by
  rw [remainingBytes n hn]
  simp only [BitVec.toNat_ofNat]
  omega

end Md5.Proofs.Buffered.FinalizeReset
