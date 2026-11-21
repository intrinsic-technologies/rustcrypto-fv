import P256.Proofs.Verifying.Combination.Naf.Iterator.Interface
import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.Shift.Values

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open Iterator

theorem low_five_mask (x : BitVec 64) :
    x &&& 31 = BitVec.ofNat 64 (x.toNat % 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = x.toNat % 32 % 2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem low_five_join (x y : BitVec 64) {j : Nat} (hj : j + 5 ≤ 64) :
    ((x >>> j) ||| (y <<< (64-j))) &&& 31 = (x >>> j) &&& 31 := by
  have mask : (31 : BitVec 64) = (BitVec.allOnes 5).setWidth 64 := by decide +kernel
  rw [mask]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases small : i < 5
  · have low : i < 64-j := by omega
    simp [BitVec.getLsbD_shiftLeft, low]
  · simp [small]

set_option exponentiation.threshold 320 in
theorem joined_window {n k j : Nat} (hn : n < 2^256) (hj : j ≤ 64) :
    ((word n k >>> j) ||| (word n (k+1) <<< (64-j))) &&& 31 =
      BitVec.ofNat 64 (n / 2^(64*k+j) % 32) := by
  have large : n < 2^320 := by omega
  have joined := P256.Proofs.Field.Inverse.SafeGcd.Core.Shift.shift_limb
    (j := k) large hj
  rw [word, word, joined, low_five_mask]
  simp only [BitVec.toNat_ofNat, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [Nat.add_comm j (64*k), Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2^64)]

theorem window_within_word {n k j : Nat} (hn : n < 2^256) (hj : j+5 ≤ 64) :
    (word n k >>> j) &&& 31 = BitVec.ofNat 64 (n / 2^(64*k+j) % 32) := by
  rw [← low_five_join (word n k) (word n (k+1)) hj]
  exact joined_window hn (by omega)

theorem window_at_index {n i : Nat} (hn : n < 2^256) :
    (if i % 64 + 5 < 64 then (word n (i/64) >>> (i%64))
      else (word n (i/64) >>> (i%64)) ||| (word n (i/64+1) <<< (64-i%64))) &&& 31 =
        BitVec.ofNat 64 (n / 2^i % 32) := by
  have split_index : 64 * (i/64) + i%64 = i := by omega
  split
  · simpa only [split_index] using window_within_word hn (k := i/64) (j := i%64) (by omega)
  · simpa only [split_index] using joined_window hn (k := i/64) (j := i%64) (by omega)

end P256.Proofs.Verifying.Combination.Naf.Machine
