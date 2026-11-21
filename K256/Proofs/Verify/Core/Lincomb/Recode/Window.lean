import K256.Proofs.Verify.Naf.Recoding

namespace K256.Proofs.Verify.Core.Lincomb.Recode

private theorem nextWindow (lo hi : BitVec 64) (i : Nat) (bound : i < 64) :
    (((lo >>> i) ||| (hi <<< (64 - i))).setWidth 5).toNat =
      (hi ++ lo).toNat / 2^i % 32 := by
  have result : ((lo >>> i) ||| (hi <<< (64 - i))).setWidth 5 = ((hi ++ lo) >>> i).setWidth 5 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
    by_cases inside : i+j < 64
    · have lower : j < 64 - i := by omega
      simp [lower, inside]
    · have lower : ¬j < 64 - i := by omega
      have off : j - (64-i) = i+j-64 := by omega
      have zero := BitVec.getLsbD_of_ge (x := lo) (i := i+j) (by omega)
      simp [inside, lower, off, zero, show j < 64 by omega]
  rw [result, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem currentWindow (lo hi : BitVec 64) (i : Nat) (bound : i < 64) :
    (if i + 5 < 64 then ((lo >>> i).setWidth 5).toNat
     else (((lo >>> i) ||| (hi <<< (64-i))).setWidth 5).toNat) =
      (hi ++ lo).toNat / 2^i % 32 := by
  rw [← nextWindow lo hi i bound]
  split
  · rename_i small
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have below : j < 64-i := by omega
    simp [hj, below]
  · rfl

theorem remainingWindow (lo hi : BitVec 64) (i : Nat) (lower : 64 ≤ i) (bound : i < 128) :
    (if i % 64 + 5 < 64 then ((hi >>> (i % 64)).setWidth 5).toNat
     else (((hi >>> (i % 64)) ||| ((0 : BitVec 64) <<< (64-i%64))).setWidth 5).toNat) =
      (hi ++ lo).toNat / 2^i % 32 := by
  have irep : i = 64 + i%64 := by omega
  have upper : (hi ++ lo).toNat / 2^64 = hi.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
    omega
  have shift : (hi ++ lo).toNat / 2^i = hi.toNat / 2^(i%64) := by
    calc
      (hi ++ lo).toNat / 2^i = (hi ++ lo).toNat / 2^(64+i%64) :=
        congrArg (fun k => (hi ++ lo).toNat / 2^k) irep
      _ = hi.toNat / 2^(i%64) := by rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, upper]
  rw [shift]
  have concat : ((0 : BitVec 64) ++ hi).toNat = hi.toNat := by
    rw [BitVec.toNat_append]
    simp
  simpa only [concat] using currentWindow hi 0 (i%64) (by omega)

theorem shiftedSuffix {n i j : Nat} :
    (n / 2^i) / 2^j = n / 2^(i+j) := by
  rw [Nat.pow_add, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem recodeEvenStep {n i c : Nat} (bit : i < 128) (even : (n / 2^i % 32 + c) % 2 = 0) :
    Naf.recode (128-i+1) (128-i) (n/2^i) c =
      [0] ++ Naf.recode (128-(i+1)+1) (128-(i+1)) (n/2^(i+1)) c := by
  rw [Naf.recode_even (by omega) even, show 128-i-1 = 128-(i+1) by omega,
    show 128-i = 128-(i+1)+1 by omega]
  rw [show (n/2^i)/2 = n/2^(i+1) from shiftedSuffix (j := 1)]
  rfl

theorem recodeOddStep {n i c : Nat} (input : n < 2^128) (bit : i < 128) (carry : c ≤ 1)
    (odd : (n / 2^i % 32 + c) % 2 = 1) :
    let window := n / 2^i % 32 + c
    let skip := Naf.skip (128-i) window
    1 ≤ skip ∧ skip ≤ 128-i ∧ skip ≤ 5 ∧
      Naf.recode (128-i+1) (128-i) (n/2^i) c =
        ([Naf.digit window] ++ List.replicate (skip-1) 0) ++
          Naf.recode (128-(i+skip)+1) (128-(i+skip)) (n/2^(i+skip)) (Naf.carry window) := by
  dsimp only
  have remaining := Naf.shifted_bound input (by omega : i ≤ 128)
  obtain ⟨pos, fit, max⟩ := Naf.odd_skip_bounds (by omega) remaining carry odd
  refine ⟨pos, fit, max, ?_⟩
  rw [Naf.recode_odd (by omega) remaining carry odd, shiftedSuffix, Nat.sub_sub]
  rfl

theorem windowWord (lo hi : BitVec 64) (i c : Nat) (hiBound : i < 128) (hc : c ≤ 1) :
    let s := i % 64
    let x := if i < 64 then lo else hi
    let y := if i < 64 then hi else 0
    let shifted := if s + 5 < 64 then x >>> s else (y <<< (64-s)) ||| (x >>> s)
    (shifted &&& (31 : BitVec 64)) + BitVec.ofNat 64 c =
      BitVec.ofNat 64 ((hi ++ lo).toNat / 2^i % 32 + c) := by
  dsimp only
  have masked (x : BitVec 64) : (x &&& (31 : BitVec 64)).toNat = (x.setWidth 5).toNat := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth]
    exact Nat.and_two_pow_sub_one_eq_mod _ 5
  have shiftedNat :
      ((if i % 64 + 5 < 64 then (if i < 64 then lo else hi) >>> (i % 64)
        else ((if i < 64 then hi else 0) <<< (64 - i % 64)) |||
          ((if i < 64 then lo else hi) >>> (i % 64))).setWidth 5).toNat =
        (hi ++ lo).toNat / 2^i % 32 := by
    by_cases small : i < 64
    · simp only [small, ite_true, Nat.mod_eq_of_lt small, BitVec.or_comm
        (hi <<< (64-i)) (lo >>> i)]
      simpa only [apply_ite] using currentWindow lo hi i small
    · simp only [small, ite_false, BitVec.or_comm ((0 : BitVec 64) <<< (64 - i % 64)) (hi >>> (i % 64))]
      simpa only [apply_ite] using remainingWindow lo hi i (by omega) hiBound
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, masked, shiftedNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := c) (by omega)]

theorem negativeDigit (w : Nat) :
    BitVec.ofNat 8 w - BitVec.ofNat 8 (if 16 ≤ w then 32 else 0) =
      BitVec.ofInt 8 (Naf.digit w) := by
  unfold Naf.digit Naf.carry
  by_cases pos : w < 16
  · simp only [pos, Nat.not_le_of_lt pos, ite_true, ite_false]
    simp
  · simp only [pos, Nat.le_of_not_gt pos, ite_true, ite_false]
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]
    rfl

end K256.Proofs.Verify.Core.Lincomb.Recode
