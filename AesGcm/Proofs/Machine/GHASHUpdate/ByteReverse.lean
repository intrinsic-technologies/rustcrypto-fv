import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.GHASHUpdate
open X86Proofs

theorem word64_eq_of_bytes (a b : BitVec 64)
    (h : ∀ i : Fin 8, a.extractLsb' (8*i.val) 8 = b.extractLsb' (8*i.val) 8) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have he := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8)) (h ⟨k / 8, by omega⟩)
  simp only [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega,
    decide_true, Bool.true_and, show 8*(k/8)+k%8 = k by omega] at he
  exact he

theorem bswap64_extract_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (bswapSpec x).extractLsb' (8*i) 8 = x.extractLsb' (8*(7-i)) 8 := by
  have hh := lane_ofLanes (n := 64) (w := 8) (fun j => lane 8 x (7-j)) i hi
  unfold bswapSpec
  simp only [Nat.reduceDiv, Nat.reduceSub]
  rw [Nat.mul_comm 8 i, Nat.mul_comm 8 (7-i)]
  exact hh

theorem rotate16_extract_low (x : BitVec 16) :
    (x.rotateLeft 8).extractLsb' 0 8 = x.extractLsb' 8 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, Nat.reduceMod,
    Nat.zero_add, hi, decide_true, Bool.true_and, ite_true, Nat.reduceSub]

theorem rotate16_extract_high (x : BitVec 16) :
    (x.rotateLeft 8).extractLsb' 8 8 = x.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateLeft, Nat.reduceMod,
    hi, decide_true, Bool.true_and, show ¬8+i<8 by omega, ite_false,
    show 8+i<16 by omega, Nat.add_sub_cancel_left, Nat.zero_add]

theorem bswap64_eq_bytes (x : BitVec 64) :
    bswapSpec x = x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++
      x.extractLsb' 24 8 ++ x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++
      x.extractLsb' 48 8 ++ x.extractLsb' 56 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bswapSpec, getLsbD_ofLanes, lane, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', Nat.reduceDiv, Nat.reduceMul, hi, ite_true]
  have hc : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases hc with h | h | h | h | h | h | h | h
  · simp only [show (i < 8) by omega,
      show i % 8 < 8 by omega, decide_true, ite_true, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show (i - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show (i - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 8 - 8 < 8) by omega,
      show (i - 8 - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 < 8) by omega,
      show (i - 8 - 8 - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 < 8) by omega,
      show (i - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show (i - 8 - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_true, ite_false, Bool.true_and]
    congr 1
    omega
  · simp only [show ¬ (i < 8) by omega,
      show ¬ (i - 8 < 8) by omega,
      show ¬ (i - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show ¬ (i - 8 - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show (i - 8 - 8 - 8 - 8 - 8 - 8 - 8 < 8) by omega,
      show i % 8 < 8 by omega, decide_true, decide_false, ite_false, Bool.true_and]
    congr 1
    omega

end AesGcm.Proofs.Machine.GHASHUpdate
