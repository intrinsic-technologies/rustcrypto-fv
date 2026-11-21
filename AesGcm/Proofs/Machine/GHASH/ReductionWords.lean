import AesGcm.Proofs.Machine.GHASH.Reduction

namespace AesGcm.Proofs.Machine.GHASH

theorem polyvalReduce64_word0 (w0 w1 w2 w3 : BitVec 64) (i : Nat) (hi : i < 64) :
    (polyvalReduce64 (joinWords w0 w1 w2 w3)).getLsbD (0 + i) = (w1 ^^^ reductionCarry w0).getLsbD i := by
  simp only [polyvalReduce64, joinWords_low]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
      i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨
      i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨
      i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [joinWords, reductionCarry,
      BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append] <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem polyvalReduce64_word1 (w0 w1 w2 w3 : BitVec 64) (i : Nat) (hi : i < 64) :
    (polyvalReduce64 (joinWords w0 w1 w2 w3)).getLsbD (64 + i) =
      (w2 ^^^ reductionHigh w0).getLsbD i := by
  simp only [polyvalReduce64, reductionHigh, joinWords,
    BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  grind


theorem polyvalReduce64_word2 (w0 w1 w2 w3 : BitVec 64) (i : Nat) (hi : i < 64) :
    (polyvalReduce64 (joinWords w0 w1 w2 w3)).getLsbD (128 + i) = w3.getLsbD i := by
  simp only [polyvalReduce64, joinWords_low]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
      i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨
      i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨
      i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [joinWords,
      BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append] <;>
    simp

theorem polyvalReduce64_word3 (w0 w1 w2 w3 : BitVec 64) (i : Nat) (hi : i < 64) :
    (polyvalReduce64 (joinWords w0 w1 w2 w3)).getLsbD (192 + i) = false := by
  simp only [polyvalReduce64, joinWords_low]
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
      i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨
      i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨
      i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨
      i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [joinWords,
      BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_append] <;>
    simp

theorem polyvalReduce64_words (w0 w1 w2 w3 : BitVec 64) :
    polyvalReduce64 (joinWords w0 w1 w2 w3) =
      joinWords (w1 ^^^ reductionCarry w0) (w2 ^^^ reductionHigh w0) w3 (0#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : i < 64
  · have hw := polyvalReduce64_word0 w0 w1 w2 w3 i h0
    simp only [Nat.zero_add] at hw
    rw [hw]
    simp only [joinWords, BitVec.getLsbD_append]
    simp [h0]
  · by_cases h1 : i < 128
    · have hj : i - 64 < 64 := by omega
      have he : i = 64 + (i - 64) := by omega
      conv => lhs; rw [he]
      rw [polyvalReduce64_word1 w0 w1 w2 w3 (i - 64) hj]
      simp only [joinWords, BitVec.getLsbD_append]
      simp [h0, hj]
    · by_cases h2 : i < 192
      · have hj : i - 128 < 64 := by omega
        have he : i = 128 + (i - 128) := by omega
        conv => lhs; rw [he]
        rw [polyvalReduce64_word2 w0 w1 w2 w3 (i - 128) hj]
        simp only [joinWords, BitVec.getLsbD_append]
        simp [h0, show ¬i - 64 < 64 by omega,
          show i - 64 - 64 = i - 128 by omega, hj]
      · have hj : i - 192 < 64 := by omega
        have he : i = 192 + (i - 192) := by omega
        conv => lhs; rw [he]
        rw [polyvalReduce64_word3 w0 w1 w2 w3 (i - 192) hj]
        simp only [joinWords, BitVec.getLsbD_append]
        simp [h0, show ¬i - 64 < 64 by omega,
          show ¬i - 64 - 64 < 64 by omega]

theorem reductionCarry_xor (x y : BitVec 64) :
    reductionCarry (x ^^^ y) = reductionCarry x ^^^ reductionCarry y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [reductionCarry, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor,
    Bool.and_xor_distrib_left]
  simp [Bool.xor_left_comm]

theorem reductionCarry_twice (x : BitVec 64) : reductionCarry (reductionCarry x) = 0#64 := by
  simp [reductionCarry, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]


theorem polyvalSteps_128_words (w0 w1 w2 w3 : BitVec 64) :
    polyvalSteps 128 (joinWords w0 w1 w2 w3) =
      joinWords (polyvalReduceWords w0 w1 w2 w3).1 (polyvalReduceWords w0 w1 w2 w3).2 0 0 := by
  rw [polyvalSteps_128, polyvalReduce64_words, polyvalReduce64_words,
    reductionCarry_xor, reductionCarry_twice, BitVec.xor_zero]
  simp only [polyvalReduceWords, reductionHigh]
  congr 1
  ac_rfl

end AesGcm.Proofs.Machine.GHASH
