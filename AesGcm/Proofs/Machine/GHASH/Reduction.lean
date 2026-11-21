import Std

namespace AesGcm.Proofs.Machine.GHASH

def truncateBits (n : Nat) (x : BitVec 256) : BitVec 256 := (x.setWidth n).setWidth 256

theorem truncateBits_succ (n : Nat) (x : BitVec 256) :
    truncateBits (n + 1) x = truncateBits n x ^^^
      (if x.getLsbD n then BitVec.twoPow 256 n else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncateBits, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, hi, decide_true,
    Bool.true_and]
  by_cases hin : i = n
  · subst i
    cases x.getLsbD n <;> simp [hi]
  · have he : i < n + 1 ↔ i < n := by omega
    cases x.getLsbD n <;> simp [BitVec.getLsbD_twoPow, he, Ne.symm hin]

def shiftedPrefix (c n : Nat) (x : BitVec 256) : BitVec 256 := truncateBits n x <<< (c - n)

theorem shiftedPrefix_half (c n : Nat) (x : BitVec 256) (hn : n < c) (hc : c ≤ 256) :
    shiftedPrefix c n x >>> (1 : Nat) = truncateBits n x <<< (c - (n + 1)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [shiftedPrefix, truncateBits, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hs : i < c - (n + 1)
  · have h1 : 1 + i < c - n := by omega
    simp [hs, h1]
  · have h1 : ¬1 + i < c - n := by omega
    have he : 1 + i - (c - n) = i - (c - (n + 1)) := by omega
    simp only [hs, h1, he, decide_false, Bool.not_false, Bool.true_and]
    by_cases ht : 1 + i < 256
    · simp [ht]
    · have hsmall : ¬i - (c - (n + 1)) < n := by omega
      simp [ht, hsmall]

theorem shiftedPrefix_succ (c n : Nat) (x : BitVec 256) (hn : n < c) (hc : c ≤ 256) :
    shiftedPrefix c (n + 1) x = (shiftedPrefix c n x >>> (1 : Nat)) ^^^
      (if x.getLsbD n then BitVec.twoPow 256 (c - 1) else 0) := by
  rw [shiftedPrefix_half c n x hn hc]
  simp only [shiftedPrefix, truncateBits_succ, BitVec.shiftLeft_xor_distrib]
  cases h : x.getLsbD n
  · simp
  · simp only [ite_true]
    congr 1
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.twoPow_mul_twoPow_eq]
    congr 1
    omega

def polyvalStep (x : BitVec 256) : BitVec 256 :=
  (x >>> (1 : Nat)) ^^^ (if x.getLsbD 0 then 0xe1000000000000000000000000000000#256 else 0)

def polyvalSteps : Nat → BitVec 256 → BitVec 256
  | 0, x => x
  | n + 1, x => polyvalStep (polyvalSteps n x)

def polyvalPrefix (n : Nat) (x : BitVec 256) : BitVec 256 :=
  (x >>> n) ^^^ shiftedPrefix 128 n x ^^^ shiftedPrefix 127 n x ^^^
    shiftedPrefix 126 n x ^^^ shiftedPrefix 121 n x

theorem polyvalPrefix_low (n : Nat) (x : BitVec 256) (hn : n < 121) :
    (polyvalPrefix n x).getLsbD 0 = x.getLsbD n := by
  have h128 : 0 < 128 - n := by omega
  have h127 : 0 < 127 - n := by omega
  have h126 : 0 < 126 - n := by omega
  have h121 : 0 < 121 - n := by omega
  simp [polyvalPrefix, shiftedPrefix, h128, h127, h126, h121]

theorem ushiftRight_succ {w : Nat} (x : BitVec w) (n : Nat) :
    (x >>> n) >>> (1 : Nat) = x >>> (n + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [Nat.add_assoc]

theorem polyvalPrefix_step (n : Nat) (x : BitVec 256) (hn : n < 121) :
    polyvalStep (polyvalPrefix n x) = polyvalPrefix (n + 1) x := by
  have hk : 0xe1000000000000000000000000000000#256 =
      BitVec.twoPow 256 127 ^^^ BitVec.twoPow 256 126 ^^^
        BitVec.twoPow 256 125 ^^^ BitVec.twoPow 256 120 := by decide +kernel
  rw [polyvalStep, polyvalPrefix_low n x hn]
  simp only [polyvalPrefix, BitVec.ushiftRight_xor_distrib, ushiftRight_succ,
    shiftedPrefix_succ 128 n x (by omega) (by decide),
    shiftedPrefix_succ 127 n x (by omega) (by decide),
    shiftedPrefix_succ 126 n x (by omega) (by decide),
    shiftedPrefix_succ 121 n x hn (by decide)]
  cases h : x.getLsbD n <;> simp only [Bool.false_eq_true, ite_true, ite_false, BitVec.ofNat_eq_ofNat, BitVec.xor_zero, hk] <;> ac_rfl

theorem polyvalSteps_eq_prefix (n : Nat) (x : BitVec 256) (hn : n ≤ 121) :
    polyvalSteps n x = polyvalPrefix n x := by
  induction n with
  | zero => simp [polyvalSteps, polyvalPrefix, shiftedPrefix, truncateBits, BitVec.of_length_zero]
  | succ n ih =>
    rw [polyvalSteps, ih (by omega), polyvalPrefix_step n x (by omega)]

def polyvalReduce64 (x : BitVec 256) : BitVec 256 :=
  (x >>> (64 : Nat)) ^^^ ((x.setWidth 64).setWidth 256 <<< (64 : Nat)) ^^^
    ((x.setWidth 64).setWidth 256 <<< (63 : Nat)) ^^^
    ((x.setWidth 64).setWidth 256 <<< (62 : Nat)) ^^^
    ((x.setWidth 64).setWidth 256 <<< (57 : Nat))

theorem polyvalSteps_64 (x : BitVec 256) : polyvalSteps 64 x = polyvalReduce64 x := by
  rw [polyvalSteps_eq_prefix 64 x (by decide)]
  rfl

theorem polyvalSteps_add (n m : Nat) (x : BitVec 256) :
    polyvalSteps (n + m) x = polyvalSteps m (polyvalSteps n x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change polyvalStep (polyvalSteps (n + m) x) = polyvalStep (polyvalSteps m (polyvalSteps n x))
    rw [ih]

theorem polyvalSteps_128 (x : BitVec 256) :
    polyvalSteps 128 x = polyvalReduce64 (polyvalReduce64 x) := by
  rw [show 128 = 64 + 64 from rfl, polyvalSteps_add, polyvalSteps_64, polyvalSteps_64]

def joinWords (w0 w1 w2 w3 : BitVec 64) : BitVec 256 := w3 ++ w2 ++ w1 ++ w0

theorem joinWords_low (w0 w1 w2 w3 : BitVec 64) :
    (joinWords w0 w1 w2 w3).setWidth 64 = w0 := by
  simp only [joinWords, BitVec.setWidth_append_eq_right]

def reductionCarry (x : BitVec 64) : BitVec 64 :=
  (x <<< (57 : Nat)) ^^^ (x <<< (62 : Nat)) ^^^ (x <<< (63 : Nat))

def reductionHigh (x : BitVec 64) : BitVec 64 :=
  x ^^^ (x >>> (1 : Nat)) ^^^ (x >>> (2 : Nat)) ^^^ (x >>> (7 : Nat))

def polyvalReduceWords (w0 w1 w2 w3 : BitVec 64) : BitVec 64 × BitVec 64 :=
  (w0 ^^^ w2 ^^^ reductionCarry w1 ^^^ (w0 >>> (1 : Nat)) ^^^
    (w0 >>> (2 : Nat)) ^^^ (w0 >>> (7 : Nat)),
   w3 ^^^ reductionHigh (w1 ^^^ reductionCarry w0))

end AesGcm.Proofs.Machine.GHASH
