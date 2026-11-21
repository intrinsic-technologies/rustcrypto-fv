import Sha2.Proofs.FIPS180.Encoding
import Sha2.Proofs.Common.SHA256.Mathematics.BitVecModel

namespace Sha2.Proofs.FIPS180
open Standards.NIST.SHA2
open Sha2.Proofs.Common.SHA256

def scheduleStep (M : Vector (BitVec 32) 16) (W : Vector (BitVec 32) 64) (t : Nat) :
    Vector (BitVec 32) 64 :=
  if ht : t < 64 then
    W.set t (if h16 : t < 16 then M[t]
      else SHA256.σ₁ W[t-2] + W[t-7] + SHA256.σ₀ W[t-15] + W[t-16])
  else W

theorem W_eq_foldl (M : Vector (BitVec 32) 16) :
    SHA256.W M = (List.range 64).foldl (scheduleStep M) (Vector.replicate 64 0) := by
  unfold SHA256.W
  have hbody : (fun t (ht : t ∈ ([:64] : Std.Legacy.Range)) (W : Vector (BitVec 32) 64) =>
      (do
        have htlt : t < 64 := ht.2.1
        if h16 : t < 16 then
          pure (ForInStep.yield (W.set t M[t] (by have := ht.2.1; omega)))
        else
          pure (ForInStep.yield (W.set t
            (SHA256.σ₁ W[t-2] + W[t-7] + SHA256.σ₀ W[t-15] + W[t-16])
            (by have := ht.2.1; omega))) : Id (ForInStep (Vector (BitVec 32) 64)))) =
      (fun t _ W => pure (ForInStep.yield (scheduleStep M W t))) := by
    funext t ht W
    simp only [scheduleStep, ht.2.1, ↓reduceDIte]
    split <;> rfl
  change Id.run (do
    let W ← forIn' ([:64] : Std.Legacy.Range) (Vector.replicate 64 0) _
    pure W) = _
  rw [hbody]
  change Id.run (do
    let W ← forIn ([:64] : Std.Legacy.Range) (Vector.replicate 64 0)
      (fun t W => pure (ForInStep.yield (scheduleStep M W t)))
    pure W) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Id.run]
  rfl

theorem bitVecSmallSigma0_eq (x : BitVec 32) : bitVecSmallSigma0 x = SHA256.σ₀ x := by
  exact (smallSigma0_toBitVec_rotateLeft (UInt32.ofBitVec x)).symm.trans
    (smallSigma0_toBitVec (UInt32.ofBitVec x))

theorem bitVecSmallSigma1_eq (x : BitVec 32) : bitVecSmallSigma1 x = SHA256.σ₁ x := by
  exact (smallSigma1_toBitVec_rotateLeft (UInt32.ofBitVec x)).symm.trans
    (smallSigma1_toBitVec (UInt32.ofBitVec x))

theorem W_eq_schedule (block : Array Bool) (M : Vector (BitVec 32) 16)
    (hM : ∀ i (hi : i < 16), (initialSchedule block)[i]!.toBitVec = M[i]) :
    (SHA256.W M).toArray = (schedule block).map UInt32.toBitVec := by
  have hinv (n : Nat) (hn : n ≤ 64) : ∀ i (hi : i < 64), i < n →
      ((List.range n).foldl (scheduleStep M) (Vector.replicate 64 0))[i] =
        ((schedule block).map UInt32.toBitVec)[i]! := by
    induction n with
    | zero => omega
    | succ n ih =>
      intro i hi hin
      have hn64 : n < 64 := by omega
      have ih := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        scheduleStep, hn64, ↓reduceDIte, Vector.getElem_set]
      by_cases heq : n = i
      · subst i
        simp only [↓reduceIte]
        by_cases hn16 : n < 16
        · simp only [hn16, ↓reduceDIte, map_toBitVec_getElem!,
            schedule_getElem!_initial block n hn16]
          exact (hM n hn16).symm
        · simp only [hn16, ↓reduceDIte]
          rw [ih (n-2) (by omega) (by omega), ih (n-7) (by omega) (by omega),
            ih (n-15) (by omega) (by omega), ih (n-16) (by omega) (by omega),
            schedule_toBitVec_recurrence block n (by omega) hn64,
            bitVecSmallSigma0_eq, bitVecSmallSigma1_eq]
          ac_rfl
      · simp only [heq, ↓reduceIte]
        exact ih i hi (by omega)
  rw [W_eq_foldl]
  apply Array.ext
  · simp [schedule_size]
  · intro i hi hi'
    have hi64 : i < 64 := by simpa only [Vector.size_toArray] using hi
    have h := hinv 64 (by omega) i hi64 hi64
    rw [getElem!_pos _ i hi'] at h
    exact h

end Sha2.Proofs.FIPS180
