import P256.Proofs.SHA256.Mathematics.Schedule
import P256.Proofs.SHA256.Mathematics.Model

set_option autoImplicit false

namespace P256.Proofs.SHA256

open Standards.NIST.SHA2 in
private def standardScheduleStep (M : Vector (BitVec 32) 16)
    (words : Vector (BitVec 32) 64) (t : Nat) : Vector (BitVec 32) 64 :=
  if ht : t < 64 then
    words.set t (if t < 16 then M[t]! else
      SHA256.σ₁ words[t - 2]! + words[t - 7]! + SHA256.σ₀ words[t - 15]! + words[t - 16]!) ht
  else words

private theorem standardSchedule_eq_foldl (M : Vector (BitVec 32) 16) :
    Standards.NIST.SHA2.SHA256.W M =
      (List.range 64).foldl (standardScheduleStep M) (Vector.replicate 64 0) := by
  unfold Standards.NIST.SHA2.SHA256.W
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', Id.run]
  change (forIn' (List.range 64) (Vector.replicate 64 0) _) = _
  apply Eq.trans (b := (forIn' (List.range 64) (Vector.replicate 64 0)
    (fun t _ words => pure (ForInStep.yield (standardScheduleStep M words t))) :
      Id (Vector (BitVec 32) 64)))
  · apply List.forIn'_congr rfl rfl
    intro t ht words
    have ht64 : t < 64 := List.mem_range.mp ht
    by_cases ht16 : t < 16
    · simp [ht16, standardScheduleStep, getElem!_pos, ht64]
    · simp [ht16, standardScheduleStep, getElem!_pos, ht64,
        show t - 2 < 64 by omega, show t - 7 < 64 by omega,
        show t - 15 < 64 by omega, show t - 16 < 64 by omega]
  · simp only [List.forIn'_pure_yield_eq_foldl, List.foldl_attach]
    rfl

private theorem smallSigma0_toStandard (x : UInt32) :
    (smallSigma0 x).toBitVec = Standards.NIST.SHA2.SHA256.σ₀ x.toBitVec := by
  rfl

private theorem smallSigma1_toStandard (x : UInt32) :
    (smallSigma1 x).toBitVec = Standards.NIST.SHA2.SHA256.σ₁ x.toBitVec := by
  rfl

private def standardBlock (block : Array Bool) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun j : Fin 16 => BitVec.ofNat 32
    (Reference.bitsToNat (block.extract (32 * j.val) (32 * (j.val + 1))))

private theorem schedule_initial_toStandard (block : Array Bool) (i : Nat) (hi : i < 16) :
    (schedule block)[i]!.toBitVec = (standardBlock block)[i] := by
  rw [schedule_getElem!_initial block i hi]
  rw [getElem!_pos (initialSchedule block) i (by rw [initialSchedule_size]; exact hi)]
  simp only [initialSchedule, Array.getElem_map, Array.getElem_range,
    standardBlock, Vector.getElem_ofFn]
  rfl

private theorem standardScheduleStep_agrees (block : Array Bool)
    (words : Vector (BitVec 32) 64) (n : Nat) (hn64 : n < 64)
    (ih : ∀ (j : Nat) (hj : j < n), words[j]'(by omega) = (schedule block)[j]!.toBitVec)
    (i : Nat) (hi : i < n + 1) :
    (standardScheduleStep (standardBlock block) words n)[i]'(by omega) =
      (schedule block)[i]!.toBitVec := by
  by_cases hin : i = n
  · subst i
    simp only [standardScheduleStep, dite_eq_left hn64, Vector.getElem_set_self]
    by_cases hn16 : n < 16
    · rw [ite_eq_left hn16, getElem!_pos (standardBlock block) n hn16]
      exact (schedule_initial_toStandard block n hn16).symm
    · rw [ite_eq_right hn16, schedule_getElem!_recurrence block n (by omega) hn64]
      rw [getElem!_pos words (n - 2) (by omega),
        getElem!_pos words (n - 7) (by omega),
        getElem!_pos words (n - 15) (by omega),
        getElem!_pos words (n - 16) (by omega)]
      rw [ih (n - 2) (by omega), ih (n - 7) (by omega),
        ih (n - 15) (by omega), ih (n - 16) (by omega)]
      generalize (schedule block)[n - 16]! = a
      generalize (schedule block)[n - 15]! = b
      generalize (schedule block)[n - 7]! = c
      generalize (schedule block)[n - 2]! = d
      simp only [UInt32.toBitVec_add, smallSigma0_toStandard, smallSigma1_toStandard]
      ac_rfl
  · simp only [standardScheduleStep, dite_eq_left hn64, Vector.getElem_set,
      ite_eq_right (Ne.symm hin)]
    exact ih i (by omega)

private theorem standardSchedule_foldl_getElem (block : Array Bool) (n : Nat)
    (hn : n ≤ 64) (i : Nat) (hi : i < n) :
    ((List.range n).foldl (standardScheduleStep (standardBlock block))
      (Vector.replicate 64 0))[i]'(by omega) = (schedule block)[i]!.toBitVec := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact standardScheduleStep_agrees block _ n (by omega) (ih (by omega)) i hi

theorem schedule_toStandard (block : Array Bool) (i : Fin 64) :
    (schedule block)[i.val]!.toBitVec =
      (Standards.NIST.SHA2.SHA256.W (Vector.ofFn fun j : Fin 16 => BitVec.ofNat 32
        (Reference.bitsToNat
          (block.extract (32 * j.val) (32 * (j.val + 1))))))[i.val] := by
  rw [standardSchedule_eq_foldl]
  exact (standardSchedule_foldl_getElem block 64 (by omega) i.val i.isLt).symm

end P256.Proofs.SHA256
