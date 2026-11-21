import Sha1.Proofs.Compress.Rounds.Algebra
import Sha1.Proofs.Compress.Rounds.Schedule

namespace Sha1.Proofs.Compress.Rounds

open Standards.NIST.SHA1

def workingAfter (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) (n : Nat) :
    WorkingVariables :=
  applySteps (messageSchedule M) ((List.finRange 80).take n) (WorkingVariables.ofHashValue H)

theorem workingAfter_zero (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) :
    workingAfter M H 0 = WorkingVariables.ofHashValue H := by
  simp only [workingAfter, applySteps, List.take_zero, List.foldl_nil]

theorem workingAfter_step (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    workingAfter M H (n + 1) =
      step (Fin.mk n h) (messageSchedule M)[n] (workingAfter M H n) := by
  unfold workingAfter applySteps
  rw [List.take_succ_eq_append_getElem (by simp only [List.length_finRange]; exact h)]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_finRange]
  congr 1 <;> apply Fin.ext <;> rfl

theorem workingAfter_step_b (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    (workingAfter M H (n + 1)).b = (workingAfter M H n).a := by
  rw [workingAfter_step M H n h]
  rfl

theorem workingAfter_step_c (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    (workingAfter M H (n + 1)).c = ROTL 30 (workingAfter M H n).b := by
  rw [workingAfter_step M H n h]
  rfl

theorem workingAfter_step_d (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    (workingAfter M H (n + 1)).d = (workingAfter M H n).c := by
  rw [workingAfter_step M H n h]
  rfl

theorem workingAfter_step_e (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    (workingAfter M H (n + 1)).e = (workingAfter M H n).d := by
  rw [workingAfter_step M H n h]
  rfl

theorem workingAfter_interval (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n m : Nat) :
    workingAfter M H (n + m) =
      applySteps (messageSchedule M) (((List.finRange 80).drop n).take m)
        (workingAfter M H n) := by
  unfold workingAfter applySteps
  rw [List.take_add, List.foldl_append]

theorem workingAfter_prefix_five (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) :
    workingAfter M H 5 =
      applySteps (messageSchedule M) [0, 1, 2, 3, 4] (WorkingVariables.ofHashValue H) := by
  have hlist : ((List.finRange 80).take 5 : List (Fin 80)) = [0, 1, 2, 3, 4] := by decide
  rw [← Nat.zero_add 5, workingAfter_interval M H 0 5, workingAfter_zero, List.drop_zero, hlist]

theorem compress_eq_workingAfter (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) :
    compress H M = intermediateHashValue H (workingAfter M H 80) := by
  rfl

theorem workingAfter_step_a (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (h : n < 80) :
    (workingAfter M H (n + 1)).a =
      ROTL 5 (workingAfter M H n).a +
        f ⟨n, h⟩ (workingAfter M H n).b (workingAfter M H n).c (workingAfter M H n).d +
        K ⟨n, h⟩ + scheduleWord M ⟨n, h⟩ + (workingAfter M H n).e := by
  rw [workingAfter_step M H n h, sha1_step_a_compiler_order]
  rfl

theorem intermediateHashValue_eq_add (H : Vector (BitVec 32) 5) (v : WorkingVariables) :
    intermediateHashValue H v =
      #v[H[0] + v.a, H[1] + v.b, H[2] + v.c, H[3] + v.d, H[4] + v.e] := by
  simp only [intermediateHashValue, BitVec.add_comm]

theorem compress_eq_add_workingAfter (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) :
    compress H M =
      #v[H[0] + (workingAfter M H 80).a, H[1] + (workingAfter M H 80).b,
        H[2] + (workingAfter M H 80).c, H[3] + (workingAfter M H 80).d,
        H[4] + (workingAfter M H 80).e] := by
  rw [compress_eq_workingAfter, intermediateHashValue_eq_add]

theorem workingAfter_eq_of_round_invariant (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) (states : Nat → WorkingVariables)
    (hzero : states 0 = WorkingVariables.ofHashValue H)
    (hstep : ∀ n (hn : n < 80),
      states (n + 1) = step ⟨n, hn⟩ (scheduleWord M ⟨n, hn⟩) (states n))
    (n : Nat) (hn : n ≤ 80) :
    workingAfter M H n = states n := by
  induction n with
  | zero => rw [hzero, workingAfter_zero]
  | succ n ih =>
    have hn' : n < 80 := by omega
    rw [hstep n hn', workingAfter_step M H n hn', ih (by omega)]
    rfl

theorem compress_eq_of_round_invariant (M : Vector (BitVec 32) 16)
    (H : Vector (BitVec 32) 5) (states : Nat → WorkingVariables)
    (hzero : states 0 = WorkingVariables.ofHashValue H)
    (hstep : ∀ n (hn : n < 80),
      states (n + 1) = step ⟨n, hn⟩ (scheduleWord M ⟨n, hn⟩) (states n)) :
    compress H M = intermediateHashValue H (states 80) := by
  rw [compress_eq_workingAfter,
    workingAfter_eq_of_round_invariant M H states hzero hstep 80 (by omega)]

end Sha1.Proofs.Compress.Rounds
