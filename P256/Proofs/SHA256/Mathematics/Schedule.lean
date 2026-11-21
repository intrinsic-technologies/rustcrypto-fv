import P256.Proofs.SHA256.Mathematics.Model

set_option autoImplicit false

namespace P256.Proofs.SHA256

theorem initialSchedule_size (block : Array Bool) :
    (initialSchedule block).size = 16 := by
  simp only [initialSchedule, Array.size_map, Array.size_range]

theorem scheduleStep_size (words : Array UInt32) (i : Nat) :
    (scheduleStep words i).size = words.size + 1 := by
  simp only [scheduleStep, Array.size_push]

theorem schedulePrefix_size (block : Array Bool) (n : Nat) :
    (schedulePrefix block n).size = 16 + n := by
  induction n with
  | zero => exact initialSchedule_size block
  | succ n ih =>
      rw [schedulePrefix_succ, scheduleStep_size, ih]
      omega

theorem scheduleStep_getElem!_lt (words : Array UInt32) (i j : Nat)
    (hj : j < words.size) :
    (scheduleStep words i)[j]! = words[j]! := by
  rw [scheduleStep]
  rw [getElem!_pos _ _ (by simpa only [Array.size_push] using Nat.lt_succ_of_lt hj)]
  rw [Array.getElem_push_lt hj]
  exact (getElem!_pos words j hj).symm

theorem schedulePrefix_getElem!_of_le (block : Array Bool) {n m j : Nat}
    (hnm : n ≤ m) (hj : j < 16 + n) :
    (schedulePrefix block m)[j]! = (schedulePrefix block n)[j]! := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      rfl
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · rw [schedulePrefix_succ,
          scheduleStep_getElem!_lt _ _ j (by rw [schedulePrefix_size]; omega), ih hnm']
      · have hn : n = m + 1 := by omega
        subst n
        rfl

theorem schedulePrefix_getElem!_next (block : Array Bool) (n : Nat) :
    (schedulePrefix block (n + 1))[16 + n]! =
      (schedulePrefix block n)[16 + n - 16]! +
        smallSigma0 (schedulePrefix block n)[16 + n - 15]! +
        (schedulePrefix block n)[16 + n - 7]! +
        smallSigma1 (schedulePrefix block n)[16 + n - 2]! := by
  rw [schedulePrefix_succ, scheduleStep]
  rw [getElem!_pos _ _ (by rw [Array.size_push, schedulePrefix_size]; omega)]
  simp only [← schedulePrefix_size block n, Array.getElem_push_eq]

theorem schedulePrefix_getElem!_recurrence (block : Array Bool) (n i : Nat)
    (hi : 16 ≤ i) (hin : i < 16 + n) :
    (schedulePrefix block n)[i]! =
      (schedulePrefix block n)[i - 16]! +
        smallSigma0 (schedulePrefix block n)[i - 15]! +
        (schedulePrefix block n)[i - 7]! +
        smallSigma1 (schedulePrefix block n)[i - 2]! := by
  have hnext := schedulePrefix_getElem!_next block (i - 16)
  have hindex : 16 + (i - 16) = i := by omega
  rw [hindex] at hnext
  rw [schedulePrefix_getElem!_of_le block (n := i - 16 + 1) (m := n) (j := i)
    (by omega) (by omega), hnext]
  rw [schedulePrefix_getElem!_of_le block (n := i - 16) (m := n) (j := i - 16)
      (by omega) (by omega),
    schedulePrefix_getElem!_of_le block (n := i - 16) (m := n) (j := i - 15)
      (by omega) (by omega),
    schedulePrefix_getElem!_of_le block (n := i - 16) (m := n) (j := i - 7)
      (by omega) (by omega),
    schedulePrefix_getElem!_of_le block (n := i - 16) (m := n) (j := i - 2)
      (by omega) (by omega)]

theorem schedule_getElem!_initial (block : Array Bool) (i : Nat) (hi : i < 16) :
    (schedule block)[i]! = (initialSchedule block)[i]! := by
  exact schedulePrefix_getElem!_of_le block (n := 0) (m := 48) (by omega) hi

theorem schedule_getElem!_recurrence (block : Array Bool) (i : Nat)
    (hi : 16 ≤ i) (hi64 : i < 64) :
    (schedule block)[i]! =
      (schedule block)[i - 16]! + smallSigma0 (schedule block)[i - 15]! +
        (schedule block)[i - 7]! + smallSigma1 (schedule block)[i - 2]! := by
  exact schedulePrefix_getElem!_recurrence block 48 i hi hi64

end P256.Proofs.SHA256
