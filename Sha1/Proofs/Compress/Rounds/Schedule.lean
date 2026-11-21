import Standards.NIST.SHA1.Computation

namespace Sha1.Proofs.Compress.Rounds

open Standards.NIST.SHA1

def scheduleWord (M : Vector (BitVec 32) 16) (t : Fin 80) : BitVec 32 :=
  (messageSchedule M)[t]

def scheduleUpdate (M : Vector (BitVec 32) 16) (W : Vector (BitVec 32) 80)
    (t : Fin 80) : Vector (BitVec 32) 80 :=
  if h : t.val < 16 then
    W.set t.val (M[t.val]'(by omega)) (by omega)
  else
    W.set t.val (ROTL 1 (W[t.val - 3]'(by omega) ^^^ W[t.val - 8]'(by omega) ^^^
      W[t.val - 14]'(by omega) ^^^ W[t.val - 16]'(by omega))) (by omega)

theorem scheduleUpdate_get_ne (M : Vector (BitVec 32) 16) (W : Vector (BitVec 32) 80)
    (t : Fin 80) (i : Nat) (hi : i < 80) (h : t.val ≠ i) :
    (scheduleUpdate M W t)[i]'hi = W[i]'hi := by
  by_cases hsmall : t.val < 16 <;> simp [scheduleUpdate, hsmall, h]

theorem scheduleUpdate_get_self (M : Vector (BitVec 32) 16) (W : Vector (BitVec 32) 80)
    (t : Fin 80) :
    (scheduleUpdate M W t)[t.val]'t.isLt =
      if h : t.val < 16 then M[t.val]'(by omega) else
        ROTL 1 (W[t.val - 3]'(by omega) ^^^ W[t.val - 8]'(by omega) ^^^
          W[t.val - 14]'(by omega) ^^^ W[t.val - 16]'(by omega)) := by
  by_cases hsmall : t.val < 16 <;> simp [scheduleUpdate, hsmall]

def schedulePrefix (M : Vector (BitVec 32) 16) : Nat → Vector (BitVec 32) 80
  | 0 => Vector.replicate 80 0
  | n + 1 =>
    if h : n < 80 then scheduleUpdate M (schedulePrefix M n) ⟨n, h⟩
    else schedulePrefix M n

def scheduleFold (M : Vector (BitVec 32) 16) (n : Nat) (hn : n ≤ 80) :
    Vector (BitVec 32) 80 :=
  (List.finRange n).foldl
    (fun W t => scheduleUpdate M W (Fin.castLE hn t)) (Vector.replicate 80 0)

theorem schedulePrefix_eq_fold (M : Vector (BitVec 32) 16) (n : Nat) (hn : n ≤ 80) :
    schedulePrefix M n = scheduleFold M n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n ≤ 80 := by omega
    have hlt : n < 80 := by omega
    simp only [scheduleFold, List.finRange_succ_last, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_map]
    have hcast (i : Fin n) :
        Fin.castLE hn (Fin.castSucc i) = Fin.castLE hn' i := by
      apply Fin.ext
      rfl
    have hfold : (List.finRange n).foldl
        (fun W i => scheduleUpdate M W (Fin.castLE hn (Fin.castSucc i)))
        (Vector.replicate 80 0) = scheduleFold M n hn' := by
      unfold scheduleFold
      congr 1
    have hlast : Fin.castLE hn (Fin.last n) = ⟨n, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [schedulePrefix, dite_eq_left hlt]
    rw [ih hn', hfold, hlast]

theorem schedulePrefix_correct (M : Vector (BitVec 32) 16) (n : Nat)
    (i : Fin 80) (hi : i.val < n) :
    if h : i.val < 16 then (schedulePrefix M n)[i] = M[i.val]'(by omega)
    else (schedulePrefix M n)[i] =
      ROTL 1 ((schedulePrefix M n)[i.val - 3]'(by omega) ^^^
        (schedulePrefix M n)[i.val - 8]'(by omega) ^^^
        (schedulePrefix M n)[i.val - 14]'(by omega) ^^^
        (schedulePrefix M n)[i.val - 16]'(by omega)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : n < 80
    · by_cases heq : i.val = n
      · have hiEq : i = ⟨n, hn⟩ := Fin.ext heq
        subst i
        have hself := scheduleUpdate_get_self M (schedulePrefix M n) ⟨n, hn⟩
        simp only [schedulePrefix, dite_eq_left hn]
        by_cases hsmall : n < 16
        · simp only [hsmall, ↓reduceDIte] at hself ⊢
          simpa using hself
        · simp only [hsmall, ↓reduceDIte] at hself ⊢
          have h3 := scheduleUpdate_get_ne M (schedulePrefix M n) ⟨n, hn⟩ (n - 3)
            (by omega) (by omega)
          have h8 := scheduleUpdate_get_ne M (schedulePrefix M n) ⟨n, hn⟩ (n - 8)
            (by omega) (by omega)
          have h14 := scheduleUpdate_get_ne M (schedulePrefix M n) ⟨n, hn⟩ (n - 14)
            (by omega) (by omega)
          have h16 := scheduleUpdate_get_ne M (schedulePrefix M n) ⟨n, hn⟩ (n - 16)
            (by omega) (by omega)
          simp only [h3, h8, h14, h16]
          exact hself
      · have hi' : i.val < n := by omega
        have hrec := ih hi'
        simp only [schedulePrefix, dite_eq_left hn]
        have hget (j : Nat) (hj : j < 80) (hji : n ≠ j) :
            (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[j]'hj =
              (schedulePrefix M n)[j]'hj := by
          exact scheduleUpdate_get_ne M (schedulePrefix M n) ⟨n, hn⟩ j hj (by omega)
        by_cases hsmall : i.val < 16
        · simp only [dite_eq_left hsmall]
          simp only [dite_eq_left hsmall] at hrec
          change (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val]'i.isLt =
            M[i.val]'(by omega)
          rw [hget i.val i.isLt (by omega)]
          exact hrec
        · simp only [dite_eq_right (by omega)]
          simp only [dite_eq_right (by omega)] at hrec
          have h3 := hget (i.val - 3) (by omega) (by omega)
          have h8 := hget (i.val - 8) (by omega) (by omega)
          have h14 := hget (i.val - 14) (by omega) (by omega)
          have h16 := hget (i.val - 16) (by omega) (by omega)
          change (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val]'i.isLt =
            ROTL 1 ((scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val - 3]'(by omega) ^^^
              (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val - 8]'(by omega) ^^^
              (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val - 14]'(by omega) ^^^
              (scheduleUpdate M (schedulePrefix M n) ⟨n, hn⟩)[i.val - 16]'(by omega))
          rw [hget i.val i.isLt (by omega), h3, h8, h14, h16]
          exact hrec
    · have hi' : i.val < n := by omega
      have hrec := ih hi'
      simpa [schedulePrefix, hn] using hrec

set_option maxRecDepth 2048 in
theorem messageSchedule_eq_schedulePrefix (M : Vector (BitVec 32) 16) :
    messageSchedule M = schedulePrefix M 80 := by
  rw [schedulePrefix_eq_fold M 80 (by omega)]
  change (forIn (List.finRange 80) (Vector.replicate 80 0)
    (fun t W => .yield <$> (show Id (Vector (BitVec 32) 80) from
      scheduleUpdate M W (Fin.castLE (Nat.le_refl 80) t)))).run =
      scheduleFold M 80 (by omega)
  rw [List.idRun_forIn_yield_eq_foldl]
  rfl

theorem scheduleWord_initial (M : Vector (BitVec 32) 16) (t : Fin 80)
    (ht : t.val < 16) :
    scheduleWord M t = M[t.val]'ht := by
  rw [scheduleWord, messageSchedule_eq_schedulePrefix]
  have h := schedulePrefix_correct M 80 t (by omega)
  simpa [ht] using h

theorem scheduleWord_recurrence (M : Vector (BitVec 32) 16) (t : Fin 80)
    (ht : 16 ≤ t.val) :
    scheduleWord M t = ROTL 1 (scheduleWord M ⟨t.val - 3, by omega⟩ ^^^
      scheduleWord M ⟨t.val - 8, by omega⟩ ^^^
      scheduleWord M ⟨t.val - 14, by omega⟩ ^^^
      scheduleWord M ⟨t.val - 16, by omega⟩) := by
  rw [scheduleWord, messageSchedule_eq_schedulePrefix]
  have h := schedulePrefix_correct M 80 t (by omega)
  simp only [show ¬ t.val < 16 by omega, ↓reduceDIte] at h
  simpa [scheduleWord, messageSchedule_eq_schedulePrefix] using h

end Sha1.Proofs.Compress.Rounds
