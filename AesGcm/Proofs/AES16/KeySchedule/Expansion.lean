import Standards.NIST.AES.KeyExpansion

namespace AesGcm.Proofs.Machine.KeySchedule

open Standards.NIST.AES

abbrev Word := Vector UInt8 4

def initialWords (v : Variant) (key : Vector UInt8 v.keyBytes) : Array Word :=
  Array.ofFn fun i : Fin v.Nk ↦ Vector.ofFn fun j : Fin 4 ↦
    key[4 * i.val + j.val]'(by
      have := i.isLt; have := j.isLt; unfold Variant.keyBytes; omega)

def expansionTemp (v : Variant) (i : Nat) (previous : Word) : Word :=
  if i % v.Nk = 0 then xorWord (subWord (rotWord previous)) (rcon (i / v.Nk))
  else if v.Nk > 6 ∧ i % v.Nk = 4 then subWord previous
  else previous

def expansionStep (v : Variant) (w : Array Word) (k : Nat) : Array Word :=
  let i := v.Nk + k
  w.push (xorWord w[i - v.Nk]! (expansionTemp v i w[i - 1]!))

def expansionPrefix (v : Variant) (key : Vector UInt8 v.keyBytes) (n : Nat) : Array Word :=
  (List.range n).foldl (expansionStep v) (initialWords v key)

theorem expansionPrefix_zero (v : Variant) (key : Vector UInt8 v.keyBytes) :
    expansionPrefix v key 0 = initialWords v key := rfl

theorem expansionPrefix_succ (v : Variant) (key : Vector UInt8 v.keyBytes) (n : Nat) :
    expansionPrefix v key (n + 1) = expansionStep v (expansionPrefix v key n) n := by
  simp only [expansionPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

theorem size_expansionPrefix (v : Variant) (key : Vector UInt8 v.keyBytes) (n : Nat) :
    (expansionPrefix v key n).size = v.Nk + n := by
  induction n with
  | zero => simp only [expansionPrefix_zero, initialWords, Array.size_ofFn, Nat.add_zero]
  | succ n ih =>
    simp only [expansionPrefix_succ, expansionStep, Array.size_push, ih, Nat.add_assoc]

theorem expansionPrefix_getElem_preserved (v : Variant) (key : Vector UInt8 v.keyBytes)
    {n m i : Nat} (hnm : n ≤ m) (hi : i < v.Nk + n) :
    (expansionPrefix v key m)[i]! = (expansionPrefix v key n)[i]! := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases he : n = m + 1
    · subst n; rfl
    have hnm' : n ≤ m := by omega
    rw [expansionPrefix_succ]
    have hi' : i < (expansionPrefix v key m).size := by
      rw [size_expansionPrefix]; omega
    simp only [expansionStep]
    rw [getElem!_pos ((expansionPrefix v key m).push _) i (by
      simpa only [Array.size_push] using Nat.lt_succ_of_lt hi'),
      Array.getElem_push_lt hi', ← getElem!_pos (expansionPrefix v key m) i hi']
    exact ih hnm'

theorem keyExpansion_eq_prefix (v : Variant) (key : Vector UInt8 v.keyBytes) :
    keyExpansion v key = Vector.ofFn (fun i : Fin (4 * (v.Nr + 1)) ↦
      (expansionPrefix v key (4 * (v.Nr + 1) - v.Nk))[i.val]!) := rfl

theorem keyExpansion_initial (v : Variant) (key : Vector UInt8 v.keyBytes)
    (i : Fin v.Nk) :
    (keyExpansion v key)[i.val]'(by have := i.isLt; cases v <;> simp_all [Variant.Nk,
      Variant.Nr] <;> omega) = Vector.ofFn (fun j : Fin 4 ↦ key[4 * i.val + j.val]'(by
        have := i.isLt; have := j.isLt; unfold Variant.keyBytes; omega)) := by
  rw [keyExpansion_eq_prefix]
  simp only [Vector.getElem_ofFn]
  rw [expansionPrefix_getElem_preserved v key (Nat.zero_le _) (by
    simpa only [Nat.add_zero] using i.isLt)]
  rw [expansionPrefix_zero]
  have hi : i.val < (initialWords v key).size := by
    simpa only [initialWords, Array.size_ofFn] using i.isLt
  rw [getElem!_pos (initialWords v key) i.val hi]
  simp only [initialWords, Array.getElem_ofFn]

theorem expansionPrefix_next (v : Variant) (key : Vector UInt8 v.keyBytes) (n : Nat) :
    (expansionPrefix v key (n + 1))[v.Nk + n]! =
      xorWord (expansionPrefix v key n)[n]!
        (expansionTemp v (v.Nk + n) (expansionPrefix v key n)[v.Nk + n - 1]!) := by
  rw [expansionPrefix_succ]
  simp only [expansionStep, Nat.add_sub_cancel_left]
  rw [getElem!_pos _ _ (by rw [Array.size_push, size_expansionPrefix]; omega)]
  have hs : v.Nk + n = (expansionPrefix v key n).size :=
    (size_expansionPrefix v key n).symm
  simp only [hs, Array.getElem_push_eq]

theorem keyExpansion_recurrence (v : Variant) (key : Vector UInt8 v.keyBytes)
    (i : Nat) (hNk : v.Nk ≤ i) (hi : i < 4 * (v.Nr + 1)) :
    (keyExpansion v key)[i] = xorWord
      ((keyExpansion v key)[i - v.Nk]'(by omega))
      (expansionTemp v i ((keyExpansion v key)[i - 1]'(by omega))) := by
  have hpos : 0 < v.Nk := by cases v <;> decide
  let n := i - v.Nk
  have hni : v.Nk + n = i := by omega
  have hn : n + 1 ≤ 4 * (v.Nr + 1) - v.Nk := by omega
  simp only [keyExpansion_eq_prefix, Vector.getElem_ofFn]
  rw [expansionPrefix_getElem_preserved v key hn (by omega), ← hni,
    expansionPrefix_next]
  rw [expansionPrefix_getElem_preserved v key (Nat.le_of_succ_le hn) (by omega),
    expansionPrefix_getElem_preserved v key (Nat.le_of_succ_le hn) (by omega)]
  simp only [hni, n]

theorem rcon_eq_source_bits (r : Fin 10) :
    rcon (r.val + 1) = #v[
      if r.val < 8 then (1 : UInt8) <<< r.val.toUInt8 else
        ((1 : UInt8) <<< (r.val - 8).toUInt8) ^^^
        ((1 : UInt8) <<< (r.val - 7).toUInt8) ^^^
        ((1 : UInt8) <<< (r.val - 5).toUInt8) ^^^
        ((1 : UInt8) <<< (r.val - 4).toUInt8), 0, 0, 0] := by
  have h : ∀ r : Fin 10,
      rcon (r.val + 1) = #v[
        if r.val < 8 then (1 : UInt8) <<< r.val.toUInt8 else
          ((1 : UInt8) <<< (r.val - 8).toUInt8) ^^^
          ((1 : UInt8) <<< (r.val - 7).toUInt8) ^^^
          ((1 : UInt8) <<< (r.val - 5).toUInt8) ^^^
          ((1 : UInt8) <<< (r.val - 4).toUInt8), 0, 0, 0] := by decide +kernel
  exact h r

end AesGcm.Proofs.Machine.KeySchedule
