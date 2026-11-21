import Std

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

def mixedNibble (c : UInt8) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

theorem mixedNibble_lt {c : UInt8} {n : Nat} (h : mixedNibble c = some n) : n < 16 := by
  unfold mixedNibble at h
  split at h
  · simp only [Option.some.injEq] at h
    omega
  · split at h
    · simp only [Option.some.injEq] at h
      omega
    · split at h
      · simp only [Option.some.injEq] at h
        omega
      · contradiction

theorem mixedNibble_eq_none_iff (c : UInt8) :
    mixedNibble c = none ↔
      ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧
      ¬ (65 ≤ c.toNat ∧ c.toNat ≤ 70) ∧
      ¬ (97 ≤ c.toNat ∧ c.toNat ≤ 102) := by
  by_cases hd : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · simp [mixedNibble, hd]
  · by_cases hu : 65 ≤ c.toNat ∧ c.toNat ≤ 70
    · simp [mixedNibble, hd, hu]
    · by_cases hl : 97 ≤ c.toNat ∧ c.toNat ≤ 102 <;> simp [mixedNibble, hd, hu, hl]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect
