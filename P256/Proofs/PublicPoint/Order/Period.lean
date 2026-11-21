import P256.Proofs.Projective.Algebra.Field.Prime

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Order

theorem exists_least_positive {P : Nat → Prop} (n : Nat) (hn : 0 < n) (hp : P n) :
    ∃ m, 0 < m ∧ P m ∧ ∀ k, 0 < k → P k → m ≤ k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    classical
    by_cases hsmaller : ∃ k, 0 < k ∧ k < n ∧ P k
    · obtain ⟨k, hk, hkn, hpk⟩ := hsmaller
      exact ih k hkn hk hpk
    · refine ⟨n, hn, hp, ?_⟩
      intro k hk hpk
      by_cases hle : n ≤ k
      · exact hle
      · exact False.elim (hsmaller ⟨k, hk, by omega, hpk⟩)

theorem periodic_eq_mod {α : Sort _} (f : Nat → α) (period : Nat)
    (hpositive : 0 < period) (hperiod : ∀ k, f (period + k) = f k) (n : Nat) :
    f n = f (n % period) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hlt : n < period
    · rw [Nat.mod_eq_of_lt hlt]
    · have hle : period ≤ n := by omega
      calc
        f n = f (period + (n - period)) := by rw [Nat.add_sub_of_le hle]
        _ = f (n - period) := hperiod _
        _ = f ((n - period) % period) := ih _ (by omega)
        _ = f (n % period) := congrArg f (Nat.mod_eq_sub_mod hle).symm

theorem nonzero_of_prime_period {α : Sort _} (f : Nat → α) (zero : α) (n : Nat)
    (hn : P256.Proofs.Projective.Algebra.FieldArithmetic.IsPrime n) (hnzero : f n = zero) (hone : f 1 ≠ zero)
    (hperiod : ∀ m, f m = zero → ∀ k, f (m + k) = f k)
    (d : Nat) (hd : 0 < d) (hdn : d < n) : f d ≠ zero := by
  intro hdzero
  obtain ⟨m, hm, hmzero, hminimal⟩ :=
    exists_least_positive (P := fun k => f k = zero) n (by have := hn.1; omega) hnzero
  have hdivides : ∀ k, f k = zero → m ∣ k := by
    intro k hk
    have hmod : f (k % m) = zero :=
      (periodic_eq_mod f m hm (hperiod m hmzero) k).symm.trans hk
    apply Nat.dvd_of_mod_eq_zero
    by_cases hz : k % m = 0
    · exact hz
    · have hbound := hminimal (k % m) (by omega) hmod
      have hlt := Nat.mod_lt k hm
      omega
  rcases hn.2 m (hdivides n hnzero) with hmone | hmn
  · exact hone (hmone ▸ hmzero)
  · have hnd := Nat.le_of_dvd hd (hdivides d hdzero)
    omega

end P256.Proofs.PublicPoint.Order
