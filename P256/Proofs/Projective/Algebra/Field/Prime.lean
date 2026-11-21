import Init.Data.Nat.Coprime

set_option autoImplicit false
namespace P256.Proofs.Projective.Algebra.FieldArithmetic

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrime.coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (ha : ¬p ∣ a) :
    Nat.Coprime a p := by
  rcases hp.2 (Nat.gcd a p) (Nat.gcd_dvd_right a p) with h | h
  · exact h
  · exact False.elim (ha (h ▸ Nat.gcd_dvd_left a p))

theorem IsPrime.coprime_of_lt {p a : Nat} (hp : IsPrime p) (ha : 0 < a) (hlt : a < p) :
    Nat.Coprime a p := by
  apply hp.coprime_of_not_dvd
  intro hd
  have := Nat.le_of_dvd ha hd
  omega

theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · exact Or.inr ((hp.coprime_of_not_dvd ha).symm.dvd_of_dvd_mul_left h)

theorem exists_prime_divisor (n : Nat) (hn : 2 ≤ n) :
    ∃ p, IsPrime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    classical
    by_cases hp : IsPrime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have hd : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction
        intro hnone
        apply hp
        refine ⟨hn, fun d hdn => ?_⟩
        by_cases hd1 : d = 1
        · exact Or.inl hd1
        by_cases hdne : d = n
        · exact Or.inr hdne
        exact False.elim (hnone ⟨d, hdn, hd1, hdne⟩)
      obtain ⟨d, hdn, hd1, hdne⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hdlt : d < n := by
        have := Nat.le_of_dvd (by omega : 0 < n) hdn
        omega
      obtain ⟨p, hp, hpd⟩ := ih d hdlt (by omega)
      exact ⟨p, hp, Nat.dvd_trans hpd hdn⟩

theorem coprime_mul_mod_injective {p a b c : Nat}
    (ha : Nat.Coprime a p) (hb : b < p) (hc : c < p)
    (h : a * b % p = a * c % p) : b = c := by
  have hbc : p ∣ b - c := by
    apply ha.symm.dvd_of_dvd_mul_left
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
  have hcb : p ∣ c - b := by
    apply ha.symm.dvd_of_dvd_mul_left
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have hzero₁ : b - c = 0 := Nat.eq_zero_of_dvd_of_lt hbc (by omega)
  have hzero₂ : c - b = 0 := Nat.eq_zero_of_dvd_of_lt hcb (by omega)
  omega

end P256.Proofs.Projective.Algebra.FieldArithmetic
