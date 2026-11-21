import K256.Proofs.Common.Arithmetic.CubicNonzero.Prime

set_option autoImplicit false
namespace K256.Proofs.Common.Arithmetic.CubicNonzero

theorem IsPrime.mem_of_dvd_foldr_mul {p : Nat} (hp : IsPrime p)
    (factors : List Nat) (hprimes : ∀ q ∈ factors, IsPrime q)
    (hdvd : p ∣ factors.foldr (· * ·) 1) : p ∈ factors := by
  induction factors with
  | nil =>
    have h := Nat.eq_one_of_dvd_one hdvd
    have := hp.1
    omega
  | cons q factors ih =>
    rcases hp.dvd_mul hdvd with hq | htail
    · have hqprime := hprimes q (by simp)
      rcases hqprime.2 p hq with heq | heq
      · have := hp.1
        omega
      · simp [heq]
    · exact List.mem_cons_of_mem q (ih (fun r hr => hprimes r (List.mem_cons_of_mem q hr)) htail)

theorem eq_of_dvd_of_not_dvd_quotients (n d : Nat) (factors : List Nat)
    (hn : 0 < n) (hd : d ∣ n) (hfac : factors.foldr (· * ·) 1 = n)
    (hprimes : ∀ q ∈ factors, IsPrime q)
    (hnon : ∀ q ∈ factors, ¬ d ∣ n / q) : d = n := by
  by_cases heq : d = n
  · exact heq
  obtain ⟨k, hk⟩ := hd
  have hk2 : 2 ≤ k := by
    by_cases hk0 : k = 0
    · simp only [hk0, Nat.mul_zero] at hk
      omega
    by_cases hk1 : k = 1
    · simp only [hk1, Nat.mul_one] at hk
      omega
    omega
  obtain ⟨q, hqprime, hqk⟩ := exists_prime_divisor k hk2
  have hqn : q ∣ n := by
    rw [hk]
    exact Nat.dvd_mul_left_of_dvd hqk d
  have hmem := hqprime.mem_of_dvd_foldr_mul factors hprimes (hfac ▸ hqn)
  apply False.elim
  apply hnon q hmem
  apply Nat.dvd_div_of_mul_dvd
  rw [hk, Nat.mul_comm q d]
  exact Nat.mul_dvd_mul_left d hqk

end K256.Proofs.Common.Arithmetic.CubicNonzero
