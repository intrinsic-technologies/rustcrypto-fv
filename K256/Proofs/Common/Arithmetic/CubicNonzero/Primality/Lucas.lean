import K256.Proofs.Common.Arithmetic.CubicNonzero.Order
import K256.Proofs.Common.Arithmetic.CubicNonzero.Fermat
import K256.Proofs.Common.Arithmetic.CubicNonzero.Primality.Lucas.Factorization

set_option autoImplicit false
namespace K256.Proofs.Common.Arithmetic.CubicNonzero

theorem pow_mod_ne_one_of_coprime {n p x : Nat} (hp : 1 < p) (hpn : p ∣ n)
    (hc : Nat.Coprime (x % n + n - 1) n) : x % p ≠ 1 := by
  intro heq
  have hmod : (x % n + n) % p = 1 % p := by
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hpn, Nat.mod_eq_zero_of_dvd hpn,
      Nat.add_zero, heq]
  have hd : p ∣ x % n + n - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  exact Nat.not_coprime_of_dvd_of_dvd hp hd hpn hc

theorem lucas_primality (n a : Nat) (factors : List Nat) (hn : 2 ≤ n)
    (hfac : factors.foldr (· * ·) 1 = n - 1)
    (hprimes : ∀ q ∈ factors, IsPrime q)
    (hpow : a ^ (n - 1) % n = 1)
    (hnon : ∀ q ∈ factors, Nat.Coprime (a ^ ((n - 1) / q) % n + n - 1) n) :
    IsPrime n := by
  obtain ⟨p, hp, hpn⟩ := exists_prime_divisor n hn
  have hp1 : 1 < p := by have := hp.1; omega
  have hpowp : a ^ (n - 1) % p = 1 := by
    rw [← Nat.mod_mod_of_dvd _ hpn, hpow, Nat.mod_eq_of_lt hp1]
  obtain ⟨d, hd⟩ := exists_modularOrder p a (n - 1) (by omega) hpowp
  have hdeq : d = n - 1 := by
    apply eq_of_dvd_of_not_dvd_quotients (n - 1) d factors (by omega)
      (hd.dvd_of_pow_eq_one hpowp) hfac hprimes
    intro q hq hdiv
    apply pow_mod_ne_one_of_coprime hp1 hpn (hnon q hq)
    rw [pow_mod_eq_pow_mod_order hd.power, Nat.mod_eq_zero_of_dvd hdiv,
      Nat.pow_zero, Nat.mod_eq_of_lt hp1]
  have hac : Nat.Coprime a p := by
    apply hp.coprime_of_not_dvd
    intro hpa
    have hz : a % p = 0 := Nat.mod_eq_zero_of_dvd hpa
    rw [Nat.pow_mod, hz, Nat.zero_pow (by omega), Nat.zero_mod] at hpowp
    omega
  have hdp := hd.dvd_of_pow_eq_one (pow_pred_prime_mod p a hp hac)
  have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hdp
  have hpnle := Nat.le_of_dvd (by omega : 0 < n) hpn
  have heq : p = n := by omega
  exact heq ▸ hp

end K256.Proofs.Common.Arithmetic.CubicNonzero
