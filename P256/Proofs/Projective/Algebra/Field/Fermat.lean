import P256.Proofs.Projective.Algebra.Field.Fermat.Residues

set_option autoImplicit false

namespace P256.Proofs.Projective.Algebra.FieldArithmetic

theorem prod_map_mul_mod (p x : Nat) (l : List Nat) :
    (l.map (fun a => x * a % p)).prod % p = x ^ l.length * l.prod % p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Nat.mul_mod, Nat.mod_mod, ih]
    rw [← Nat.mul_mod]
    congr 1
    rw [Nat.pow_succ]
    ac_rfl

theorem coprime_prod {p : Nat} {l : List Nat}
    (h : ∀ a ∈ l, Nat.Coprime a p) : Nat.Coprime l.prod p := by
  induction l with
  | nil => exact Nat.coprime_one_left p
  | cons a l ih =>
    exact (h a (by simp)).mul_left (ih (fun b hb => h b (by simp [hb])))

theorem pow_pred_prime_mod (p x : Nat) (hp : IsPrime p) (hx : Nat.Coprime x p) :
    x ^ (p - 1) % p = 1 := by
  let l := List.range' 1 (p - 1)
  have hpos : 0 < p := by have := hp.1; omega
  have hc : Nat.Coprime l.prod p := by
    apply coprime_prod
    intro a ha
    have hmem := List.mem_range'.mp ha
    apply hp.coprime_of_lt <;> omega
  have hprod := congrArg (fun n => n % p) (residues_perm p x hpos hx.symm).prod_nat
  rw [prod_map_mul_mod, List.length_range'] at hprod
  have heq : l.prod * x ^ (p - 1) % p = l.prod * 1 % p := by
    simpa only [Nat.mul_comm, Nat.one_mul] using hprod
  have hcancel := mul_mod_cancel p l.prod (x ^ (p - 1)) 1 hc.symm heq
  simpa only [Nat.mod_eq_of_lt (show 1 < p by have := hp.1; omega)] using hcancel

theorem pow_prime_mod (p x : Nat) (hp : IsPrime p) : x ^ p % p = x % p := by
  have hpos : 0 < p := by have := hp.1; omega
  by_cases hx : p ∣ x
  · have hz : x % p = 0 := Nat.mod_eq_zero_of_dvd hx
    rw [Nat.pow_mod, hz, Nat.zero_pow (by omega), Nat.zero_mod]
  · have hpred := pow_pred_prime_mod p x hp (hp.coprime_of_not_dvd hx)
    have he : p = (p - 1) + 1 := by omega
    calc
      x ^ p % p = x ^ ((p - 1) + 1) % p := by rw [← he]
      _ = (x ^ (p - 1) % p) * (x % p) % p := by rw [Nat.pow_succ, Nat.mul_mod]
      _ = x % p := by rw [hpred, Nat.one_mul, Nat.mod_mod]

end P256.Proofs.Projective.Algebra.FieldArithmetic
