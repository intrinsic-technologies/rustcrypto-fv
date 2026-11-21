import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Common.Arithmetic.CubicNonzero.Primality.Lucas
import K256.Proofs.Common.Field.PowMod

set_option autoImplicit false
open K256.Proofs.Common.Field.PowMod (powMod_eq_pow_mod)

namespace K256.Proofs.Common.Arithmetic.CubicNonzero

open Standards.SECG.ECC.Curve Standards.SECG.DomainParameters

namespace Primality

private theorem of_lucas_checks (n a : Nat) (factors : List Nat)
    (hchecks : 2 ≤ n ∧ factors.foldr (· * ·) 1 = n - 1 ∧
      powMod n a (n - 1) = 1 ∧
      (factors.all fun q => decide (Nat.Coprime
        (powMod n a ((n - 1) / q) + n - 1) n)) = true)
    (hprimes : ∀ q ∈ factors, IsPrime q) : IsPrime n := by
  apply lucas_primality n a factors hchecks.1 hchecks.2.1 hprimes
  · rw [← powMod_eq_pow_mod]
    exact hchecks.2.2.1
  · intro q hq
    rw [← powMod_eq_pow_mod]
    have h := List.all_eq_true.mp hchecks.2.2.2 q hq
    exact of_decide_eq_true h

private theorem prime_2 : IsPrime 2 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hlo := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 2)
  have hhi := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

private theorem prime_3 : IsPrime 3 := by
  apply of_lucas_checks 3 2 [2]
  · decide +kernel
  · simp [prime_2]

private theorem prime_5 : IsPrime 5 := by
  apply of_lucas_checks 5 2 [2, 2]
  · decide +kernel
  · simp [prime_2]

private theorem prime_7 : IsPrime 7 := by
  apply of_lucas_checks 7 3 [2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

private theorem prime_11 : IsPrime 11 := by
  apply of_lucas_checks 11 2 [2, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

private theorem prime_13 : IsPrime 13 := by
  apply of_lucas_checks 13 2 [2, 2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

private theorem prime_17 : IsPrime 17 := by
  apply of_lucas_checks 17 3 [2, 2, 2, 2]
  · decide +kernel
  · simp [prime_2]

private theorem prime_19 : IsPrime 19 := by
  apply of_lucas_checks 19 2 [2, 3, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

private theorem prime_29 : IsPrime 29 := by
  apply of_lucas_checks 29 2 [2, 2, 7]
  · decide +kernel
  · simp [prime_2, prime_7]

private theorem prime_31 : IsPrime 31 := by
  apply of_lucas_checks 31 3 [2, 3, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

private theorem prime_41 : IsPrime 41 := by
  apply of_lucas_checks 41 6 [2, 2, 2, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

private theorem prime_53 : IsPrime 53 := by
  apply of_lucas_checks 53 2 [2, 2, 13]
  · decide +kernel
  · simp [prime_2, prime_13]

private theorem prime_67 : IsPrime 67 := by
  apply of_lucas_checks 67 2 [2, 3, 11]
  · decide +kernel
  · simp [prime_2, prime_3, prime_11]

private theorem prime_83 : IsPrime 83 := by
  apply of_lucas_checks 83 2 [2, 41]
  · decide +kernel
  · simp [prime_2, prime_41]

private theorem prime_97 : IsPrime 97 := by
  apply of_lucas_checks 97 5 [2, 2, 2, 2, 2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

private theorem prime_101 : IsPrime 101 := by
  apply of_lucas_checks 101 2 [2, 2, 5, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

private theorem prime_103 : IsPrime 103 := by
  apply of_lucas_checks 103 5 [2, 3, 17]
  · decide +kernel
  · simp [prime_2, prime_3, prime_17]

private theorem prime_131 : IsPrime 131 := by
  apply of_lucas_checks 131 2 [2, 5, 13]
  · decide +kernel
  · simp [prime_2, prime_5, prime_13]

private theorem prime_239 : IsPrime 239 := by
  apply of_lucas_checks 239 7 [2, 7, 17]
  · decide +kernel
  · simp [prime_2, prime_7, prime_17]

private theorem prime_271 : IsPrime 271 := by
  apply of_lucas_checks 271 6 [2, 3, 3, 3, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

private theorem prime_419 : IsPrime 419 := by
  apply of_lucas_checks 419 2 [2, 11, 19]
  · decide +kernel
  · simp [prime_2, prime_11, prime_19]

private theorem prime_443 : IsPrime 443 := by
  apply of_lucas_checks 443 2 [2, 13, 17]
  · decide +kernel
  · simp [prime_2, prime_13, prime_17]

private theorem prime_887 : IsPrime 887 := by
  apply of_lucas_checks 887 5 [2, 443]
  · decide +kernel
  · simp [prime_2, prime_443]

private theorem prime_971 : IsPrime 971 := by
  apply of_lucas_checks 971 6 [2, 5, 97]
  · decide +kernel
  · simp [prime_2, prime_5, prime_97]

private theorem prime_1373 : IsPrime 1373 := by
  apply of_lucas_checks 1373 2 [2, 2, 7, 7, 7]
  · decide +kernel
  · simp [prime_2, prime_7]

private theorem prime_1627 : IsPrime 1627 := by
  apply of_lucas_checks 1627 3 [2, 3, 271]
  · decide +kernel
  · simp [prime_2, prime_3, prime_271]

private theorem prime_2621 : IsPrime 2621 := by
  apply of_lucas_checks 2621 2 [2, 2, 5, 131]
  · decide +kernel
  · simp [prime_2, prime_5, prime_131]

private theorem prime_2657 : IsPrime 2657 := by
  apply of_lucas_checks 2657 3 [2, 2, 2, 2, 2, 83]
  · decide +kernel
  · simp [prime_2, prime_83]

private theorem prime_4423 : IsPrime 4423 := by
  apply of_lucas_checks 4423 3 [2, 3, 11, 67]
  · decide +kernel
  · simp [prime_2, prime_3, prime_11, prime_67]

private theorem prime_5323 : IsPrime 5323 := by
  apply of_lucas_checks 5323 5 [2, 3, 887]
  · decide +kernel
  · simp [prime_2, prime_3, prime_887]

private theorem prime_7723 : IsPrime 7723 := by
  apply of_lucas_checks 7723 3 [2, 3, 3, 3, 11, 13]
  · decide +kernel
  · simp [prime_2, prime_3, prime_11, prime_13]

private theorem prime_13441 : IsPrime 13441 := by
  apply of_lucas_checks 13441 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_7]

private theorem prime_20113 : IsPrime 20113 := by
  apply of_lucas_checks 20113 10 [2, 2, 2, 2, 3, 419]
  · decide +kernel
  · simp [prime_2, prime_3, prime_419]

private theorem prime_24809 : IsPrime 24809 := by
  apply of_lucas_checks 24809 6 [2, 2, 2, 7, 443]
  · decide +kernel
  · simp [prime_2, prime_7, prime_443]

private theorem prime_41201 : IsPrime 41201 := by
  apply of_lucas_checks 41201 3 [2, 2, 2, 2, 5, 5, 103]
  · decide +kernel
  · simp [prime_2, prime_5, prime_103]

private theorem prime_96557 : IsPrime 96557 := by
  apply of_lucas_checks 96557 2 [2, 2, 101, 239]
  · decide +kernel
  · simp [prime_2, prime_101, prime_239]

private theorem prime_1206781 : IsPrime 1206781 := by
  apply of_lucas_checks 1206781 10 [2, 2, 3, 5, 20113]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_20113]

private theorem prime_7240687 : IsPrime 7240687 := by
  apply of_lucas_checks 7240687 3 [2, 3, 1206781]
  · decide +kernel
  · simp [prime_2, prime_3, prime_1206781]

private theorem prime_13331831 : IsPrime 13331831 := by
  apply of_lucas_checks 13331831 13 [2, 5, 971, 1373]
  · decide +kernel
  · simp [prime_2, prime_5, prime_971, prime_1373]

private theorem prime_107590001 : IsPrime 107590001 := by
  apply of_lucas_checks 107590001 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
  · decide +kernel
  · simp [prime_2, prime_5, prime_7, prime_29, prime_53]

private theorem prime_173378833005251801 : IsPrime 173378833005251801 := by
  apply of_lucas_checks 173378833005251801 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831]
  · decide +kernel
  · simp [prime_2, prime_5, prime_2621, prime_24809, prime_13331831]

private theorem prime_22149492674086928081353 : IsPrime 22149492674086928081353 := by
  apply of_lucas_checks 22149492674086928081353 5 [2, 2, 2, 3, 5323, 173378833005251801]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5323, prime_173378833005251801]

private theorem prime_132896956044521568488119 : IsPrime 132896956044521568488119 := by
  apply of_lucas_checks 132896956044521568488119 6 [2, 3, 22149492674086928081353]
  · decide +kernel
  · simp [prime_2, prime_3, prime_22149492674086928081353]

private theorem prime_255515944373312847190720520512484175977 : IsPrime 255515944373312847190720520512484175977 := by
  apply of_lucas_checks 255515944373312847190720520512484175977 3
    [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
  · decide +kernel
  · simp [prime_2, prime_7, prime_11, prime_1627, prime_2657, prime_4423, prime_41201, prime_96557,
      prime_7240687, prime_107590001]

private theorem prime_205115282021455665897114700593932402728804164701536103180137503955397371 : IsPrime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  apply of_lucas_checks 205115282021455665897114700593932402728804164701536103180137503955397371 10
    [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_29, prime_31, prime_7723, prime_132896956044521568488119,
      prime_255515944373312847190720520512484175977]

end Primality

theorem prime_secp256k1 : IsPrime Secp256k1.domain.p := by
  apply Primality.of_lucas_checks 115792089237316195423570985008687907853269984665640564039457584007908834671663 3
    [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
  · decide +kernel
  · simp [Primality.prime_2, Primality.prime_3, Primality.prime_7, Primality.prime_13441,
      Primality.prime_205115282021455665897114700593932402728804164701536103180137503955397371]

end K256.Proofs.Common.Arithmetic.CubicNonzero
