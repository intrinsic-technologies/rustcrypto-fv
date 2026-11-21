import P256.Spec.Operations
import P256.Proofs.Projective.Algebra.Field.Primality.Lucas
import P256.Proofs.Projective.Algebra.Field.Power

set_option autoImplicit false


namespace P256.Proofs.Projective.Algebra.FieldArithmetic

open Standards.SECG.ECC.Curve

namespace Primality

theorem of_lucas_checks (n a : Nat) (factors : List Nat)
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

theorem prime_2 : IsPrime 2 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hlo := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 2)
  have hhi := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem prime_3 : IsPrime 3 := by
  apply of_lucas_checks 3 2 [2]
  · decide +kernel
  · simp [prime_2]

theorem prime_5 : IsPrime 5 := by
  apply of_lucas_checks 5 2 [2, 2]
  · decide +kernel
  · simp [prime_2]

theorem prime_7 : IsPrime 7 := by
  apply of_lucas_checks 7 3 [2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_11 : IsPrime 11 := by
  apply of_lucas_checks 11 2 [2, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

theorem prime_13 : IsPrime 13 := by
  apply of_lucas_checks 13 2 [2, 2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_17 : IsPrime 17 := by
  apply of_lucas_checks 17 3 [2, 2, 2, 2]
  · decide +kernel
  · simp [prime_2]

theorem prime_23 : IsPrime 23 := by
  apply of_lucas_checks 23 5 [2, 11]
  · decide +kernel
  · simp [prime_2, prime_11]

theorem prime_43 : IsPrime 43 := by
  apply of_lucas_checks 43 3 [2, 3, 7]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7]

theorem prime_53 : IsPrime 53 := by
  apply of_lucas_checks 53 2 [2, 2, 13]
  · decide +kernel
  · simp [prime_2, prime_13]

theorem prime_107 : IsPrime 107 := by
  apply of_lucas_checks 107 2 [2, 53]
  · decide +kernel
  · simp [prime_2, prime_53]

theorem prime_157 : IsPrime 157 := by
  apply of_lucas_checks 157 5 [2, 2, 3, 13]
  · decide +kernel
  · simp [prime_2, prime_3, prime_13]

theorem prime_173 : IsPrime 173 := by
  apply of_lucas_checks 173 2 [2, 2, 43]
  · decide +kernel
  · simp [prime_2, prime_43]

theorem prime_181 : IsPrime 181 := by
  apply of_lucas_checks 181 2 [2, 2, 3, 3, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

theorem prime_197 : IsPrime 197 := by
  apply of_lucas_checks 197 2 [2, 2, 7, 7]
  · decide +kernel
  · simp [prime_2, prime_7]

theorem prime_241 : IsPrime 241 := by
  apply of_lucas_checks 241 7 [2, 2, 2, 2, 3, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

theorem prime_257 : IsPrime 257 := by
  apply of_lucas_checks 257 3 [2, 2, 2, 2, 2, 2, 2, 2]
  · decide +kernel
  · simp [prime_2]

theorem prime_313 : IsPrime 313 := by
  apply of_lucas_checks 313 10 [2, 2, 2, 3, 13]
  · decide +kernel
  · simp [prime_2, prime_3, prime_13]

theorem prime_641 : IsPrime 641 := by
  apply of_lucas_checks 641 3 [2, 2, 2, 2, 2, 2, 2, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

theorem prime_661 : IsPrime 661 := by
  apply of_lucas_checks 661 2 [2, 2, 3, 5, 11]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_11]

theorem prime_727 : IsPrime 727 := by
  apply of_lucas_checks 727 5 [2, 3, 11, 11]
  · decide +kernel
  · simp [prime_2, prime_3, prime_11]

theorem prime_757 : IsPrime 757 := by
  apply of_lucas_checks 757 2 [2, 2, 3, 3, 3, 7]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7]

theorem prime_919 : IsPrime 919 := by
  apply of_lucas_checks 919 7 [2, 3, 3, 3, 17]
  · decide +kernel
  · simp [prime_2, prime_3, prime_17]

theorem prime_1087 : IsPrime 1087 := by
  apply of_lucas_checks 1087 3 [2, 3, 181]
  · decide +kernel
  · simp [prime_2, prime_3, prime_181]

theorem prime_1531 : IsPrime 1531 := by
  apply of_lucas_checks 1531 2 [2, 3, 3, 5, 17]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_17]

theorem prime_2411 : IsPrime 2411 := by
  apply of_lucas_checks 2411 6 [2, 5, 241]
  · decide +kernel
  · simp [prime_2, prime_5, prime_241]

theorem prime_3677 : IsPrime 3677 := by
  apply of_lucas_checks 3677 2 [2, 2, 919]
  · decide +kernel
  · simp [prime_2, prime_919]

theorem prime_3769 : IsPrime 3769 := by
  apply of_lucas_checks 3769 7 [2, 2, 2, 3, 157]
  · decide +kernel
  · simp [prime_2, prime_3, prime_157]

theorem prime_4349 : IsPrime 4349 := by
  apply of_lucas_checks 4349 2 [2, 2, 1087]
  · decide +kernel
  · simp [prime_2, prime_1087]

theorem prime_17449 : IsPrime 17449 := by
  apply of_lucas_checks 17449 14 [2, 2, 2, 3, 727]
  · decide +kernel
  · simp [prime_2, prime_3, prime_727]

theorem prime_18169 : IsPrime 18169 := by
  apply of_lucas_checks 18169 11 [2, 2, 2, 3, 757]
  · decide +kernel
  · simp [prime_2, prime_3, prime_757]

theorem prime_65537 : IsPrime 65537 := by
  apply of_lucas_checks 65537 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
  · decide +kernel
  · simp [prime_2]

theorem prime_78283 : IsPrime 78283 := by
  apply of_lucas_checks 78283 3 [2, 3, 3, 4349]
  · decide +kernel
  · simp [prime_2, prime_3, prime_4349]

theorem prime_490463 : IsPrime 490463 := by
  apply of_lucas_checks 490463 14 [2, 7, 53, 661]
  · decide +kernel
  · simp [prime_2, prime_7, prime_53, prime_661]

theorem prime_704251 : IsPrime 704251 := by
  apply of_lucas_checks 704251 2 [2, 3, 3, 5, 5, 5, 313]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_313]

theorem prime_6700417 : IsPrime 6700417 := by
  apply of_lucas_checks 6700417 5 [2, 2, 2, 2, 2, 2, 2, 3, 17449]
  · decide +kernel
  · simp [prime_2, prime_3, prime_17449]

theorem prime_204061199 : IsPrime 204061199 := by
  apply of_lucas_checks 204061199 11 [2, 11, 23, 107, 3769]
  · decide +kernel
  · simp [prime_2, prime_11, prime_23, prime_107, prime_3769]

theorem prime_34282281433 : IsPrime 34282281433 := by
  apply of_lucas_checks 34282281433 17 [2, 2, 2, 3, 7, 204061199]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7, prime_204061199]

theorem prime_66417393611 : IsPrime 66417393611 := by
  apply of_lucas_checks 66417393611 6 [2, 5, 53, 173, 197, 3677]
  · decide +kernel
  · simp [prime_2, prime_5, prime_53, prime_173, prime_197, prime_3677]

theorem prime_11290956913871 : IsPrime 11290956913871 := by
  apply of_lucas_checks 11290956913871 13 [2, 5, 17, 66417393611]
  · decide +kernel
  · simp [prime_2, prime_5, prime_17, prime_66417393611]

theorem prime_46076956964474543 : IsPrime 46076956964474543 := by
  apply of_lucas_checks 46076956964474543 5 [2, 23, 18169, 78283, 704251]
  · decide +kernel
  · simp [prime_2, prime_23, prime_18169, prime_78283, prime_704251]

theorem prime_774023187263532362759620327192479577272145303 : IsPrime 774023187263532362759620327192479577272145303 := by
  apply of_lucas_checks 774023187263532362759620327192479577272145303 3
    [2, 3, 3, 2411, 34282281433, 11290956913871, 46076956964474543]
  · decide +kernel
  · simp [prime_2, prime_3, prime_2411, prime_34282281433, prime_11290956913871,
      prime_46076956964474543]

theorem prime_835945042244614951780389953367877943453916927241 : IsPrime 835945042244614951780389953367877943453916927241 := by
  apply of_lucas_checks 835945042244614951780389953367877943453916927241 11
    [2, 2, 2, 3, 3, 3, 5, 774023187263532362759620327192479577272145303]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_774023187263532362759620327192479577272145303]

end Primality

theorem prime_p256 : IsPrime P256.Spec.Operations.domain.p := by
  apply P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.of_lucas_checks 115792089210356248762697446949407573530086143415290314195533631308867097853951 6
    [2, 3, 5, 5, 17, 257, 641, 1531, 65537, 490463, 6700417,
      835945042244614951780389953367877943453916927241]
  · decide +kernel
  · simp [P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_2, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_3, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_5, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_17, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_257, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_641, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_1531, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_65537,
      P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_490463, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_6700417, P256.Proofs.Projective.Algebra.FieldArithmetic.Primality.prime_835945042244614951780389953367877943453916927241]

end P256.Proofs.Projective.Algebra.FieldArithmetic
