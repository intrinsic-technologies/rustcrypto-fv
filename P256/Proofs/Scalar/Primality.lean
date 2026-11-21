import P256.Proofs.Projective.Algebra.Field.Primality

set_option autoImplicit false

open P256.Proofs.Projective.Algebra.FieldArithmetic (IsPrime)
open P256.Proofs.Projective.Algebra.FieldArithmetic.Primality (of_lucas_checks prime_11 prime_13 prime_17 prime_17449 prime_2 prime_3 prime_43 prime_5 prime_7)

namespace P256.Proofs.Scalar

open P256.Spec.Operations

theorem prime_131 : IsPrime 131 := by
  apply of_lucas_checks 131 2
    [2, 5, 13]
  · decide +kernel
  · simp [prime_2, prime_5, prime_13]

theorem prime_71 : IsPrime 71 := by
  apply of_lucas_checks 71 7
    [2, 5, 7]
  · decide +kernel
  · simp [prime_2, prime_5, prime_7]

theorem prime_37 : IsPrime 37 := by
  apply of_lucas_checks 37 2
    [2, 2, 3, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_9547 : IsPrime 9547 := by
  apply of_lucas_checks 9547 2
    [2, 3, 37, 43]
  · decide +kernel
  · simp [prime_2, prime_3, prime_37, prime_43]

theorem prime_38189 : IsPrime 38189 := by
  apply of_lucas_checks 38189 2
    [2, 2, 9547]
  · decide +kernel
  · simp [prime_2, prime_9547]

theorem prime_3407 : IsPrime 3407 := by
  apply of_lucas_checks 3407 5
    [2, 13, 131]
  · decide +kernel
  · simp [prime_2, prime_13, prime_131]

theorem prime_263 : IsPrime 263 := by
  apply of_lucas_checks 263 5
    [2, 131]
  · decide +kernel
  · simp [prime_2, prime_131]

theorem prime_126241 : IsPrime 126241 := by
  apply of_lucas_checks 126241 7
    [2, 2, 2, 2, 2, 3, 5, 263]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_263]

theorem prime_19 : IsPrime 19 := by
  apply of_lucas_checks 19 2
    [2, 3, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_337 : IsPrime 337 := by
  apply of_lucas_checks 337 10
    [2, 2, 2, 2, 3, 7]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7]

theorem prime_31 : IsPrime 31 := by
  apply of_lucas_checks 31 3
    [2, 3, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

theorem prime_104471 : IsPrime 104471 := by
  apply of_lucas_checks 104471 11
    [2, 5, 31, 337]
  · decide +kernel
  · simp [prime_2, prime_5, prime_31, prime_337]

theorem prime_3969899 : IsPrime 3969899 := by
  apply of_lucas_checks 3969899 2
    [2, 19, 104471]
  · decide +kernel
  · simp [prime_2, prime_19, prime_104471]

theorem prime_1002328039319 : IsPrime 1002328039319 := by
  apply of_lucas_checks 1002328039319 19
    [2, 126241, 3969899]
  · decide +kernel
  · simp [prime_2, prime_126241, prime_3969899]

theorem prime_97 : IsPrime 97 := by
  apply of_lucas_checks 97 5
    [2, 2, 2, 2, 2, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_29 : IsPrime 29 := by
  apply of_lucas_checks 29 2
    [2, 2, 7]
  · decide +kernel
  · simp [prime_2, prime_7]

theorem prime_16879 : IsPrime 16879 := by
  apply of_lucas_checks 16879 3
    [2, 3, 29, 97]
  · decide +kernel
  · simp [prime_2, prime_3, prime_29, prime_97]

theorem prime_1297 : IsPrime 1297 := by
  apply of_lucas_checks 1297 10
    [2, 2, 2, 2, 3, 3, 3, 3]
  · decide +kernel
  · simp [prime_2, prime_3]

theorem prime_41 : IsPrime 41 := by
  apply of_lucas_checks 41 6
    [2, 2, 2, 5]
  · decide +kernel
  · simp [prime_2, prime_5]

theorem prime_155317 : IsPrime 155317 := by
  apply of_lucas_checks 155317 5
    [2, 2, 3, 7, 43, 43]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7, prime_43]

theorem prime_191039911 : IsPrime 191039911 := by
  apply of_lucas_checks 191039911 3
    [2, 3, 5, 41, 155317]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5, prime_41, prime_155317]

theorem prime_151 : IsPrime 151 := by
  apply of_lucas_checks 151 6
    [2, 3, 5, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

theorem prime_1511 : IsPrime 1511 := by
  apply of_lucas_checks 1511 11
    [2, 5, 151]
  · decide +kernel
  · simp [prime_2, prime_5, prime_151]

theorem prime_3023 : IsPrime 3023 := by
  apply of_lucas_checks 3023 5
    [2, 1511]
  · decide +kernel
  · simp [prime_2, prime_1511]

theorem prime_127 : IsPrime 127 := by
  apply of_lucas_checks 127 3
    [2, 3, 3, 7]
  · decide +kernel
  · simp [prime_2, prime_3, prime_7]

theorem prime_208150935158385979 : IsPrime 208150935158385979 := by
  apply of_lucas_checks 208150935158385979 2
    [2, 3, 11, 43, 127, 3023, 191039911]
  · decide +kernel
  · simp [prime_2, prime_3, prime_11, prime_43, prime_127, prime_3023, prime_191039911]

theorem prime_2624747550333869278416773953 : IsPrime 2624747550333869278416773953 := by
  apply of_lucas_checks 2624747550333869278416773953 7
    [2, 2, 2, 2, 2, 2, 3, 3, 1297, 16879, 208150935158385979]
  · decide +kernel
  · simp [prime_2, prime_3, prime_1297, prime_16879, prime_208150935158385979]

theorem prime_373 : IsPrime 373 := by
  apply of_lucas_checks 373 2
    [2, 2, 3, 31]
  · decide +kernel
  · simp [prime_2, prime_3, prime_31]

theorem prime_311 : IsPrime 311 := by
  apply of_lucas_checks 311 17
    [2, 5, 31]
  · decide +kernel
  · simp [prime_2, prime_5, prime_31]

theorem prime_311245691 : IsPrime 311245691 := by
  apply of_lucas_checks 311245691 2
    [2, 5, 7, 17, 29, 29, 311]
  · decide +kernel
  · simp [prime_2, prime_5, prime_7, prime_17, prime_29, prime_311]

theorem prime_622491383 : IsPrime 622491383 := by
  apply of_lucas_checks 622491383 5
    [2, 311245691]
  · decide +kernel
  · simp [prime_2, prime_311245691]

theorem prime_1201 : IsPrime 1201 := by
  apply of_lucas_checks 1201 11
    [2, 2, 2, 2, 3, 5, 5]
  · decide +kernel
  · simp [prime_2, prime_3, prime_5]

theorem prime_229 : IsPrime 229 := by
  apply of_lucas_checks 229 6
    [2, 2, 3, 19]
  · decide +kernel
  · simp [prime_2, prime_3, prime_19]

theorem prime_9350987 : IsPrime 9350987 := by
  apply of_lucas_checks 9350987 2
    [2, 17, 229, 1201]
  · decide +kernel
  · simp [prime_2, prime_17, prime_229, prime_1201]

theorem prime_187019741 : IsPrime 187019741 := by
  apply of_lucas_checks 187019741 2
    [2, 2, 5, 9350987]
  · decide +kernel
  · simp [prime_2, prime_5, prime_9350987]

theorem prime_order : IsPrime domain.n := by
  apply of_lucas_checks 115792089210356248762697446949407573529996955224135760342422259061068512044369 7
    [2, 2, 2, 2, 3, 71, 131, 373, 3407, 17449, 38189, 187019741, 622491383, 1002328039319, 2624747550333869278416773953]
  · decide +kernel
  · simp [prime_2, prime_3, prime_71, prime_131, prime_373, prime_3407, prime_17449, prime_38189, prime_187019741, prime_622491383, prime_1002328039319, prime_2624747550333869278416773953]

end P256.Proofs.Scalar
