import K256.Proofs.Common.Arithmetic.CubicNonzero.Primality.Lucas
import K256.Proofs.Common.Field.PowMod
import Standards.SECG.DomainParameters.Secp256k1

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve

open K256.Proofs.Common.Arithmetic.CubicNonzero
open K256.Proofs.Common.Field.PowMod (powMod_eq_pow_mod)
open Standards.SECG.ECC.Curve Standards.SECG.DomainParameters.Secp256k1

private def certifyPrimes (known : List Nat) : List (Nat × Nat × List Nat) → List Nat
  | [] => known
  | (p, a, factors) :: rest =>
    if 2 ≤ p ∧ factors.foldr (· * ·) 1 = p - 1 ∧ powMod p a (p - 1) = 1 ∧
        (factors.all fun q => known.contains q &&
          decide (Nat.Coprime (powMod p a ((p - 1) / q) + p - 1) p)) = true then
      certifyPrimes (p :: known) rest
    else []

private theorem certifyPrimes_sound (known : List Nat) (hn : ∀ p ∈ known, IsPrime p)
    (rows : List (Nat × Nat × List Nat)) : ∀ p ∈ certifyPrimes known rows, IsPrime p := by
  induction rows generalizing known with
  | nil => exact hn
  | cons row rest ih =>
    obtain ⟨p, a, factors⟩ := row
    rw [certifyPrimes]
    split
    · rename_i h
      apply ih
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · apply lucas_primality q a factors h.1 h.2.1
        · intro r hr
          exact hn _ (by simpa only [List.contains_iff_mem] using
            (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h.2.2.2 r hr)).1)
        · rw [← powMod_eq_pow_mod]
          exact h.2.2.1
        · intro r hr
          rw [← powMod_eq_pow_mod]
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h.2.2.2 r hr)).2
      · exact hn _ hmem
    · simp

private def orderCertificate : List (Nat × Nat × List Nat) :=
  [(2, 1, []),
   (3, 2, [2]),
   (5, 2, [2, 2]),
   (7, 3, [2, 3]),
   (11, 2, [2, 5]),
   (13, 2, [2, 2, 3]),
   (17, 3, [2, 2, 2, 2]),
   (19, 2, [2, 3, 3]),
   (23, 5, [2, 11]),
   (29, 2, [2, 2, 7]),
   (37, 2, [2, 2, 3, 3]),
   (41, 6, [2, 2, 2, 5]),
   (59, 2, [2, 29]),
   (67, 2, [2, 3, 11]),
   (73, 5, [2, 2, 2, 3, 3]),
   (97, 5, [2, 2, 2, 2, 2, 3]),
   (109, 6, [2, 2, 3, 3, 3]),
   (113, 3, [2, 2, 2, 2, 7]),
   (149, 2, [2, 2, 37]),
   (199, 3, [2, 3, 3, 11]),
   (293, 2, [2, 2, 73]),
   (461, 2, [2, 2, 5, 23]),
   (631, 3, [2, 3, 3, 5, 7]),
   (797, 2, [2, 2, 199]),
   (1409, 3, [2, 2, 2, 2, 2, 2, 2, 11]),
   (1871, 14, [2, 5, 11, 17]),
   (2011, 3, [2, 3, 5, 67]),
   (2731, 3, [2, 3, 5, 7, 13]),
   (2861, 2, [2, 2, 5, 11, 13]),
   (4051, 10, [2, 3, 3, 3, 3, 5, 5]),
   (9349, 2, [2, 2, 3, 19, 41]),
   (16699, 3, [2, 3, 11, 11, 23]),
   (28181, 2, [2, 2, 5, 1409]),
   (85831, 3, [2, 3, 5, 2861]),
   (120233, 3, [2, 2, 2, 7, 19, 113]),
   (305873, 3, [2, 2, 2, 2, 7, 2731]),
   (1627771, 3, [2, 3, 5, 29, 1871]),
   (4681609, 23, [2, 2, 2, 3, 97, 2011]),
   (44706919, 6, [2, 3, 797, 9349]),
   (545358713, 5, [2, 2, 2, 41, 59, 28181]),
   (297159362677, 2, [2, 2, 3, 3, 11, 461, 1627771]),
   (107361793816595537, 3, [2, 2, 2, 2, 16699, 85831, 4681609]),
   (174723607534414371449, 3, [2, 2, 2, 17, 59, 4051, 120233, 44706919]),
   (29047611873442575647497758179, 2, [2, 293, 305873, 545358713, 297159362677]),
   (341948486974166000522343609283189, 2, [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]),
   (115792089237316195423570985008687907852837564279074904382605163141518161494337, 7, [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189])]

theorem order_prime : IsPrime domain.n :=
  certifyPrimes_sound [] (by simp) orderCertificate domain.n (by decide +kernel)

end K256.Proofs.Generate.Curve
