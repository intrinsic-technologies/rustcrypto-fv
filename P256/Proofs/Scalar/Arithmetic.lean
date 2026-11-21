import P256.Proofs.Scalar.Primality
import P256.Proofs.Projective.Algebra.Field.Fermat
import P256.Proofs.Projective.Algebra.Field.Power

set_option autoImplicit false

open P256.Proofs.Projective.Algebra.FieldArithmetic (pow_pred_prime_mod coprime_mul_mod_injective)
open P256.Proofs.Projective.Algebra.FieldArithmetic (powMod_eq_pow_mod powMod_lt)

namespace P256.Proofs.Scalar

open P256.Spec.Operations Standards.SECG.ECC

theorem order_pos : 0 < domain.n := by decide +kernel

theorem order_lt_radix : domain.n < 2^256 := by decide +kernel

theorem inverse_lt (a : Nat) : Curve.inverse domain.n a < domain.n :=
  powMod_lt _ _ _ order_pos

theorem mul_inverse {a : Nat} (positive : 0 < a) (canonical : a < domain.n) :
    a * Curve.inverse domain.n a % domain.n = 1 := by
  have exponent : domain.n - 1 = (domain.n - 2) + 1 := by
    decide +kernel
  have inverse := pow_pred_prime_mod domain.n a
    prime_order
    (prime_order.coprime_of_lt positive canonical)
  rw [exponent, Nat.pow_succ, Nat.mul_comm] at inverse
  simpa only [Curve.inverse, powMod_eq_pow_mod, Nat.mul_mod_mod] using inverse

theorem inverse_unique {a result : Nat} (positive : 0 < a)
    (canonical : a < domain.n) (resultBound : result < domain.n)
    (product : result * a % domain.n = 1) :
    result = Curve.inverse domain.n a := by
  apply coprime_mul_mod_injective
    (prime_order.coprime_of_lt positive canonical)
    resultBound (inverse_lt a)
  exact (Nat.mul_comm a result ▸ product).trans (mul_inverse positive canonical).symm

theorem mod_order_eq_sub {a : Nat} (bound : a < 2^256) :
    a % domain.n = if a < domain.n then a else a - domain.n := by
  split
  · exact Nat.mod_eq_of_lt ‹a < domain.n›
  · have half : 2^256 < 2 * domain.n := by decide +kernel
    have small : a - domain.n < domain.n := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt small]

end P256.Proofs.Scalar
