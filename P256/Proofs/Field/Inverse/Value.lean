import P256.Proofs.Field.Inverse.Interface
import P256.Proofs.Field.Montgomery.Arithmetic
import P256.Proofs.Projective.Algebra.Field

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Operations (domain)
open P256.Proofs.Projective.Algebra (modulus_pos inverse_lt mul_inverse)
open P256.Proofs.Projective.Algebra.FieldArithmetic (coprime_mul_mod_injective prime_p256)
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC
open X86.Machine

def AdjustedInverse (argument result : Nat) : Prop :=
  result < domain.p ∧ result * argument % domain.p = 2^512 % domain.p

theorem montgomery_input_positive {z : Nat} (bound : z < domain.p)
    (nonzero : z ≠ 0) : 0 < z * 2^256 % domain.p := by
  have hne : z * 2^256 % domain.p ≠ 0 := by
    intro hz
    apply nonzero
    have h := congrArg (fun n => n * Montgomery.radixInverse % domain.p) hz
    simpa only [Nat.mod_mul_mod, Nat.mul_assoc,
      Nat.mul_mod _ (2^256 * Montgomery.radixInverse), Montgomery.radix_mul_inverse,
      Nat.mul_one, Nat.mod_mod, Nat.zero_mul, Nat.zero_mod, Nat.mod_eq_of_lt bound] using h
  omega

set_option exponentiation.threshold 512 in
theorem montgomery_inverse_adjusted {z : Nat} (bound : z < domain.p)
    (nonzero : z ≠ 0) :
    AdjustedInverse (z * 2^256 % domain.p)
      (Curve.inverse domain.p z * 2^256 % domain.p) := by
  refine ⟨Nat.mod_lt _ modulus_pos, ?_⟩
  have hinv := mul_inverse (show 0 < z by omega) bound
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod]
  calc
    (Curve.inverse domain.p z * 2^256) * (z * 2^256) % domain.p =
        (z * Curve.inverse domain.p z) * (2^256 * 2^256) % domain.p := by
      congr 1
      ac_rfl
    _ = 2^512 % domain.p := by
      rw [Nat.mul_mod, hinv, Nat.one_mul, Nat.mod_mod]

theorem adjustedInverse_unique {a b c : Nat} (positive : 0 < a)
    (bound : a < domain.p) (left : AdjustedInverse a b)
    (right : AdjustedInverse a c) : b = c := by
  apply coprime_mul_mod_injective (prime_p256.coprime_of_lt positive bound) left.1 right.1
  simpa only [Nat.mul_comm] using left.2.trans right.2.symm

theorem montgomery_result {t : RamState} {address : BitVec 64} {z result : Nat}
    (bound : z < domain.p) (nonzero : z ≠ 0)
    (output : Nat256At t address result)
    (inverse : AdjustedInverse (z * 2^256 % domain.p) result) :
    MontgomeryAt t address (Curve.inverse domain.p z) := by
  have hresult := adjustedInverse_unique (montgomery_input_positive bound nonzero)
    (Nat.mod_lt _ modulus_pos) inverse (montgomery_inverse_adjusted bound nonzero)
  exact ⟨inverse_lt z, hresult ▸ output⟩

end P256.Proofs.Field.Inverse
