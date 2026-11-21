import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Convergence
import P256.Proofs.Scalar.Primality

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse

open P256.Proofs.Field.Inverse.SafeGcd

theorem divsteps_591_converges {g : Nat} (hg : g < P256.Spec.Operations.domain.n) :
    (divsteps 591 ⟨1, P256.Spec.Operations.domain.n, g⟩).g = 0 := by
  have odd : (P256.Spec.Operations.domain.n : Int) % 2=1 := by decide +kernel
  apply Contraction.divsteps_terminate 591 odd
    (t := (111/100)*((P256.Spec.Operations.domain.n : Int) : Rat))
  · apply Contraction.Region.positive 0
    simp only [Rat.pow_zero, Rat.one_mul]
    apply Contraction.positive_initial
    · exact Rat.intCast_nonneg.mpr (by omega)
    · exact Rat.intCast_le_intCast.mpr (by omega)
  · change Contraction.Budget 1 ((111/100)*((P256.Spec.Operations.domain.n : Int) : Rat))
    unfold Contraction.Budget
    decide +kernel
  · decide +kernel

theorem divsteps_591_unit {g : Nat} (positive : 0 < g)
    (bound : g < P256.Spec.Operations.domain.n) :
    (divsteps 591 ⟨1, P256.Spec.Operations.domain.n, g⟩).f.natAbs = 1 := by
  rw [divsteps_terminal_natAbs 591 (by decide +kernel :
    (P256.Spec.Operations.domain.n : Int) % 2 = 1) (divsteps_591_converges bound),
    Int.gcd_natCast_natCast, Nat.gcd_comm]
  exact prime_order.coprime_of_lt positive bound

end P256.Proofs.Scalar.Inverse
