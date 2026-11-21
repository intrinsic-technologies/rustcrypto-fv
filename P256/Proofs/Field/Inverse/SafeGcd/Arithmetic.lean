import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Convergence

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd

theorem divsteps_591_converges {g : Nat} (hg : g < P256.Spec.Operations.domain.p) :
    (divsteps 591 ⟨1, P256.Spec.Operations.domain.p, g⟩).g = 0 := by
  have odd : (P256.Spec.Operations.domain.p : Int) % 2=1 := by decide +kernel
  apply Contraction.divsteps_terminate 591 odd
    (t := (111/100)*((P256.Spec.Operations.domain.p : Int) : Rat))
  · apply Contraction.Region.positive 0
    simp only [Rat.pow_zero, Rat.one_mul]
    apply Contraction.positive_initial
    · exact Rat.intCast_nonneg.mpr (by omega)
    · exact Rat.intCast_le_intCast.mpr (by omega)
  · change Contraction.Budget 1 ((111/100)*((P256.Spec.Operations.domain.p : Int) : Rat))
    unfold Contraction.Budget
    decide +kernel
  · exact Contraction.tail_lt_one

theorem divsteps_591_unit {g : Nat} (positive : 0 < g)
    (bound : g < P256.Spec.Operations.domain.p) :
    (divsteps 591 ⟨1, P256.Spec.Operations.domain.p, g⟩).f.natAbs = 1 := by
  exact divsteps_terminal_unit 591 positive bound (divsteps_591_converges bound)

end P256.Proofs.Field.Inverse.SafeGcd
