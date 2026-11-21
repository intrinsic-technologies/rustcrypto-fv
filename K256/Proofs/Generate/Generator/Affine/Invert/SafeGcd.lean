import K256.Proofs.Common.Field.Repr
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Convergence

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd

theorem divsteps_591_converges {g : Nat} (hg : g < K256.Proofs.Common.Field.modulus) :
    (divsteps 591 ⟨1, K256.Proofs.Common.Field.modulus, g⟩).g = 0 := by
  have odd : (K256.Proofs.Common.Field.modulus : Int) % 2=1 := by decide +kernel
  apply Contraction.divsteps_terminate 591 odd
    (t := (111/100)*((K256.Proofs.Common.Field.modulus : Int) : Rat))
  · apply Contraction.Region.positive 0
    simp only [Rat.pow_zero, Rat.one_mul]
    apply Contraction.positive_initial
    · exact Rat.intCast_nonneg.mpr (by omega)
    · exact Rat.intCast_le_intCast.mpr (by omega)
  · change Contraction.Budget 1 ((111/100)*((K256.Proofs.Common.Field.modulus : Int) : Rat))
    unfold Contraction.Budget
    decide +kernel
  · exact Contraction.tail_lt_one

theorem divsteps_591_unit {g : Nat} (positive : 0 < g)
    (bound : g < K256.Proofs.Common.Field.modulus) :
    (divsteps 591 ⟨1, K256.Proofs.Common.Field.modulus, g⟩).f.natAbs = 1 := by
  exact divsteps_terminal_unit 591 positive bound (divsteps_591_converges bound)

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd
