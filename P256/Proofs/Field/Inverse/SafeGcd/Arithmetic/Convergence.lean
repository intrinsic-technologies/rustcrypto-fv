import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Budget
import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Invariants

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Contraction

theorem divsteps_terminate (n : Nat) {s : DivState} {t : Rat}
    (odd : s.f % 2=1) (region : Region (s.f : Rat) (s.g : Rat) t s.delta)
    (budget : Budget s.delta t) (small : t*alpha^n < 1) :
    (divsteps n s).g=0 := by
  induction n generalizing s t with
  | zero =>
    have h := budget.one_le
    simp only [Rat.pow_zero, Rat.mul_one] at small
    exfalso
    grind only
  | succ n ih =>
    by_cases zero : (divstep s).g=0
    · exact divsteps_zero n zero
    · have ht : 0 ≤ t := Rat.le_trans (by decide) budget.one_le
      have hr := divstep_region region ht odd
      have hb := divstep_budget hr budget zero
      apply ih (divstep_odd odd) hr hb
      rw [Rat.pow_succ] at small
      have heq : (alpha*t)*alpha^n=t*(alpha^n*alpha) := by grind only
      rwa [heq]

end P256.Proofs.Field.Inverse.SafeGcd.Contraction
