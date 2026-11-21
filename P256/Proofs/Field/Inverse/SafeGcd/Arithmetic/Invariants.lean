import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Model
import P256.Proofs.Projective.Algebra.Field.Primality

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd

theorem divstep_odd {s : DivState} (odd : s.f % 2 = 1) :
    (divstep s).f % 2 = 1 := by
  dsimp only [divstep]
  split
  · exact odd
  · split
    · change s.g % 2 = 1
      omega
    · exact odd

theorem divsteps_odd (n : Nat) {s : DivState} (odd : s.f % 2 = 1) :
    (divsteps n s).f % 2 = 1 := by
  induction n generalizing s with
  | zero => exact odd
  | succ n ih => exact ih (divstep_odd odd)

theorem divsteps_add (n k : Nat) (s : DivState) :
    divsteps (n + k) s = divsteps k (divsteps n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add, divsteps]
  | succ n ih =>
    simpa only [Nat.succ_add, divsteps] using ih (divstep s)

theorem divsteps_zero (n : Nat) {s : DivState} (zero : s.g = 0) :
    (divsteps n s).g = 0 := by
  induction n generalizing s with
  | zero => exact zero
  | succ n ih =>
    apply ih
    simp [divstep, zero]

theorem gcd_two_of_odd {f : Int} (odd : f % 2 = 1) : Int.gcd f 2 = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hf hc
  have hd : c ∣ f - 2 * (f / 2) := Int.dvd_sub hf (Int.dvd_trans hc (Int.dvd_mul_right 2 _))
  have heq : f - 2 * (f / 2) = 1 := by omega
  rwa [heq] at hd

theorem gcd_half {f g : Int} (odd : f % 2 = 1) (even : g % 2 = 0) :
    Int.gcd f (g / 2) = Int.gcd f g := by
  have heq : 2 * (g / 2) = g := by omega
  have h := Int.gcd_mul_right_right_of_gcd_eq_one (k := g / 2) (gcd_two_of_odd odd)
  rw [heq] at h
  exact h.symm

theorem divstep_gcd {s : DivState} (odd : s.f % 2 = 1) :
    Int.gcd (divstep s).f (divstep s).g = Int.gcd s.f s.g := by
  dsimp only [divstep]
  split
  · rename_i even
    exact gcd_half odd even
  · rename_i not_even
    have oddg : s.g % 2 = 1 := by omega
    split
    · rw [gcd_half oddg (by omega), Int.gcd_self_sub_right, Int.gcd_comm]
    · rw [gcd_half odd (by omega), Int.gcd_add_self_right]

theorem divsteps_gcd (n : Nat) {s : DivState} (odd : s.f % 2 = 1) :
    Int.gcd (divsteps n s).f (divsteps n s).g = Int.gcd s.f s.g := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    exact (ih (divstep_odd odd)).trans (divstep_gcd odd)

theorem divsteps_terminal_natAbs (n : Nat) {s : DivState}
    (odd : s.f % 2 = 1) (terminal : (divsteps n s).g = 0) :
    (divsteps n s).f.natAbs = Int.gcd s.f s.g := by
  have h := divsteps_gcd n odd
  simpa only [terminal, Int.gcd_zero] using h

theorem divsteps_terminal_unit (n : Nat) {g : Nat}
    (positive : 0 < g) (bound : g < P256.Spec.Operations.domain.p)
    (terminal : (divsteps n ⟨1, P256.Spec.Operations.domain.p, g⟩).g = 0) :
    (divsteps n ⟨1, P256.Spec.Operations.domain.p, g⟩).f.natAbs = 1 := by
  have odd : (P256.Spec.Operations.domain.p : Int) % 2 = 1 := by decide +kernel
  rw [divsteps_terminal_natAbs n odd terminal, Int.gcd_natCast_natCast, Nat.gcd_comm]
  exact P256.Proofs.Projective.Algebra.FieldArithmetic.prime_p256.coprime_of_lt positive bound

end P256.Proofs.Field.Inverse.SafeGcd
