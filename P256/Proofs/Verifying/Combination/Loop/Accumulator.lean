import P256.Proofs.Verifying.Combination.Algebra.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop

open P256.Proofs.Projective P256.Proofs.Program
open Algebra Table

theorem pairDigits_drop (xs ys : List Int) (k : Nat) :
    (pairDigits xs ys).drop k = pairDigits (xs.drop k) (ys.drop k) := by
  induction k generalizing xs ys with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp only [pairDigits, List.drop_nil]
      | cons y ys => simpa only [pairDigits, List.drop_succ_cons, List.drop_nil] using ih [] ys
    | cons x xs =>
      cases ys with
      | nil => simpa only [pairDigits, List.drop_succ_cons, List.drop_nil] using ih xs []
      | cons y ys => simpa only [pairDigits, List.drop_succ_cons] using ih xs ys

theorem pairDigits_head (xs ys : List Int) (h : 0 < max xs.length ys.length) :
    pairDigits xs ys = (xs.headD 0, ys.headD 0) :: pairDigits xs.tail ys.tail := by
  cases xs <;> cases ys <;> simp_all [pairDigits]

def remainingAccumulator (p q : Projective) (u v k : Nat) : Projective :=
  accumulator (oddTable p) (oddTable q) ((pairDigits (Naf.digits u) (Naf.digits v)).drop k)

theorem remainingAccumulator_initial (p q : Projective) (u v : Nat) :
    remainingAccumulator p q u v (max (Naf.digits u).length (Naf.digits v).length) =
      Projective.identity := by
  unfold remainingAccumulator
  rw [← (pairDigits_values (Naf.digits u) (Naf.digits v)).2.2, List.drop_length]
  rfl

theorem remainingAccumulator_zero (p q : Projective) (u v : Nat) :
    remainingAccumulator p q u v 0 = linearCombination p q u v := rfl

theorem remainingAccumulator_step (p q : Projective) (u v k : Nat)
    (h : k < max (Naf.digits u).length (Naf.digits v).length) :
    remainingAccumulator p q u v k =
      addDigit (oddTable q)
        (addDigit (oddTable p) (remainingAccumulator p q u v (k+1)).double
          (((Naf.digits u)[k]?).getD 0))
        (((Naf.digits v)[k]?).getD 0) := by
  unfold remainingAccumulator
  rw [pairDigits_drop, pairDigits_drop]
  have positive : 0 < max ((Naf.digits u).drop k).length ((Naf.digits v).drop k).length := by
    simp only [List.length_drop]
    omega
  rw [pairDigits_head _ _ positive]
  change addDigit _ (addDigit _ (accumulator _ _ _).double _) _ = _
  simp only [List.headD_eq_head?_getD, List.head?_drop, List.tail_drop]

end P256.Proofs.Verifying.Combination.Loop
