import Init.Grind.Ring.Basic

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Lean.Grind

universe u

def naturalMultiple {G : Type u} [AddCommGroup G] (point : G) : Nat → G
  | 0 => 0
  | n + 1 => naturalMultiple point n + point

def integerMultiple {G : Type u} [AddCommGroup G] (point : G) : Int → G
  | .ofNat n => naturalMultiple point n
  | .negSucc n => -(naturalMultiple point (n + 1))

theorem integerMultiple_add_one {G : Type u} [AddCommGroup G] (point : G) (n : Int) :
    integerMultiple point (n + 1) = integerMultiple point n + point := by
  cases n with
  | ofNat n => rfl
  | negSucc n =>
    cases n with
    | zero =>
      change 0 = -(0 + point) + point
      rw [AddCommMonoid.zero_add, AddCommGroup.neg_add_cancel]
    | succ n =>
      have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he]
      change -(naturalMultiple point (n + 1)) =
        -(naturalMultiple point (n + 1) + point) + point
      rw [AddCommGroup.neg_add, AddCommMonoid.add_assoc,
        AddCommGroup.neg_add_cancel, AddCommMonoid.add_zero]

theorem integerMultiple_add {G : Type u} [AddCommGroup G] (point : G) (m n : Int) :
    integerMultiple point (m + n) = integerMultiple point m + integerMultiple point n := by
  have positive (k : Nat) : integerMultiple point (m + (k : Int)) =
      integerMultiple point m + integerMultiple point (k : Int) := by
    induction k with
    | zero => simp only [Int.natCast_zero, integerMultiple,
        naturalMultiple, AddCommMonoid.add_zero]
    | succ k ih =>
      rw [Int.natCast_add_one, ← Int.add_assoc, integerMultiple_add_one,
        integerMultiple_add_one, ih, AddCommMonoid.add_assoc]
  cases n with
  | ofNat n => exact positive n
  | negSucc n =>
    induction n with
    | zero =>
      apply (AddCommGroup.add_left_inj point).mp
      rw [← integerMultiple_add_one]
      have he : m + Int.negSucc 0 + 1 = m := by omega
      rw [he, AddCommMonoid.add_assoc, ← integerMultiple_add_one]
      change integerMultiple point m = integerMultiple point m + 0
      rw [AddCommMonoid.add_zero]
    | succ n ih =>
      apply (AddCommGroup.add_left_inj point).mp
      rw [← integerMultiple_add_one]
      have he : m + Int.negSucc (n + 1) + 1 = m + Int.negSucc n := by omega
      have hn : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he, AddCommMonoid.add_assoc, ← integerMultiple_add_one, hn]
      exact ih

theorem integerMultiple_twice {G : Type u} [AddCommGroup G] (point : G) (n : Int) :
    integerMultiple point (2 * n) = integerMultiple point n + integerMultiple point n := by
  rw [show 2 * n = n + n by omega, integerMultiple_add]

end P256.Proofs.Verifying.Combination.Algebra
