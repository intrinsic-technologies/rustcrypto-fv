import Init

set_option autoImplicit false

namespace P256.Proofs.Projective.Algebra.FieldArithmetic

structure Quadratic where
  constant : Nat
  linear : Nat
  quadratic : Nat
  deriving DecidableEq

namespace Quadratic

def eval (p x : Nat) (q : Quadratic) : Nat :=
  (q.constant + q.linear * x + q.quadratic * x * x) % p

def one : Quadratic := ⟨1, 0, 0⟩

def indeterminate : Quadratic := ⟨0, 1, 0⟩

def add (p : Nat) (q r : Quadratic) : Quadratic :=
  ⟨(q.constant + r.constant) % p, (q.linear + r.linear) % p,
    (q.quadratic + r.quadratic) % p⟩

def mul (p c d : Nat) (q r : Quadratic) : Quadratic :=
  let cubic := q.linear * r.quadratic + q.quadratic * r.linear
  let quartic := q.quadratic * r.quadratic
  ⟨(q.constant * r.constant + c * cubic) % p,
    (q.constant * r.linear + q.linear * r.constant + d * cubic + c * quartic) % p,
    (q.constant * r.quadratic + q.linear * r.linear + q.quadratic * r.constant +
      d * quartic) % p⟩

theorem eval_one (p x : Nat) : eval p x one = 1 % p := by
  simp [eval, one]

theorem eval_indeterminate (p x : Nat) : eval p x indeterminate = x % p := by
  simp [eval, indeterminate]

theorem eval_modCoeffs (p x a b c : Nat) :
    eval p x ⟨a % p, b % p, c % p⟩ = (a + b * x + c * x * x) % p := by
  simp [eval, Nat.add_mod, Nat.mul_mod]

theorem eval_add (p x : Nat) (q r : Quadratic) :
    eval p x (add p q r) = (eval p x q + eval p x r) % p := by
  dsimp only [add]
  rw [eval_modCoeffs]
  simp only [eval, ← Nat.add_mod]
  congr 1
  grind

theorem eval_mul (p c d x : Nat) (q r : Quadratic)
    (hx : x * x * x % p = (c + d * x) % p) :
    eval p x (mul p c d q r) = eval p x q * eval p x r % p := by
  dsimp only [mul]
  rw [eval_modCoeffs]
  simp only [eval, ← Nat.mul_mod]
  let base := q.constant * r.constant +
    (q.constant * r.linear + q.linear * r.constant) * x +
    (q.constant * r.quadratic + q.linear * r.linear + q.quadratic * r.constant) * x * x
  let cubic := q.linear * r.quadratic + q.quadratic * r.linear
  let quartic := q.quadratic * r.quadratic
  calc
    _ = (base + cubic * (c + d * x) + quartic * x * (c + d * x)) % p := by
      congr 1
      dsimp only [base, cubic, quartic]
      grind only
    _ = (base + cubic * (x * x * x) + quartic * x * (x * x * x)) % p := by
      have hmul (a : Nat) :
          a * (c + d * x) % p = a * (x * x * x) % p := by
        rw [Nat.mul_mod a (c + d * x), Nat.mul_mod a (x * x * x), hx]
      calc
        _ = ((base + cubic * (c + d * x)) % p +
          (quartic * x * (c + d * x)) % p) % p := Nat.add_mod _ _ _
        _ = ((base + cubic * (x * x * x)) % p +
          (quartic * x * (x * x * x)) % p) % p := by
          rw [Nat.add_mod base, Nat.add_mod base, hmul cubic, hmul (quartic * x)]
        _ = _ := (Nat.add_mod _ _ _).symm
    _ = _ := by
      congr 1
      dsimp only [base, cubic, quartic]
      grind only

def pow (p c d : Nat) (q : Quadratic) (e : Nat) : Quadratic :=
  if e = 0 then one else
    let half := pow p c d q (e / 2)
    let square := mul p c d half half
    if e % 2 = 0 then square else mul p c d square q
termination_by e

theorem eval_pow (p c d x : Nat) (q : Quadratic) (e : Nat)
    (hx : x * x * x % p = (c + d * x) % p) :
    eval p x (pow p c d q e) = eval p x q ^ e % p := by
  induction e using Nat.strongRecOn with
  | ind e ih =>
    rw [pow]
    split
    · rename_i he
      rw [eval_one, he, Nat.pow_zero]
    · rename_i he
      have hi := ih (e / 2) (by omega)
      split
      · rename_i hbit
        rw [eval_mul p c d x _ _ hx, hi, ← Nat.mul_mod, ← Nat.pow_add]
        congr 2
        omega
      · rename_i hbit
        rw [eval_mul p c d x _ _ hx, eval_mul p c d x _ _ hx, hi,
          ← Nat.mul_mod, Nat.mod_mul_mod, ← Nat.pow_add, ← Nat.pow_succ]
        congr 2
        omega

end Quadratic
end P256.Proofs.Projective.Algebra.FieldArithmetic
