import P256.Proofs.Sec1.SquareRoot.Exponent.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec

theorem exponent_prefix_step (exponent remaining : Nat) :
    exponent / 16 ^ (remaining + 1) * 16 + exponent / 16 ^ remaining % 16 =
      exponent / 16 ^ remaining := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

theorem sqrtExponent_lt : sqrtExponent < 16 ^ 64 := by decide +kernel

theorem sqrtExponent_initial_prefix : sqrtExponent / 16 ^ 64 = 0 :=
  Nat.div_eq_of_lt sqrtExponent_lt

theorem exponent_prefix_after_square (x n : Nat) :
    (x ^ (sqrtExponent / 16 ^ (n + 1)) % P256.Spec.Operations.domain.p) ^ 16 %
      P256.Spec.Operations.domain.p =
      x ^ (sqrtExponent / 16 ^ (n + 1) * 16) % P256.Spec.Operations.domain.p := by
  rw [← Nat.pow_mod, ← Nat.pow_mul]

theorem exponent_prefix_after_multiply (x n : Nat) :
    x ^ (sqrtExponent / 16 ^ (n + 1) * 16) % P256.Spec.Operations.domain.p *
      (x ^ (sqrtExponent / 16 ^ n % 16) % P256.Spec.Operations.domain.p) %
      P256.Spec.Operations.domain.p =
      x ^ (sqrtExponent / 16 ^ n) % P256.Spec.Operations.domain.p := by
  rw [← Nat.mul_mod, ← Nat.pow_add, exponent_prefix_step]

theorem sqrtExponent_digit (n : Nat) (hn : n < 64) :
    (((BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (n / 16)))) >>> (4 * (n % 16))).setWidth 32 &&&
      (if n = 63 then 3 else 15)) = BitVec.ofNat 32 (sqrtExponent / 16 ^ n % 16) := by
  have h : ∀ i : Fin 64,
      (((BitVec.ofNat 64 (sqrtExponent / 2 ^ (64 * (i.val / 16)))) >>>
        (4 * (i.val % 16))).setWidth 32 &&& (if i.val = 63 then 3 else 15)) =
          BitVec.ofNat 32 (sqrtExponent / 16 ^ i.val % 16) := by
    decide +kernel
  exact h ⟨n, hn⟩

end P256.Proofs.Sec1.SquareRoot
