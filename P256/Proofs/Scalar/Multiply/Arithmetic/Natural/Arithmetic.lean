import P256.Proofs.Scalar.Multiply.Arithmetic.Support

set_option autoImplicit false

namespace P256.Proofs.Scalar.Multiply.Arithmetic.Natural



def barrettMu : Nat :=
  0x100000000fffffffffffffffeffffffff43190552df1a6c21012ffd85eedf9bfe

def barrettQuotient (x : Nat) : Nat := x / 2^192 * barrettMu / 2^320

def barrettRemainder (x : Nat) : Nat := x - barrettQuotient x * P256.Spec.Operations.domain.n

def subtractOrder (x : Nat) : Nat :=
  if x < P256.Spec.Operations.domain.n then x else x - P256.Spec.Operations.domain.n

set_option exponentiation.threshold 512 in
theorem barrettQuotient_le (x : Nat) :
    barrettQuotient x * P256.Spec.Operations.domain.n ≤ x := by
  have hd := Nat.mod_add_div x (2^192)
  have hq := Nat.mod_add_div (x / 2^192 * barrettMu) (2^320)
  change x % 2^192 + 2^192 * (x / 2^192) = x at hd
  dsimp only [barrettQuotient, barrettMu, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

set_option exponentiation.threshold 512 in
theorem barrettRemainder_lt {x : Nat} (bound : x < 2^512) :
    barrettRemainder x < 2 * P256.Spec.Operations.domain.n := by
  have hd := Nat.mod_add_div x (2^192)
  have hr := Nat.mod_lt x (by decide : 0 < 2^192)
  have hq := Nat.mod_add_div (x / 2^192 * barrettMu) (2^320)
  have hqr := Nat.mod_lt (x / 2^192 * barrettMu) (by decide : 0 < 2^320)
  have below := barrettQuotient_le x
  dsimp only [barrettRemainder, barrettQuotient, barrettMu, P256.Spec.Operations.domain, Standards.NIST.EllipticCurves.P256.domain] at *
  omega

theorem barrettRemainder_mod (x : Nat) :
    barrettRemainder x % P256.Spec.Operations.domain.n = x % P256.Spec.Operations.domain.n := by
  unfold barrettRemainder
  rw [Nat.mul_comm]
  exact Nat.sub_mul_mod (by simpa only [Nat.mul_comm] using barrettQuotient_le x)

theorem subtractOrder_eq_mod {x : Nat} (bound : x < 2 * P256.Spec.Operations.domain.n) :
    subtractOrder x = x % P256.Spec.Operations.domain.n := by
  unfold subtractOrder
  split
  · exact (Nat.mod_eq_of_lt ‹x < P256.Spec.Operations.domain.n›).symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem barrett_correct {x : Nat} (bound : x < 2^512) :
    subtractOrder (barrettRemainder x) = x % P256.Spec.Operations.domain.n := by
  rw [subtractOrder_eq_mod (barrettRemainder_lt bound), barrettRemainder_mod]

end P256.Proofs.Scalar.Multiply.Arithmetic.Natural
