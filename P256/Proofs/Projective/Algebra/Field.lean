import P256.Spec.Operations
import P256.Proofs.Projective.Algebra.Field.Primality
import P256.Proofs.Projective.Algebra.Field.Fermat
import P256.Proofs.Projective.Algebra.Field.Power
import P256.Proofs.Projective.Algebra.Field.Certificate
import Init.GrindInstances.Ring.Fin
import Init.Grind.Ring.Field

set_option autoImplicit false

open P256.Proofs.Projective.Algebra.FieldArithmetic (pow_pred_prime_mod prime_p256)
open P256.Proofs.Projective.Algebra.FieldArithmetic (powMod_eq_pow_mod powMod_lt)

namespace P256.Proofs.Projective.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Fin.NatCast Fin.IntCast

abbrev Fp := Fin domain.p

instance : NeZero domain.p := ⟨by decide +kernel⟩

theorem modulus_pos : 0 < domain.p := by decide +kernel

theorem inverse_lt (x : Nat) : Curve.inverse domain.p x < domain.p :=
  powMod_lt _ _ _ modulus_pos

theorem inverse_zero : Curve.inverse domain.p 0 = 0 := by
  rw [Curve.inverse, powMod_eq_pow_mod, Nat.zero_pow (by decide +kernel), Nat.zero_mod]

theorem mul_inverse {x : Nat} (hx : 0 < x) (hlt : x < domain.p) :
    x * Curve.inverse domain.p x % domain.p = 1 := by
  have he : domain.p - 1 = (domain.p - 2) + 1 := by decide +kernel
  have hp := pow_pred_prime_mod domain.p x prime_p256
    (prime_p256.coprime_of_lt hx hlt)
  rw [he, Nat.pow_succ, Nat.mul_comm] at hp
  simpa only [Curve.inverse, powMod_eq_pow_mod, Nat.mul_mod_mod] using hp

def fieldInverse (x : Fp) : Fp := ⟨Curve.inverse domain.p x.val, inverse_lt x.val⟩

instance : Inv Fp := ⟨fieldInverse⟩
instance : Div Fp := ⟨fun x y => x * y⁻¹⟩

theorem fp_inv_zero : (0 : Fp)⁻¹ = 0 := by
  apply Fin.ext
  exact inverse_zero

theorem fp_mul_inv {x : Fp} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  apply Fin.ext
  change x.val * Curve.inverse domain.p x.val % domain.p = 1
  apply mul_inverse (by
    have : x.val ≠ 0 := fun h => hx (Fin.ext h)
    omega) x.isLt

theorem fp_inv_one : (1 : Fp)⁻¹ = 1 := by
  have h : (1 : Fp) ≠ 0 := by decide +kernel
  simpa only [Semiring.one_mul] using fp_mul_inv h

theorem fp_inv_ne_zero {x : Fp} (hx : x ≠ 0) : x⁻¹ ≠ 0 := by
  intro hi
  have h := fp_mul_inv hx
  rw [hi, Semiring.mul_zero] at h
  exact (by decide +kernel : (0 : Fp) ≠ 1) h

theorem fp_inv_inv (x : Fp) : x⁻¹⁻¹ = x := by
  by_cases hx : x = 0
  · rw [hx, fp_inv_zero, fp_inv_zero]
  · calc
      x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := (Semiring.one_mul _).symm
      _ = (x * x⁻¹) * x⁻¹⁻¹ := by rw [fp_mul_inv hx]
      _ = x * (x⁻¹ * x⁻¹⁻¹) := Semiring.mul_assoc _ _ _
      _ = x := by rw [fp_mul_inv (fp_inv_ne_zero hx), Semiring.mul_one]

def fpIntPow (x : Fp) : Int → Fp
  | .ofNat n => x ^ n
  | .negSucc n => (x ^ (n + 1))⁻¹

instance : HPow Fp Int Fp := ⟨fpIntPow⟩

instance : Field Fp where
  toCommRing := inferInstance
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := by decide +kernel
  inv_zero := fp_inv_zero
  mul_inv_cancel := fp_mul_inv
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg x n := by
    cases n with
    | ofNat n =>
      cases n with
      | zero => exact fp_inv_one.symm
      | succ n => rfl
    | negSucc n => exact (fp_inv_inv _).symm

theorem cast_inverse (x : Nat) :
    (Curve.inverse domain.p x : Fp) = (x : Fp)⁻¹ := by
  apply Fin.ext
  change Curve.inverse domain.p x % domain.p =
    Curve.inverse domain.p (x % domain.p)
  rw [Nat.mod_eq_of_lt (inverse_lt x)]
  simp only [Curve.inverse, powMod_eq_pow_mod]
  exact Nat.pow_mod _ _ _

theorem cast_fieldSub (x y : Nat) :
    (Curve.fieldSub domain.p x y : Fp) = (x : Fp) - (y : Fp) := by
  apply Fin.ext
  change ((x % domain.p + domain.p - y % domain.p) %
    domain.p) % domain.p =
      (domain.p - y % domain.p + x % domain.p) %
        domain.p
  rw [Nat.mod_mod]
  congr 1
  have hy : y % domain.p < domain.p := Nat.mod_lt _ modulus_pos
  omega

theorem coefficient_a : (domain.a : Fp) = -3 := by decide +kernel

theorem cubic_ne_zero (x : Fp) : x * x * x - 3 * x + (domain.b : Fp) ≠ 0 := by
  intro h
  have hx : (x.val : Fp) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  have hc : ((x.val * x.val * x.val + domain.a * x.val + domain.b : Nat) : Fp) = 0 := by
    simp only [Semiring.natCast_add, Semiring.natCast_mul, hx, coefficient_a]
    grind only
  have hz : FieldArithmetic.cubicValue x.val = 0 :=
    (IsCharP.natCast_eq_zero_iff (α := Fp) domain.p _).mp hc
  exact FieldArithmetic.no_root_of_fermat x.val
    (FieldArithmetic.pow_prime_mod domain.p x.val prime_p256) hz

end P256.Proofs.Projective.Algebra
