import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Common.Arithmetic.CubicNonzero.Primality
import K256.Proofs.Common.Arithmetic.CubicNonzero.Fermat
import K256.Proofs.Common.Field.PowMod
import Init.GrindInstances.Ring.Fin
import Init.Grind.Ring.Field

set_option autoImplicit false

open K256.Proofs.Common.Arithmetic.CubicNonzero (pow_pred_prime_mod prime_secp256k1)
open K256.Proofs.Common.Field.PowMod (powMod_eq_pow_mod)

namespace K256.Proofs.Generate.Curve.Group.CurveArithmetic

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Lean.Grind Fin.NatCast Fin.IntCast

abbrev Fp := Fin domain.p

instance : NeZero domain.p := ⟨by decide +kernel⟩

theorem modulus_pos : 0 < domain.p := by decide +kernel

theorem inverse_lt (x : Nat) : Curve.inverse domain.p x < domain.p := by
  rw [Curve.inverse, powMod_eq_pow_mod]
  exact Nat.mod_lt _ modulus_pos

theorem inverse_zero : Curve.inverse domain.p 0 = 0 := by
  rw [Curve.inverse, powMod_eq_pow_mod, Nat.zero_pow (by decide +kernel), Nat.zero_mod]

theorem mul_inverse {x : Nat} (hx : 0 < x) (hlt : x < domain.p) :
    x * Curve.inverse domain.p x % domain.p = 1 := by
  have he : domain.p - 1 = (domain.p - 2) + 1 := by decide +kernel
  have hp := pow_pred_prime_mod domain.p x prime_secp256k1
    (prime_secp256k1.coprime_of_lt hx hlt)
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

end K256.Proofs.Generate.Curve.Group.CurveArithmetic
