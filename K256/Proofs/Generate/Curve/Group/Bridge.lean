import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Generate.Curve.Group.Field
import K256.Proofs.Generate.Curve.Group.Affine
import K256.Proofs.Generate.Curve.Group.PointLaws
import K256.Proofs.Common.Arithmetic.CubicNonzero

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 CurveArithmetic
open Lean.Grind Fin.NatCast Fin.IntCast

def encodePoint : Curve.Point → Affine.Point Fp
  | .infinity => .infinity
  | .affine x y => .affine (x : Fp) (y : Fp)

def decodePoint : Affine.Point Fp → Curve.Point
  | .infinity => .infinity
  | .affine x y => .affine x.val y.val

theorem cast_mod (x : Nat) : ((x % domain.p : Nat) : Fp) = (x : Fp) := by
  apply Fin.ext
  exact Nat.mod_mod _ _

theorem cast_eq_iff (x y : Nat) (hx : x < domain.p)
    (hy : y < domain.p) : (x : Fp) = (y : Fp) ↔ x = y := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change x % domain.p = y % domain.p at hv
    simpa only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using hv
  · exact congrArg (fun n : Nat => (n : Fp))

theorem cast_eq_zero_iff (x : Nat) : (x : Fp) = 0 ↔ x % domain.p = 0 := by
  exact Fin.ext_iff

theorem decode_encode (point : Curve.Point) (h : Curve.onCurve domain point = true) :
    decodePoint (encodePoint point) = point := by
  cases point with
  | infinity => rfl
  | affine x y =>
    simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    change Curve.Point.affine (x % domain.p) (y % domain.p) = _
    rw [Nat.mod_eq_of_lt h.1.1, Nat.mod_eq_of_lt h.1.2]

theorem encode_onCurve (point : Curve.Point) (h : Curve.onCurve domain point = true) :
    Affine.onCurve (domain.a : Fp) (domain.b : Fp) (encodePoint point) := by
  cases point with
  | infinity => trivial
  | affine x y =>
    simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    change (y : Fp) * (y : Fp) = (x : Fp) * (x : Fp) * (x : Fp) +
      (domain.a : Fp) * (x : Fp) + (domain.b : Fp)
    have he := congrArg (fun n : Nat => (n : Fp)) h.2
    simpa only [cast_mod, Semiring.natCast_mul, Semiring.natCast_add] using he

theorem decode_onCurve (point : Affine.Point Fp)
    (h : Affine.onCurve (domain.a : Fp) (domain.b : Fp) point) :
    Curve.onCurve domain (decodePoint point) = true := by
  cases point with
  | infinity => rfl
  | affine x y =>
    simp only [decodePoint, Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨x.isLt, y.isLt⟩, ?_⟩
    have he := congrArg Fin.val h
    change (y.val * y.val) % domain.p =
      (((x.val * x.val % domain.p) * x.val % domain.p +
        (domain.a % domain.p * x.val) % domain.p) %
          domain.p + domain.b % domain.p) % domain.p at he
    simpa only [Nat.mod_mul_mod, Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_mod_mul_left,
      Nat.mul_mod_mod] using he

theorem encode_add (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) :
    encodePoint (Curve.add domain p q) =
      Affine.add (domain.a : Fp) (encodePoint p) (encodePoint q) := by
  cases p with
  | infinity => rfl
  | affine x₁ y₁ =>
    cases q with
    | infinity => rfl
    | affine x₂ y₂ =>
      simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp hq
      have hx : (x₁ : Fp) = (x₂ : Fp) ↔ x₁ = x₂ := cast_eq_iff _ _ hp.1.1 hq.1.1
      have hy : (y₁ : Fp) + (y₂ : Fp) = 0 ↔ (y₁ + y₂) % domain.p = 0 := by
        rw [← Semiring.natCast_add]
        exact cast_eq_zero_iff _
      by_cases hzero : x₁ = x₂ ∧ (y₁ + y₂) % domain.p = 0
      · simp only [Curve.add, encodePoint, Affine.add, Bool.and_eq_true, beq_iff_eq,
          hy, hzero, ite_true]
        rfl
      · simp only [Curve.add, encodePoint, Affine.add, Bool.and_eq_true, beq_iff_eq,
          hx, hy, hzero, ite_false]
        by_cases heq : x₁ = x₂
        · simp only [heq, ite_true, cast_fieldSub, cast_mod,
            Semiring.natCast_mul, Semiring.natCast_add, cast_inverse, Field.div_eq_mul_inv]
          rfl
        · simp only [heq, ite_false, cast_fieldSub, cast_mod,
            Semiring.natCast_mul, cast_inverse, Field.div_eq_mul_inv]

end K256.Proofs.Generate.Curve.Group
