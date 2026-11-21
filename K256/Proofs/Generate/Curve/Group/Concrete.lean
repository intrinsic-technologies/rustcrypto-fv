import Standards.SECG.DomainParameters.Secp256k1
import K256.Proofs.Generate.Curve.Group.Bridge
import K256.Proofs.Generate.Curve.Group.Infinity

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1 CurveArithmetic
open Lean.Grind Fin.NatCast Fin.IntCast

theorem decode_encode_add (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) :
    decodePoint (encodePoint (Curve.add domain p q)) = Curve.add domain p q := by
  cases p with
  | infinity => exact decode_encode q hq
  | affine x₁ y₁ =>
    cases q with
    | infinity => exact decode_encode _ hp
    | affine x₂ y₂ =>
      simp only [Curve.add]
      split
      · rfl
      · simp only [encodePoint, decodePoint]
        change Curve.Point.affine (_ % domain.p) (_ % domain.p) = _
        simp only [Curve.fieldSub, Nat.mod_mod]

theorem secp256k1_add_closed (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) :
    Curve.onCurve domain (Curve.add domain p q) = true := by
  rw [← decode_encode_add p q hp hq, encode_add p q hp hq]
  apply decode_onCurve
  exact Affine.add_onCurve _ _ _ _ (encode_onCurve p hp) (encode_onCurve q hq)

theorem secp256k1_cubic_ne_zero (x : Fp) :
    x * x * x + (domain.a : Fp) * x + (domain.b : Fp) ≠ 0 := by
  intro hz
  apply K256.Proofs.Common.Arithmetic.decompressSquare_ne_zero x.val
  have hv := congrArg Fin.val hz
  change (((x.val * x.val % domain.p) * x.val % domain.p +
    (domain.a % domain.p * x.val) % domain.p) %
      domain.p + domain.b % domain.p) % domain.p = 0 at hv
  simpa only [K256.Proofs.Common.Arithmetic.decompressSquare, Nat.mod_mul_mod, Nat.mod_add_mod,
    Nat.add_mod_mod, Nat.mul_mod_mul_left, Nat.mul_mod_mod] using hv

theorem secp256k1_two_ne_zero : (2 : Fp) ≠ 0 := by decide +kernel

theorem decode_neg (p : Curve.Point) (hp : Curve.onCurve domain p = true) :
    decodePoint (Affine.neg (encodePoint p)) = Curve.neg domain p := by
  cases p with
  | infinity => rfl
  | affine x y =>
    simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    have hy := cast_fieldSub 0 y
    have hv := congrArg Fin.val hy
    change (Curve.fieldSub domain.p 0 y) % domain.p = _ at hv
    rw [show Curve.fieldSub domain.p 0 y % domain.p = Curve.fieldSub domain.p 0 y from
      Nat.mod_mod _ _] at hv
    have hz : (0 : Fp) - (y : Fp) = -(y : Fp) := by grind
    simp only [Semiring.natCast_zero, hz] at hv
    exact (Curve.Point.affine.injEq _ _ _ _).mpr ⟨Nat.mod_eq_of_lt hp.1.1, hv.symm⟩

theorem neg_eq_of_add_eq_infinity (p q : Curve.Point) (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) (h : Curve.add domain p q = .infinity) :
    Curve.neg domain p = q := by
  have he := encode_add p q hp hq
  rw [h] at he
  have hn := (Affine.add_eq_infinity_iff _ _ _).mp he.symm
  rw [← decode_neg p hp, ← hn, decode_encode q hq]

end K256.Proofs.Generate.Curve.Group
