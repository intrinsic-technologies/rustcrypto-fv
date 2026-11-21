import P256.Proofs.Verifying.Combination.Algebra.Integer
import P256.Proofs.Projective.Multiply.Algebra
import P256.Proofs.Projective.Multiply.Group.Laws
import P256.Proofs.Projective.Multiply.Group.Scalar

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective P256.Proofs.Projective.Algebra
open P256.Proofs.Projective.Multiply.Group
open Lean.Grind Fin.NatCast Fin.IntCast

abbrev CurvePoint := {point : Affine.Point Fp //
  Affine.onCurve (domain.a : Fp) (domain.b : Fp) point}

instance : AddCommGroup CurvePoint where
  zero := ⟨.infinity, True.intro⟩
  add p q := ⟨Affine.add (domain.a : Fp) p.val q.val,
    Affine.add_onCurve _ _ _ _ p.property q.property⟩
  neg p := ⟨Affine.neg p.val, Affine.neg_onCurve _ _ _ p.property⟩
  sub p q := ⟨Affine.add (domain.a : Fp) p.val (Affine.neg q.val),
    Affine.add_onCurve _ _ _ _ p.property (Affine.neg_onCurve _ _ _ q.property)⟩
  add_zero _ := Subtype.ext (Affine.add_infinity _ _)
  add_comm p q := Subtype.ext (Affine.add_comm _ _ _ _ p.property q.property)
  add_assoc p q r := Subtype.ext (Affine.add_assoc _ _ p256_two_ne_zero
    p256_cubic_ne_zero _ _ _ p.property q.property r.property)
  neg_add_cancel _ := Subtype.ext (Affine.neg_add_cancel _ _)
  sub_eq_add_neg _ _ := rfl

def affineValue (point : Curve.Point) (hp : Curve.onCurve domain point = true) :
    CurvePoint := ⟨encodePoint point, encode_onCurve point hp⟩

def projectiveValue (point : Projective) (hp : point.valid) : CurvePoint :=
  affineValue point.toAffine (Projective.toAffine_onCurve point hp)

theorem affineValue_add (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true)
    (hq : Curve.onCurve domain q = true) :
    affineValue (Curve.add domain p q) (p256_add_closed p q hp hq) =
      affineValue p hp + affineValue q hq :=
  Subtype.ext (encode_add p q hp hq)

theorem naturalMultiple_affineValue (point : Curve.Point)
    (hp : Curve.onCurve domain point = true) (n : Nat) :
    naturalMultiple (affineValue point hp) n =
      affineValue (multiple domain point n)
        (multiple_onCurve domain p256_add_laws point hp n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change naturalMultiple (affineValue point hp) n + affineValue point hp = _
    rw [ih]
    exact (affineValue_add _ _ _ _).symm

theorem projectiveValue_add (p q : Projective) (hp : p.valid) (hq : q.valid) :
    projectiveValue (p.add q) (Projective.add_valid p q hp hq) =
      projectiveValue p hp + projectiveValue q hq := by
  apply Subtype.ext
  change encodePoint (p.add q).toAffine = _
  rw [Projective.add_toAffine p q hp hq]
  exact encode_add _ _ (Projective.toAffine_onCurve p hp) (Projective.toAffine_onCurve q hq)

theorem projectiveValue_double (p : Projective) (hp : p.valid) :
    projectiveValue p.double (Projective.double_valid p hp) =
      projectiveValue p hp + projectiveValue p hp := by
  apply Subtype.ext
  change encodePoint p.double.toAffine = _
  rw [Projective.double_toAffine p hp]
  exact encode_add _ _ (Projective.toAffine_onCurve p hp) (Projective.toAffine_onCurve p hp)

theorem projectiveValue_negate (p : Projective) (hp : p.valid) :
    projectiveValue p.negate (Projective.negate_valid p hp) = -projectiveValue p hp :=
  Subtype.ext (Projective.encode_toAffine_negate p hp.1)

theorem projectiveValue_eq_iff (p : Projective) (hp : p.valid) (q : Curve.Point)
    (hq : Curve.onCurve domain q = true) :
    projectiveValue p hp = affineValue q hq ↔ p.toAffine = q := by
  constructor
  · intro he
    have he' := congrArg (fun v : CurvePoint => decodePoint v.val) he
    change decodePoint (encodePoint p.toAffine) = decodePoint (encodePoint q) at he'
    simpa only [decode_encode p.toAffine (Projective.toAffine_onCurve p hp),
      decode_encode q hq] using he'
  · intro he
    apply Subtype.ext
    exact congrArg encodePoint he

end P256.Proofs.Verifying.Combination.Algebra
