import P256.Proofs.ProjectiveWrapper.Decode.Interface
import P256.Proofs.Sec1.Affine.Model
import P256.Proofs.Projective.Algebra
import P256.Proofs.Projective.Multiply.Coordinates

set_option autoImplicit false

namespace P256.Proofs.ProjectiveWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective.Algebra
open Lean.Grind Fin.NatCast Fin.IntCast

theorem projective_toAffine (point : Curve.Point) (canonical : (Decode.projective point).canonical) :
    (Decode.projective point).toAffine = point := by
  cases point with
  | infinity => rfl
  | affine x y =>
    have inv : Curve.inverse domain.p 1 = 1 := by decide +kernel
    simp only [Decode.projective, Projective.canonical] at canonical
    simp [Decode.projective, Projective.toAffine, inv, Nat.mod_eq_of_lt canonical.1,
      Nat.mod_eq_of_lt canonical.2.1]

theorem projective_valid (point : Curve.Point) (curve : Curve.onCurve domain point = true) :
    (Decode.projective point).valid := by
  cases point with
  | infinity => exact Projective.identity_valid
  | affine x y =>
    have encoded := encode_onCurve (.affine x y) curve
    simp only [encodePoint, Projective.Affine.onCurve, coefficient_a] at encoded
    simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at curve
    apply (Projective.valid_iff _).mpr
    refine ⟨⟨curve.1.1, curve.1.2, by change 1 < domain.p; decide +kernel⟩, ?_, ?_⟩
    · right; right
      exact (by decide +kernel : (1 : Fp) ≠ 0)
    · change (y : Fp) * y * 1 + 3 * x * 1 * 1 =
        (x : Fp) * x * x + (domain.b : Fp) * 1 * 1 * 1
      grind only

theorem call_decoded [Bindings] {s : RamState} {point other : ByteArray}
    {slices : Array Input} (call : ValidCallWithSlices projectivePointAdd s [point, other] slices) :
    ∃ left right, Points.decodePoint point = some left ∧ Points.decodePoint other = some right := by
  have valid : Points.isAffineEncoding point = true ∧ Points.isAffineEncoding other = true := by
    simpa [projectivePointAdd, Functions.projectivePointAddArguments, Arith.slices] using
      call.argumentsValid
  obtain ⟨left, hl⟩ := Option.isSome_iff_exists.mp valid.1
  obtain ⟨right, hr⟩ := Option.isSome_iff_exists.mp valid.2
  exact ⟨left, right, hl, hr⟩

theorem pointAdd_of_decoded {point other : ByteArray} {left right : Curve.Point}
    (hl : Points.decodePoint point = some left) (hr : Points.decodePoint other = some right) :
    Points.pointAdd #[point, other] = Points.encode (Points.add left right) := by
  simp [Points.pointAdd, Points.pointArgument, Arith.argument, Points.pointOf, hl, hr]

theorem projective_add_encoding {point other : ByteArray} {left right : Curve.Point}
    (hl : Points.decodePoint point = some left) (hr : Points.decodePoint other = some right) :
    Points.encode ((Decode.projective left).add (Decode.projective right)).toAffine =
      Points.pointAdd #[point, other] := by
  have vl := projective_valid left (Sec1.Affine.decodePoint_some_onCurve hl)
  have vr := projective_valid right (Sec1.Affine.decodePoint_some_onCurve hr)
  rw [Projective.add_toAffine _ _ vl vr, projective_toAffine left vl.1,
    projective_toAffine right vr.1, pointAdd_of_decoded hl hr]

end P256.Proofs.ProjectiveWrapper
