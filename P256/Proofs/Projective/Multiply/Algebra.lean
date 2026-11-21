import P256.Proofs.Projective.Multiply.Negate

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

theorem negate_valid (point : Projective) (h : point.valid) : point.negate.valid := by
  have hv := (valid_iff point).mp h
  apply (valid_iff point.negate).mpr
  refine ⟨negate_canonical point hv.1, ?_, ?_⟩
  · rw [coordinates_negate]
    exact RCB.negate_nonzero _ hv.2.1
  · rw [coordinates_negate]
    exact RCB.negate_onCurve _ _ hv.2.2

theorem encode_toAffine_negate (point : Projective) (hc : point.canonical) :
    encodePoint point.negate.toAffine = Affine.neg (encodePoint point.toAffine) := by
  rw [encode_toAffine _ (negate_canonical point hc), coordinates_negate,
    RCB.toAffine_negate, encode_toAffine point hc]

theorem double_valid (point : Projective) (h : point.valid) : point.double.valid := by
  have hv := (valid_iff point).mp h
  apply (valid_iff point.double).mpr
  refine ⟨double_canonical point, ?_, ?_⟩
  · rw [coordinates_double, RCB.double_eq_add _ _ hv.2.2]
    exact (RCB.add_correct _ _ _ cubic_ne_zero (by decide +kernel)
      hv.2.2 hv.2.1 hv.2.2 hv.2.1).1
  · rw [coordinates_double, RCB.double_eq_add _ _ hv.2.2]
    exact RCB.add_onCurve _ _ _ hv.2.2 hv.2.2

theorem double_toAffine (point : Projective) (h : point.valid) :
    point.double.toAffine = Curve.add domain point.toAffine point.toAffine := by
  have hv := (valid_iff point).mp h
  have ha := toAffine_onCurve point h
  have he := (RCB.add_correct _ _ _ cubic_ne_zero (by decide +kernel)
    hv.2.2 hv.2.1 hv.2.2 hv.2.1).2
  rw [← decode_toAffine point.double (double_canonical point), coordinates_double,
    RCB.double_eq_add _ _ hv.2.2, he, ← coefficient_a,
    ← encode_toAffine point hv.1, ← encode_add point.toAffine point.toAffine ha ha,
    decode_encode_add point.toAffine point.toAffine ha ha]

end P256.Proofs.Projective
