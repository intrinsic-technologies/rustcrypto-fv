import P256.Proofs.Projective.Algebra.Bridge

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

theorem add_valid (left right : Projective) (hl : left.valid) (hr : right.valid) :
    (left.add right).valid := by
  have hlv := (valid_iff left).mp hl
  have hrv := (valid_iff right).mp hr
  apply (valid_iff (left.add right)).mpr
  refine ⟨add_canonical left right, ?_, ?_⟩
  · rw [coordinates_add]
    exact (RCB.add_correct _ _ _ cubic_ne_zero (by decide +kernel)
      hlv.2.2 hlv.2.1 hrv.2.2 hrv.2.1).1
  · rw [coordinates_add]
    exact RCB.add_onCurve _ _ _ hlv.2.2 hrv.2.2

theorem add_toAffine (left right : Projective) (hl : left.valid) (hr : right.valid) :
    (left.add right).toAffine =
      P256.Spec.Points.add left.toAffine right.toAffine := by
  have hlv := (valid_iff left).mp hl
  have hrv := (valid_iff right).mp hr
  have hla := toAffine_onCurve left hl
  have hra := toAffine_onCurve right hr
  have h := (RCB.add_correct _ _ _ cubic_ne_zero (by decide +kernel)
    hlv.2.2 hlv.2.1 hrv.2.2 hrv.2.1).2
  rw [← decode_toAffine (left.add right) (add_canonical left right), coordinates_add, h,
    ← coefficient_a, ← encode_toAffine left hlv.1, ← encode_toAffine right hrv.1,
    ← encode_add left.toAffine right.toAffine hla hra,
    decode_encode_add left.toAffine right.toAffine hla hra]
  rfl

end P256.Proofs.Projective
