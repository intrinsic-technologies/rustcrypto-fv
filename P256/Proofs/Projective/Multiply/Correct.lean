import P256.Proofs.Projective.Multiply.Loop.Correct
import P256.Proofs.Projective.Multiply.Group.Laws

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Group

def model (point : Projective) (d : Nat) : Projective :=
  ProjectiveLoop.linearCombination (Projective.table point) (ProjectiveRadix.digitByte d)

theorem model_correct (point : Projective) (hp : point.valid) (d : Nat) (hd : d < 2 ^ 256) :
    (model point d).valid ∧ (model point d).toAffine = P256.Spec.Points.mul d point.toAffine := by
  have h := ScalarMul.accumulator_correct p256_add_laws point hp d hd 64 (by decide)
  simp only [Nat.sub_self, ScalarMul.radixPrefix_zero] at h
  refine ⟨h.1, ?_⟩
  change (model point d).toAffine = Curve.scalarMul domain d point.toAffine
  rw [scalarMul_eq_multiple domain p256_add_laws point.toAffine
    (Projective.toAffine_onCurve point hp)]
  exact h.2

end P256.Proofs.Projective.Multiply
