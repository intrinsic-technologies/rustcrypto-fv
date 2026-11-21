import P256.Proofs.Verifying.Combination.Algebra.Model
import P256.Proofs.Verifying.Combination.Algebra.Group

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Algebra

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open P256.Proofs.Projective P256.Proofs.Projective.Multiply.Group
open Table (oddTable oddTableEntry)

theorem oddTableEntry_correct (point : Projective) (hp : point.valid) (i : Nat) :
    (oddTableEntry point i).valid ∧
      (oddTableEntry point i).toAffine = multiple domain point.toAffine (2 * i + 1) := by
  have hb := toAffine_onCurve point hp
  have hd := double_valid point hp
  have he : point.double.toAffine = multiple domain point.toAffine 2 := by
    simpa only [multiple, Curve.add] using double_toAffine point hp
  induction i with
  | zero =>
    refine ⟨hp, ?_⟩
    change point.toAffine = Curve.add domain .infinity point.toAffine
    cases point.toAffine <;> rfl
  | succ i ih =>
    refine ⟨add_valid _ _ ih.1 hd, ?_⟩
    change ((oddTableEntry point i).add point.double).toAffine = _
    rw [add_toAffine _ _ ih.1 hd, ih.2, he]
    change Curve.add domain _ _ = _
    rw [← multiple_add domain p256_add_laws point.toAffine hb]
    congr 1

theorem selectMagnitude_correct (point : Projective) (hp : point.valid)
    (magnitude : Nat) (hm : magnitude = 0 ∨ magnitude % 2 = 1 ∧ magnitude ≤ 15) :
    (selectMagnitude (oddTable point) magnitude).valid ∧
      (selectMagnitude (oddTable point) magnitude).toAffine =
        multiple domain point.toAffine magnitude := by
  rcases hm with hz | hm
  · subst magnitude
    simp only [selectMagnitude, Nat.lt_irrefl, false_and, dite_false]
    exact ⟨identity_valid, rfl⟩
  · have hcond : 0 < magnitude ∧ magnitude ≤ 15 ∧ magnitude % 2 = 1 := by omega
    simp only [selectMagnitude, dite_eq_left hcond, oddTable]
    have he : 2 * (magnitude / 2) + 1 = magnitude := by omega
    simpa only [he] using oddTableEntry_correct point hp (magnitude / 2)

end P256.Proofs.Verifying.Combination.Algebra
