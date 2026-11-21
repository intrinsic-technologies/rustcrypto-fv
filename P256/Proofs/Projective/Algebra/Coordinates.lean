import P256.Proofs.Projective.Algebra.Affine
import P256.Proofs.Projective.Formula

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

def coordinates (point : Projective) : RCB.Coordinates Fp :=
  ⟨point.x, point.y, point.z⟩

theorem coordinates_add (left right : Projective) :
    (left.add right).coordinates =
      RCB.add (domain.b : Fp) left.coordinates right.coordinates := by
  apply RCB.Coordinates.ext
  all_goals
    dsimp only [add, coordinates, RCB.add]
    simp only [IsCharP.natCast_emod domain.p, cast_fieldSub,
      Semiring.natCast_add, Semiring.natCast_mul]
    grind only

theorem coordinates_onCurve_iff (point : Projective) :
    RCB.onCurve (domain.b : Fp) point.coordinates ↔
      (point.y * point.y * point.z + 3 * point.x * point.z * point.z) %
          domain.p =
        (point.x * point.x * point.x +
          domain.b * point.z * point.z * point.z) % domain.p := by
  rw [← IsCharP.natCast_ext_iff (α := Fp) domain.p]
  simp only [Semiring.natCast_add, Semiring.natCast_mul]
  rfl

theorem coordinates_nonzero_iff (point : Projective) (h : point.canonical) :
    RCB.nonzero point.coordinates ↔ point.x ≠ 0 ∨ point.y ≠ 0 ∨ point.z ≠ 0 := by
  dsimp only [RCB.nonzero, coordinates]
  simp only [ne_eq,
    IsCharP.natCast_eq_zero_iff_of_lt (α := Fp) domain.p h.1,
    IsCharP.natCast_eq_zero_iff_of_lt (α := Fp) domain.p h.2.1,
    IsCharP.natCast_eq_zero_iff_of_lt (α := Fp) domain.p h.2.2]

theorem valid_iff (point : Projective) :
    point.valid ↔ point.canonical ∧ RCB.nonzero point.coordinates ∧
      RCB.onCurve (domain.b : Fp) point.coordinates := by
  constructor
  · intro ⟨hc, hn, he⟩
    exact ⟨hc, (coordinates_nonzero_iff point hc).mpr hn,
      (coordinates_onCurve_iff point).mpr he⟩
  · intro ⟨hc, hn, he⟩
    exact ⟨hc, (coordinates_nonzero_iff point hc).mp hn,
      (coordinates_onCurve_iff point).mp he⟩

end P256.Proofs.Projective
