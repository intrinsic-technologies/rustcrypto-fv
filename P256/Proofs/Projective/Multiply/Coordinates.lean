import P256.Proofs.Projective.Multiply.Operations

set_option autoImplicit false

namespace P256.Proofs.Projective

open Standards.SECG.ECC
open P256.Spec.Operations (domain)
open Lean.Grind Algebra Fin.NatCast Fin.IntCast

theorem identity_valid : identity.valid := by
  unfold valid canonical identity
  decide +kernel

theorem double_canonical (point : Projective) : point.double.canonical := by
  dsimp only [double, canonical, Curve.fieldSub]
  exact ⟨Nat.mod_lt _ modulus_pos, Nat.mod_lt _ modulus_pos, Nat.mod_lt _ modulus_pos⟩

theorem negate_canonical (point : Projective) (h : point.canonical) : point.negate.canonical :=
  ⟨h.1, Nat.mod_lt _ modulus_pos, h.2.2⟩

theorem coordinates_double (point : Projective) :
    point.double.coordinates =
      RCB.double (domain.b : Fp) point.coordinates := by
  apply RCB.Coordinates.ext
  all_goals
    dsimp only [double, coordinates, RCB.double]
    simp only [IsCharP.natCast_emod domain.p, cast_fieldSub,
      Semiring.natCast_add, Semiring.natCast_mul]
    grind only

theorem coordinates_negate (point : Projective) :
    point.negate.coordinates = RCB.negate point.coordinates := by
  apply RCB.Coordinates.ext
  · rfl
  · dsimp only [negate, coordinates, RCB.negate]
    rw [cast_fieldSub, Semiring.natCast_zero]
    grind only
  · rfl

end P256.Proofs.Projective
