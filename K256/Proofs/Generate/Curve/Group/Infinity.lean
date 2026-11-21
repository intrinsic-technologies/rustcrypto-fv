import K256.Proofs.Generate.Curve.Group.PointLaws

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group.Affine

open Lean.Grind

theorem add_eq_infinity_iff {F : Type} [Field F] [DecidableEq F]
    (a : F) (p q : Point F) : add a p q = .infinity ↔ q = neg p := by
  cases p with
  | infinity => rfl
  | affine x₁ y₁ =>
    cases q with
    | infinity => simp [add, neg]
    | affine x₂ y₂ =>
      constructor
      · intro h
        change (if x₁ = x₂ ∧ y₁ + y₂ = 0 then (Point.infinity : Point F) else _) =
          Point.infinity at h
        split at h
        · rename_i hz
          simp only [neg]
          congr 1 <;> grind
        · contradiction
      · intro h
        rw [h]
        exact add_neg_cancel a (.affine x₁ y₁)

end K256.Proofs.Generate.Curve.Group.Affine
