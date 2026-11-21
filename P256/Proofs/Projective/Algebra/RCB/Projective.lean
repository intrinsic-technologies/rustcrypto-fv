import P256.Proofs.Projective.Algebra.RCB.AddAffine

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

variable {R : Type} [Field R]

theorem nonzero_scale (point : Coordinates R) (factor : R)
    (hf : factor ≠ 0) (hp : nonzero point) : nonzero (scale factor point) := by
  dsimp only [nonzero, scale] at *
  rcases hp with hx | hy | hz
  · exact Or.inl (fun h => hx ((Field.of_mul_eq_zero h).resolve_left hf))
  · exact Or.inr (Or.inl (fun h => hy ((Field.of_mul_eq_zero h).resolve_left hf)))
  · exact Or.inr (Or.inr (fun h => hz ((Field.of_mul_eq_zero h).resolve_left hf)))

theorem add_of_z_zero (b : R) (left right : Coordinates R)
    (hc : onCurve b right) (hz : right.z = 0) :
    add b left right = scale (right.y * right.y * left.y) left := by
  have hx := onCurve_x_of_z_zero b right hc hz
  apply Coordinates.ext <;> dsimp only [add, scale] <;> rw [hx, hz] <;> grind only

variable [DecidableEq R]

theorem add_infinity_correct (b : R) (left right : Coordinates R)
    (noRoot : ∀ x : R, x * x * x - 3 * x + b ≠ 0)
    (hlc : onCurve b left) (hln : nonzero left)
    (hrc : onCurve b right) (hrn : nonzero right) (hz : right.z = 0) :
    nonzero (add b left right) ∧ toAffine (add b left right) = toAffine left := by
  have hly := y_ne_zero b noRoot left hlc hln
  have hry := nonzero_y_of_z_zero b right hrc hrn hz
  have hs : right.y * right.y * left.y ≠ 0 := by grind only
  rw [add_of_z_zero b left right hrc hz]
  exact ⟨nonzero_scale left _ hs hln, toAffine_scale left _ hs⟩

theorem add_correct (b : R) (left right : Coordinates R)
    (noRoot : ∀ x : R, x * x * x - 3 * x + b ≠ 0) (h8 : (8 : R) ≠ 0)
    (hlc : onCurve b left) (hln : nonzero left)
    (hrc : onCurve b right) (hrn : nonzero right) :
    nonzero (add b left right) ∧
      toAffine (add b left right) = Affine.add (-3) (toAffine left) (toAffine right) := by
  by_cases hrz : right.z = 0
  · have hi := add_infinity_correct b left right noRoot hlc hln hrc hrn hrz
    refine ⟨hi.1, ?_⟩
    rw [hi.2, (toAffine_eq_infinity_iff right).mpr hrz, Affine.add_infinity]
  by_cases hlz : left.z = 0
  · have hi := add_infinity_correct b right left noRoot hrc hrn hlc hln hlz
    rw [add_comm b left right]
    refine ⟨hi.1, ?_⟩
    rw [hi.2, (toAffine_eq_infinity_iff left).mpr hlz, Affine.infinity_add]
  have hs : left.z * left.z * right.z * right.z ≠ 0 := by grind only
  have hli := Field.mul_inv_cancel hlz
  have hri := Field.mul_inv_cancel hrz
  have hl : (left.y / left.z) * (left.y / left.z) + 3 * (left.x / left.z) =
      (left.x / left.z) * (left.x / left.z) * (left.x / left.z) + b := by
    dsimp only [onCurve] at hlc
    simp only [Field.div_eq_mul_inv]
    grind only
  have hr : (right.y / right.z) * (right.y / right.z) + 3 * (right.x / right.z) =
      (right.x / right.z) * (right.x / right.z) * (right.x / right.z) + b := by
    dsimp only [onCurve] at hrc
    simp only [Field.div_eq_mul_inv]
    grind only
  have he : add b left right = scale (left.z * left.z * right.z * right.z)
      (add b ⟨left.x / left.z, left.y / left.z, 1⟩
        ⟨right.x / right.z, right.y / right.z, 1⟩) := by
    conv => lhs; rw [normalize left hlz, normalize right hrz]
    exact add_scale b _ _ _ _
  rw [he]
  refine ⟨nonzero_scale _ _ hs (add_affine_nonzero b _ _ _ _ noRoot h8 hl hr), ?_⟩
  rw [toAffine_scale _ _ hs, add_affine_toAffine b _ _ _ _ noRoot h8 hl hr]
  simp only [toAffine, hlz, hrz, ite_false]

end P256.Proofs.Projective.RCB
