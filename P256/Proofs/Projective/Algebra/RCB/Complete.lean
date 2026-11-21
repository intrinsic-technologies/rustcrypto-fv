import P256.Proofs.Projective.Algebra.RCB.Affine

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

open Lean.Grind

variable {R : Type} [Field R]

theorem add_zero_cubic (b x y u v : R)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b)
    (hx : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).x = 0)
    (hy : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).y = 0)
    (hz : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).z = 0) :
    (x * v + y * u) * (x * v + y * u) * (x * v + y * u) -
      3 * (x * v + y * u) * (y + v) * (y + v) + b * (y + v) * (y + v) * (y + v) = 0 := by
  dsimp only [add] at hx hy hz
  grind only

theorem cubic_homogeneous_zero (b a c : R)
    (noRoot : ∀ t : R, t * t * t - 3 * t + b ≠ 0)
    (h : a * a * a - 3 * a * c * c + b * c * c * c = 0) :
    a = 0 ∧ c = 0 := by
  by_cases hc : c = 0
  · constructor
    · grind only
    · exact hc
  · have hi := Field.mul_inv_cancel hc
    have hn := noRoot (a / c)
    clear noRoot
    apply False.elim
    apply hn
    simp only [Field.div_eq_mul_inv]
    grind only

theorem add_distinct_nonzero (b x y u v : R)
    (noRoot : ∀ t : R, t * t * t - 3 * t + b ≠ 0)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b)
    (hxu : x ≠ u) :
    nonzero (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩) := by
  have hy : y ≠ 0 := by
    intro he
    apply noRoot x
    grind only
  apply Classical.byContradiction
  intro hn
  have hx0 : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).x = 0 := by
    apply Classical.byContradiction
    intro hx
    exact hn (Or.inl hx)
  have hy0 : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).y = 0 := by
    apply Classical.byContradiction
    intro hy
    exact hn (Or.inr (Or.inl hy))
  have hz0 : (add b ⟨x, y, 1⟩ ⟨u, v, 1⟩).z = 0 := by
    apply Classical.byContradiction
    intro hz
    exact hn (Or.inr (Or.inr hz))
  have he := add_zero_cubic b x y u v hl hr hx0 hy0 hz0
  have hab := cubic_homogeneous_zero b (x * v + y * u) (y + v) noRoot he
  have ha := hab.1
  have hb := hab.2
  clear noRoot hl hr hn hx0 hy0 hz0 he hab
  grind only

theorem add_distinct_proportional (b x y u v : R)
    (hl : y * y + 3 * x = x * x * x + b)
    (hr : v * v + 3 * u = u * u * u + b)
    (hxu : x ≠ u) :
    let s := (v - y) / (u - x)
    let rx := s * s - x - u
    let ry := s * (x - rx) - y
    let result := add b ⟨x, y, 1⟩ ⟨u, v, 1⟩
    result.x = result.z * rx ∧ result.y = result.z * ry := by
  have hd : u - x ≠ 0 := by grind only
  have hi := Field.mul_inv_cancel hd
  dsimp only [add]
  simp only [Field.div_eq_mul_inv]
  constructor <;> grind only

end P256.Proofs.Projective.RCB
