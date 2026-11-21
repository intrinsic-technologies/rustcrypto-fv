import Init.Grind

set_option autoImplicit false

namespace P256.Proofs.Projective.RCB

structure Coordinates (R : Type) where
  x : R
  y : R
  z : R

variable {R : Type} [Lean.Grind.CommRing R]

def add (b : R) (left right : Coordinates R) : Coordinates R :=
  let xx := left.x * right.x
  let yy := left.y * right.y
  let zz := left.z * right.z
  let xy := (left.x + left.y) * (right.x + right.y) - (xx + yy)
  let yz := (left.y + left.z) * (right.y + right.z) - (yy + zz)
  let xz := (left.x + left.z) * (right.x + right.z) - (xx + zz)
  let bzz3 := 3 * (xz - b * zz)
  let yyMinus := yy - bzz3
  let yyPlus := yy + bzz3
  let zz3 := 3 * zz
  let bxz3 := 3 * (b * xz - (zz3 + xx))
  let xxMinus := 3 * xx - zz3
  ⟨yyPlus * xy - yz * bxz3,
    yyPlus * yyMinus + xxMinus * bxz3,
    yyMinus * yz + xy * xxMinus⟩

def double (b : R) (point : Coordinates R) : Coordinates R :=
  let xx := point.x * point.x
  let yy := point.y * point.y
  let zz := point.z * point.z
  let xy2 := 2 * (point.x * point.y)
  let xz2 := 2 * (point.x * point.z)
  let bzz3 := 3 * (b * zz - xz2)
  let yyMinus := yy - bzz3
  let yyPlus := yy + bzz3
  let bxz6 := 3 * (b * xz2 - (3 * zz + xx))
  let xxMinus := 3 * xx - 3 * zz
  let yz2 := 2 * (point.y * point.z)
  ⟨yyMinus * xy2 - bxz6 * yz2,
    yyPlus * yyMinus + xxMinus * bxz6,
    4 * (yz2 * yy)⟩

def negate (point : Coordinates R) : Coordinates R :=
  ⟨point.x, -point.y, point.z⟩

def onCurve (b : R) (point : Coordinates R) : Prop :=
  point.y * point.y * point.z + 3 * point.x * point.z * point.z =
    point.x * point.x * point.x + b * point.z * point.z * point.z

def nonzero (point : Coordinates R) : Prop :=
  point.x ≠ 0 ∨ point.y ≠ 0 ∨ point.z ≠ 0

def scale (factor : R) (point : Coordinates R) : Coordinates R :=
  ⟨factor * point.x, factor * point.y, factor * point.z⟩

omit [Lean.Grind.CommRing R] in
theorem Coordinates.ext {left right : Coordinates R}
    (hx : left.x = right.x) (hy : left.y = right.y) (hz : left.z = right.z) :
    left = right := by
  cases left
  cases right
  simp_all

theorem add_comm (b : R) (left right : Coordinates R) :
    add b left right = add b right left := by
  apply Coordinates.ext <;> dsimp only [add] <;> grind only

theorem add_scale (b s t : R) (left right : Coordinates R) :
    add b (scale s left) (scale t right) = scale (s * s * t * t) (add b left right) := by
  apply Coordinates.ext <;> dsimp only [add, scale] <;> grind only

theorem double_eq_add (b : R) (point : Coordinates R) (h : onCurve b point) :
    double b point = add b point point := by
  apply Coordinates.ext <;> dsimp only [double, add, onCurve] at * <;> grind only

theorem add_onCurve (b : R) (left right : Coordinates R)
    (hl : onCurve b left) (hr : onCurve b right) :
    onCurve b (add b left right) := by
  dsimp only [onCurve, add] at *
  grind only

theorem add_negate (b : R) (point : Coordinates R) :
    add b point (negate point) = scale (double b point).y ⟨0, 1, 0⟩ := by
  apply Coordinates.ext <;> dsimp only [add, double, negate, scale] <;> grind only

end P256.Proofs.Projective.RCB
