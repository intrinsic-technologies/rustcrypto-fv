import Init.Grind

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group.Affine

inductive Point (F : Type) where
  | infinity
  | affine (x y : F)
  deriving DecidableEq

def onCurve {F : Type} [Lean.Grind.Field F] (a b : F) : Point F → Prop
  | .infinity => True
  | .affine x y => y * y = x * x * x + a * x + b

def add {F : Type} [Lean.Grind.Field F] [DecidableEq F] (a : F) :
    Point F → Point F → Point F
  | .infinity, right => right
  | left, .infinity => left
  | .affine x₁ y₁, .affine x₂ y₂ =>
    if x₁ = x₂ ∧ y₁ + y₂ = 0 then .infinity else
    let slope := if x₁ = x₂ then (3 * x₁ * x₁ + a) / (2 * y₁)
      else (y₂ - y₁) / (x₂ - x₁)
    let x₃ := slope * slope - x₁ - x₂
    let y₃ := slope * (x₁ - x₃) - y₁
    .affine x₃ y₃

def neg {F : Type} [Lean.Grind.Field F] : Point F → Point F
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

theorem add_infinity {F : Type} [Lean.Grind.Field F] [DecidableEq F]
    (a : F) (p : Point F) : add a p .infinity = p := by
  cases p <;> rfl

theorem infinity_add {F : Type} [Lean.Grind.Field F] [DecidableEq F]
    (a : F) (p : Point F) : add a .infinity p = p := by
  rfl

end K256.Proofs.Generate.Curve.Group.Affine
