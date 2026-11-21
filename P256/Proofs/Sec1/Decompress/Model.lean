import P256.Spec.Points

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open P256.Spec Standards.SECG.ECC

theorem decompress_isSome (x : Nat) (odd : Bool) :
    (Points.decompress x odd).isSome =
      (decide (x < Operations.domain.p) && (Operations.sqrtMod (Points.curveRhs x)).isSome) := by
  unfold Points.decompress
  by_cases h : x ≥ Operations.domain.p
  · simp [h, Nat.not_lt.mpr h]
  · have hlt : x < Operations.domain.p := by omega
    simp only [h, ↓reduceIte, decide_eq_true hlt, Bool.true_and]
    cases Operations.sqrtMod (Points.curveRhs x) <;> rfl

theorem decompress_some_affine {x : Nat} {odd : Bool} {point : Curve.Point}
    (decoded : Points.decompress x odd = some point) : ∃ y, point = .affine x y := by
  unfold Points.decompress at decoded
  split at decoded
  · simp at decoded
  · cases hr : Operations.sqrtMod (Points.curveRhs x) with
    | none => simp [hr] at decoded
    | some root =>
      rw [hr] at decoded
      exact ⟨_, (Option.some.inj decoded).symm⟩

end P256.Proofs.Sec1.Decompress
