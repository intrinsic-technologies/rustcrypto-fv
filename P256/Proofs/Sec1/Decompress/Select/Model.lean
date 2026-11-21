import P256.Proofs.Sec1.Affine.Model
import P256.Proofs.Sec1.Decompress.Select.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select
open P256.Spec

theorem decompress_coordinates {x y : Nat} {odd : Bool}
    (h : Points.decompress x odd = some (Standards.SECG.ECC.Curve.Point.affine x y)) :
    x < Operations.domain.p ∧
      y = if candidateRoot x % 2 == odd.toNat then candidateRoot x
        else (Operations.domain.p - candidateRoot x) % Operations.domain.p := by
  unfold Points.decompress at h
  by_cases hx : x ≥ Operations.domain.p
  · simp [hx] at h
  · have hlt : x < Operations.domain.p := by omega
    simp only [hx, ↓reduceIte] at h
    cases hr : Operations.sqrtMod (Points.curveRhs x) with
    | none => simp [hr] at h
    | some root =>
      have root_eq : candidateRoot x = root := by
        simp [candidateRoot, checkedX, hlt, hr]
      rw [root_eq]
      have hp : ((root % 2 == 1) == odd) = (root % 2 == odd.toNat) := by
        have cases : root % 2 = 0 ∨ root % 2 = 1 := by omega
        rcases cases with hp | hp <;> cases odd <;> simp [hp]
      have bound := (P256.Proofs.Sec1.Affine.sqrtMod_some hr).1
      rw [hr] at h
      change some (Standards.SECG.ECC.Curve.Point.affine x (if ((root % 2 == 1) == odd) then root else Points.negElement root)) =
        some (Standards.SECG.ECC.Curve.Point.affine x y) at h
      have hy := (Standards.SECG.ECC.Curve.Point.affine.inj (Option.some.inj h)).2
      refine ⟨hlt, ?_⟩
      simpa only [hp, Points.negElement, Standards.SECG.ECC.Curve.fieldSub, Nat.zero_mod, Nat.zero_add,
        Nat.mod_eq_of_lt bound] using hy.symm

end P256.Proofs.Sec1.Decompress.Select
