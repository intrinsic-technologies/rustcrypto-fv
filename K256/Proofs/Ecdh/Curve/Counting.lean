import K256.Proofs.Generate.Curve.Group.Bridge
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

set_option autoImplicit false

namespace K256.Proofs.Ecdh.Curve

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve.Group
open CurveArithmetic Lean.Grind Fin.NatCast

private theorem fin_collision {m n : Nat} (f : Fin m → Fin n) (h : n < m) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  classical
  by_cases hcoll : ∃ i j, i ≠ j ∧ f i = f j
  · exact hcoll
  exfalso
  have hnodup : ((List.finRange m).map f).Nodup :=
    (List.nodup_finRange m).map f fun i j hne heq => hcoll ⟨i, j, hne, heq⟩
  have hlen := hnodup.length_le_of_subset (fun {i} _ => List.mem_finRange i)
  exact Nat.not_le_of_lt h (by simpa only [List.length_map, List.length_finRange] using hlen)

private theorem affine_y_eq_of_same_parity (x y z : Nat)
    (hy : Curve.onCurve domain (.affine x y) = true)
    (hz : Curve.onCurve domain (.affine x z) = true)
    (hparity : y % 2 = z % 2) : y = z := by
  have hyField := encode_onCurve _ hy
  have hzField := encode_onCurve _ hz
  simp only [encodePoint, Affine.onCurve] at hyField hzField
  simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hy hz
  rcases Affine.square_eq_square_cases (y : Fp) (z : Fp) (hyField.trans hzField.symm) with he | hs
  · exact (cast_eq_iff y z hy.1.2 hz.1.2).mp he
  · rw [← Semiring.natCast_add] at hs
    have hmod := (cast_eq_zero_iff (y + z)).mp hs
    by_cases hlt : y + z < domain.p
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hlt), Nat.mod_eq_of_lt (by omega)] at hmod
      have hp : domain.p % 2 = 1 := by decide +kernel
      omega

private def pointCode : Curve.Point → Nat
  | .infinity => 2 * domain.p
  | .affine x y => 2 * x + y % 2

private theorem affine_code_lt (x y : Nat) (h : Curve.onCurve domain (.affine x y) = true) :
    pointCode (.affine x y) < 2 * domain.p := by
  simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hx := h.1.1
  dsimp only [pointCode]
  omega

private theorem pointCode_injective {p q : Curve.Point}
    (hp : Curve.onCurve domain p = true) (hq : Curve.onCurve domain q = true)
    (heq : pointCode p = pointCode q) : p = q := by
  cases p with
  | infinity =>
    cases q with
    | infinity => rfl
    | affine x y =>
      exact False.elim (Nat.ne_of_lt (affine_code_lt x y hq) heq.symm)
  | affine x y =>
    cases q with
    | infinity =>
      exact False.elim (Nat.ne_of_lt (affine_code_lt x y hp) heq)
    | affine x' y' =>
      dsimp only [pointCode] at heq
      have hx : x = x' := by omega
      subst x'
      rw [affine_y_eq_of_same_parity x y y' hp hq (by omega)]

theorem point_collision (f : Fin (3 * domain.n) → Curve.Point)
    (h : ∀ i, Curve.onCurve domain (f i) = true) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  let code (i : Fin (3 * domain.n)) : Fin (2 * domain.p + 1) :=
    ⟨pointCode (f i), by
      have hi := h i
      cases hpoint : f i with
      | infinity => exact Nat.lt_succ_self _
      | affine x y =>
        rw [hpoint] at hi
        exact Nat.lt_succ_of_lt (affine_code_lt x y hi)⟩
  have hsize : 2 * domain.p + 1 < 3 * domain.n := by decide +kernel
  obtain ⟨i, j, hij, heq⟩ := fin_collision code hsize
  exact ⟨i, j, hij, pointCode_injective (h i) (h j) (congrArg Fin.val heq)⟩

end K256.Proofs.Ecdh.Curve
