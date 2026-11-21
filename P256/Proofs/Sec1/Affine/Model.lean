import P256.Proofs.Sec1.Model
import P256.Proofs.Projective.Algebra.Field

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec
open Standards.SECG.ECC
open P256.Proofs.Projective.Algebra
open Lean.Grind Fin.NatCast Fin.IntCast

theorem negElement_lt (y : Nat) : Points.negElement y < Operations.domain.p :=
  Nat.mod_lt _ modulus_pos

theorem negElement_square (y : Nat) :
    Points.negElement y * Points.negElement y % Operations.domain.p =
      y * y % Operations.domain.p := by
  rw [← IsCharP.natCast_ext_iff (α := Fp) Operations.domain.p]
  simp only [Points.negElement, Semiring.natCast_mul, cast_fieldSub, Semiring.natCast_zero]
  grind only

theorem negElement_onCurve {x y : Nat}
    (on : Curve.onCurve Operations.domain (.affine x y) = true) :
    Curve.onCurve Operations.domain (.affine x (Points.negElement y)) = true := by
  simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at on ⊢
  exact ⟨⟨on.1.1, negElement_lt y⟩, (negElement_square y).trans on.2⟩

theorem sqrtMod_some {x root : Nat} (result : Operations.sqrtMod x = some root) :
    root < Operations.domain.p ∧ root * root % Operations.domain.p = x % Operations.domain.p := by
  unfold Operations.sqrtMod Standards.NIST.EllipticCurves.Field.sqrtMod3Mod4 at result
  dsimp only [] at result
  split at result
  next valid =>
    cases result
    exact ⟨FieldArithmetic.powMod_lt _ _ _ modulus_pos, beq_iff_eq.mp valid⟩
  next invalid => contradiction

theorem decompress_some_onCurve {x : Nat} {odd : Bool} {point : Curve.Point}
    (decoded : Points.decompress x odd = some point) :
    Curve.onCurve Operations.domain point = true := by
  unfold Points.decompress at decoded
  split at decoded
  next invalid => contradiction
  next valid =>
    cases root_eq : Operations.sqrtMod (Points.curveRhs x) with
    | none => simp [root_eq] at decoded
    | some root =>
      rw [root_eq] at decoded
      change some (.affine x (if (root % 2 == 1) == odd then root else Points.negElement root)) = some point at decoded
      cases decoded
      obtain ⟨root_lt, root_square⟩ := sqrtMod_some root_eq
      simp only [Points.curveRhs, Nat.mod_mod] at root_square
      have on : Curve.onCurve Operations.domain (.affine x root) = true := by
        simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨⟨by omega, root_lt⟩, root_square⟩
      split
      · exact on
      · exact negElement_onCurve on

theorem decompact_some_onCurve {x : Nat} {point : Curve.Point}
    (decoded : Points.decompact x = some point) : Curve.onCurve Operations.domain point = true := by
  obtain ⟨raw, hraw, rfl⟩ := Option.map_eq_some_iff.mp decoded
  have on := decompress_some_onCurve hraw
  cases raw with
  | infinity => exact on
  | affine x y =>
    change Curve.onCurve Operations.domain (.affine x (Points.compactY y)) = true
    unfold Points.compactY
    split
    · exact negElement_onCurve on
    · exact on

theorem standard_decodePoint_some_onCurve {domain : Curve.Domain}
    {sqrtMod : Nat → Option Nat} {bytes : ByteArray} {point : Curve.Point}
    (positive : 0 < domain.p)
    (decoded : Standards.SECG.ECC.Points.decodePoint domain sqrtMod bytes = some point) :
    Curve.onCurve domain point = true := by
  unfold Standards.SECG.ECC.Points.decodePoint at decoded
  dsimp only [] at decoded
  split at decoded
  next identity => cases decoded; rfl
  next nonidentity =>
    split at decoded
    next uncompressed =>
      split at decoded
      next on => cases decoded; exact on
      next off => contradiction
    next other =>
      split at decoded
      next compressed =>
        split at decoded
        next large => contradiction
        next small =>
          obtain ⟨root, _, output⟩ := Option.bind_eq_some_iff.mp decoded
          split at output <;> split at output
          all_goals first
            | contradiction
            | (rename_i parity valid
               cases output
               simp only [Bool.and_eq_true, beq_iff_eq] at valid
               simp only [Curve.onCurve, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
               exact ⟨⟨by omega, Nat.mod_lt _ positive⟩, valid.1⟩)
      next invalid => contradiction

theorem decodePoint_some_onCurve {bytes : ByteArray} {point : Curve.Point}
    (decoded : P256.Spec.Points.decodePoint bytes = some point) :
    Curve.onCurve Operations.domain point = true := by
  unfold P256.Spec.Points.decodePoint at decoded
  split at decoded
  · exact decompact_some_onCurve decoded
  · exact standard_decodePoint_some_onCurve modulus_pos decoded

end P256.Proofs.Sec1.Affine
