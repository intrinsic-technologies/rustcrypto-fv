import P256.Proofs.Sec1.Affine.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec Standards.SECG.ECC
open P256.Proofs.Projective.Algebra
open Lean.Grind Fin.NatCast Fin.IntCast

theorem curveRhs_ne_zero (x : Nat) : Points.curveRhs x ≠ 0 := by
  intro h
  have hc : ((x * x * x + Operations.domain.a * x + Operations.domain.b : Nat) : Fp) = 0 :=
    (IsCharP.natCast_eq_zero_iff (α := Fp) Operations.domain.p _).mpr h
  apply cubic_ne_zero (x : Fp)
  simp only [Semiring.natCast_add, Semiring.natCast_mul, coefficient_a] at hc
  grind only

theorem sqrt_curveRhs_positive {x root : Nat}
    (result : Operations.sqrtMod (Points.curveRhs x) = some root) : 0 < root := by
  obtain ⟨_, square⟩ := sqrtMod_some result
  have rhs_lt : Points.curveRhs x < Operations.domain.p := Nat.mod_lt _ modulus_pos
  rw [Nat.mod_eq_of_lt rhs_lt] at square
  have ne := curveRhs_ne_zero x
  by_cases zero : root = 0
  · simp only [zero, Nat.zero_mul, Nat.zero_mod] at square
    exact (ne square.symm).elim
  · omega

theorem negElement_parity {y : Nat} (positive : 0 < y) (bound : y < Operations.domain.p) :
    Points.negElement y % 2 = 1 - y % 2 := by
  have odd : Operations.domain.p % 2 = 1 := by decide +kernel
  have neg : Points.negElement y = Operations.domain.p - y := by
    simp only [Points.negElement, Curve.fieldSub, Nat.zero_mod, Nat.zero_add,
      Nat.mod_eq_of_lt bound]
    exact Nat.mod_eq_of_lt (by omega)
  rw [neg]
  omega

theorem selected_root_valid {x root : Nat} (odd : Bool)
    (result : Operations.sqrtMod (Points.curveRhs x) = some root) :
    let y := if (root % 2 == 1) == odd then root else Points.negElement root
    y * y % Operations.domain.p = Points.curveRhs x ∧ y % 2 = odd.toNat := by
  have ⟨bound, square⟩ := sqrtMod_some result
  have positive := sqrt_curveRhs_positive result
  have parity := negElement_parity positive bound
  have rhs_lt : Points.curveRhs x < Operations.domain.p := Nat.mod_lt _ modulus_pos
  rw [Nat.mod_eq_of_lt rhs_lt] at square
  have options : root % 2 = 0 ∨ root % 2 = 1 := by omega
  rcases options with h | h <;> cases odd
  all_goals simp [h, square, negElement_square, parity]

theorem parity_test (root : Nat) (odd : Bool) :
    (root % 2 == odd.toNat) = ((root % 2 == 1) == odd) := by
  have options : root % 2 = 0 ∨ root % 2 = 1 := by omega
  rcases options with h | h <;> cases odd <;> simp [h]

theorem checked_decompress (x : Nat) (odd : Bool) :
    (if x ≥ Operations.domain.p then none else
      (Operations.sqrtMod (Points.curveRhs x)).bind fun root ↦
        let root := root % Operations.domain.p
        let y := if root % 2 == odd.toNat then root else Points.negElement root
        if y * y % Operations.domain.p == Points.curveRhs x && y % 2 == odd.toNat then
          some (Curve.Point.affine x y) else none) = Points.decompress x odd := by
  unfold Points.decompress
  split
  · rfl
  · cases result : Operations.sqrtMod (Points.curveRhs x) with
    | none => rfl
    | some root =>
      have bound := (sqrtMod_some result).1
      have valid := selected_root_valid odd result
      simp only [Option.bind_some, Nat.mod_eq_of_lt bound, parity_test root odd]
      change (if _ then _ else _) = some _
      rw [show ((if (root % 2 == 1) == odd then root else Points.negElement root) *
          (if (root % 2 == 1) == odd then root else Points.negElement root) %
          Operations.domain.p == Points.curveRhs x &&
          (if (root % 2 == 1) == odd then root else Points.negElement root) % 2 == odd.toNat)
          = true by simpa only [Bool.and_eq_true, beq_iff_eq] using valid]
      rfl

theorem decodePoint_eq_decompress {bytes : ByteArray} {tag : UInt8}
    (size : bytes.size = 33) (tagByte : bytes.data[0]? = some tag)
    (valid : tag = 2 ∨ tag = 3) :
    P256.Spec.Points.decodePoint bytes =
      Points.decompress (Points.element bytes 1) (tag == 3) := by
  have nonidentity : (bytes == (⟨#[0]⟩ : ByteArray)) = false := by
    change (bytes.data == #[0]) = false
    apply Bool.eq_false_iff.mpr
    intro h
    have he := ByteArray.ext (eq_of_beq h)
    have hs := congrArg ByteArray.size he
    change bytes.size = 1 at hs
    omega
  have compressed :
      P256.Spec.Points.decodePoint bytes =
        Standards.SECG.ECC.Points.decodePoint Operations.domain Operations.sqrtMod bytes := by
    rcases valid with rfl | rfl <;> simp [P256.Spec.Points.decodePoint, tagByte]
  rw [compressed]
  simp only [Standards.SECG.ECC.Points.decodePoint, nonidentity, Bool.false_eq_true,
    ↓reduceIte, field_octets, size, tagByte, Option.getD_some]
  simp only [show (33 == 1 + 2 * 32) = false from rfl,
    show (33 == 1 + 32) = true from rfl, Bool.false_and, Bool.true_and,
    Bool.false_eq_true, ite_false]
  rcases valid with rfl | rfl
  · simp only [show ((2 : UInt8) == 2) = true from rfl,
      show ((2 : UInt8) == 3) = false from rfl, Bool.true_or, ite_true]
    change _ = Points.decompress (Points.element bytes 1) false
    exact checked_decompress (Points.element bytes 1) false
  · simp only [show ((3 : UInt8) == 2) = false from rfl,
      show ((3 : UInt8) == 3) = true from rfl, Bool.false_or, ite_true]
    change _ = Points.decompress (Points.element bytes 1) true
    exact checked_decompress (Points.element bytes 1) true

end P256.Proofs.Sec1.Affine.Compressed
