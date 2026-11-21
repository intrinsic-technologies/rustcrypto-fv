import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Sec1.Decompress.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

theorem decompress_isSome_checkedX (x : Nat) (odd : Bool) :
    (Points.decompress x odd).isSome =
      (decide (x < Operations.domain.p) &&
        (Operations.sqrtMod (Points.curveRhs (checkedX x))).isSome) := by
  rw [decompress_isSome]
  by_cases h : x < Operations.domain.p <;> simp [checkedX, h]

theorem validity_and (x : Nat) (odd : Bool) :
    BitVec.ofNat 8 (Operations.sqrtMod (Points.curveRhs (checkedX x))).isSome.toNat &&&
        BitVec.ofNat 8 (decide (x < Operations.domain.p)).toNat =
      BitVec.ofNat 8 (Points.decompress x odd).isSome.toNat := by
  rw [decompress_isSome_checkedX]
  generalize decide (x < Operations.domain.p) = a
  generalize (Operations.sqrtMod (Points.curveRhs (checkedX x))).isSome = b
  cases a <;> cases b <;> rfl

theorem affineResult_of_tag_coordinates {s : RamState} {address : BitVec 64}
    {x : Nat} {odd : Bool}
    (tag : s.external[address + 72]? = some (UInt8.ofNat (Points.decompress x odd).isSome.toNat))
    (coordinates : ∀ y, Points.decompress x odd = some (.affine x y) →
      AffineAt s address (.affine x y)) :
    AffineResultAt s address (Points.decompress x odd) := by
  have zero : UInt8.ofNat 0 = (0 : UInt8) := by decide +kernel
  have one : UInt8.ofNat 1 = (1 : UInt8) := by decide +kernel
  cases decoded : Points.decompress x odd with
  | none => simpa only [AffineResultAt, decoded, Option.isSome_none, Bool.toNat_false, zero] using tag
  | some point =>
    obtain ⟨y, rfl⟩ := decompress_some_affine decoded
    exact ⟨coordinates y decoded, by simpa only [decoded, Option.isSome_some, Bool.toNat_true, one] using tag⟩

end P256.Proofs.Sec1.Decompress.Output
