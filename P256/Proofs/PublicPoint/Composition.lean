import P256.Proofs.PublicPoint.Interface
import P256.Proofs.PublicPoint.Loop
import P256.Proofs.PublicPoint.Value

set_option autoImplicit false

namespace P256.Proofs.PublicPoint

open P256.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs Program
open Projective.Multiply Projective.Multiply.Machine

theorem public_point_correct_of_stages (bindings : Bindings)
    (prepare : Basepoint.Contract bindings)
    (normalize : ∀ (s t : RamState) (boundary : ReturnBoundary) (d : Nat),
      CalleePre s boundary 0x10e6f0 32 65 3352 → Multiplied s t boundary d →
      ∃ u, CalleeResult s u boundary 65 3352 ∧
        Sec1.AffineAt u (s.regValue .rdi) ((model Basepoint.basePoint d).toAffine)) :
    Contract bindings := by
  intro s boundary d pre value
  obtain ⟨t, ready⟩ := prepare s boundary d pre value
  obtain ⟨u, multiplied⟩ := multiply_call pre ready
  obtain ⟨v, result, affine⟩ := normalize s u boundary d pre multiplied
  rw [model_toAffine d value.1] at affine
  exact ⟨v, result, affine⟩

end P256.Proofs.PublicPoint
