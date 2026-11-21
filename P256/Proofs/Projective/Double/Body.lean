import P256.Proofs.Projective.Double.CrossTerms.Correct
import P256.Proofs.Projective.Double.Products
import P256.Proofs.Projective.Double.Combinations
import P256.Proofs.Projective.Double.Output

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem body_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x105dc3)
    (input : SquaresAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x106462 ∧ OutputAt s u point := by
  obtain ⟨n₁, t₁, run₁, frame₁, rip₁, values₁⟩ := cross_terms_correct pre state rip input
  obtain ⟨n₂, t₂, run₂, frame₂, rip₂, values₂⟩ := products_correct pre frame₁ rip₁ values₁
  obtain ⟨n₃, t₃, run₃, frame₃, rip₃, values₃⟩ := combinations_correct pre frame₂ rip₂ values₂
  obtain ⟨n₄, t₄, run₄, frame₄, rip₄, values₄⟩ := output_correct pre frame₃ rip₃ values₃
  exact ⟨n₁ + n₂ + n₃ + n₄, t₄, ((run₁.trans run₂).trans run₃).trans run₄,
    frame₄, rip₄, values₄⟩

end P256.Proofs.Projective.Double
