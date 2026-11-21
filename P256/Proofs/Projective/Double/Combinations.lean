import P256.Proofs.Projective.Double.Combinations.BProduct
import P256.Proofs.Projective.Double.Combinations.Difference
import P256.Proofs.Projective.Double.Combinations.Triple
import P256.Proofs.Projective.Double.Combinations.Finish

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem combinations_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x1060fe)
    (input : ProductsAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x10635a ∧ CombinationsAt s u point := by
  obtain ⟨_, u, run₁, state₁, rip₁, values₁⟩ := Combinations.b_product pre state rip input
  obtain ⟨_, v, run₂, state₂, rip₂, values₂⟩ := Combinations.difference pre state₁ rip₁ values₁
  obtain ⟨_, w, run₃, state₃, rip₃, values₃⟩ := Combinations.triple pre state₂ rip₂ values₂
  obtain ⟨_, z, run₄, state₄, rip₄, values₄⟩ := Combinations.finish pre state₃ rip₃ values₃
  exact ⟨_, z, ((run₁.trans run₂).trans run₃).trans run₄, state₄, rip₄, values₄⟩

end P256.Proofs.Projective.Double
