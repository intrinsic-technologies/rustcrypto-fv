import P256.Proofs.Projective.Add.CrossTerms.XY
import P256.Proofs.Projective.Add.CrossTerms.YZ
import P256.Proofs.Projective.Add.CrossTerms.XZ

set_option autoImplicit false


namespace P256.Proofs.Projective.Add

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem cross_terms_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (rip : t.RIP = 0x10531f)
    (input : ProductsAt s t left right) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x10573e ∧ CrossTermsAt s u left right := by
  obtain ⟨n₁, u₁, run₁, frame₁, rip₁, products₁, xy₁⟩ :=
    CrossTerms.xy_correct pre state rip input
  obtain ⟨n₂, u₂, run₂, frame₂, rip₂, products₂, xy₂, yz₂⟩ :=
    CrossTerms.yz_correct pre frame₁ rip₁ products₁ xy₁
  obtain ⟨n₃, u₃, run₃, frame₃, rip₃, result⟩ :=
    CrossTerms.xz_correct pre frame₂ rip₂ products₂ xy₂ yz₂
  exact ⟨n₁ + n₂ + n₃, u₃, (run₁.trans run₂).trans run₃, frame₃, rip₃, result⟩

end P256.Proofs.Projective.Add
