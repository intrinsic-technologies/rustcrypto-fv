import P256.Proofs.Ecdh.Normalize.Invert.Select

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize

open P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem inversion_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : Pre s boundary) (state : Multiplied s t point)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, Selected s u boundary point := by
  obtain ⟨v, inverted⟩ := invert pre.toCalleePre state execution
  exact select_inverse pre.toCalleePre inverted

end P256.Proofs.Ecdh.Normalize
