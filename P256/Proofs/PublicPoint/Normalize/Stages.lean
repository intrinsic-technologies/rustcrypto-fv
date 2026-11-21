import P256.Proofs.PublicPoint.Normalize.Invert.Select
import P256.Proofs.PublicPoint.Normalize.Coordinates

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem coordinates_from_multiplied [Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Multiplied s t boundary d) :
    ∃ u, Coordinates s u boundary
      (Projective.Multiply.model Projective.Multiply.Machine.Basepoint.basePoint d) := by
  obtain ⟨v, inverted⟩ := invert pre state
  obtain ⟨w, selected⟩ := select_inverse pre inverted
  exact coordinates pre selected

end P256.Proofs.PublicPoint.Normalize
