import P256.Proofs.PublicPoint.Normalize.Stages
import P256.Proofs.PublicPoint.Normalize.Finish

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem normalize [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Multiplied s t boundary d) :
    ∃ u, CalleeResult s u boundary 65 3352 ∧
      Sec1.AffineAt u (s.regValue .rdi)
        (Projective.Multiply.model Projective.Multiply.Machine.Basepoint.basePoint d).toAffine := by
  obtain ⟨v, coordinates⟩ := coordinates_from_multiplied pre state
  exact finish pre coordinates

end P256.Proofs.PublicPoint.Normalize
