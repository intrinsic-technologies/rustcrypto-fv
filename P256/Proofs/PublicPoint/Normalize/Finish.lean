import P256.Proofs.PublicPoint.Normalize.Finish.Prepare
import P256.Proofs.PublicPoint.Normalize.Finish.Select

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : Coordinates s t boundary point) :
    ∃ u, CalleeResult s u boundary 65 3352 ∧ Sec1.AffineAt u (s.regValue .rdi) point.toAffine := by
  obtain ⟨a, saved⟩ := Finish.save_coordinates pre state
  obtain ⟨b, prepared⟩ := Finish.prepare pre saved
  obtain ⟨c, selected⟩ := Finish.select pre prepared
  exact Finish.finish_selected pre selected

end P256.Proofs.PublicPoint.Normalize
