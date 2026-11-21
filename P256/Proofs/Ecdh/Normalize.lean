import P256.Proofs.Ecdh.Normalize.Invert
import P256.Proofs.Ecdh.Normalize.Coordinates
import P256.Proofs.Ecdh.Normalize.Finish

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem normalize_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : Pre s boundary) (state : Multiplied s t point)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 3464 ∧
      (registerRegion s .rdi 32).HasBytes u.external (Points.xBytes point.toAffine) := by
  obtain ⟨v, inverted⟩ := Normalize.inversion_correct pre state execution
  obtain ⟨w, coordinates⟩ := Normalize.coordinates pre.toCalleePre inverted
  obtain ⟨q, prepared⟩ := Normalize.Finish.prepare pre.toCalleePre coordinates
  obtain ⟨r, selected⟩ := Normalize.Finish.select pre.toCalleePre prepared
  obtain ⟨u, result, bytes⟩ := Normalize.Finish.output pre.toCalleePre selected
  exact ⟨u, result, by simpa only [Normalize.Finish.selected_xBytes] using bytes⟩

end P256.Proofs.Ecdh
