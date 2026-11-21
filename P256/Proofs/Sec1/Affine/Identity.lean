import P256.Proofs.Sec1.Affine.Identity.Setup
import P256.Proofs.Sec1.Affine.Identity.Copy
import P256.Proofs.Sec1.Affine.Identity.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Identity

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩)
    (state : Tagged s t 0) (rip : t.RIP = 0x110612) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (Spec.Points.decodePoint ⟨#[0]⟩) := by
  obtain ⟨a, aa, sa, ia, output, dst, src, count⟩ := setup pre state rip
  obtain ⟨b, ab, sb, ib, value, output'⟩ := copy pre sa ia src dst count
  obtain ⟨u, au, su, iu, result⟩ := finish pre sb ib (output'.trans output) value
  exact ⟨16, u, (aa.trans ab).trans au, su, iu, by
    simpa only [decodePoint_identity] using result⟩

end P256.Proofs.Sec1.Affine.Identity
