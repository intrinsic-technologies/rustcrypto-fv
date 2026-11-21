import P256.Proofs.Sec1.Affine.Compact.Finish.Relocate
import P256.Proofs.Sec1.Affine.Compact.Finish.Initialize
import P256.Proofs.Sec1.Affine.Compact.Finish.Select
import P256.Proofs.Sec1.Affine.Compact.Finish.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Prepared s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) (point.map fun
        | .affine x y => .affine x (Spec.Points.compactY y)
        | .infinity => .infinity) := by
  obtain ⟨n,a,runA,stateA⟩ := relocate pre state
  obtain ⟨m,b,runB,stateB⟩ := initialize_identity pre stateA
  obtain ⟨k,c,runC,stateC⟩ := select_x pre stateB
  obtain ⟨l,d,runD,stateD⟩ := select_y pre stateC
  obtain ⟨f,u,runU,frame,rip,result⟩ := selected_result pre stateD
  exact ⟨n+m+k+l+f,u,(((runA.trans runB).trans runC).trans runD).trans runU,frame,rip,result⟩

end P256.Proofs.Sec1.Affine.Compact.Finish
