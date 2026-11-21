import P256.Proofs.Sec1.Affine.Compressed.Finish.Prepare
import P256.Proofs.Sec1.Affine.Compressed.Finish.Select
import P256.Proofs.Sec1.Affine.Compressed.Finish.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem finish_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110128)
    (source : t.regValue .r15 = stackPtr s - 592)
    (output : t.regValue .rbx = s.regValue .rdi)
    (decoded : AffineResultAt t (stackPtr s - 592) point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x110d22 ∧
      AffineResultAt u (s.regValue .rdi) point := by
  obtain ⟨n,a,runA,stateA⟩ := Finish.prepare pre state rip source output decoded
  obtain ⟨m,b,runB,stateB⟩ := Finish.select_x pre stateA
  obtain ⟨k,c,runC,stateC⟩ := Finish.select_y pre stateB
  obtain ⟨l,u,runU,frame,rip,result⟩ := Finish.selected_result pre stateC
  exact ⟨n+m+k+l,u,((runA.trans runB).trans runC).trans runU,frame,rip,result⟩

end P256.Proofs.Sec1.Affine.Compressed
