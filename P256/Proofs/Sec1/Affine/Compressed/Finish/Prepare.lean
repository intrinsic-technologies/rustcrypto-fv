import P256.Proofs.Sec1.Affine.Compressed.Finish.Relocate
import P256.Proofs.Sec1.Affine.Compressed.Finish.Initialize
import P256.Proofs.Sec1.Affine.Compressed.Finish.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compressed.Finish

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    {point : Option Curve.Point} (pre : AffineDecodePre s boundary bytes)
    (state : Frame s t) (rip : t.RIP = 0x110128)
    (source : t.regValue .r15 = stackPtr s - 592)
    (output : t.regValue .rbx = s.regValue .rdi)
    (decoded : AffineResultAt t (stackPtr s - 592) point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Prepared s u point := by
  obtain ⟨n,a,runA,frameA,ripA,decodedA,rdxA,r14A,rbxA⟩ := relocate pre state rip source decoded
  obtain ⟨m,u,runU,frameU,ripU,decodedU,_,raxU,agrees⟩ := prepare_identity pre frameA ripA decodedA
  refine ⟨n+m,u,runA.trans runU,frameU,ripU,?_,decodedU,raxU,?_,?_⟩
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans (rbxA.trans output)
  · exact (agrees.read (n := 64) (r := 2) (by simp)).trans rdxA
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans r14A

end P256.Proofs.Sec1.Affine.Compressed.Finish
