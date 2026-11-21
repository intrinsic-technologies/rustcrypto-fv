import P256.Proofs.Sec1.Affine.Compact.Select.Initialize
import P256.Proofs.Sec1.Affine.Compact.Select.Correct

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Standards.SECG.ECC

theorem select_decompressed [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {point : Option Curve.Point}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x11022c) (decoded : AffineResultAt t (stackPtr s - 744) point)
    (output : t.regValue .rbx = s.regValue .rdi)
    (source : t.regValue .r15 = stackPtr s - 744) (zero : t.regValue .r13 = 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Select.Selected s u point := by
  obtain ⟨n,a,runA,frameA,ripA,decodedA,identity,rax,agrees⟩ :=
    Select.initialize_identity pre state rip decoded
  have initialized : Select.Initialized s a point :=
    ⟨frameA,ripA,(agrees.read (n := 64) (r := 3) (by simp)).trans output,
      decodedA,identity,rax,(agrees.read (n := 64) (r := 15) (by simp)).trans source,
      (agrees.read (n := 64) (r := 13) (by simp)).trans zero⟩
  obtain ⟨m,b,runB,frameB⟩ := Select.select_x pre initialized
  obtain ⟨k,u,runU,frameU⟩ := Select.select_y pre frameB
  exact ⟨n+m+k,u,(runA.trans runB).trans runU,frameU⟩

end P256.Proofs.Sec1.Affine.Compact
