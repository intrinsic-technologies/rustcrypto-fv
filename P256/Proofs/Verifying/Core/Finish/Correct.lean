import P256.Proofs.Verifying.Core.Finish.Normalize
import P256.Proofs.Verifying.Core.Finish.Tail.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y r : Nat} {nonzero : Bool} (pre : Core.Pre s boundary)
    (frame : Frame s t) (rip : t.RIP = 0x10df44)
    (hx : Field.MontgomeryAt t (stackPtr s-600) x)
    (hy : Field.MontgomeryAt t (stackPtr s-784) y)
    (r15 : t.regValue .r15 = stackPtr s-600)
    (choice : (t.regValue .rbx).setWidth 8 = if nonzero then 1 else 0)
    (scalar : Nat256At t (stackPtr s-472) r)
    (output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e16c ∧
      memLoad u.external (frameBase s+384) 64 = s.regValue .rdi ∧
      (u.regValue .rax).setWidth 8 =
        if (if nonzero then x else 0) % Operations.domain.n == r then 1 else 0 := by
  obtain ⟨n,a,runA,frameA,ripA,xA,rA,outA⟩ :=
    normalize pre frame rip hx hy r15 choice scalar output
  obtain ⟨m,u,runU,frameU,ripU,outU,result⟩ := Tail.finish pre frameA ripA xA rA outA
  exact ⟨n+m,u,runA.trans runU,frameU,ripU,outU,result⟩

end P256.Proofs.Verifying.Core.Finish
