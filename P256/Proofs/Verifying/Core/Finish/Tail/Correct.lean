import P256.Proofs.Verifying.Core.Finish.Tail.Decode
import P256.Proofs.Verifying.Core.Finish.Tail.Compare

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e098)
    (input : x < 2^256 ∧ (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes t.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x))
    (scalar : Nat256At t (frameBase s+704) r)
    (output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e16c ∧
      memLoad u.external (frameBase s+384) 64 = s.regValue .rdi ∧
      (u.regValue .rax).setWidth 8 = if x % Operations.domain.n == r then 1 else 0 := by
  obtain ⟨n,a,runA,stateA,ripA,bxA,xA,rA⟩ := decode pre state rip input scalar
  obtain ⟨m,u,runU,stateU,ripU,bxU,result⟩ := compare pre stateA ripA xA rA
  exact ⟨n+m,u,runA.trans runU,stateU,ripU,(bxU.trans bxA).trans output,result⟩

end P256.Proofs.Verifying.Core.Finish.Tail
