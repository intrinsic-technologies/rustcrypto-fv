import P256.Proofs.Verifying.Core.Digest.Decode
import P256.Proofs.Verifying.Core.Digest.Finish.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem digest_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} {r scalarS : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dbb2)
    (pointers : Prepare.Pointers s t)
    (bytes : (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion).HasBytes t.external digest)
    (savedR : Nat256At t (frameBase s+704) r)
    (savedS : Nat256At t (frameBase s+736) scalarS) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10dc78 ∧
      Prepare.Pointers s u ∧
      Nat256At u (frameBase s+968) (Arith.uint digest % Operations.domain.n) ∧
      Nat256At u (frameBase s+704) r ∧ Nat256At u (frameBase s+736) scalarS ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,ripA,pointersA,valueA,rA,sA,memoryA⟩ :=
    decode pre state rip pointers bytes savedR savedS
  obtain ⟨m,u,runU,stateU,ripU,pointersU,valueU,rU,sU,memoryU⟩ :=
    Finish.finish pre stateA ripA pointersA valueA rA sA
  exact ⟨n+m,u,runA.trans runU,stateU,ripU,pointersU,valueU,rU,sU,
    memoryWriteFrame_trans memoryA memoryU⟩

end P256.Proofs.Verifying.Core.Digest
