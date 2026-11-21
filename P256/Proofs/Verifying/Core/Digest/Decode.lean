import P256.Proofs.Verifying.Core.Digest.Setup.Correct
import P256.Proofs.Verifying.Core.Digest.Read

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)

theorem decode [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} {r scalarS : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dbb2)
    (pointers : Prepare.Pointers s t)
    (bytes : (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion).HasBytes t.external digest)
    (savedR : Nat256At t (frameBase s+704) r)
    (savedS : Nat256At t (frameBase s+736) scalarS) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10dc30 ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s) (Arith.uint digest) ∧
      Nat256At u (frameBase s+704) r ∧ Nat256At u (frameBase s+736) scalarS ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,agrees⟩ := setup pre state rip pointers
  have rA := setup_slot (offset := 704) agrees (by decide) (by decide) (by decide) savedR
  have sA := setup_slot (offset := 736) agrees (by decide) (by decide) (by decide) savedS
  have memoryA := agrees.memoryWriteFrame (setup_prefix_writes pre state)
  obtain ⟨m,u,runU,stateU,ripU,pointersU,valueU,rU,sU,memoryU⟩ :=
    read pre stateA (digest_bytes pre memoryA bytes) rA sA
  exact ⟨n+m,u,runA.trans runU,stateU,ripU,pointersU,valueU,rU,sU,
    memoryWriteFrame_trans memoryA memoryU⟩

end P256.Proofs.Verifying.Core.Digest
