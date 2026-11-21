import P256.Proofs.Verifying.Core.Scalars.Invert
import P256.Proofs.Verifying.Core.Scalars.FirstProduct
import P256.Proofs.Verifying.Core.Scalars.SecondProduct
import P256.Proofs.Verifying.Core.Digest.Correct
import P256.Proofs.Verifying.Core.Prepare.Signature
import P256.Proofs.Verifying.Core.Arithmetic
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Scalars

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar
open Standards.SECG.ECC

structure Prepared [Bindings] (s t : RamState) (point : Projective) (digest : ByteArray)
    (r scalarS : Nat) : Prop extends Frame s t where
  rip : t.RIP = 0x10dd69
  pointers : Prepare.Pointers s t
  key : ProjectiveAt t (frameBase s+1000) point
  first : Nat256At t (frameBase s+800)
    (ECDSA.digestToInt Operations.domain.n digest * Curve.inverse Operations.domain.n scalarS % Operations.domain.n)
  second : Nat256At t (frameBase s+832)
    (r * Curve.inverse Operations.domain.n scalarS % Operations.domain.n)
  savedR : Nat256At t (frameBase s+704) r
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi

set_option maxHeartbeats 800000 in
theorem prepare_of_inverse [Bindings] {s entry : RamState} {boundary : ReturnBoundary}
    {point : Projective} {digest : ByteArray} {r scalarS : Nat}
    (core : Core.Inverse.CoreStage) (pre : Core.Pre s boundary)
    (frame : Frame s entry) (rip : entry.RIP = 0x10da4d)
    (input : Core.InputAt s entry point digest r scalarS)
    (rPositive : 0 < r) (sPositive : 0 < scalarS) (sBound : scalarS < Operations.domain.n) :
    ∃ n t, Advances boundary n entry t ∧ Prepared s t point digest r scalarS := by
  obtain ⟨n,a,runA,stateA,ripA,pointersA,rA,sA,memoryA⟩ :=
    Prepare.signature_scalars pre frame rip input.signature input.r input.scalarS rPositive sPositive
  have rA' : Nat256At a (frameBase s+704) r := by
    change Nat256At a (frameBase s+704#64) r
    rw [slot_address s 704 (by decide)]
    exact rA
  have sA' : Nat256At a (frameBase s+736) scalarS := by
    change Nat256At a (frameBase s+736#64) scalarS
    rw [slot_address s 736 (by decide)]
    exact sA
  obtain ⟨m,b,runB,stateB,ripB,pointersB,dB,rB,sB,memoryB⟩ :=
    Digest.digest_correct pre stateA ripA pointersA (Digest.digest_bytes pre memoryA input.digest) rA' sA'
  obtain ⟨k,c,runC,stateC,ripC,pointersC,invC,dC,rC,memoryC⟩ :=
    invert core sPositive sBound pre stateB ripB pointersB dB rB sB
  obtain ⟨l,d,runD,stateD,ripD,pointersD,u1D,invD,rD,memoryD⟩ :=
    first_product pre stateC ripC pointersC dC invC rC
  have memorySD := memoryWriteFrame_trans
    (memoryWriteFrame_trans (memoryWriteFrame_trans memoryA memoryB) memoryC) memoryD
  have signatureD : Nat256At d (s.regValue .r8) r := by
    have h := signature_nat256 pre (offset := 0) (by decide) (prefix_memory_stack pre memorySD)
      (by simpa only [BitVec.add_zero] using input.r)
    simpa only [BitVec.add_zero] using h
  obtain ⟨q,t,runT,stateT,ripT,pointersT,u1T,u2T,rT,memoryT⟩ :=
    second_product pre stateD ripD pointersD signatureD u1D invD rD
  have memory := memoryWriteFrame_trans memorySD memoryT
  refine ⟨n+m+k+l+q,t,(((runA.trans runB).trans runC).trans runD).trans runT,
    ⟨stateT,ripT,pointersT,?_,?_,u2T,rT,?_⟩⟩
  · apply input.point.of_bytes_eq
    intro i hi
    exact prefix_byte pre memory (offset := 1000) (len := 96) (by decide) (by decide) hi
  · rw [Core.reduced_digest_product digest _ input.digest.1] at u1T
    exact u1T
  · exact (prefix_load pre memory (offset := 384) (n := 64) (by decide) (by decide)).trans input.output

end P256.Proofs.Verifying.Core.Scalars
