import P256.Proofs.Verifying.Wrapper.SignatureCopied
import P256.Proofs.Verifying.Wrapper.MessageSetup
import P256.Proofs.Verifying.Wrapper.MessageCall

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open SecretKeyFromBytes.Scalar (Nat256At)

theorem message_entry [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input} {point : Curve.Point} {r scalarS : Nat}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : SignatureReady initial s point r scalarS)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ a t, ReturnState initial a ∧ a.regValue .r12 = initial.regValue .rcx ∧
      a.regValue .r13 = initial.regValue .r8 ∧ Message.Pre t (returnBoundary initial) message ∧
      Message.InputAt t point r scalarS ∧ t.regValue .rdi = stackPtr initial-208 ∧
      stackPtr t = stackPtr initial-288 ∧ (returnBoundary t).rip = 0x1031e9 ∧
      AgreesExcept (messageCallComponents initial) a t ∧
      MemoryWriteFrame a t #v[workRegion initial] ∧
      MemoryWriteFrame initial t (wrapperRegions verifyingKeyVerify initial) ∧
      ∃ fuel, Advances (returnBoundary initial) fuel initial t := by
  obtain ⟨na,a,runA,stateA,ripA,outputA,sourceA,descriptorA,scalarA,countA,
    pointerA,lengthA,agA,frameA⟩ := message_setup call state.toReturnState state.frame outside
      state.rip state.count state.pointers state.lengths
  have originalA := memoryWriteFrame_trans state.frame (work_frame call.stackAvailable.1 frameA)
  obtain ⟨t,runT,pre,outputT,sourceT,scalarT,sp,ret,agT,frameT⟩ :=
    enter_message call stateA originalA outside ripA outputA sourceA descriptorA
      scalarA countA pointerA lengthA
  have unchanged (offset len : Nat) (above : offset+8 ≤ 288) (extent : len ≤ offset+8)
      (apart1 : 128+len ≤ offset ∨ offset+8 ≤ 128)
      (apart2 : 120+len ≤ offset ∨ offset+8 ≤ 120) :
      ∀ i < len, t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
        s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
    intro i hi
    exact (message_call_byte call.stackAvailable.1 agT above extent i hi).trans
      (message_setup_byte call.stackAvailable.1 agA (by omega) extent apart1 apart2 i hi)
  have pointT : Sec1.AffineAt t (stackPtr initial-112) point :=
    state.pointAt.of_bytes_eq (unchanged 112 65 (by decide) (by decide)
      (Or.inr (by decide)) (Or.inr (by decide)))
  have rT : Nat256At t (stackPtr initial-280) r := by
    refine ⟨state.rAt.1,?_⟩
    intro i hi
    exact (unchanged 280 32 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)) i hi).trans (state.rAt.2 i hi)
  have sT : Nat256At t (stackPtr initial-248) scalarS := by
    refine ⟨state.sAt.1,?_⟩
    intro i hi
    exact (unchanged 248 32 (by decide) (by decide)
      (Or.inl (by decide)) (Or.inl (by decide)) i hi).trans (state.sAt.2 i hi)
  obtain ⟨nf,first⟩ := state.execution
  refine ⟨a,t,stateA,?_,?_,pre,?_,outputT,sp,ret,agT,frameT,
    memoryWriteFrame_trans originalA (work_frame call.stackAvailable.1 frameT),
    ⟨nf+na+1,(first.trans runA).trans runT⟩⟩
  · exact (agA.read (n := 64) (r := 12) (by simp [messageSetupComponents])).trans state.output
  · exact (agA.read (n := 64) (r := 13) (by simp [messageSetupComponents])).trans state.capacity
  · refine ⟨sourceT ▸ pointT,scalarT ▸ rT,?_⟩
    rw [scalarT]
    have address : stackPtr initial-280+32 = stackPtr initial-248 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    simpa only [address] using sT

end P256.Proofs.Verifying.Wrapper
