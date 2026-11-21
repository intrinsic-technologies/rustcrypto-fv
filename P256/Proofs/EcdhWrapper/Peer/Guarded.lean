import P256.Proofs.EcdhWrapper.Scalar.Prefix
import P256.Proofs.EcdhWrapper.Scalar.Payload
import P256.Proofs.EcdhWrapper.Peer.Guards

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem guarded [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ address t, (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      MachineRamUnitStrideDecodable bindings t ∧
      SupportedIntegerMachineState bindings.processor t ∧ DirectionFlagUnset t ∧
      ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP = 0x106a04 ∧ stackPtr t = stackPtr initial-504 ∧
      t.regValue .r12 = address ∧ t.regValue .rbp = BitVec.ofNat 64 peer.size ∧
      memLoad initial.external (initial.regValue .rdi+8) 64 = address ∧
      Nat256At t (stackPtr initial-160) (Arith.uint secret) ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ reg ∈ savedRegisters,
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
          initial.regValue reg.1) ∧
      memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip ∧
      memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx ∧
      memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8 ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨a,start⟩ := Scalar.prefix_correct hb hm call
  obtain ⟨b,⟨nb,runB⟩,readyB,loadedB,ripB,rspB,scalarB,frameB,agB⟩ :=
    Scalar.payload_correct call (outer_boundary call hm hb)
      (readyToStep start.machine start.bindingsSupported) start.loaded start.allocated
      start.frame start.rip start.rsp start.nonzero start.valid start.scalar
  have hbB := bindingsSupported_of_ready_agrees start.bindingsSupported readyB agB
  have hmB := supportedMachine_of_ready_agrees start.machine readyB agB
  have directionB := agB.directionFlagClear
    (by simp [Scalar.payloadClobbers,Nonzero.clobbers]) start.directionFlag
  have pointersB : b.regValue .r12 = initial.regValue .rdi :=
    (agB.read (n := 64) (r := 12)
      (by simp [Scalar.payloadClobbers,Nonzero.clobbers])).trans start.pointers
  have countB : b.regValue .r13 = 2 :=
    (agB.read (n := 64) (r := 13)
      (by simp [Scalar.payloadClobbers,Nonzero.clobbers])).trans start.count
  have lengthsB : b.regValue .r15 = initial.regValue .rdx :=
    (agB.read (n := 64) (r := 15)
      (by simp [Scalar.payloadClobbers,Nonzero.clobbers])).trans start.lengths
  obtain ⟨address,t,runT,readyT,loadedT,ripT,source,length,pointer,_,_,_,memory,frame,agT⟩ :=
    Guards.correct hb hm call readyB loadedB frameB ripB countB pointersB lengthsB
  have word (offset : Nat) (range : offset ≤ 48 ∨ offset=464 ∨ offset=472) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad a.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
    rw [memory]
    exact Scalar.payload_word call.stackAvailable.1 agB range
  obtain ⟨na,runA⟩ := start.execution
  refine ⟨address,t,⟨na+nb+17,(runA.trans runB).trans runT⟩,
    bindingsSupported_of_ready_agrees hbB readyT agT,
    supportedMachine_of_ready_agrees hmB readyT agT,
    agT.directionFlagClear (by simp) directionB,loadedT,
    fun p hp => agT.grow p (agB.grow p (start.allocated p hp)),ripT,
    (agT.read (n := 64) (r := 4) (by simp)).trans rspB,
    source,length,pointer,?_,frame,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat256At,memory] using scalarB
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (word reg.2 (.inl bound)).trans (start.saved reg member)
  · have keep : memLoad t.external (stackPtr initial) 64 =
        memLoad a.external (stackPtr initial) 64 := by
      simpa only [BitVec.sub_zero] using word 0 (.inl (by decide))
    exact keep.trans start.returnAddress
  · exact (word 472 (.inr (.inr rfl))).trans start.output
  · exact (word 464 (.inr (.inl rfl))).trans start.capacity
  · exact (agT.mxcsr (by simp)).trans
      ((agB.mxcsr (by simp [Scalar.payloadClobbers,Nonzero.clobbers])).trans start.mxcsr)
  · exact (agT.fcw (by simp)).trans
      ((agB.fcw (by simp [Scalar.payloadClobbers,Nonzero.clobbers])).trans start.fp87)

end P256.Proofs.EcdhWrapper.Peer
