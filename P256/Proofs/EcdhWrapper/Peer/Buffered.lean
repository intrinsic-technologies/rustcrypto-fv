import P256.Proofs.EcdhWrapper.Peer.Padded
import P256.Proofs.EcdhWrapper.Peer.Buffer

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem buffer_frame [Bindings] {initial s t : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (rsp : stackPtr s = stackPtr initial-504)
    (ag : AgreesExcept (Buffer.components (stackPtr s)) s t) :
    MemoryWriteFrame s t (wrapperRegions ecdhDiffieHellman initial) := by
  apply ag.memoryWriteFrame
  intro c hc a cover
  simp only [Buffer.components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact cover.elim
  all_goals exact ⟨callStack ecdhDiffieHellman initial,by simp [wrapperRegions],
    stack_contains_callStack (Buffer.inside call rsp (by decide) cover)⟩

theorem buffer_scalar {initial s t : RamState} {x : Nat}
    (rsp : stackPtr s = stackPtr initial-504)
    (ag : AgreesExcept (Buffer.components (stackPtr s)) s t)
    (value : Nat256At s (stackPtr initial-160) x) :
    Nat256At t (stackPtr initial-160) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  have eq : stackPtr s+BitVec.ofNat 64 (344+i) =
      stackPtr initial-160+BitVec.ofNat 64 i := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc,Buffer.address rsp (by decide)]
    rfl
  have copied := Buffer.byte_preserved ag (i := 344+i) (by omega) (.inr (by omega))
  rw [eq] at copied
  exact copied.trans (value.2 i hi)

theorem buffered [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      MachineRamUnitStrideDecodable bindings t ∧
      SupportedIntegerMachineState bindings.processor t ∧ DirectionFlagUnset t ∧
      ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP = 0x106b70 ∧ stackPtr t = stackPtr initial-504 ∧
      Nat256At t (stackPtr initial-160) (Arith.uint secret) ∧
      Sec1.EncodedPointAt t (stackPtr initial-264) peer ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ reg ∈ savedRegisters,
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
          initial.regValue reg.1) ∧
      memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip ∧
      memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx ∧
      memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8 ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨s,⟨n,run⟩,hs,ms,ds,ls,gs,ips,sps,scalar,bytes,frame,saved,ret,out,cap,mx,fp⟩ :=
    padded hb hm call
  obtain ⟨t,step,readyT,loadedT,ripT,rspT,encoded,_,words,ag⟩ :=
    Buffer.correct call (outer_boundary call hm hb) (readyToStep ms hs) ls gs sps ips bytes
  refine ⟨t,⟨n+45,run.trans step⟩,bindingsSupported_of_ready_agrees hs readyT ag,
    supportedMachine_of_ready_agrees ms readyT ag,
    ag.directionFlagClear (by simp [Buffer.components]) ds,loadedT,
    fun a ha => ag.grow a (gs a ha),ripT,rspT,buffer_scalar sps ag scalar,encoded,
    memoryWriteFrame_trans frame (buffer_frame call sps ag),?_,?_,
    (words 472 (.inr (by decide))).trans out,(words 464 (.inr (by decide))).trans cap,
    (ag.mxcsr (by simp [Buffer.components])).trans mx,
    (ag.fcw (by simp [Buffer.components])).trans fp⟩
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (words reg.2 (.inl bound)).trans (saved reg member)
  · have keep : memLoad t.external (stackPtr initial) 64 =
        memLoad s.external (stackPtr initial) 64 := by
      simpa only [BitVec.sub_zero] using words 0 (.inl (by decide))
    exact keep.trans ret

end P256.Proofs.EcdhWrapper.Peer
