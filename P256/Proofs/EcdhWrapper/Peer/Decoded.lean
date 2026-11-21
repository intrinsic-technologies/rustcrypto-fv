import P256.Proofs.EcdhWrapper.Peer.Buffered
import P256.Proofs.EcdhWrapper.Peer.Return
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem decoded_of_raw [bindings : Bindings]
    (raw : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      Sec1.AffineDecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3360 ∧
        Sec1.AffineResultAt t (s.regValue .rdi) (Points.decodePoint bytes))
    {initial : RamState} {secret peer : ByteArray} {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ point t, Points.decodePoint peer = some point ∧
      (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      MachineRamUnitStrideDecodable bindings t ∧
      SupportedIntegerMachineState bindings.processor t ∧ DirectionFlagUnset t ∧
      ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP = 0x106b85 ∧ stackPtr t = stackPtr initial-504 ∧
      Nat256At t (stackPtr initial-160) (Arith.uint secret) ∧
      Sec1.AffineAt t (stackPtr initial-128) point ∧
      t.external[stackPtr initial-56]? = some 1 ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ reg ∈ savedRegisters,
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
          initial.regValue reg.1) ∧
      memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip ∧
      memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx ∧
      memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8 ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨s,⟨n,run⟩,hs,ms,ds,ls,gs,ips,sps,scalar,bytes,frame,saved,ret,out,cap,mx,fp⟩ :=
    buffered hb hm call
  obtain ⟨called,⟨m,step⟩,pre,calledRsp,calledOutput,calledReturn,ag⟩ :=
    enter call hs ms ds ls gs (outer_boundary call hm hb) ips sps bytes
  obtain ⟨t,result,value⟩ := raw called (returnBoundary initial) peer pre
  obtain ⟨point,_,_,_,decoded,_,_⟩ := arguments_decoded call.argumentsValid
  rw [decoded,calledOutput] at value
  have validAddress : stackPtr initial-128+72 = stackPtr initial-56 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have word (offset : Nat) (range : offset ≤ 48 ∨ offset=464 ∨ offset=472) :=
    return_word call.stackAvailable.1 ag calledRsp calledOutput result range
  obtain ⟨k,finish⟩ := result.execution
  refine ⟨point,t,decoded,⟨n+m+k,(run.trans step).trans finish⟩,
    result.bindingsSupported,result.machine,result.directionFlag,result.loaded,
    fun a ha => result.allocated a (ag.grow a (gs a ha)),result.rip.trans calledReturn,?_,
    return_scalar call.stackAvailable.1 ag calledRsp calledOutput result scalar,value.1,?_,
    return_frame call.stackAvailable.1 frame ag calledRsp calledOutput result,?_,?_,
    (word 472 (.inr (.inr rfl))).trans out,(word 464 (.inr (.inl rfl))).trans cap,
    result.mxcsr.trans ((ag.mxcsr (by simp [callComponents])).trans mx),
    result.fp87.trans ((ag.fcw (by simp [callComponents])).trans fp)⟩
  · have returned : stackPtr t = stackPtr called+8 := result.rsp
    rw [returned,calledRsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · simpa only [validAddress] using value.2
  · intro reg member
    have bound : reg.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (word reg.2 (.inl bound)).trans (saved reg member)
  · have keep : memLoad t.external (stackPtr initial) 64 =
        memLoad s.external (stackPtr initial) 64 := by
      simpa only [BitVec.sub_zero] using word 0 (.inl (by decide))
    exact keep.trans ret

end P256.Proofs.EcdhWrapper.Peer
