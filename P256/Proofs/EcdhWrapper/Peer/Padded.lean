import P256.Proofs.EcdhWrapper.Peer.Guarded
import P256.Proofs.EcdhWrapper.Peer.Pad

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)

theorem scalar_after_padding {initial s t : RamState} {x : Nat}
    (stack : Stack.Valid initial 4104)
    (frame : MemoryWriteFrame s t #v[Pad.work initial])
    (value : Nat256At s (stackPtr initial-160) x) :
    Nat256At t (stackPtr initial-160) x := by
  have bounds := stack_bounds stack
  have low : (stackPtr initial-160).toNat = (stackPtr initial).toNat-160 :=
    stack_sub_toNat stack (offset := 160) (by decide)
  refine ⟨value.1,fun i hi => ?_⟩
  rw [frame _]
  · exact value.2 i hi
  · intro region hr hin
    have eq : region = Pad.work initial := by simpa using hr
    subst region
    change _ ≤ _ ∧ _ < (stackPtr initial).toNat-4104+(4104-264) at hin
    rw [toNat_add_ofNat _ _ (by rw [low]; omega),low] at hin
    omega

theorem padded [bindings : Bindings] {initial : RamState} {secret peer : ByteArray}
    {slices : Array Input}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel initial t) ∧
      MachineRamUnitStrideDecodable bindings t ∧
      SupportedIntegerMachineState bindings.processor t ∧ DirectionFlagUnset t ∧
      ProgramLoaded t ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome) ∧
      t.RIP = 0x106a3d ∧ stackPtr t = stackPtr initial-504 ∧
      Nat256At t (stackPtr initial-160) (Arith.uint secret) ∧
      Sec1.EncodedPointAt t (stackPtr initial-336) peer ∧
      MemoryWriteFrame initial t (wrapperRegions ecdhDiffieHellman initial) ∧
      (∀ reg ∈ savedRegisters,
        memLoad t.external (stackPtr initial-BitVec.ofNat 64 reg.2) 64 =
          initial.regValue reg.1) ∧
      memLoad t.external (stackPtr initial) 64 = (returnBoundary initial).rip ∧
      memLoad t.external (stackPtr initial-472) 64 = initial.regValue .rcx ∧
      memLoad t.external (stackPtr initial-464) 64 = initial.regValue .r8 ∧
      t.MXCSR = initial.MXCSR ∧ t.FP87_Control = initial.FP87_Control := by
  obtain ⟨address,s,⟨n,run⟩,hs,ms,ds,ls,gs,ips,sps,source,length,pointer,
    scalar,frame,saved,ret,out,cap,mx,fp⟩ := guarded hb hm call
  obtain ⟨t,⟨m,step⟩,ht,mt,dt,lt,gt,ipt,spt,_,mxt,fpt,work,frameT,words,slots,encoded⟩ :=
    Pad.correct hb hm call hs ms ds ls gs frame ips sps source length pointer
  refine ⟨t,⟨n+m,run.trans step⟩,ht,mt,dt,lt,gt,ipt,spt,
    scalar_after_padding call.stackAvailable.1 work scalar,encoded,frameT,
    ?_,?_,(slots 472 (.inr rfl)).trans out,(slots 464 (.inl rfl)).trans cap,
    mxt.trans mx,fpt.trans fp⟩
  · intro reg member
    have bound : reg.2 ≤ 264 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (words reg.2 bound).trans (saved reg member)
  · have keep : memLoad t.external (stackPtr initial) 64 =
        memLoad s.external (stackPtr initial) 64 := by
      simpa only [BitVec.sub_zero] using words 0 (by decide)
    exact keep.trans ret

end P256.Proofs.EcdhWrapper.Peer
