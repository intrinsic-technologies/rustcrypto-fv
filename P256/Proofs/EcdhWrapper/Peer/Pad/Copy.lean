import P256.Proofs.EcdhWrapper.Peer.Pad.Fill
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray} {slices : Array Input}

theorem copy (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x106a37) (rsp : stackPtr s=stackPtr initial-504)
    (shape : Sec1.EncodingShape peer)
    (destination : s.regValue .rdi=stackPtr initial-336#64)
    {address : BitVec 64} (source : s.regValue .rsi=address)
    (count : s.regValue .rdx=BitVec.ofNat 64 peer.size)
    (pointer : memLoad initial.external (initial.regValue .rdi+8) 64=address)
    (bound : (MemoryRegion.mk address.toNat peer.size).Bounded)
    (bytes : (MemoryRegion.mk address.toNat peer.size).HasBytes s.external peer)
    (padding : ∀ i<65, peer.size≤i → s.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=some 0) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      u.RIP=0x106a3d ∧ stackPtr u=stackPtr initial-504 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r=s.regValue r) ∧
      u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[work initial] ∧
      (∀ offset, offset=464 ∨ offset=472 →
        memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      Sec1.EncodedPointAt u (stackPtr initial-336) peer := by
  have sizeBound : peer.size≤65 := by have := shape.size; omega
  obtain ⟨v,run,ready,effect⟩ := memory_call true call outside (readyToStep hm hb) loaded grow rsp rip
  have push : pushAddr s=stackPtr initial-512#64 := by rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  have sp : stackPtr v=stackPtr initial-512#64 := effect.writes.1.trans push
  have dst : v.regValue .rdi=stackPtr initial-336#64 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have src : v.regValue .rsi=address := (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have bytesV := peer_bytes call pointer bound
    (effect.agrees.memoryWriteFrame (push_writes call.stackAvailable.1 rsp)) bytes
  let layout : StackBufferLayout 4104 peer.size 0 := ⟨512,336,by decide,by decide,by decide,by omega⟩
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have avoid : (Stack.region initial 4104).Avoids (fun a ↦ InProgram a ∨ P256.Spec.Program.Routines.InPageTables a) :=
    call_stack_avoids (routine := ecdhDiffieHellman) call
  have child : CalleePre v (returnBoundary initial) 0x11c930 peer.size peer.size 0 := by
    apply CalleePre.of_disjoint_input_and_stack layout stack avoid
      (bindingsSupported_of_ready_agrees hb ready effect.agrees)
      (supportedMachine_of_ready_agrees hm ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp) direction)
      (loaded_after call (effect.agrees.memoryWriteFrame (push_writes call.stackAvailable.1 rsp)) loaded)
      effect.rip sp
    · simpa only [registerRegion,src] using bound
    · simpa only [registerRegion,src] using hasBytes_allocated bytesV
    · simpa only [registerRegion,src] using peer_disjoint call pointer
    · exact dst
    · exact fun a ha ↦ effect.agrees.grow a (grow a ha)
    · exact outside
    · change InProgram (stackTop v)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0x6a3d (by decide)
  obtain ⟨u,result,copied,_⟩ := memcpy_correct child
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by omega)
  obtain ⟨n,runU⟩ := result.execution
  refine ⟨u,⟨1+n,run.trans runU⟩,result.bindingsSupported,result.machine,result.directionFlag,
    result.loaded,fun a ha ↦ result.allocated a (effect.agrees.grow a (grow a ha)),
    result.rip.trans (callEffect_stack effect).1,?_,
    Sec1.Decode.Prepare.memory_callee_saved effect result,
    result.mxcsr.trans (effect.agrees.mxcsr (by simp)),
    result.fp87.trans (effect.agrees.fcw (by simp)),
    result_memory call.stackAvailable.1 rsp effect dst (by decide) (by omega) result,?_,shape,?_⟩
  · have hu : stackPtr u=stackPtr v+8 := result.rsp
    rw [hu,sp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro offset ho
    exact result_word stack rsp effect dst result (by omega) (by omega)
  · intro i hi
    change u.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=_
    by_cases inside : i<peer.size
    · have data := bytesV.2 ⟨i,inside⟩
      simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at data
      have h := copied i inside
      rw [dst,src] at h
      rw [h,data]
      simp only [Array.getElem?_eq_getElem (show i<peer.data.size from inside),
        Option.getD_some,ByteArray.getElem_eq_getElem_data]
    · have stack : Stack.Valid initial 4104 := call.stackAvailable.1
      have bounds := stack_bounds stack
      have addr : (stackPtr initial-336#64+BitVec.ofNat 64 i).toNat=(stackPtr initial).toNat-336+i := by
        rw [toNat_add_ofNat _ _ (by rw [stack_sub_toNat stack (by decide : 336≤4104)]; omega),
          stack_sub_toNat stack (by decide : 336≤4104)]
      have mem : u.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=
          v.external[stackPtr initial-336#64+BitVec.ofNat 64 i]? := by
        apply result.frame
        intro r hr hin
        have cases : r=registerRegion v .rdi peer.size ∨ r=Stack.region v 0 := by simpa using hr
        rcases cases with rfl | rfl
        · change (v.regValue .rdi).toNat≤_ ∧ _<(v.regValue .rdi).toNat+peer.size at hin
          rw [dst,addr,stack_sub_toNat stack (by decide : 336≤4104)] at hin
          omega
        · change (stackPtr v).toNat-0≤_ ∧ _<(Stack.region v 0).start+(Stack.region v 0).size at hin
          rw [stack_region_end,sp,addr,stack_sub_toNat stack (by decide : 512≤4104)] at hin
          omega
      have old : v.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=
          s.external[stackPtr initial-336#64+BitVec.ofNat 64 i]? := by
        apply effect.agrees.byte
        intro c hc cover
        simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl | rfl <;> try exact cover.elim
        rw [push] at cover
        obtain ⟨j,hj,eq⟩ := cover
        exact stack_sub_apart stack (a := 512) (b := 336) (na := 8) (nb := 65)
          (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) j hj i hi eq.symm
      rw [mem,old,padding i hi (by omega)]
      rw [Array.getElem?_eq_none (show peer.data.size≤i from Nat.le_of_not_gt inside)]
      rfl

end P256.Proofs.EcdhWrapper.Peer.Pad
