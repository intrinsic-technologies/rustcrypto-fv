import P256.Proofs.EcdhWrapper.Peer.Pad.Call
import P256.Proofs.Sec1.Decode.Prepare.Prefix.Fill

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s : RamState} {secret peer : ByteArray} {slices : Array Input}

omit bindings in
theorem buffer_offset (initial : RamState) {n : Nat} (bound : n≤336) :
    stackPtr initial-BitVec.ofNat 64 (336-n)=stackPtr initial-336#64+BitVec.ofNat 64 n := by
  rw [← BitVec.ofNat_sub_ofNat_of_le 336 n (by omega) bound]
  simp only [BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.neg_neg,BitVec.add_assoc]

theorem fill (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (hb : MachineRamUnitStrideDecodable bindings s)
    (hm : SupportedIntegerMachineState bindings.processor s)
    (direction : DirectionFlagUnset s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rip : s.RIP=0x106a23) (rsp : stackPtr s=stackPtr initial-504)
    (bound : peer.size≤65)
    (destination : s.regValue .rdi=stackPtr initial-336#64+BitVec.ofNat 64 peer.size)
    (zero : s.regValue .rsi=0) (count : s.regValue .rdx=BitVec.ofNat 64 (65-peer.size)) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      MachineRamUnitStrideDecodable bindings u ∧ SupportedIntegerMachineState bindings.processor u ∧
      DirectionFlagUnset u ∧ ProgramLoaded u ∧
      (∀ a : BitVec 64, (initial.external[a]?).isSome → (u.external[a]?).isSome) ∧
      u.RIP=0x106a29 ∧ stackPtr u=stackPtr initial-504 ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r=s.regValue r) ∧
      u.MXCSR=s.MXCSR ∧ u.FP87_Control=s.FP87_Control ∧
      MemoryWriteFrame s u #v[work initial] ∧
      (∀ offset, offset=464 ∨ offset=472 →
        memLoad u.external (stackPtr initial-BitVec.ofNat 64 offset) 64=
          memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64) ∧
      (∀ i<65, peer.size≤i → u.external[stackPtr initial-336#64+BitVec.ofNat 64 i]?=some 0) := by
  obtain ⟨v,run,ready,effect⟩ := memory_call false call outside (readyToStep hm hb) loaded grow rsp rip
  have push : pushAddr s=stackPtr initial-512#64 := by rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  have sp : stackPtr v=stackPtr initial-512#64 := effect.writes.1.trans push
  have dst : v.regValue .rdi=stackPtr initial-BitVec.ofNat 64 (336-peer.size) := by
    rw [buffer_offset initial (by omega)]
    exact (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have si : v.regValue .rsi=0 := (effect.agrees.read (n := 64) (r := 6) (by simp)).trans zero
  let layout : StackBufferLayout 4104 (65-peer.size) 0 :=
    ⟨512,336-peer.size,by decide,by decide,by omega,by omega⟩
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have avoid : (Stack.region initial 4104).Avoids (fun a ↦ InProgram a ∨ P256.Spec.Program.Routines.InPageTables a) :=
    call_stack_avoids (routine := ecdhDiffieHellman) call
  have child : CalleePre v (returnBoundary initial) 0x11c810 0 (65-peer.size) 0 := by
    apply CalleePre.of_disjoint_input_and_stack layout stack avoid
      (bindingsSupported_of_ready_agrees hb ready effect.agrees)
      (supportedMachine_of_ready_agrees hm ready effect.agrees)
      (effect.agrees.directionFlagClear (by simp) direction)
      (loaded_after call (effect.agrees.memoryWriteFrame (push_writes call.stackAvailable.1 rsp)) loaded)
      effect.rip sp
    · change (v.regValue .rsi).toNat+0<2^32
      rw [si]; decide
    · intro a ha
      change (v.regValue .rsi).toNat≤a.toNat ∧ a.toNat<(v.regValue .rsi).toNat+0 at ha
      omega
    · intro a ha _
      change (v.regValue .rsi).toNat≤a ∧ a<(v.regValue .rsi).toNat+0 at ha
      omega
    · exact dst
    · exact fun a ha ↦ effect.agrees.grow a (grow a ha)
    · exact outside
    · change InProgram (stackTop v)
      rw [(callEffect_stack effect).1]
      exact inProgram_of_textOffset 0x6a29 (by decide)
  obtain ⟨u,result,zeros,_⟩ := memset_zero_correct child (by rw [si]; rfl)
    ((effect.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by omega)
  obtain ⟨n,runU⟩ := result.execution
  refine ⟨u,⟨1+n,run.trans runU⟩,result.bindingsSupported,result.machine,result.directionFlag,
    result.loaded,fun a ha ↦ result.allocated a (effect.agrees.grow a (grow a ha)),
    result.rip.trans (callEffect_stack effect).1,?_,
    Sec1.Decode.Prepare.memory_callee_saved effect result,
    result.mxcsr.trans (effect.agrees.mxcsr (by simp)),
    result.fp87.trans (effect.agrees.fcw (by simp)),
    result_memory call.stackAvailable.1 rsp effect dst (by omega) (by omega) result,?_,?_⟩
  · have hu : stackPtr u=stackPtr v+8 := result.rsp
    rw [hu,sp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro offset ho
    exact result_word stack rsp effect dst result (by omega) (by omega)
  · intro i hi hsize
    have h := zeros (i-peer.size) (by omega)
    rw [dst,buffer_offset initial (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      Nat.add_sub_of_le hsize] at h
    exact h

end P256.Proofs.EcdhWrapper.Peer.Pad
