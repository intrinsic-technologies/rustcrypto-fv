import P256.Proofs.Verifying.Wrapper.MessagePre
import P256.Proofs.Verifying.Wrapper.LocalMemory
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def messageCallComponents (initial : RamState) : List Component :=
  [.reg 4,.mem (stackPtr initial-288) 8,.rip]

theorem message_call_byte {initial s t : RamState} {offset len : Nat}
    (stack : Stack.Valid initial 10280)
    (ag : AgreesExcept (messageCallComponents initial) s t)
    (above : offset+8 ≤ 288) (extent : len ≤ offset+8) :
    ∀ i < len, t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply ag.byte
  intro c hc covered
  simp only [messageCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j,hj,he⟩ := covered
  exact stack_sub_apart (a := 288) (b := offset) (na := 8) (nb := len)
    stack (by decide) (by omega) (by decide) extent (Or.inl above) j hj i hi he.symm

theorem enter_message [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s)
    (frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial))
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x1031e4)
    (output : s.regValue .rdi = stackPtr initial-208)
    (source : s.regValue .rsi = stackPtr initial-112)
    (descriptor : s.regValue .rdx = stackPtr initial-128)
    (scalars : s.regValue .r8 = stackPtr initial-280) (count : s.regValue .rcx = 1)
    (pointer : memLoad s.external (stackPtr initial-128) 64 =
      memLoad initial.external (initial.regValue .rdi+16#64) 64)
    (length : memLoad s.external (stackPtr initial-120) 64 = BitVec.ofNat 64 message.size) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Message.Pre t (returnBoundary initial) message ∧
      t.regValue .rdi = stackPtr initial-208 ∧ t.regValue .rsi = stackPtr initial-112 ∧
      t.regValue .r8 = stackPtr initial-280 ∧ stackPtr t = stackPtr initial-288 ∧
      (returnBoundary t).rip = 0x1031e9 ∧
      AgreesExcept (messageCallComponents initial) s t ∧
      MemoryWriteFrame s t #v[workRegion initial] := by
  obtain ⟨t,run,ready,loaded,effect,_⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated 280 0x31e4 0xa387 state.rsp rip
    (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0xd570 (by decide))
  have push : pushAddr s = stackPtr initial-288 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have ag : AgreesExcept (messageCallComponents initial) s t := by
    simpa only [messageCallComponents,pushEffect_components,push] using effect.agrees
  have localFrame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc a covered
    simp only [messageCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
      (by decide) (by decide) covered⟩
  have fullFrame := memoryWriteFrame_trans frame (work_frame call.stackAvailable.1 localFrame)
  have sp : stackPtr t = stackPtr initial-288 := effect.writes.1.trans push
  have outputT : t.regValue .rdi = stackPtr initial-208 :=
    (ag.read (n := 64) (r := 7) (by simp [messageCallComponents])).trans output
  have sourceT : t.regValue .rsi = stackPtr initial-112 :=
    (ag.read (n := 64) (r := 6) (by simp [messageCallComponents])).trans source
  have scalarT : t.regValue .r8 = stackPtr initial-280 :=
    (ag.read (n := 64) (r := 8) (by simp [messageCallComponents])).trans scalars
  have descriptorT : t.regValue .rdx = stackPtr initial-128 :=
    (ag.read (n := 64) (r := 2) (by simp [messageCallComponents])).trans descriptor
  have countT : t.regValue .rcx = 1 :=
    (ag.read (n := 64) (r := 1) (by simp [messageCallComponents])).trans count
  have ret : (returnBoundary t).rip = 0x1031e9 := (callEffect_stack effect).1
  have grow := fun a ha => ag.grow a (state.allocated a ha)
  have stack : Stack.Valid initial 10280 := call.stackAvailable.1
  have avoids := call_stack_avoids call
  change (Stack.region initial 10280).Avoids (fun a => InProgram a ∨ InPageTables a) at avoids
  have base : CalleePre t (returnBoundary initial) 0x10d570 72 24 9992 :=
    CalleePre.of_stack_region stack avoids outside messageLayout
      (bindingsSupported_of_ready_agrees state.bindingsSupported ready ag)
      (supportedMachine_of_ready_agrees state.machine ready ag)
      (ag.directionFlagClear (by simp [messageCallComponents]) state.directionFlag)
      loaded grow effect.rip sp sourceT outputT
      (by rw [ret]; exact inProgram_of_textOffset 0x31e9 (by decide))
  have preserve (offset : Nat) (above : offset+8 ≤ 288) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 offset) 64 := by
    apply memLoad_agrees_apart ag
    intro a len member
    have eq : a = stackPtr initial-288 ∧ len = 8 := by
      simpa [messageCallComponents] using member
    obtain ⟨rfl,rfl⟩ := eq
    exact stack_sub_apart stack (by decide) (by omega) (by decide) (by omega) (Or.inl above)
  have pre := message_pre call base fullFrame grow sp descriptorT scalarT countT
    ((preserve 128 (by decide)).trans pointer) ((preserve 120 (by decide)).trans length)
  exact ⟨t,run,pre,outputT,sourceT,scalarT,sp,ret,ag,localFrame⟩

end P256.Proofs.Verifying.Wrapper
