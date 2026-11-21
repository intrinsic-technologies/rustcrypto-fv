import P256.Proofs.Verifying.Wrapper.MessageRead
import P256.Proofs.Verifying.Wrapper.MessageDescriptor
import P256.Proofs.Verifying.Wrapper.MessageArguments

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def messageSetupComponents (initial : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 8,.flags,
    .mem (stackPtr initial-128) 8,.mem (stackPtr initial-120) 8,.rip]

theorem message_setup [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s)
    (frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial))
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x1031a0)
    (count : s.regValue .r15 = 3) (pointers : s.regValue .r14 = initial.regValue .rdi)
    (lengths : s.regValue .rbx = initial.regValue .rdx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x1031e4 ∧ t.regValue .rdi = stackPtr initial-208 ∧
      t.regValue .rsi = stackPtr initial-112 ∧ t.regValue .rdx = stackPtr initial-128 ∧
      t.regValue .r8 = stackPtr initial-280 ∧ t.regValue .rcx = 1 ∧
      memLoad t.external (stackPtr initial-128) 64 =
        memLoad initial.external (initial.regValue .rdi+16#64) 64 ∧
      memLoad t.external (stackPtr initial-120) 64 = BitVec.ofNat 64 message.size ∧
      AgreesExcept (messageSetupComponents initial) s t ∧
      MemoryWriteFrame s t #v[workRegion initial] := by
  obtain ⟨na,a,runA,stateA,ripA,ptrA,lenA,_,agA⟩ :=
    message_read call state frame outside rip count pointers lengths
  obtain ⟨nb,b,runB,stateB,ripB,ptrB,lenB,agB,frameB⟩ :=
    store_message_descriptor call stateA outside ripA
  obtain ⟨nt,t,runT,readyT,_,effect⟩ := message_arguments (returnBoundary initial) outside b
    (readyToStep stateB.machine stateB.bindingsSupported)
    (programText_slice (programLoaded_codeIn stateB.loaded) 0x31c7 messageArgumentBytes
      (by decide) (by decide +kernel)) ripB
  have agT : AgreesExcept [.reg 7,.reg 6,.reg 2,.reg 8,.reg 1,.rip] b t := by
    simpa only [messageArgumentEffect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append] using effect.agrees
  have stateT := stateB.after_registers readyT agT
    (by simp [Component.Covers]) (by simp) (by simp)
  have memory := agT.external (by simp [Component.Covers])
  have values : t.regValue .rdi = stackPtr b+72 ∧ t.regValue .rsi = stackPtr b+168 ∧
      t.regValue .rdx = stackPtr b+152 ∧ t.regValue .r8 = stackPtr b ∧
      t.regValue .rcx = 1 := effect.writes
  rw [stateB.rsp] at values
  refine ⟨na+nb+nt,t,(runA.trans runB).trans runT,stateT,effect.rip,
    ?_,?_,?_,values.2.2.2.1,values.2.2.2.2,?_,?_,?_,?_⟩
  · rw [values.1]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · rw [values.2.1]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · rw [values.2.2.1]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · rw [memory]
    exact ptrB.trans ptrA
  · rw [memory]
    exact lenB.trans lenA
  · apply ((agA.trans agB).trans agT).mono
    intro c hc
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl | rfl | rfl) |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [messageSetupComponents]
  · intro address away
    rw [memory,frameB address away,agA.external (by simp [Component.Covers])]

theorem message_setup_byte {initial s t : RamState} {offset len : Nat}
    (stack : Stack.Valid initial 10280)
    (ag : AgreesExcept (messageSetupComponents initial) s t)
    (within : offset ≤ 10280) (extent : len ≤ offset+8)
    (apart1 : 128+len ≤ offset ∨ offset+8 ≤ 128)
    (apart2 : 120+len ≤ offset ∨ offset+8 ≤ 120) :
    ∀ i < len, t.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      s.external[stackPtr initial-BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  intro i hi
  apply ag.byte
  intro c hc covered
  simp only [messageSetupComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  · obtain ⟨j,hj,he⟩ := covered
    exact stack_sub_apart (a := 128) (b := offset) (na := 8) (nb := len)
      stack (by decide) within (by decide) extent apart1.symm j hj i hi he.symm
  · obtain ⟨j,hj,he⟩ := covered
    exact stack_sub_apart (a := 120) (b := offset) (na := 8) (nb := len)
      stack (by decide) within (by decide) extent apart2.symm j hj i hi he.symm

end P256.Proofs.Verifying.Wrapper
