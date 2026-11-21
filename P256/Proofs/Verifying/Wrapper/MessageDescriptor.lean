import P256.Proofs.Verifying.Wrapper.MessageStore

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem store_message_descriptor [Bindings] {initial s : RamState}
    {key signature message : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x1031b7) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x1031c7 ∧
      memLoad t.external (stackPtr initial-128) 64 = s.regValue .rcx ∧
      memLoad t.external (stackPtr initial-120) 64 = s.regValue .rax ∧
      AgreesExcept [.mem (stackPtr initial-128) 8,.mem (stackPtr initial-120) 8,.rip] s t ∧
      MemoryWriteFrame s t #v[workRegion initial] := by
  have pre : MessageStore.Pre s := by
    refine ⟨rip,?_,?_⟩
    · exact state.local_writable call (by decide : 152+16 ≤ 240) (by decide)
    · exact state.local_code call (by decide : 152+16 ≤ 240)
        (by decide : 0x31b7+16 ≤ 118431)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := MessageStore.run (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x31b7 MessageStore.bytes
      (by decide) (by decide +kernel)) pre
  have addr1 : (Operand.reg 4#5 : Operand 64).read s+152 = stackPtr initial-128 := by
    change stackPtr s+152 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have addr2 : (Operand.reg 4#5 : Operand 64).read s+160 = stackPtr initial-120 := by
    change stackPtr s+160 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have ag : AgreesExcept [.mem (stackPtr initial-128) 8,.mem (stackPtr initial-120) 8,.rip] s t := by
    simpa only [MessageStore.effect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append,Nat.reduceDiv,addr1,addr2] using effect.agrees
  have frame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc a covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
        (by decide) (by decide) covered⟩
    · exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1
        (by decide) (by decide) covered⟩
    · exact covered.elim
  have values := effect.writes
  change memLoad t.external ((Operand.reg 4#5 : Operand 64).read s+152) 64 = s.regValue .rcx ∧
    memLoad t.external ((Operand.reg 4#5 : Operand 64).read s+160) 64 = s.regValue .rax at values
  rw [addr1,addr2] at values
  exact ⟨fuel,t,run,state.after_work call ready ag frame (by simp) (by simp) (by simp),
    effect.rip,values.1,values.2,ag,frame⟩

end P256.Proofs.Verifying.Wrapper
