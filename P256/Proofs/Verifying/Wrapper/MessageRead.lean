import P256.Proofs.Verifying.Wrapper.MessageLoad
import P256.Proofs.Verifying.Wrapper.MessageGuards
import P256.Proofs.Verifying.Wrapper.MessageInput
import P256.Proofs.Verifying.Wrapper.ReturnState

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_read [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s)
    (frame : MemoryWriteFrame initial s (wrapperRegions verifyingKeyVerify initial))
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x1031a0)
    (count : s.regValue .r15 = 3) (pointers : s.regValue .r14 = initial.regValue .rdi)
    (lengths : s.regValue .rbx = initial.regValue .rdx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x1031b7 ∧
      t.regValue .rcx = memLoad initial.external (initial.regValue .rdi+16#64) 64 ∧
      t.regValue .rax = BitVec.ofNat 64 message.size ∧ (registerRegion t .rcx message.size).HasBytes t.external message ∧
      AgreesExcept [.reg 1,.reg 0,.flags,.rip] s t := by
  obtain ⟨a,runA,readyA,ripA,agA⟩ := message_count_guard
    (readyToStep state.machine state.bindingsSupported) state.loaded outside rip count
  have stateA := state.after_registers readyA agA
    (by simp [Component.Covers]) (by simp) (by simp)
  have frameA : MemoryWriteFrame initial a (wrapperRegions verifyingKeyVerify initial) := by
    intro address away
    rw [agA.external (by simp [Component.Covers])]
    exact frame address away
  obtain ⟨address,original,nonzero,bounded,bytes,readP,readL,pointer,length⟩ :=
    preserved_message_input call frameA
  have r14 : a.regValue .r14 = initial.regValue .rdi :=
    (agA.read (n := 64) (r := 14) (by simp)).trans pointers
  have rbx : a.regValue .rbx = initial.regValue .rdx :=
    (agA.read (n := 64) (r := 3) (by simp)).trans lengths
  obtain ⟨nb,b,runB,readyB,_,effectB⟩ := message_load (returnBoundary initial) outside a readyA
    (programText_slice (programLoaded_codeIn stateA.loaded) 0x31aa messageLoadBytes
      (by decide) (by decide +kernel))
    ⟨ripA,by simpa only [r14] using readP,by simpa only [rbx] using readL⟩
  have agB : AgreesExcept [.reg 1,.reg 0,.rip] a b := by
    simpa only [messageLoadEffect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append] using effectB.agrees
  have stateB := stateA.after_registers readyB agB
    (by simp [Component.Covers]) (by simp) (by simp)
  have values : b.regValue .rcx = memLoad a.external (a.regValue .r14+16#64) 64 ∧
      b.regValue .rax = memLoad a.external (a.regValue .rbx+16#64) 64 := effectB.writes
  have inputB : b.regValue .rcx = address := by
    rw [values.1,r14]
    exact pointer
  have lengthB : b.regValue .rax = BitVec.ofNat 64 message.size := by
    rw [values.2,rbx]
    exact length
  obtain ⟨t,runT,readyT,ripT,agT⟩ := message_pointer_guard readyB stateB.loaded outside
    effectB.rip (by rw [inputB]; exact nonzero)
  have stateT := stateB.after_registers readyT agT
    (by simp [Component.Covers]) (by simp) (by simp)
  have inputT : t.regValue .rcx = address :=
    (agT.read (n := 64) (r := 1) (by simp)).trans inputB
  refine ⟨_,t,(runA.trans runB).trans runT,stateT,ripT,inputT.trans original.symm,?_,?_,?_⟩
  · exact (agT.read (n := 64) (r := 0) (by simp)).trans lengthB
  · change (MemoryRegion.mk (t.regValue .rcx).toNat message.size).HasBytes t.external message
    rw [inputT,(agB.trans agT).external (by simp [Component.Covers])]
    exact bytes
  · apply ((agA.trans agB).trans agT).mono
    intro c hc
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with ((rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> simp

end P256.Proofs.Verifying.Wrapper
