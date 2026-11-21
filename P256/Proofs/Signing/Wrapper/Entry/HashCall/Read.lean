import P256.Proofs.Signing.Wrapper.Entry.HashCall.Load
import P256.Proofs.Signing.Wrapper.Entry.HashCall.Guard
import P256.Proofs.Signing.Wrapper.Entry.HashCall.Input
import P256.Proofs.Signing.Wrapper.Entry.HashCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.HashCall

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_read [Bindings] {initial s : RamState} {secret message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret,message] slices)
    (state : State initial s 520)
    (frame : MemoryWriteFrame initial s (wrapperRegions signingKeyTrySign initial))
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x102706)
    (pointers : s.regValue .r12 = initial.regValue .rdi)
    (lengths : memLoad s.external (stackPtr initial-192) 64 = initial.regValue .rdx) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ State initial t 520 ∧
      t.RIP = 0x102720 ∧
      t.regValue .rsi = memLoad initial.external (initial.regValue .rdi+8#64) 64 ∧
      t.regValue .rbp = BitVec.ofNat 64 message.size ∧ (registerRegion t .rsi message.size).HasBytes t.external message ∧
      AgreesExcept [.reg 6,.reg 0,.reg 5,.flags,.rip] s t := by
  obtain ⟨address,original,nonzero,bounded,bytes,readP,readL,pointer,length⟩ :=
    preserved_message_input call frame
  have slotAddress : stackPtr s+328=stackPtr initial-192 := by
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  obtain ⟨nb,b,runB,readyB,_,effectB⟩ := message_load (returnBoundary initial) outside s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x2706 messageLoadBytes
      (by decide) (by decide +kernel))
    ⟨rip,by simpa only [pointers] using readP,
      local_readable state call.stackAvailable.1 (by decide),
      by rw [slotAddress,lengths]; exact readL⟩
  have agB : AgreesExcept [.reg 6,.reg 0,.reg 5,.rip] s b := by
    simpa only [messageLoadEffect,Effect.components,Write.component,Operand.component,
      List.map,List.cons_append,List.nil_append] using effectB.agrees
  have stateB := after_registers call state runB readyB agB (by simp [Component.Covers])
    (by simp) (by simp)
  have values : b.regValue .rsi = memLoad s.external (s.regValue .r12+8#64) 64 ∧
      b.regValue .rax = memLoad s.external (stackPtr s+328) 64 ∧
      b.regValue .rbp = memLoad s.external (memLoad s.external (stackPtr s+328) 64+8#64) 64 := effectB.writes
  have inputB : b.regValue .rsi = address := by
    rw [values.1,pointers]
    exact pointer
  have lengthB : b.regValue .rbp = BitVec.ofNat 64 message.size := by
    rw [values.2.2,slotAddress,lengths]
    exact length
  obtain ⟨t,runT,readyT,ripT,agT⟩ := message_pointer_guard readyB stateB.loaded outside
    effectB.rip (by rw [inputB]; exact nonzero)
  have stateT := after_registers call stateB runT readyT agT (by simp [Component.Covers])
    (by simp) (by simp)
  have inputT : t.regValue .rsi = address :=
    (agT.read (n := 64) (r := 6) (by simp)).trans inputB
  refine ⟨_,t,runB.trans runT,stateT,ripT,inputT.trans original.symm,?_,?_,?_⟩
  · exact (agT.read (n := 64) (r := 5) (by simp)).trans lengthB
  · change (MemoryRegion.mk (t.regValue .rsi).toNat message.size).HasBytes t.external message
    rw [inputT,(agB.trans agT).external (by simp [Component.Covers])]
    exact bytes
  · apply (agB.trans agT).mono
    simp

end P256.Proofs.Signing.Wrapper.Entry.HashCall
