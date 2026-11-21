import P256.Proofs.Verifying.Wrapper.SignatureCopy.Tail
import P256.Proofs.Verifying.Wrapper.SignatureCopy.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper.SignatureCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem tail_correct [Bindings] {initial s : RamState} {key signature message : ByteArray}
    {slices : Array Input}
    (call : ValidCallWithSlices verifyingKeyVerify initial [key,signature,message] slices)
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x10318d) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x1031a0 ∧
      memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s+80) 64 ∧
      memLoad t.external (stackPtr s+8) 64 = memLoad s.external (stackPtr s+88) 64 ∧
      AgreesExcept [.reg 0,.reg 1,.mem (stackPtr s) 16,.rip] s t := by
  have zeroAdd (a : BitVec 64) : a+0#64 = a := BitVec.add_zero a
  have pre : Tail.Pre s := by
    refine ⟨rip,state.local_readable call.stackAvailable.1 (by decide : 80+8 ≤ 280),
      state.local_readable call.stackAvailable.1 (by decide : 88+8 ≤ 280),?_,?_⟩
    · simpa [stackPtr,Operand.read_reg64,State.regValue,gprIndex,Syntax.Reg.fin,Extracted.textAddress,zeroAdd] using
        state.local_writable call (by decide : 0+16 ≤ 240) (by decide)
    · simpa [stackPtr,Operand.read_reg64,State.regValue,gprIndex,Syntax.Reg.fin,Extracted.textAddress,zeroAdd] using
        state.local_code call (offset := 0) (by decide : 0+16 ≤ 240)
          (by decide : 0x318d+19 ≤ 118431)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Tail.run (returnBoundary initial) outside s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x318d Tail.bytes
      (by decide) (by decide +kernel)) pre
  have narrow : AgreesExcept [.reg 0,.reg 1,.mem (stackPtr s+8) 8,.mem (stackPtr s) 8,.rip] s t := by
    simpa [Tail.effect,Effect.components,Write.component,Operand.component,List.map,
      List.cons_append,List.nil_append,Nat.reduceDiv,BitVec.add_zero,
      stackPtr,Operand.read_reg64,gprIndex,State.regValue,Syntax.Reg.fin,zeroAdd] using effect.agrees
  have ag : AgreesExcept [.reg 0,.reg 1,.mem (stackPtr s) 16,.rip] s t := by
    apply narrow.widen
    · intro c hc hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp_all [Component.isMem]
    · intro a c hc covered
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      · obtain ⟨i,hi,he⟩ := covered
        refine ⟨.mem (stackPtr s) 16,by simp,8+i,by omega,?_⟩
        simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using he
      · obtain ⟨i,hi,he⟩ := covered
        exact ⟨.mem (stackPtr s) 16,by simp,i,by omega,he⟩
  have frame : MemoryWriteFrame s t #v[workRegion initial] := by
    apply ag.memoryWriteFrame
    intro c hc a covered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial,by simp,state.local_work call.stackAvailable.1
      (offset := 0) (len := 16) (by decide) (by simpa [stackPtr,Operand.read_reg64,State.regValue,gprIndex,Syntax.Reg.fin,Extracted.textAddress,zeroAdd] using covered)⟩
  have values := effect.writes
  change _ ∧ _ ∧ memLoad t.external (stackPtr s+8) 64 = memLoad s.external (stackPtr s+88) 64 ∧
    memLoad t.external (stackPtr s+0) 64 = memLoad s.external (stackPtr s+80) 64 at values
  refine ⟨fuel,t,run,state.after_work call ready ag frame (by simp) (by simp) (by simp),
    effect.rip,?_,values.2.2.1,ag⟩
  simpa [stackPtr,Operand.read_reg64,State.regValue,gprIndex,Syntax.Reg.fin,Extracted.textAddress,zeroAdd] using values.2.2.2

end P256.Proofs.Verifying.Wrapper.SignatureCopy
