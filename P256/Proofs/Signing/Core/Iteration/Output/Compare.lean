import P256.Proofs.Signing.Core.Iteration.Output.Memory
import P256.Proofs.Program.Compare.Correct
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program
open NextNonce (scalarFrame coreFrame base_add)

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem compare_callee (pre : CalleePre s boundary 0x11c860 32 32 64)
    (count : s.regValue .rdx = 32) : ∃ t, CalleeResult s t boundary 32 64 := by
  have cf : Compare.CallFrame s 64 :=
    ⟨readyToStep pre.machine pre.bindingsSupported,programLoaded_codeIn pre.loaded,pre.stack,
      fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp),
      fun a ha hp => pre.avoids _ (by simp) a ha (.inl hp),pre.directionFlag,
      inProgram_low pre.returnInProgram⟩
  have cp : Compare.CallPre s := by
    have n : ((Operand.reg 2 : Operand 64).read s).toNat = 32 := by
      change (s.regValue .rdx).toNat = 32
      rw [count]; rfl
    refine ⟨pre.rip,by rw [n]; decide,cf,?_,?_,?_,?_⟩
    · rw [n]
      exact memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _)
    · rw [n]
      exact memoryRegion_memReadable pre.inputBounded pre.inputAllocated (Nat.le_refl _) (Nat.le_refl _)
    · rw [n]
      intro i hi j hj eq
      apply pre.separation (1:Fin 3) (2:Fin 3) (by decide) _
        (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj)
      change (Stack.region s 64).Contains (((Operand.reg 7 : Operand 64).read s)+BitVec.ofNat 64 j).toNat
      rw [← eq]
      exact cf.stack_sub_contains (offset:=64) (len:=64) (by decide) (by decide) hi
    · rw [n]
      intro i hi j hj eq
      apply pre.separation (0:Fin 3) (2:Fin 3) (by decide) _
        (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hj)
      change (Stack.region s 64).Contains (((Operand.reg 6 : Operand 64).read s)+BitVec.ofNat 64 j).toNat
      rw [← eq]
      exact cf.stack_sub_contains (offset:=64) (len:=64) (by decide) (by decide) hi
  obtain ⟨n,u,run,result⟩ := Compare.correct boundary s cp
    ⟨pre.outerBoundary,boundary_ne_program pre.outerBoundary pre.returnInProgram⟩
  have memory := result.stackFrame cp
  refine ⟨u,⟨⟨n,run⟩,result.rip,result.rsp,
    bindingsSupported_of_ready_agrees pre.bindingsSupported result.ready result.agrees,
    supportedMachine_of_ready_agrees pre.machine result.ready result.agrees,result.calleeSaved,
    result.agrees.directionFlagClear (by simp [Compare.callChanges]) pre.directionFlag,
    result.agrees.mxcsr (by simp [Compare.callChanges]),result.agrees.fcw (by simp [Compare.callChanges]),
    ?_,?_,result.agrees.grow⟩⟩
  · intro a ha
    exact memory a (fun r hr => ha r (by simpa using Or.inr hr))
  · intro a b hb
    apply (memory a ?_).trans (pre.loaded a b hb)
    intro r hr hin
    have eq : r = Stack.region s 64 := by simpa using hr
    subst r
    exact pre.avoids _ (by simp) a hin (.inl ⟨b,hb⟩)

omit [Bindings] in
theorem compare_pointer (loaded : ProgramLoaded t) :
    MemReadable t 0x204540 8 ∧ (Operand.mem 0x204540 : Operand 64).read t = 0x11c860 := by
  have hb : ∀ i : Fin 8, Extracted.programSections.fetchByte (0x204540+BitVec.ofNat 64 i.val) =
      some (storedByte (0x11c860:BitVec 64) i.val) := by decide +kernel
  have bytes : Bytes t.external 0x204540 8 (storedByte (0x11c860:BitVec 64)) :=
    fun i hi => loaded _ _ (hb ⟨i,hi⟩)
  exact ⟨bytes.readable (by decide),bytes.memLoad (by decide) (by decide)⟩

theorem compare_call (pre : SignPre s boundary) (frame : Frame s t)
    (rip : t.RIP = 0x10d484) (src : t.regValue .rsi = frameBase s+528)
    (dst : t.regValue .rdi = frameBase s+432) (count : t.regValue .rdx = 32) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d48a ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],u.regValue r = t.regValue r) ∧
      (∀ i < 65,u.external[s.regValue .rdi+BitVec.ofNat 64 i]? = t.external[s.regValue .rdi+BitVec.ofNat 64 i]?) ∧
      (∀ i < 32,u.external[frameBase s+136+BitVec.ofNat 64 i]? = t.external[frameBase s+136+BitVec.ofNat 64 i]?) := by
  have push : pushAddr t = stackPtr s-2288 := ScalarFrame.scalar_call_address (scalarFrame frame)
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow
      (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (offset:=2288) (by decide) (by decide)) frame.allocated
  have apart : RangeApart (pushAddr t) 8 0x10d484 6 := by
    rw [push]
    intro i hi j hj eq
    apply pre.avoids (Stack.region s 4584) (by simp) _
      (ScalarFrame.stack_contains pre.toCalleePre (offset:=2288) (len:=8)
        (by decide) (by decide) ⟨i,hi,rfl⟩)
    apply Or.inl
    change InProgram (stackPtr s - (2288:BitVec 64)+BitVec.ofNat 64 i)
    rw [eq]
    simpa only [Extracted.textAddress,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,← BitVec.add_assoc,BitVec.reduceAdd] using
      inProgram_of_textOffset (0xd484+j) (by omega)

  have ptr := compare_pointer frame.loaded
  have target : callMemPtr 0x10d484 (.rip 0xf70b6) t = 0x11c860 := ptr.2
  obtain ⟨v,runV,readyV,effect⟩ :=
    (call_m64_effect_step 0x10d484 (.rip 0xf70b6) trivial rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd484 _ (by decide) (by decide +kernel))
      ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,ptr.1⟩
      (by change callMemPtr 0x10d484 (.rip 0xf70b6) t ≠ boundary.rip
          rw [target]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c860 (by decide)))
  change (callEffect (callMemPtr 0x10d484 (.rip 0xf70b6)) 0x10d48a t).Holds t v at effect
  have ec : (callEffect (fun _ => 0x11c860) 0x10d48a t).Holds t v := by
    simpa only [callEffect,pushEffect,target] using effect
  have cp := local_call_pre pre frame readyV ec (inProgram_of_textOffset 0xd48a (by decide))
    (reserve:=64) (by decide) (inputBytes:=32) (outputBytes:=32) (by decide) (by decide)
    (by decide) (by decide) (.inr (by decide)) src dst
  obtain ⟨u,result⟩ := compare_callee cp ((ec.agrees.read (n:=64) (r:=2) (by simp)).trans count)
  obtain ⟨n,run⟩ := result.execution
  exact ⟨1+n,u,runV.trans run,after_call pre frame readyV ec result (by decide) (by decide) dst,
    result.rip.trans (callEffect_stack ec).1,call_preserved ec result,
    call_output pre frame ec result (by decide) (by decide) dst,
    local_result_copy pre frame ec result dst (by decide) (by decide) (.inl (by decide))⟩

end P256.Proofs.Signing.Core.Iteration.Output
