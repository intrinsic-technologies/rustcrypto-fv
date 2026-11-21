import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import P256.Proofs.Sec1.SquareRoot.Exponent.Finish.Memory
import P256.Proofs.Program.Copy
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

theorem copy_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114ba0 144 32 1584)
    (state : FrameState s t 32 1584 1416) (rip : t.RIP = 0x1153ce)
    (source : t.regValue .rsi = stackPtr s-1256)
    (destination : t.regValue .rdi = stackPtr s-592) (count : t.regValue .rdx = 512) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 1584 1416 ∧
      u.RIP = 0x1153d4 ∧
      (∀ i < 512, u.external[stackPtr s-592+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-1256+BitVec.ofNat 64 i]?) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = t.regValue r) ∧
      (∀ off len : Nat, off+len≤1416 → off+len≤824 ∨ 1336≤off → ∀ i<len,
        u.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
        t.external[exponentFrameBase s+BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  have push : pushAddr t = stackPtr s-1424 := scalar_call_address state
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha h => pre.avoids _ (by simp) a ha (.inr h)) (by decide) (by decide))
      state.allocated
  have apart : RangeApart (pushAddr t) 8 0x1153ce 6 := by
    rw [push]
    intro i hi j hj eq
    apply pre.avoids (Stack.region s 1584) (by simp)
      (stackPtr s-1424+BitVec.ofNat 64 i)
      (stack_contains pre (by decide) (by decide) ⟨i,hi,rfl⟩) (.inl ?_)
    rw [eq]
    have h := inProgram_of_textOffset (0x153ce+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  have pointer := memcpy_pointer state.loaded
  have target : callMemPtr 0x1153ce (.rip 0xef124) t = 0x11c930 := pointer.2
  obtain ⟨entry,step,ready,effect⟩ := call_m64_effect_step 0x1153ce (.rip 0xef124)
    trivial rfl rfl t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x153ce _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,pointer.1⟩
  have callNext : (0x1153ce : BitVec 64)+BitVec.ofNat 64 (callMemLen (.rip 0xef124)) =
      0x1153d4 := by decide
  have effect' : (callEffect (fun _ => 0x11c930) 0x1153d4 t).Holds t entry := by
    simpa only [callEffect,pushEffect,target,callNext] using effect
  have run : Advances boundary 1 t entry := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have frame := state.after_call pre (by decide) (by decide) ready effect'
  have sourceE : entry.regValue .rsi = stackPtr s-1256 :=
    (effect'.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationE : entry.regValue .rdi = stackPtr s-592 :=
    (effect'.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary entry).rip = 0x1153d4 := (callEffect_stack effect').1
  have callee : CalleePre entry boundary 0x11c930 512 512 8 :=
    CalleePre.of_stack pre
      (⟨1424,1256,592,by decide,by decide,by decide,by decide,by decide,by decide,
        .inl (by decide)⟩ : StackCallLayout 1584 512 512 8)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect'.rip frame.rsp sourceE destinationE
      (ret ▸ inProgram_of_textOffset 0x153d4 (by decide))
  obtain ⟨u,result,copied,_⟩ := memcpy_correct callee
    ((effect'.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by decide)
  have memory := stack_result_work_frame (frameOffset := 1416) pre frame result
    destinationE (by decide) (by decide) (by decide) (by decide)
  obtain ⟨fuel,called⟩ := result.execution
  refine ⟨1+fuel,u,run.trans called,
    after_result (frameOffset := 1416) pre frame result (by decide) memory,
    result.rip.trans ret,?_,?_,?_⟩
  · intro i hi
    have h := copied i hi
    rw [sourceE,destinationE] at h
    exact h.trans (scalar_call_byte (by decide) state effect' (by decide) (by decide) hi)
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect'.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect'.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect'.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect'.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect'.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect'.agrees.read (n := 64) (r := 15) (by simp)
  · intro off len hb ha i hi
    rw [ExponentTail.frame_address (by omega)]
    exact (stack_result_byte (frameOffset := 1416) pre frame result destinationE
      (by decide) (by decide) (by omega) (by omega)
      (by change (1416-off)+512≤592 ∨ 592+len≤1416-off; omega) hi).trans
      (scalar_call_byte (frameOffset := 1416) (by decide) state effect' (by omega) (by omega) hi)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
