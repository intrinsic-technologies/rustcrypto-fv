import P256.Proofs.Program.Copy
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Prepare

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame Program.FieldCall

theorem copy_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x10031c)
    (source : t.regValue .rsi = stackPtr s-1040)
    (destination : t.regValue .rdi = stackPtr s-1808) (count : t.regValue .rdx = 768) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x100322 ∧
      (∀ i < 768, u.external[stackPtr s-1808+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-1040+BitVec.ofNat 64 i]?) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = t.regValue r) ∧
      (∀ i < 65, u.external[stackPtr s-1976+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-1976+BitVec.ofNat 64 i]?) := by
  have push : pushAddr t = stackPtr s-2064 := scalar_call_address state
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha h => pre.avoids _ (by simp) a ha (.inr h)) (by decide) (by decide))
      state.allocated
  have apart : RangeApart (pushAddr t) 8 0x10031c 6 := by
    rw [push]
    intro i hi j hj eq
    apply pre.avoids (Stack.region s 3464) (by simp)
      (stackPtr s-2064+BitVec.ofNat 64 i)
      (stack_contains pre (by decide) (by decide) ⟨i,hi,rfl⟩) (.inl ?_)
    rw [eq]
    have h := inProgram_of_textOffset (0x31c+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  have pointer := memcpy_pointer state.loaded
  have target : callMemPtr 0x10031c (.rip 0x1041d6) t = 0x11c930 := pointer.2
  obtain ⟨entry,step,ready,effect⟩ := call_m64_effect_step 0x10031c (.rip 0x1041d6)
    trivial rfl rfl t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x31c _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,pointer.1⟩
  have callNext : (0x10031c : BitVec 64)+BitVec.ofNat 64 (callMemLen (.rip 0x1041d6)) =
      0x100322 := by decide
  have effect' : (callEffect (fun _ => 0x11c930) 0x100322 t).Holds t entry := by
    simpa only [callEffect,pushEffect,target,callNext] using effect
  have run : Advances boundary 1 t entry := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have frame := state.after_call pre (by decide) (by decide) ready effect'
  have sourceE : entry.regValue .rsi = stackPtr s-1040 :=
    (effect'.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationE : entry.regValue .rdi = stackPtr s-1808 :=
    (effect'.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary entry).rip = 0x100322 := (callEffect_stack effect').1
  have callee : CalleePre entry boundary 0x11c930 768 768 8 :=
    CalleePre.of_stack pre
      (⟨2064,1040,1808,by decide,by decide,by decide,by decide,by decide,by decide,
        .inr (by decide)⟩ : StackCallLayout 3464 768 768 8)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect'.rip frame.rsp sourceE destinationE
      (ret ▸ inProgram_of_textOffset 0x322 (by decide))
  obtain ⟨u,result,copied,_⟩ := memcpy_correct callee
    ((effect'.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by decide)
  have memory := stack_result_work_frame (frameOffset := 2056) pre frame result
    destinationE (by decide) (by decide) (by decide) (by decide)
  obtain ⟨fuel,called⟩ := result.execution
  refine ⟨1+fuel,u,run.trans called,
    after_result (frameOffset := 2056) pre frame result (by decide) memory,
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
  · intro i hi
    exact (stack_result_byte (frameOffset := 2056) pre frame result destinationE
      (by decide) (by decide) (by decide) (by decide) (.inr (by decide)) hi).trans
      (scalar_call_byte (by decide) state effect' (by decide) (by decide) hi)

end P256.Proofs.Ecdh.Prepare
