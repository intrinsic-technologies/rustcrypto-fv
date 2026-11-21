import P256.Proofs.Projective.Multiply.Machine.Radix.Memory
import P256.Proofs.Program.Copy
import P256.Proofs.Program.CalleeStackOutput

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def copyCallComponents (s : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 8,.flags,.rip,
    .mem (stackPtr s-128) 8,.mem (s.regValue .rdi) 65]

theorem copy_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : Nat → UInt8} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t) (rip : t.RIP = 0x10ba79)
    (source : t.regValue .rsi = stackPtr s-112) (destination : t.regValue .rdi = s.regValue .rdi)
    (count : t.regValue .rdx = 65) (input : Bytes t.external (stackPtr s-112) 65 bytes) :
    ∃ u fuel, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x10ba7f ∧
      Bytes u.external (s.regValue .rdi) 65 bytes ∧
      AgreesExcept (copyCallComponents s) t u := by
  have push : pushAddr t = stackPtr s-128 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha h => pre.avoids _ (by simp) a ha (.inr h)) (by decide) (by decide)) state.agrees.grow
  have apart : RangeApart (pushAddr t) 8 0x10ba79 6 := by
    rw [push]
    intro i hi j hj eq
    apply pre.avoids (Stack.region s 136) (by simp)
      (stackPtr s-128+BitVec.ofNat 64 i)
      (ScalarFrame.stack_contains pre (by decide) (by decide) ⟨i,hi,rfl⟩) (.inl ?_)
    rw [eq]
    have h := inProgram_of_textOffset (0xba79+j) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at h
    exact h
  have pointer := memcpy_pointer (state.loaded pre)
  have target : callMemPtr 0x10ba79 (.rip 0xf8a79) t = 0x11c930 := pointer.2
  obtain ⟨entry,step,ready,effect⟩ := call_m64_effect_step 0x10ba79 (.rip 0xf8a79)
    trivial rfl rfl t state.ready
    (programText_slice (programLoaded_codeIn (state.loaded pre)) 0xba79 _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,pointer.1⟩
  have callNext : (0x10ba79 : BitVec 64)+BitVec.ofNat 64 (callMemLen (.rip 0xf8a79)) =
      0x10ba7f := by decide
  have effect' : (callEffect (fun _ => 0x11c930) 0x10ba7f t).Holds t entry := by
    simpa only [callEffect,pushEffect,target,callNext] using effect
  have run : Advances boundary 1 t entry := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))))
  have rspE : stackPtr entry = stackPtr s-128 := effect'.writes.1.trans push
  have frameE : State s entry 128 := by
    apply state.after_stack pre ready effect'.agrees
    · intro c hc hm
      simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl <;> simp_all [Component.isMem,registers]
    · intro p n hc
      simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false,
        reduceCtorEq,false_or,or_false,Component.mem.injEq] at hc
      obtain ⟨rfl,rfl⟩ := hc
      exact ⟨128,by decide,by decide,push⟩
    · exact rspE
  have sourceE : entry.regValue .rsi = stackPtr s-112 :=
    (effect'.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have destinationE : entry.regValue .rdi = s.regValue .rdi :=
    (effect'.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary entry).rip = 0x10ba7f := (callEffect_stack effect').1
  have callee : CalleePre entry boundary 0x11c930 65 65 8 :=
    CalleePre.of_stack_and_output pre
      (⟨128,112,by decide,by decide,by decide,by decide⟩ : StackBufferLayout 136 65 8)
      (bindingsSupported_of_ready_agrees pre.bindingsSupported ready frameE.agrees)
      (supportedMachine_of_ready_agrees pre.machine ready frameE.agrees)
      (frameE.agrees.directionFlagClear (by simp [components,registers]) pre.directionFlag)
      (frameE.loaded pre) frameE.agrees.grow effect'.rip rspE sourceE destinationE
      (ret ▸ inProgram_of_textOffset 0xba7f (by decide))
  have inputE : Bytes entry.external (stackPtr s-112) 65 bytes := by
    apply input.of_agreesExcept effect'.agrees
    intro i hi c hc covered
    simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl
    all_goals try exact covered.elim
    rw [push] at covered
    obtain ⟨j,hj,eq⟩ := covered
    have ranges : RangeApart (stackPtr s-128) 8 (stackPtr s-112) 65 := by
      simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd,
        BitVec.add_zero] using RangeApart.offsets (stackPtr s-128) (a := 0) (b := 16)
          (len := 8) (count := 65) (by decide) (by decide) (.inl (by decide))
    exact ranges j hj i hi eq.symm
  obtain ⟨u,result,copied,ag⟩ := memcpy_correct callee
    ((effect'.agrees.read (n := 64) (r := 2) (by simp)).trans count) (by decide)
  have narrow : AgreesExcept (copyCallComponents s) t u :=
    (effect'.agrees.trans ag).mono (by
      simp [copyCallComponents,Copy.copyComponents,Copy.registerComponents,push,destinationE])
  have rspU : stackPtr u = stackPtr s-120 := by
    have h : stackPtr u = stackPtr entry+8 := result.rsp
    rw [h,rspE]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  have frameU : State s u := by
    apply state.after pre (readyToStep result.machine result.bindingsSupported) narrow
    · intro c hc hm
      simp only [copyCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp_all [Component.isMem,registers]
    · intro c hc a ha
      simp only [copyCallComponents,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals try exact ha.elim
      · exact ⟨workRegion s,by simp,ScalarFrame.Work.contains pre (by decide) (by decide) ha⟩
      · obtain ⟨i,hi,rfl⟩ := ha
        exact ⟨registerRegion s .rdi 65,by simp,
          memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩
    · exact rspU
  obtain ⟨fuel,called⟩ := result.execution
  refine ⟨u,1+fuel,run.trans called,frameU,result.rip.trans (callEffect_stack effect').1,?_,narrow⟩
  intro i hi
  have h := copied i hi
  rw [sourceE,destinationE] at h
  exact h.trans (inputE i hi)

end P256.Proofs.Projective.Multiply.Machine.Radix
