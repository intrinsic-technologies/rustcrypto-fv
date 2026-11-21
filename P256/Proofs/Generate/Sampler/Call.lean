import P256.Proofs.Generate.Sampler.Memory
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.CalleeStackFrame

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem call_push [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    (pre : Pre s boundary input) (state : State s t)
    (offset : Nat) (disp : BitVec 32) (bound : offset+5 ≤ 118431)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (target : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 1 t u ∧ State s u 272 ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) t).Holds t u := by
  obtain ⟨u,run,ready,effect⟩ := ScalarFrame.call_step pre.toCalleePre (frameOffset := 264)
    (by decide) (by decide) (readyToStep state.machine state.bindingsSupported) state.loaded
    state.allocated state.rsp offset disp bound bytes (inProgram_low target) target rip
  have addr : pushAddr t = stackPtr s - 272#64 := by
    simp only [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have localFrame : MemoryWriteFrame t u (bodyWrites s) := effect.agrees.memoryWriteFrame (by
    intro c hc a covered
    simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covered.elim
    · refine ⟨ScalarFrame.workRegion s 3624,by simp [bodyWrites],?_⟩
      rw [addr] at covered
      exact ScalarFrame.work_contains pre.toCalleePre (offset := 272) (len := 8)
        (by decide) (by decide) covered
    · exact covered.elim)
  have stateU : State s u 272 := by
    refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees state.machine ready effect.agrees,?_,
      effect.agrees.directionFlagClear (by simp [pushEffect_components]) state.directionFlag,
      fun a ha => effect.agrees.grow a (state.allocated a ha),
      memoryWriteFrame_trans state.frame (body_frame pre localFrame),?_,?_,?_,
      (effect.agrees.mxcsr (by simp [pushEffect_components])).trans state.mxcsr,
      (effect.agrees.fcw (by simp [pushEffect_components])).trans state.fp87⟩
    · intro a b loaded
      rw [body_frame pre localFrame a]
      · exact state.loaded a b loaded
      · intro r hr hit
        have choice : r = registerRegion s .rdi 104 ∨ r = registerRegion s .rsi 16 ∨
            r = Stack.region s 3624 := by simpa [writes] using hr
        rcases choice with rfl | rfl | rfl
        · exact pre.avoids _ (by simp) a hit (.inl ⟨b,loaded⟩)
        · exact pre.descriptorAvoids a hit (.inl ⟨b,loaded⟩)
        · exact pre.avoids _ (by simp) a hit (.inl ⟨b,loaded⟩)
    · exact effect.writes.1.trans addr
    · intro entry he
      have bound : entry.2 ≤ 48 := by
        simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (body_read pre localFrame bound (by omega)).trans (state.saved entry he)
    · have h := body_read pre localFrame (offset := 0) (width := 64) (by decide) (by decide)
      simp only [BitVec.sub_zero] at h
      exact h.trans state.returnAddress
  exact ⟨u,run,stateU,effect⟩

theorem return_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {input : ByteArray}
    {outputBytes reserve outputOffset : Nat}
    (pre : Pre s boundary input) (state : State s t 272)
    (result : CalleeResult t u boundary outputBytes reserve)
    (output : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 outputOffset)
    (capacity : 272 + reserve ≤ 3624) (outputBound : outputOffset ≤ 3624)
    (outputBelow : outputBytes + 48 ≤ outputOffset) : State s u := by
  have memory := result.stack_frame pre.stack state.rsp output capacity (by decide)
    outputBound outputBelow
  have localFrame : MemoryWriteFrame t u (bodyWrites s) := by
    intro a ha
    exact memory a (fun r hr hit => ha r (by
      have eq : r = ScalarFrame.workRegion s 3624 := by simpa using hr
      subst r
      simp [bodyWrites]) hit)
  refine ⟨result.bindingsSupported,result.machine,result.loaded,result.directionFlag,
    fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (body_frame pre localFrame),?_,?_,?_,
    result.mxcsr.trans state.mxcsr,result.fp87.trans state.fp87⟩
  · have sp : stackPtr u = stackPtr t + 8 := result.rsp
    rw [sp,state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rfl
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (body_read pre localFrame bound (by omega)).trans (state.saved entry he)
  · have h := body_read pre localFrame (offset := 0) (width := 64) (by decide) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Generate.Sampler
