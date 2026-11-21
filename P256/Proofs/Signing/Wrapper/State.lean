import P256.Proofs.Signing.Wrapper.Interface
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Program.CalleeStackFrame
import P256.Proofs.Program.State
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

abbrev workRegion (initial : RamState) := ScalarFrame.Work.region initial 5112 48

theorem work_contains {initial : RamState}
    (stack : Stack.Valid initial 5112) {offset len : Nat} {a : BitVec 64}
    (bound : offset ≤ 5112) (below : len+48 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack bound
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by rw [low]; omega), low]
  change (stackPtr initial).toNat - 5112 ≤ _ ∧
    _ < (stackPtr initial).toNat - 5112 + (5112-48)
  constructor <;> omega

theorem work_frame {initial s t : RamState}
    (stack : Stack.Valid initial 5112)
    (memory : MemoryWriteFrame s t #v[workRegion initial]) :
    MemoryWriteFrame s t (wrapperRegions signingKeyTrySign initial) := by
  intro a ha
  apply memory a
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  apply ha (callStack signingKeyTrySign initial) (by simp [wrapperRegions])
  apply stack_contains_callStack
  have bounds := stack_bounds stack
  change (stackPtr initial).toNat - 5112 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 5112 + (5112 - 48) at hin
  change (stackPtr initial).toNat - 5112 ≤ a.toNat ∧
    a.toNat < (Stack.region initial 5112).start + (Stack.region initial 5112).size
  rw [stack_region_end]
  constructor <;> omega

theorem work_read {initial s t : RamState}
    (stack : Stack.Valid initial 5112)
    (memory : MemoryWriteFrame s t #v[workRegion initial])
    {offset : Nat} (bound : offset ≤ 48) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  have bounds := stack_bounds stack
  have low := stack_sub_toNat stack (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  change (stackPtr initial).toNat - 5112 ≤ _ ∧
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (stackPtr initial).toNat - 5112 + (5112 - 48) at hin
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, low] at hin
  have iBound : i < 8 := hi
  omega

theorem State.after_effect [Bindings] {initial s t : RamState} {secret message : ByteArray}
    {slices : Array Input} {offset nextOffset fuel : Nat} {cs : List Component}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret, message] slices)
    (state : State initial s offset)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t)
    (writes : WritesWithin cs #v[workRegion initial])
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 nextOffset)
    (df : Component.df ∉ cs) : State initial t nextOffset := by
  have memory := agrees.memoryWriteFrame writes
  have total := memoryWriteFrame_trans state.frame (work_frame call.stackAvailable.1 memory)
  obtain ⟨n, previous⟩ := state.execution
  refine ⟨⟨n+fuel, previous.trans run⟩,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees,
    wrapper_frame_loaded call call.programLoaded total,
    agrees.directionFlagClear df state.directionFlag,
    rsp,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbx,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR12,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR13,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR14,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR15,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbp,
    ?_, fun a ha => agrees.grow a (state.allocated a ha), total⟩
  · have h := work_read call.stackAvailable.1 memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem State.call_rel32 [Bindings] {initial s : RamState} {secret message : ByteArray}
    {slices : Array Input} {offset : Nat}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret, message] slices)
    (state : State initial s offset) (outside : ¬ InProgram (returnBoundary initial).rip)
    (codeOffset : Nat) (disp : BitVec 32)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (capacity : offset+8 ≤ 5112) (below : 48 ≤ offset) (aligned : (offset+8)%8 = 0)
    (size : codeOffset+5 ≤ 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
      5 (disp.signExtend 64))) :
    ∃ t, State initial t (offset+8) ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        5 (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 codeOffset+5) s).Holds s t ∧
      t.external = memStore s.external (stackPtr initial - BitVec.ofNat 64 (offset+8))
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset+5) := by
  obtain ⟨t,run,ready,_,effect,memory⟩ := call_rel32_exists call.stackAvailable.1
    (call_stack_avoids call) outside (readyToStep state.machine state.bindingsSupported)
    state.loaded state.allocated offset codeOffset disp state.rsp rip capacity aligned size bytes target
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (offset+8) := by
    rw [pushAddr,state.rsp,BitVec.sub_sub,BitVec.ofNat_add]
    rfl
  refine ⟨t,state.after_effect call run ready effect.agrees ?_ ?_ ?_,effect,memory⟩
  · intro c hc a ha
    simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · refine ⟨workRegion initial,by simp,?_⟩
      rw [address] at ha
      exact work_contains call.stackAvailable.1 capacity (by omega) ha
    · exact ha.elim
  · exact effect.writes.1.trans address
  · simp [pushEffect_components]

theorem State.after_callee [Bindings] {initial s t : RamState} {secret message : ByteArray}
    {slices : Array Input} {offset outputBytes reserve outputOffset : Nat}
    (call : ValidCallWithSlices signingKeyTrySign initial [secret, message] slices)
    (state : State initial s (offset+8))
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (capacity : offset+8+reserve ≤ 5112) (stackBelow : 48 ≤ offset)
    (outputBound : outputOffset ≤ 5112) (outputBelow : outputBytes+48 ≤ outputOffset) :
    State initial t offset := by
  have memory := result.stack_frame call.stackAvailable.1 state.rsp destination capacity
    (by omega) outputBound outputBelow
  obtain ⟨n, previous⟩ := state.execution
  obtain ⟨fuel, run⟩ := result.execution
  refine ⟨⟨n+fuel, previous.trans run⟩, result.bindingsSupported, result.machine, result.loaded,
    result.directionFlag, ?_,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbx,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR12,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR13,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR14,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedR15,
    (work_read call.stackAvailable.1 memory (by decide)).trans state.savedRbp,
    ?_, fun a ha => result.allocated a (state.allocated a ha),
    memoryWriteFrame_trans state.frame (work_frame call.stackAvailable.1 memory)⟩
  · change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr s+8 = _
    rw [state.rsp, BitVec.ofNat_add, ← BitVec.sub_sub]
    exact BitVec.sub_add_cancel _ _
  · have h := work_read call.stackAvailable.1 memory (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

end P256.Proofs.Signing.Wrapper
