import P256.Proofs.Signing.Wrapper.Hash.Interface
import P256.Proofs.Signing.Wrapper.State
import P256.Proofs.Program.StackBuffer

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial start s t : RamState} {secret message : ByteArray}

set_option maxRecDepth 2048 in
theorem stack (pre : Context initial secret message) : Stack.Valid initial 5112 := by
  obtain ⟨slices, call⟩ := pre.call
  exact call.stackAvailable.1

set_option maxRecDepth 2048 in
theorem stack_avoids (pre : Context initial secret message) :
    (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) := by
  obtain ⟨slices, call⟩ := pre.call
  have h := call_stack_avoids call
  change (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) at h
  exact h

set_option maxRecDepth 2048 in
theorem outside (pre : Context initial secret message) :
    ¬ InProgram (returnBoundary initial).rip := by
  obtain ⟨slices, call⟩ := pre.call
  exact outer_boundary call pre.machine pre.bindingsSupported

 theorem work_contains (pre : Context initial secret message) {offset len : Nat} {a : BitVec 64}
    (bound : offset ≤ 5112) (below : len + 240 ≤ offset)
    (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  have bounds := stack_bounds (stack pre)
  have low := stack_sub_toNat (stack pre) bound
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
    Nat.mod_eq_of_lt (by rw [low]; omega), low]
  change (stackPtr initial).toNat - 5112 ≤ _ ∧
    _ < (stackPtr initial).toNat - 5112 + (5112 - 240)
  constructor <;> omega

 theorem work_widen (pre : Context initial secret message) {a : Nat}
    (inside : (workRegion initial).Contains a) :
    (Wrapper.workRegion initial).Contains a := by
  have bounds := stack_bounds (stack pre)
  change (stackPtr initial).toNat - 5112 ≤ a ∧
    a < (stackPtr initial).toNat - 5112 + (5112 - 240) at inside
  change (stackPtr initial).toNat - 5112 ≤ a ∧
    a < (stackPtr initial).toNat - 5112 + (5112 - 48)
  constructor <;> omega

 theorem Frame.after_effect {offset nextOffset fuel : Nat} {cs : List Component}
    (pre : Context initial secret message) (state : Frame initial start s offset)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (writes : WritesWithin cs #v[workRegion initial])
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 nextOffset)
    (df : Component.df ∉ cs) : Frame initial start t nextOffset := by
  obtain ⟨slices, call⟩ := pre.call
  refine ⟨state.toState.after_effect call run ready agrees ?_ rsp df, ?_,
    memoryWriteFrame_trans state.stackFrame (agrees.memoryWriteFrame writes)⟩
  · intro c hc a ha
    obtain ⟨region, member, inside⟩ := writes c hc a ha
    have eq : region = workRegion initial := by simpa using member
    subst region
    exact ⟨Wrapper.workRegion initial, by simp, work_widen pre inside⟩
  · obtain ⟨before, previous⟩ := state.run
    exact ⟨before + fuel, previous.trans run⟩

 theorem Frame.after_registers {offset fuel : Nat} {cs : List Component}
    (pre : Context initial secret message) (state : Frame initial start s offset)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (noMem : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (rsp : Component.reg 4 ∉ cs) (df : Component.df ∉ cs := by component_not_mem) :
    Frame initial start t offset :=
  state.after_effect pre run ready agrees (by
    intro c hc a ha
    exact (noMem c hc a ha).elim)
    ((agrees.read (n := 64) rsp).trans state.rsp) df

 theorem Frame.after_callee {offset outputBytes reserve outputOffset : Nat}
    (pre : Context initial secret message) (state : Frame initial start s (offset+8))
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (capacity : offset+8+reserve ≤ 5112) (stackBelow : 240 ≤ offset)
    (outputBound : outputOffset ≤ 5112) (outputBelow : outputBytes+240 ≤ outputOffset) :
    Frame initial start t offset := by
  obtain ⟨slices, call⟩ := pre.call
  refine ⟨state.toState.after_callee call result destination capacity (by omega)
    outputBound (by omega), ?_, ?_⟩
  · obtain ⟨before, previous⟩ := state.run
    obtain ⟨fuel, run⟩ := result.execution
    exact ⟨before+fuel, previous.trans run⟩
  · exact memoryWriteFrame_trans state.stackFrame
      (result.stack_frame (stack pre) state.rsp destination capacity (by omega)
        outputBound outputBelow)

 theorem stack_readable (pre : Context initial secret message)
    (state : Frame initial start s) {offset len : Nat} (bound : offset+len ≤ 520) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by omega)]
  exact readable_of_grow (stack_sub_readable (stack pre) (by omega) (by omega)) state.allocated

 theorem stack_writable (pre : Context initial secret message)
    (state : Frame initial start s) {offset len : Nat} (bound : offset+len ≤ 520)
    (positive : 0 < len) :
    Common.Instructions.CrossPageStore.Writable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by omega)]
  exact stack_buffer_writable (stack pre) (stack_avoids pre) state.allocated
    (by omega) (by omega) positive

 theorem stack_code (pre : Context initial secret message)
    (state : Frame initial start s) {offset len codeOffset codeLen : Nat}
    (bound : offset+len ≤ 520) (codeBound : codeOffset+codeLen ≤ 118431) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen := by
  rw [ScalarFrame.scalar_stack_address state.rsp (by decide) (by omega)]
  exact stack_buffer_code_apart (stack pre) (stack_avoids pre)
    (by omega) (by omega) codeBound

theorem Frame.call_rel32 (pre : Context initial secret message) (state : Frame initial start s)
    (codeOffset : Nat) (disp : BitVec 32)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (size : codeOffset+5 ≤ 118431)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (target : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
      5 (disp.signExtend 64))) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Frame initial start t 528 ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        5 (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 codeOffset+5) s).Holds s t := by
  obtain ⟨t,run,ready,_,effect,_⟩ := call_rel32_exists (stack pre) (stack_avoids pre)
    (outside pre) (readyToStep state.machine state.bindingsSupported) state.loaded state.allocated
    520 codeOffset disp state.rsp rip (by decide) (by decide) size bytes target
  have address : pushAddr s = stackPtr initial - 528 := by
    rw [pushAddr, state.rsp]
    bv_omega
  refine ⟨t, run, state.after_effect pre run ready effect.agrees ?_
    (effect.writes.1.trans address) (by simp [pushEffect_components]), effect⟩
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · refine ⟨workRegion initial, by simp, ?_⟩
    rw [address] at ha
    exact work_contains pre (by decide) (by decide) ha
  · exact ha.elim

 theorem initial_frame (pre : HashEntry initial start secret message) :
    Frame initial start start := by
  refine ⟨pre.toState, ⟨0, ?_⟩, ?_⟩
  · rfl
  · intro a _
    rfl

end P256.Proofs.Signing.Wrapper.Hash
