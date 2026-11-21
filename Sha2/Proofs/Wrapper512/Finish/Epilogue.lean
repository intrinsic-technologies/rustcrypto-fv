import Sha2.Proofs.Wrapper512.API
import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Encoding.Serialize

theorem SavedStackAt.of_bytes {initial s t : RamState} (h : SavedStackAt initial s)
    (bytes : ∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      t.external[a]? = s.external[a]?) : SavedStackAt initial t := by
  have read (offset : Nat) (bound : offset ≤ 48) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    have addr : stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
        stackPtr initial - 48 + BitVec.ofNat 64 (48 - offset + i) := by
      have offsetEq : (48 : BitVec 64) = BitVec.ofNat 64 offset + BitVec.ofNat 64 (48 - offset) := by
        rw [← BitVec.ofNat_add, Nat.add_sub_cancel' bound]
        rfl
      rw [BitVec.ofNat_add, offsetEq]
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
      congr 2
      rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [bytes _ ⟨48 - offset + i, by omega, addr⟩]
  constructor
  · intro slot hs
    exact (read slot.2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans (h.words slot hs)
  · have zero := read 0 (by decide)
    simp only [BitVec.sub_zero] at zero
    exact zero.trans h.returnAddress

structure ReturnState [bindings : Bindings] (v : Variant) (initial s : RamState) (form : Form := .slices) : Prop where
  execution : ∃ fuel, Advances (returnBoundary initial) fuel initial s
  machine : SupportedMachine bindings s
  loaded : ProgramLoaded s
  allocated : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome
  saved : SavedStackAt initial s
  directionFlag : DirectionFlagUnset s
  frame : MemoryWriteFrame initial s
    (v.writeRegions initial form)
  rsp : ∃ offset, stackPtr s = stackPtr initial - BitVec.ofNat 64 offset

theorem ReturnState.of_state [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    (state : State v initial s form) : ReturnState v initial s form :=
  ⟨state.execution, state.machine, state.loaded, state.allocated, state.saved,
    state.directionFlag, state.frame, ⟨form.frameBytes, state.rsp⟩⟩

theorem ReturnState.of_agrees [bindings : Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {components : List Component} {fuel : Nat}
    (h : ReturnState v initial s form) (ctx : Context v initial inputs form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t)
    (writes : WritesWithin components
      (v.writeRegions initial form))
    (rspOffset : Nat) (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 rspOffset)
    (saved : ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a)
    (hdf : .df ∉ components := by simp) :
    ReturnState v initial t form := by
  have memory := frame.memoryWriteFrame writes
  obtain ⟨n, hn⟩ := h.execution
  refine ⟨⟨n + fuel, hn.trans run⟩,
    supportedMachine_of_ready_agrees h.machine ready frame, ?_,
    fun a ha => frame.grow a (h.allocated a ha), ?_,
    frame.directionFlagClear hdf h.directionFlag,
    memoryWriteFrame_trans h.frame memory, ⟨rspOffset, rsp⟩⟩
  · intro address byte fetch
    rw [memory address]
    · exact h.loaded address byte fetch
    · intro region hr ha
      exact (ctx.separation.2 region (by simpa using hr)).2 address ha (.inl ⟨byte, fetch⟩)
  · exact h.saved.of_bytes (fun a ha => frame.memory a (fun c hc => saved c hc a ha))

theorem pop_saved [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : ReturnState v initial s form)
    (codeOffset stackOffset : Nat) (dst : BitVec 4)
    (dstRsp : dst.setWidth 5 ≠ 4)
    (codeBound : codeOffset + (encodePopR64 dst).length < 71757)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset (encodePopR64 dst).length =
      encodePopR64 dst) (stackBound : stackOffset ≤ 48) (stackStep : 8 ≤ stackOffset)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 stackOffset) :
    ∃ t, ReturnState v initial t form ∧
      (popR64Effect (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        (encodePopR64 dst).length (dst.setWidth 5) s).Holds s t := by
  have initialRead := stack_valid_sub_readable ctx.stack
    (offset := stackOffset) (len := 8) (by cases form <;> change stackOffset ≤ _ <;> simp only [Variant.routine, Form.stackBytes] <;> omega) (by omega)
  have readable : MemReadable s (stackPtr s) 8 := by
    rw [rsp]
    exact ⟨initialRead.low, fun i hi => state.allocated _ (initialRead.mem i hi)⟩
  obtain ⟨t, run, ready, effect⟩ :=
    (Common.Encoding.Serialize.pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) dst dstRsp).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) codeOffset (encodePopR64 dst)
        (by omega) codeBytes) ⟨rip, readable⟩ (by
          change Extracted.textAddress + BitVec.ofNat 64 codeOffset +
            BitVec.ofNat 64 (encodePopR64 dst).length ≠ (returnBoundary initial).rip
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          exact boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
            (inProgram_of_textOffset _ codeBound))
  have rspT : stackPtr t = stackPtr initial - BitVec.ofNat 64 (stackOffset - 8) := by
    have hw : stackPtr t = stackPtr s + 8 := effect.writes.2
    rw [hw, rsp]
    rw [← BitVec.ofNat_sub_ofNat_of_le stackOffset 8 (by omega) stackStep]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    rw [BitVec.neg_add]
    rw [BitVec.sub_neg]
  refine ⟨t, ReturnState.of_agrees state ctx run ready effect.agrees ?_
    (stackOffset - 8) rspT ?_, effect⟩
  · simp [WritesWithin, Effect.components, popR64Effect, Write.component, Operand.component,
      Component.Covers]
  · simp [Effect.components, popR64Effect, Write.component, Operand.component, Component.Covers]

theorem readOutput_eq_of_external_eq {v : Variant} {form : Form}
    {initial s t : RamState} (same : t.external = s.external) :
    v.readOutput initial t form = v.readOutput initial s form := by
  have read (region : MemoryRegion) : readBytes region t = readBytes region s := by
    unfold readBytes
    rw [same]
  cases form with
  | slices => exact read _
  | digest => exact read _
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    dsimp only [Variant.readOutput]
    exact congr (congrArg (ite _) (read _)) (read _)

set_option maxHeartbeats 2000000 in
theorem run_preserving_memory [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (rip : s.RIP = v.pc (v.epilogueOffset form) form)
    (output : v.readOutput initial s form = .ok (v.digest (message inputs))) :
    ∃ final, FinishResult v initial final inputs form ∧ final.external = s.external := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (add_r64_imm32_effect_step (v.pc (v.epilogueOffset form) form) 0x48 0xc4 (BitVec.ofNat 32 (form.frameBytes - 48))
      (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded)
        ((v.textOffset form) + (v.epilogueOffset form))
        (0x48 :: 0x81 :: 0xc4 :: immBytes 32 (BitVec.ofNat 32 (form.frameBytes - 48)))
        (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)) rip
      (boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 (by
          have hnext : InProgram (v.pc ((v.epilogueOffset form) + 7) form) := by
            apply inProgram_of_textOffset
            cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel
          simpa [addR64Imm32Effect, Variant.pc_add] using hnext))
  change (addR64Imm32Effect (v.pc (v.epilogueOffset form) form) 4 (BitVec.ofNat 32 (form.frameBytes - 48)) s).Holds s a at effectA
  have rspA : stackPtr a = stackPtr initial - BitVec.ofNat 64 48 := by
    have hw : stackPtr a = stackPtr s + (BitVec.ofNat 64 (form.frameBytes - 48)) := by
      have hw := effectA.writes
      change stackPtr a = stackPtr s + (BitVec.ofNat 32 (form.frameBytes - 48)).signExtend 64 at hw
      rwa [show (BitVec.ofNat 32 (form.frameBytes - 48)).signExtend 64 =
        BitVec.ofNat 64 (form.frameBytes - 48) by cases form <;> dsimp only [Form.frameBytes] <;> decide +kernel] at hw
    calc
      stackPtr a = stackPtr s + (BitVec.ofNat 64 (form.frameBytes - 48)) := hw
      _ = (stackPtr initial - BitVec.ofNat 64 form.frameBytes) + (BitVec.ofNat 64 (form.frameBytes - 48)) := by rw [state.rsp]
      _ = stackPtr initial - BitVec.ofNat 64 48 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rw [show -BitVec.ofNat 64 form.frameBytes + (BitVec.ofNat 64 (form.frameBytes - 48)) = -BitVec.ofNat 64 48 by cases form <;> dsimp only [Form.frameBytes] <;> decide +kernel]
  have stateA : ReturnState v initial a form := ReturnState.of_agrees (ReturnState.of_state state)
    ctx runA readyA effectA.agrees
    (by simp [WritesWithin, Effect.components, addR64Imm32Effect, Write.component,
      Operand.component, Component.Covers]) 48 rspA
    (by simp [Effect.components, addR64Imm32Effect, Component.Covers])
  have ripA : a.RIP = v.pc ((v.epilogueOffset form) + 7) form := by
    rw [effectA.rip]
    change v.pc (v.epilogueOffset form) form + BitVec.ofNat 64 7 = v.pc ((v.epilogueOffset form) + 7) form
    exact Variant.pc_add v (v.epilogueOffset form) 7 form
  obtain ⟨s1, state1, effect1⟩ := pop_saved ctx stateA
    ((v.textOffset form) + (v.epilogueOffset form) + 7) 48 3 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := ripA) (rsp := rspA)
  have rsp1 : stackPtr s1 = stackPtr initial - BitVec.ofNat 64 40 := by
    have hw : stackPtr s1 = stackPtr a + 8 := effect1.writes.2
    rw [hw, rspA]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value1 : s1.regValue .rbx = initial.regValue .rbx := by
    have hw : s1.regValue .rbx = memLoad a.external (stackPtr a) 64 := effect1.writes.1
    rw [rspA] at hw
    exact hw.trans (stateA.saved.words (.rbx, 48) (by simp))
  have rip1 : s1.RIP = Extracted.textAddress + BitVec.ofNat 64
      ((v.textOffset form) + (v.epilogueOffset form) + 8) := by
    simpa [popR64Effect, encodePopR64, BitVec.add_assoc, ← BitVec.ofNat_add] using effect1.rip
  obtain ⟨s2, state2, effect2⟩ := pop_saved ctx state1
    ((v.textOffset form) + (v.epilogueOffset form) + 8) 40 12 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := rip1) (rsp := rsp1)
  have rsp2 : stackPtr s2 = stackPtr initial - BitVec.ofNat 64 32 := by
    have hw : stackPtr s2 = stackPtr s1 + 8 := effect2.writes.2
    rw [hw, rsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value2 : s2.regValue .r12 = initial.regValue .r12 := by
    have hw : s2.regValue .r12 = memLoad s1.external (stackPtr s1) 64 := effect2.writes.1
    rw [rsp1] at hw
    exact hw.trans (state1.saved.words (.r12, 40) (by simp))
  have rip2 : s2.RIP = Extracted.textAddress + BitVec.ofNat 64
      ((v.textOffset form) + (v.epilogueOffset form) + 10) := by
    simpa [popR64Effect, encodePopR64, BitVec.add_assoc, ← BitVec.ofNat_add] using effect2.rip
  obtain ⟨s3, state3, effect3⟩ := pop_saved ctx state2
    ((v.textOffset form) + (v.epilogueOffset form) + 10) 32 13 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := rip2) (rsp := rsp2)
  have rsp3 : stackPtr s3 = stackPtr initial - BitVec.ofNat 64 24 := by
    have hw : stackPtr s3 = stackPtr s2 + 8 := effect3.writes.2
    rw [hw, rsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value3 : s3.regValue .r13 = initial.regValue .r13 := by
    have hw : s3.regValue .r13 = memLoad s2.external (stackPtr s2) 64 := effect3.writes.1
    rw [rsp2] at hw
    exact hw.trans (state2.saved.words (.r13, 32) (by simp))
  have rip3 : s3.RIP = Extracted.textAddress + BitVec.ofNat 64
      ((v.textOffset form) + (v.epilogueOffset form) + 12) := by
    simpa [popR64Effect, encodePopR64, BitVec.add_assoc, ← BitVec.ofNat_add] using effect3.rip
  obtain ⟨s4, state4, effect4⟩ := pop_saved ctx state3
    ((v.textOffset form) + (v.epilogueOffset form) + 12) 24 14 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := rip3) (rsp := rsp3)
  have rsp4 : stackPtr s4 = stackPtr initial - BitVec.ofNat 64 16 := by
    have hw : stackPtr s4 = stackPtr s3 + 8 := effect4.writes.2
    rw [hw, rsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value4 : s4.regValue .r14 = initial.regValue .r14 := by
    have hw : s4.regValue .r14 = memLoad s3.external (stackPtr s3) 64 := effect4.writes.1
    rw [rsp3] at hw
    exact hw.trans (state3.saved.words (.r14, 24) (by simp))
  have rip4 : s4.RIP = Extracted.textAddress + BitVec.ofNat 64
      ((v.textOffset form) + (v.epilogueOffset form) + 14) := by
    simpa [popR64Effect, encodePopR64, BitVec.add_assoc, ← BitVec.ofNat_add] using effect4.rip
  obtain ⟨s5, state5, effect5⟩ := pop_saved ctx state4
    ((v.textOffset form) + (v.epilogueOffset form) + 14) 16 15 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := rip4) (rsp := rsp4)
  have rsp5 : stackPtr s5 = stackPtr initial - BitVec.ofNat 64 8 := by
    have hw : stackPtr s5 = stackPtr s4 + 8 := effect5.writes.2
    rw [hw, rsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value5 : s5.regValue .r15 = initial.regValue .r15 := by
    have hw : s5.regValue .r15 = memLoad s4.external (stackPtr s4) 64 := effect5.writes.1
    rw [rsp4] at hw
    exact hw.trans (state4.saved.words (.r15, 16) (by simp))
  have rip5 : s5.RIP = Extracted.textAddress + BitVec.ofNat 64
      ((v.textOffset form) + (v.epilogueOffset form) + 16) := by
    simpa [popR64Effect, encodePopR64, BitVec.add_assoc, ← BitVec.ofNat_add] using effect5.rip
  obtain ⟨s6, state6, effect6⟩ := pop_saved ctx state5
    ((v.textOffset form) + (v.epilogueOffset form) + 16) 8 5 (by decide) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel)
    (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by decide) (by decide) (rip := rip5) (rsp := rsp5)
  have rsp6 : stackPtr s6 = stackPtr initial := by
    have hw : stackPtr s6 = stackPtr s5 + 8 := effect6.writes.2
    rw [hw, rsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd,
      BitVec.add_zero]
  have value6 : s6.regValue .rbp = initial.regValue .rbp := by
    have hw : s6.regValue .rbp = memLoad s5.external (stackPtr s5) 64 := effect6.writes.1
    rw [rsp5] at hw
    exact hw.trans (state5.saved.words (.rbp, 8) (by simp))
  have readable : MemReadable s6 (stackPtr s6) 8 := by
    rw [rsp6]
    have hread := stack_valid_sub_readable ctx.stack
      (offset := 0) (len := 8) (Nat.zero_le _) (by omega)
    refine ⟨?_, fun i hi => state6.allocated _ ?_⟩
    · simpa only [BitVec.sub_zero] using hread.low
    · simpa only [BitVec.sub_zero] using hread.mem i hi
  have top : stackTop s6 = (returnBoundary initial).rip := by
    change memLoad s6.external (stackPtr s6) 64 = _
    rw [rsp6]
    exact state6.saved.returnAddress
  have rip6 : s6.RIP = v.pc ((v.epilogueOffset form) + 17) form := by
    simpa [popR64Effect, encodePopR64, Variant.pc, BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_assoc] using effect6.rip
  have topLow : (stackTop s6).toNat < 2^32 := by
    rw [top]
    obtain ⟨address, loaded, low, outside⟩ := ctx.returnAddress
    have value : memLoad initial.external (stackPtr initial) 64 = address := by
      rw [stackPtr_eq_regValue_rsp]
      apply Sha2.Proofs.Common.Memory.memLoad_of_loadBytes64
      simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded.2
    change (memLoad initial.external (stackPtr initial) 64).toNat < 2^32
    rw [value]
    exact low
  have boundaryEq : Prelude.nearReturn64Boundary initial = .ok (returnBoundary initial) := by
    have hread := stack_valid_sub_readable ctx.stack
      (offset := 0) (len := 8) (Nat.zero_le _) (by omega)
    have hread' : MemReadable initial (stackPtr initial) 8 := by
      simpa only [BitVec.sub_zero] using hread
    exact nearReturn64Boundary_eq initial (supportedMachine_readyToStep ctx.machine).dataReady
      ctx.machine.supported.integer.ss hread'
  obtain ⟨final, step, ready, effect⟩ := ret_effect_step (v.pc ((v.epilogueOffset form) + 17) form) s6
      (supportedMachine_readyToStep state6.machine)
    (programText_slice (programLoaded_codeIn state6.loaded)
      ((v.textOffset form) + (v.epilogueOffset form) + 17) [0xc3]
      (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel) (by cases form <;> cases v <;> dsimp only [Variant.pc, Variant.textOffset, Variant.epilogueOffset, Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide +kernel))
    ⟨⟨rip6, readable⟩, top ▸ topLow⟩
  have ret : X86Proofs.Returns (returnBoundary initial) 1 s6 final :=
    X86Proofs.Returns.of_step step (effect.rip.trans top) (by
      change stackPtr final = stackPtr initial + 8
      have hw : stackPtr final = stackPtr s6 + 8 := effect.writes
      rw [hw, rsp6])
  have finalFrame : AgreesExcept [.reg 4, .rip] s6 final := effect.agrees
  have calleeSaved : CalleeSavedRegistersUnchanged initial final := by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp),
        effect4.agrees.read (by simp), effect3.agrees.read (by simp), effect2.agrees.read (by simp)]
      exact value1
    · change (Operand.reg 5 : Operand 64).read final = _
      rw [finalFrame.read (by simp)]
      exact value6
    · change (Operand.reg 12 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp),
        effect4.agrees.read (by simp), effect3.agrees.read (by simp)]
      exact value2
    · change (Operand.reg 13 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp),
        effect4.agrees.read (by simp)]
      exact value3
    · change (Operand.reg 14 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp)]
      exact value4
    · change (Operand.reg 15 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp)]
      exact value5
  obtain ⟨fuel, execution⟩ := state6.execution
  have unique := (execution.returns ret).unique_of_boundary
    boundaryEq
  have finalExternal : final.external = s.external := by
    rw [finalFrame.external (by simp [Component.Covers]),
    effect6.agrees.external (by simp [Component.Covers]),
    effect5.agrees.external (by simp [Component.Covers]),
    effect4.agrees.external (by simp [Component.Covers]),
    effect3.agrees.external (by simp [Component.Covers]),
    effect2.agrees.external (by simp [Component.Covers]),
    effect1.agrees.external (by simp [Component.Covers]),
    effectA.agrees.external (by simp [Component.Covers])]
  refine ⟨final, ?_, finalExternal⟩
  refine ⟨unique, (supportedMachine_of_ready_agrees state6.machine ready finalFrame).supported,
    (supportedMachine_of_ready_agrees state6.machine ready finalFrame).to_environment ctx.stride,
    ?_, ?_, calleeSaved, finalFrame.directionFlagClear (by simp) state6.directionFlag⟩
  · intro address outside
    rw [finalFrame.external (by simp [Component.Covers])]
    exact state6.frame address outside
  · exact (readOutput_eq_of_external_eq finalExternal).trans output

theorem run [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (rip : s.RIP = v.pc (v.epilogueOffset form) form)
    (output : v.readOutput initial s form = .ok (v.digest (message inputs))) :
    ∃ final, FinishResult v initial final inputs form := by
  obtain ⟨final, result, _⟩ := run_preserving_memory ctx state rip output
  exact ⟨final, result⟩

end Sha2.Proofs.Wrapper512
