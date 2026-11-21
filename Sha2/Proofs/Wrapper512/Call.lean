import Sha2.Proofs.Wrapper.Call
import Sha2.Proofs.Wrapper512.Finish.Epilogue
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper (allocated_of_grow stack_region_contains_of_bounds)

theorem callee_regions [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {outputBytes outputOffset reserve : Nat} (ctx : Context v initial inputs form)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ form.frameBytes)
    (stackLow : reserve ≤ 544) :
    (∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
      ∀ a, region.Contains a → (Stack.region initial form.stackBytes).Contains a) ∧
    (∀ a, (Component.mem (stackPtr initial - 48) 56).Covers a →
      ∀ region ∈ #v[registerRegion s .rdi outputBytes, Stack.region s reserve],
        ¬ region.Contains a.toNat) := by
  have budget : form.stackBytes = form.frameBytes + 552 := by cases form <;> rfl
  have frameLow : 48 ≤ form.frameBytes := by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have sp : (stackPtr s).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) := by
    rw [rsp]
    exact Dispatch.stack_sub_toNat512 ctx (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide)
  have out : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [rdi]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  constructor
  · intro region hr a ha
    have cases : region = registerRegion s .rdi outputBytes ∨
        region = Stack.region s reserve := by simpa using hr
    rcases cases with rfl | rfl
    · change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + outputBytes at ha
      rw [out] at ha
      apply stack_region_contains_of_bounds
      · change (stackPtr initial).toNat - form.stackBytes ≤ a
        omega
      · omega
    · have low : (stackPtr s).toNat - reserve ≤ a := ha.1
      have high : a < (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using ha.2
      rw [sp] at low high
      apply stack_region_contains_of_bounds
      · change (stackPtr initial).toNat - form.stackBytes ≤ a
        omega
      · omega
  · intro a ha region hr hin
    obtain ⟨i, hi, rfl⟩ := ha
    have base := Dispatch.stack_sub_toNat512 ctx (offset := 48) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide)
    have addr : (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat =
        (stackPtr initial).toNat - 48 + i := by
      rw [BitVec.toNat_add]
      change ((stackPtr initial - 48#64).toNat + (BitVec.ofNat 64 i).toNat) % 2^64 = _
      rw [base, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have cases : region = registerRegion s .rdi outputBytes ∨
        region = Stack.region s reserve := by simpa using hr
    rcases cases with rfl | rfl
    · have high := hin.2
      change (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat <
        (s.regValue .rdi).toNat + outputBytes at high
      rw [out, addr] at high
      omega
    · have high : (stackPtr initial - 48 + BitVec.ofNat 64 i).toNat <
          (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using hin.2
      rw [sp, addr] at high
      omega

theorem callee_stack_frame [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {outputBytes outputOffset reserve : Nat}
    (ctx : Context v initial inputs form)
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ form.frameBytes)
    (stackLow : reserve ≤ 544) :
    MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
  have within := (callee_regions ctx rsp rdi outputHigh outputLow stackLow).1
  intro address outside
  exact result.frame address (fun region hr ha => outside _ (by simp)
    (within region hr address.toNat ha))

theorem call_stack_writes [Bindings] {v : Variant} {form : Form} {initial : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form) :
    WritesWithin [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip]
      #v[Stack.region initial form.stackBytes] := by
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · exact ⟨Stack.region initial form.stackBytes, by simp,
      stackRegion_contains_sub ctx.stack.2.2.1 (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) ha⟩
  · exact ha.elim

theorem call_stack_frame [Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {callee : RamState → BitVec 64} {returnPC : BitVec 64}
    (ctx : Context v initial inputs form) (effect : (callEffect callee returnPC s).Holds s t)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have frame : AgreesExcept
      [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s t := by
    simpa only [callEffect, pushEffect_components, address] using effect.agrees
  exact frame.memoryWriteFrame (call_stack_writes ctx)

theorem call_callee_stack_frame [Bindings] {v : Variant} {form : Form}
    {initial s u t : RamState} {inputs : Array Input}
    {callee : RamState → BitVec 64} {returnPC : BitVec 64}
    {outputBytes outputOffset reserve : Nat}
    (ctx : Context v initial inputs form) (effect : (callEffect callee returnPC s).Holds s u)
    (result : CalleeResult u t (returnBoundary initial) outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (rdi : u.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ form.frameBytes)
    (stackLow : reserve ≤ 544) :
    MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
  have rspU : stackPtr u = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    have written : stackPtr u = pushAddr s := effect.writes.1
    rw [written, pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  exact memoryWriteFrame_trans (call_stack_frame ctx effect rsp)
    (callee_stack_frame ctx result rspU rdi outputHigh outputLow stackLow)

theorem ReturnState.of_callee [bindings : Bindings] {v : Variant} {form : Form} {initial s t : RamState}
    {inputs : Array Input} {outputBytes outputOffset reserve : Nat}
    (h : ReturnState v initial s form) (ctx : Context v initial inputs form)
    (result : CalleeResult s t (returnBoundary initial) outputBytes reserve)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ form.frameBytes)
    (stackLow : reserve ≤ 544) : State v initial t form := by
  obtain ⟨n, hn⟩ := h.execution
  obtain ⟨m, hm⟩ := result.execution
  have avoids := (callee_regions ctx rsp rdi outputHigh outputLow stackLow).2
  refine ⟨⟨n + m, hn.trans hm⟩, result.machine, result.loaded,
    fun a ha => result.allocated a (h.allocated a ha),
    h.saved.of_bytes (fun a ha => result.frame a (avoids a ha)),
    result.abi.2.1,
    ?_, ?_⟩
  · apply memoryWriteFrame_trans h.frame
    have narrowed := callee_stack_frame ctx result rsp rdi outputHigh outputLow stackLow
    intro address outside
    apply narrowed address
    intro region member
    have eq : region = Stack.region initial form.stackBytes := by simpa using member
    subst region
    exact outside _ (by cases form <;> exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩)
  · have retsp : stackPtr t = stackPtr s + 8 := result.rsp
    rw [retsp, rsp]
    cases form <;> simp only [Form.frameBytes, Nat.reduceAdd, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]

theorem ReturnState.of_call [Bindings] {v : Variant} {form : Form}
    {initial s t : RamState} {inputs : Array Input} {callee : RamState → BitVec 64}
    {returnPC : BitVec 64} {fuel : Nat}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : (callEffect callee returnPC s).Holds s t)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    ReturnState v initial t form ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) ∧
      (returnBoundary t).rip = returnPC := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have frame : AgreesExcept [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip] s t := by
    simpa only [callEffect, pushEffect_components, address] using effect.agrees
  have writes : WritesWithin [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip]
      (v.writeRegions initial form) := by
    intro c hc a ha
    obtain ⟨region, member, contains⟩ := call_stack_writes ctx c hc a ha
    have eq : region = Stack.region initial form.stackBytes := by simpa using member
    subst region
    exact ⟨_, by cases form <;> exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩, contains⟩
  have saved : ∀ c ∈ [Component.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)) 8, .rip], ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact id
    · obtain ⟨i, hi, rfl⟩ := ha
      rintro ⟨j, hj, he⟩
      apply OffsetsApart.ne (c₁ := -(BitVec.ofNat 64 (form.frameBytes + 8))) (len₁ := 8) (c₂ := -48) (len₂ := 56)
        (by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes] <;> unfold OffsetsApart <;> decide +kernel) (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg] using he.symm
    · exact id
  exact ⟨(ReturnState.of_state state).of_agrees ctx run ready frame writes (form.frameBytes + 8)
    (effect.writes.1.trans address) saved,
    effect.writes.1.trans address, (callEffect_stack effect).1⟩

theorem call_local [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (offset : Nat) (displacement : BitVec 32)
    (size : offset + 5 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 displacement)
    (target : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)).toNat < 2^32)
    (targetProgram : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)))
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    ∃ t, ReturnState v initial t form ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (displacement.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) s).Holds s t ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 ∧
      Advances (returnBoundary initial) 1 s t := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    have hw := Dispatch.stack_sub_writable8_512 ctx (offset := form.frameBytes + 8) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide)
    exact ⟨hw.low, fun i hi => state.allocated _ (hw.mem i hi), hw.tables⟩
  have instruction := programText_slice (programLoaded_codeIn state.loaded) offset
    (encodeCallRel32 displacement) size bytes
  have separate : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) 5 := by
    rw [address]
    exact Machine.Stages.stack_slot_codeApart ctx (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) size
  obtain ⟨t, run, ready, effect⟩ :=
    (call_rel32_effect_step _ displacement target).advances
      (supportedMachine_readyToStep state.machine) instruction ⟨rip, writable, separate⟩
      (boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 targetProgram)
  obtain ⟨stateT, rspT, returnT⟩ := ReturnState.of_call ctx state run ready effect rsp
  exact ⟨t, stateT, effect, rspT, returnT, run⟩

theorem call [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (offset : Nat) (displacement : BitVec 32)
    (size : offset + 5 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 displacement)
    (target : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)).toNat < 2^32)
    (targetProgram : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (displacement.signExtend 64)))
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    ∃ t, ReturnState v initial t form ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (displacement.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) s).Holds s t ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 5 := by
  obtain ⟨t, stateT, effect, rspT, returnT, _⟩ := call_local ctx state offset displacement size bytes target targetProgram rip rsp
  exact ⟨t, stateT, effect, rspT, returnT⟩

theorem call_m64_local [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (offset : Nat) (displacement : BitVec 32) (callee : BitVec 64)
    (size : offset + 6 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip displacement))
    (target : callee.toNat < 2^32) (targetProgram : InProgram callee)
    (readable : MemReadable s
      ((AddrMode.rip displacement).addr s (Extracted.textAddress + BitVec.ofNat 64 offset + 6)) 8)
    (pointer : callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip displacement) s = callee)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    ∃ t, ReturnState v initial t form ∧
      (callEffect (fun _ => callee)
        (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 6 ∧
      Advances (returnBoundary initial) 1 s t := by
  have address : pushAddr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [address]
    have hw := Dispatch.stack_sub_writable8_512 ctx (offset := form.frameBytes + 8) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide)
    exact ⟨hw.low, fun i hi => state.allocated _ (hw.mem i hi), hw.tables⟩
  have instruction := programText_slice (programLoaded_codeIn state.loaded) offset
    (encodeCallM64 (.rip displacement)) size bytes
  have separate : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) 6 := by
    rw [address]
    exact Machine.Stages.stack_slot_codeApart ctx (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide) size
  obtain ⟨t, run, ready, indirectEffect⟩ :=
    (call_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset)
      (.rip displacement) trivial rfl rfl).advances
      (supportedMachine_readyToStep state.machine) instruction
      ⟨⟨⟨rip, writable, separate⟩, by rw [pointer]; exact target⟩, readable⟩
      (by change callMemPtr _ _ s ≠ (returnBoundary initial).rip
          rw [pointer]
          exact boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 targetProgram)
  change (callEffect (callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip displacement))
    (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t at indirectEffect
  have effect : (callEffect (fun _ => callee)
      (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t := by
    simpa only [callEffect, pushEffect, pointer] using indirectEffect
  obtain ⟨stateT, rspT, returnT⟩ := ReturnState.of_call ctx state run ready effect rsp
  exact ⟨t, stateT, effect, rspT, returnT, run⟩

theorem call_m64 [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (offset : Nat) (displacement : BitVec 32) (callee : BitVec 64)
    (size : offset + 6 ≤ 71757)
    (bytes : Extracted.textBytes.toListFrom offset 6 = encodeCallM64 (.rip displacement))
    (target : callee.toNat < 2^32) (targetProgram : InProgram callee)
    (readable : MemReadable s
      ((AddrMode.rip displacement).addr s (Extracted.textAddress + BitVec.ofNat 64 offset + 6)) 8)
    (pointer : callMemPtr (Extracted.textAddress + BitVec.ofNat 64 offset) (.rip displacement) s = callee)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) :
    ∃ t, ReturnState v initial t form ∧
      (callEffect (fun _ => callee)
        (Extracted.textAddress + BitVec.ofNat 64 offset + 6) s).Holds s t ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8) ∧
      (returnBoundary t).rip = Extracted.textAddress + BitVec.ofNat 64 offset + 6 := by
  obtain ⟨t, stateT, effect, rspT, returnT, _⟩ := call_m64_local ctx state offset displacement callee size bytes target targetProgram readable pointer rip rsp
  exact ⟨t, stateT, effect, rspT, returnT⟩

theorem callee_pre [bindings : Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {entry : BitVec 64} {inputBytes outputBytes outputOffset reserve : Nat}
    (ctx : Context v initial inputs form) (state : ReturnState v initial s form)
    (rip : s.RIP = entry) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8))
    (rdi : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 outputOffset)
    (outputHigh : outputBytes + 48 ≤ outputOffset) (outputLow : outputOffset ≤ form.frameBytes)
    (reserveBound : reserve ≤ 544)
    (inputBounded : (registerRegion s .rsi inputBytes).Bounded)
    (inputAllocated : (registerRegion s .rsi inputBytes).Allocated s.external)
    (inputApart : (registerRegion s .rsi inputBytes).Disjoint (Stack.region initial form.stackBytes))
    (_ret : InProgram (returnBoundary s).rip) :
    CalleePre s (returnBoundary initial) entry inputBytes outputBytes reserve := by
  have within := (callee_regions (outputBytes := outputBytes) (outputOffset := outputOffset) (reserve := reserve)
    ctx rsp rdi outputHigh outputLow reserveBound).1
  have outputWithin := within (registerRegion s .rdi outputBytes) (by simp)
  have stackWithin := within (Stack.region s reserve) (by simp)
  have budget : form.stackBytes = form.frameBytes + 552 := by cases form <;> rfl
  have frameLow : 48 ≤ form.frameBytes := by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide
  have frameAlign : (form.frameBytes + 8) % 16 = 0 := by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have spNat : (stackPtr s).toNat = (stackPtr initial).toNat - (form.frameBytes + 8) := by
    rw [rsp]
    exact Dispatch.stack_sub_toNat512 ctx (by cases v <;> cases form <;> dsimp only [Form.frameBytes, Form.stackBytes, Variant.routine] <;> decide)
  have outNat : (s.regValue .rdi).toNat = (stackPtr initial).toNat - outputOffset := by
    rw [rdi]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  refine {
    stride := ctx.stride
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := inputBounded
    inputAllocated := inputAllocated
    outputBounded := ?_
    outputAllocated := allocated_of_grow ctx.stack.2.1 outputWithin state.allocated
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  }
  · change (s.regValue .rdi).toNat + outputBytes < 2^32
    rw [outNat]
    omega
  · refine ⟨?_, allocated_of_grow ctx.stack.2.1 stackWithin state.allocated, ?_, ?_⟩
    · change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32
      rw [stack_region_end, spNat]
      omega
    · change reserve ≤ (stackPtr s).toNat
      rw [spNat]
      omega
    · change (stackPtr s).toNat % 16 = 8
      rw [spNat]
      have align : (stackPtr initial).toNat % 16 = 8 := ctx.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨
        (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · change (registerRegion s .rsi inputBytes).Disjoint (registerRegion s .rdi outputBytes)
      exact fun a ha hb => inputApart a ha (outputWithin a hb)
    · change (registerRegion s .rsi inputBytes).Disjoint (Stack.region s reserve)
      exact fun a ha hb => inputApart a ha (stackWithin a hb)
    · change (registerRegion s .rdi outputBytes).Disjoint (Stack.region s reserve)
      intro a ha hb
      have low : (s.regValue .rdi).toNat ≤ a := ha.1
      have high : a < (stackPtr s).toNat + 8 := by
        simpa only [stack_region_end] using hb.2
      rw [outNat] at low
      rw [spNat] at high
      omega
  · intro region hr address ha
    apply (ctx.separation.2 (Stack.region initial form.stackBytes) (by cases form <;> first | exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩ | simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 address
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outputWithin address.toNat ha
    · exact stackWithin address.toNat ha


theorem callee_pre_of_stack [Bindings] {v : Variant} {form : Form} {initial t : RamState}
    {inputs : Array Input} {entry : BitVec 64} {inputBytes outputBytes reserve : Nat}
    (ctx : Context v initial inputs form) (state : ReturnState v initial t form)
    (layout : Wrapper.StackCallLayout form.stackBytes inputBytes outputBytes reserve)
    (rip : t.RIP = entry)
    (rsp : stackPtr t = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (input : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 layout.inputOffset)
    (output : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (_ret : InProgram (returnBoundary t).rip) :
    CalleePre t (returnBoundary initial) entry inputBytes outputBytes reserve := by
  rcases layout with ⟨so, io, oo, align, capacity, inputAbove, outputAbove, inputEnd, outputEnd, apart⟩
  dsimp only at rsp input output
  have bounds := Dispatch.stack_bounds512 ctx
  change form.stackBytes ≤ (stackPtr initial).toNat ∧ _ at bounds
  have hsp : (stackPtr t).toNat = (stackPtr initial).toNat - so := by
    rw [rsp]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  have hin : (t.regValue .rsi).toNat = (stackPtr initial).toNat - io := by
    rw [input]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  have hout : (t.regValue .rdi).toNat = (stackPtr initial).toNat - oo := by
    rw [output]
    exact Dispatch.stack_sub_toNat512 ctx (by change _ ≤ form.stackBytes; omega)
  have hsstart : (Stack.region t reserve).start = (stackPtr initial).toNat - (so + reserve) := by
    change (stackPtr t).toNat - reserve = _
    rw [hsp]
    omega
  have hsend : (Stack.region t reserve).start + (Stack.region t reserve).size =
      (stackPtr initial).toNat - so + 8 := by
    rw [stack_region_end, hsp]
  have sub (region : MemoryRegion)
      (hstart : (stackPtr initial).toNat - form.stackBytes ≤ region.start)
      (hend : region.start + region.size ≤ (stackPtr initial).toNat + 8) :
      ∀ a, region.Contains a → (Stack.region initial form.stackBytes).Contains a := by
    intro a ha
    change region.start ≤ a ∧ a < region.start + region.size at ha
    change (Stack.region initial form.stackBytes).start ≤ a ∧
      a < (Stack.region initial form.stackBytes).start + (Stack.region initial form.stackBytes).size
    rw [stack_region_end]
    change (stackPtr initial).toNat - form.stackBytes ≤ a ∧ a < (stackPtr initial).toNat + 8
    constructor <;> omega
  have stackSub := sub (Stack.region t reserve) (by rw [hsstart]; omega) (by rw [hsend]; omega)
  have inputSub := sub (registerRegion t .rsi inputBytes)
    (by change _ ≤ (t.regValue .rsi).toNat; rw [hin]; omega)
    (by change (t.regValue .rsi).toNat + inputBytes ≤ _; rw [hin]; omega)
  have outputSub := sub (registerRegion t .rdi outputBytes)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [hout]; omega)
    (by change (t.regValue .rdi).toNat + outputBytes ≤ _; rw [hout]; omega)
  have allocated (region : MemoryRegion)
      (hsub : ∀ a, region.Contains a → (Stack.region initial form.stackBytes).Contains a) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (ctx.stack.2.1 a (hsub a.toNat ha))))
  refine {
    stride := ctx.stride
    machine := state.machine
    directionFlag := state.directionFlag
    loaded := state.loaded
    rip := rip
    inputBounded := ?_
    inputAllocated := allocated _ inputSub
    outputBounded := ?_
    outputAllocated := allocated _ outputSub
    stack := ?_
    separation := ?_
    avoids := ?_
    outerBoundary := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  }
  · change (t.regValue .rsi).toNat + inputBytes < 2^32
    rw [hin]
    omega
  · change (t.regValue .rdi).toNat + outputBytes < 2^32
    rw [hout]
    omega
  · refine ⟨?_, allocated _ stackSub, ?_, ?_⟩
    · change (Stack.region t reserve).start + (Stack.region t reserve).size < 2^32
      rw [hsend]
      omega
    · change reserve ≤ (stackPtr t).toNat
      rw [hsp]
      omega
    · change (stackPtr t).toNat % 16 = 8
      rw [hsp]
      have hm : (stackPtr initial).toNat % 16 = 8 := ctx.stack.2.2.2
      omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have pairs : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 0 ∧ j.val = 2) ∨ (i.val = 1 ∧ j.val = 2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
    all_goals have ei : i = ⟨_, hi ▸ i.isLt⟩ := Fin.ext hi
    all_goals have ej : j = ⟨_, hj ▸ j.isLt⟩ := Fin.ext hj
    all_goals rw [ei, ej]
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + inputBytes at ha
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at hb
      rw [hin] at ha
      rw [hout] at hb
      omega
    · intro a ha hb
      change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat + inputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hin] at ha
      rw [hsend] at hb
      omega
    · intro a ha hb
      change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat + outputBytes at ha
      change (Stack.region t reserve).start ≤ a ∧
        a < (Stack.region t reserve).start + (Stack.region t reserve).size at hb
      rw [hout] at ha
      rw [hsend] at hb
      omega
  · intro region hr a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (ctx.separation.2 _ (by cases form <;> first | exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩ | simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 a (outputSub a.toNat ha)
    · exact (ctx.separation.2 _ (by cases form <;> first | exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩ | simp [Variant.writeRegions, Variant.routine, Vector.toList, Form.writeRegionCount])).2 a (stackSub a.toNat ha)

theorem compress512_thunk [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (state : ReturnState v initial s form)
    (rip : s.RIP = 0x10dd00) :
    ∃ t, ReturnState v initial t form ∧ t.RIP = 0x10dd90 ∧
      Advances (returnBoundary initial) 1 s t ∧ AgreesExcept [.rip] s t := by
  obtain ⟨t, run, ready, effect⟩ :=
    (jmp_rel32_effect_step 0x10dd00 0x8b (by decide +kernel)).advances
      (supportedMachine_readyToStep state.machine)
      (programText_slice (programLoaded_codeIn state.loaded) 0xdd00
        (0xe9 :: immBytes 32 0x8b) (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
        (inProgram_of_textOffset 0xdd90 (by decide)))
  have frame : AgreesExcept [.rip] s t := effect.agrees
  obtain ⟨offset, rsp⟩ := state.rsp
  have stateT := state.of_agrees ctx run ready frame
    (by simp [WritesWithin, Component.Covers]) offset
    ((frame.read (n := 64) (r := 4) (by simp)).trans rsp)
    (by simp [Component.Covers])
  exact ⟨t, stateT, effect.rip, run, frame⟩

end Sha2.Proofs.Wrapper512
