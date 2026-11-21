import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.LoadSetup
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Wrapper512.Absorb.State
import Sha2.Proofs.Common.Memory.LoadBytes
import Sha2.Proofs.Wrapper512.Dispatch.Store
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack
import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Wrapper512.Finish.Copy
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Machine.Initialize

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512

structure Loaded [Bindings] (v : Variant) (initial s : RamState) (message : ByteArray) (form : Form := .slices)
    : Prop
    extends Working v initial s message (compressBlocks v.initialHash message) form where
  rip : s.RIP = v.pc (setupOffset v form) form
  tailBytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, message.size % 128⟩ : MemoryRegion).HasBytes
    s.external (remainderBytes message)
  paddingLength : s.regValue (paddingRegister v form) = BitVec.ofNat 64 (127 - message.size % 128)

theorem prepare_clone [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Buffered v initial s message form)
    (rip : s.RIP = v.pc (v.dispatchOffset form) form)
    (eligible : form = .slices ∨ form = .digest ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true) :
    ∃ u, (∃ fuel, Advances (returnBoundary initial) fuel s u) ∧
      MemoryWriteFrame s u #v[Stack.region initial form.stackBytes] ∧
      MemoryWriteFrame s u #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 208⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] ∧
      Buffered v initial u message form form.finalMemory ∧
      u.RIP = v.pc (v.dispatchOffset form + if form = .digest then 22 else 24) form := by
  have casesForm : (form = .slices ∨ form = .digest) ∨
      (form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true) := by
    rcases eligible with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases casesForm with eligible | eligible
  · have rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form := by
      rcases eligible with rfl | rfl <;> exact rip
    obtain ⟨u, result⟩ := Finish.Copy.initial_result ctx input.toPreserved rip eligible
    have converted : Finish.Copy.StackResult v initial s u 208 392 600
        (v.pc (Finish.Copy.Site.initial.relativeOffset form + 6) form) form := by
      refine ⟨result.execution, result.stackFrame, result.preserved.toState, result.rip,
        result.abi, ?_, result.frame, result.bytes⟩
      exact result.abi.1 .rbx (by decide)
    have buffered := converted.buffered
      (sourceMemory := form.bufferedMemory) (destinationMemory := form.finalMemory)
      (by rcases eligible with rfl | rfl <;> rfl)
      (by rcases eligible with rfl | rfl <;> rfl)
      (by decide) (by decide) input result.preserved
    refine ⟨u, result.execution, result.stackFrame, ?_, buffered, ?_⟩
    · rcases eligible with rfl | rfl <;> exact result.frame
    · rcases eligible with rfl | rfl <;> exact result.rip
  · obtain ⟨u, result, buffered⟩ := Finish.Copy.second_clone ctx input eligible rip
    refine ⟨u, result.execution, result.stackFrame, result.frame, buffered, ?_⟩
    rcases eligible with rfl | rfl <;> exact result.rip

theorem load_cloned_local [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context v initial inputs form)
    (input : Buffered v initial s message form) (rip : s.RIP = v.pc (v.dispatchOffset form) form)
    (eligible : form = .slices ∨ form = .digest ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true := by first | assumption | simp) :
    ∃ t, Loaded v initial t message form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 208⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] := by
  obtain ⟨u, executionU, stackFrameU, frameU, bufferedU, ripU⟩ := prepare_clone ctx input rip eligible
  have preservedU := bufferedU.toPreserved
  have stateU := preservedU.toState
  have rspU := preservedU.rsp
  have hashAddr : rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form) = hashPointer initial form form.finalMemory := by
    rw [Machine.Initialize.stack_address rspU]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have tailAddr : rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form - 1) = tailLengthPointer initial form form.finalMemory := by
    rw [Machine.Initialize.stack_address rspU]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have lowAddr : rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form + 64) = blockCountPointer initial form form.finalMemory := by
    rw [Machine.Initialize.stack_address rspU]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have highAddr : rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form + 72) = blockCountHighPointer initial form form.finalMemory := by
    rw [Machine.Initialize.stack_address rspU]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have ripU : u.RIP = v.pc (LoadSetup.startOffset v form) form := by
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact ripU
  have pre : LoadSetup.Pre v u form := by
    refine ⟨ripU, ?_, ?_, ?_⟩
    all_goals rw [Machine.Initialize.stack_address rspU]
    all_goals rcases eligible with rfl | rfl | rfl | rfl <;> simp only [Form.frameBytes, LoadSetup.hashOffset, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub]
    all_goals exact Machine.Initialize.stack_readable ctx stateU (by cases v <;> decide) (by decide)
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨_, t, run, ready, _, effect⟩ := LoadSetup.run (returnBoundary initial)
    outside eligible u (supportedMachine_readyToStep stateU.machine) (LoadSetup.code stateU.loaded) pre
  have noMem : ∀ c ∈ (LoadSetup.effect v u form).components, ∀ a, ¬ c.Covers a := by
    simp [LoadSetup.effect, Effect.components, Component.Covers]
  have frame := effect.agrees
  have preservedT := Absorb.preserved_of_agrees (keptFrameOutput := by rcases eligible with rfl | rfl | rfl | rfl <;> simp) ctx preservedU run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by rcases eligible with rfl | rfl | rfl | rfl <;> simp [LoadSetup.effect, Effect.components, LoadSetup.hashReg, LoadSetup.tailReg, LoadSetup.lowReg, LoadSetup.highReg, LoadSetup.padReg] <;> decide)
    (by rcases eligible with rfl | rfl | rfl | rfl <;> simp [LoadSetup.effect, Effect.components, LoadSetup.hashReg, LoadSetup.tailReg, LoadSetup.lowReg, LoadSetup.highReg, LoadSetup.padReg] <;> decide)
    (by intro hd; subst form; simp [LoadSetup.effect, Effect.components, LoadSetup.hashReg, LoadSetup.tailReg, LoadSetup.lowReg, LoadSetup.highReg, LoadSetup.padReg] <;> decide)
  have memory := frame.external noMem
  have lengthRead : (memLoad u.external (rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form - 1)) 8).setWidth 64 = BitVec.ofNat 64 (message.size % 128) := by
    rw [tailAddr, memLoad_8]
    change ((u.external[tailLengthPointer initial form form.finalMemory]?).getD 0).toBitVec.setWidth 64 = _
    rw [bufferedU.tailLength]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec, UInt8.toNat_ofNat']
    have := Nat.mod_lt message.size (by decide : 0 < 128)
    omega
  have lowRead : memLoad u.external (rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form + 64)) 64 = BitVec.ofNat 64 (message.size / 128) := by
    rw [lowAddr]; exact bufferedU.blockCount
  have highRead : memLoad u.external (rspOf u + BitVec.ofNat 64 (LoadSetup.hashOffset form + 72)) 64 = BitVec.ofNat 64 ((message.size / 128) / 2^64) := by
    rw [highAddr]; exact bufferedU.blockCountHigh
  have wHash := effect.writes.1
  have wTail := effect.writes.2.1
  have wLow := effect.writes.2.2.1
  have wHigh := effect.writes.2.2.2.1
  have wPad := effect.writes.2.2.2.2
  rw [hashAddr] at wHash
  rw [lengthRead] at wTail wPad
  rw [lowRead] at wLow
  rw [highRead] at wHigh
  have loaded : Loaded v initial t message form := by
    refine ⟨⟨⟨preservedT, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [HashStateAt, hashPointer, memory] using bufferedU.hashWords
    · rcases eligible with rfl | rfl | rfl | rfl <;> exact wHash
    · rcases eligible with rfl | rfl | rfl | rfl <;> exact wLow
    · rcases eligible with rfl | rfl | rfl | rfl <;> exact wHigh
    · rcases eligible with rfl | rfl | rfl | rfl <;> exact wTail
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact effect.rip
    · simpa only [memory, tailRegion, bufferPointer, tailData, remainderBytes] using bufferedU.tailBytes
    · have computed : ∀ tail : Fin 128, BitVec.ofNat 64 tail.val ^^^ 127 = BitVec.ofNat 64 (127 - tail.val) := by decide +kernel
      have result := wPad.trans (computed ⟨_, Nat.mod_lt _ (by decide)⟩)
      rcases eligible with rfl | rfl | rfl | rfl <;> exact result
  refine ⟨t, loaded, ?_, ?_, ?_⟩
  · obtain ⟨fuel, before⟩ := executionU
    exact ⟨_, before.trans run⟩
  · intro a ha
    rw [memory]
    exact stackFrameU a ha
  · intro a ha
    rw [memory]
    exact frameU a ha

theorem load [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Buffered v initial s message form)
    (rip : s.RIP = v.pc (if form = .slices then 0x218 else 0x143) form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, Loaded v initial t message form := by
  obtain ⟨t, loaded, _⟩ := load_cloned_local ctx input (by rcases eligible with rfl | rfl <;> exact rip)
    (by rcases eligible with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
  exact ⟨t, loaded⟩

theorem loaded_of_count_effect [Bindings] {v : Variant} {form : Form}
    {initial s t : RamState} {inputs : Array Input} {message : ByteArray} {fuel : Nat}
    (ctx : Context v initial inputs form) (input : Buffered v initial s message form)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : Effect.post (fun s => LoadSetup.countEffect v (v.pc (LoadSetup.countStartOffset v form) form) s form) s t) :
    Loaded v initial t message form ∧ t.external = s.external ∧
      (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
      (form = .finalizeIntoReset false →
        t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
          s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) := by
  have tailAddr : rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form) = tailLengthPointer initial form := by
    rw [Machine.Initialize.stack_address input.rsp]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have lowAddr : rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 65) = blockCountPointer initial form := by
    rw [Machine.Initialize.stack_address input.rsp]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have highAddr : rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 73) = blockCountHighPointer initial form := by
    rw [Machine.Initialize.stack_address input.rsp]
    rcases eligible with rfl | rfl | rfl | rfl <;> rfl
  have noMem : ∀ c ∈ (LoadSetup.countEffect v (v.pc (LoadSetup.countStartOffset v form) form) s form).components,
      ∀ a, ¬ c.Covers a := by
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
      simp [LoadSetup.countEffect, Effect.components, Component.Covers]
  have frame := effect.agrees
  have memory := frame.external noMem
  have preserved := Absorb.preserved_of_agrees
    (keptFrameOutput := fun hf => Or.inr (outputSaved hf)) ctx input.toPreserved run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
        simp [LoadSetup.countEffect, Effect.components, LoadSetup.countLowReg,
          LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])
    (by rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
        simp [LoadSetup.countEffect, Effect.components])
    (by rcases eligible with rfl | rfl | rfl | rfl <;> simp)
  have tailRead : (memLoad s.external (rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form)) 8).setWidth 64 = BitVec.ofNat 64 (message.size % 128) := by
    rw [tailAddr, memLoad_8]
    change ((s.external[tailLengthPointer initial form]?).getD 0).toBitVec.setWidth 64 = _
    rw [input.tailLength]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec, UInt8.toNat_ofNat']
    have := Nat.mod_lt message.size (by decide : 0 < 128)
    omega
  have lowRead : memLoad s.external (rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 65)) 64 = BitVec.ofNat 64 (message.size / 128) := by rw [lowAddr]; exact input.blockCount
  have highRead : memLoad s.external (rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 73)) 64 = BitVec.ofNat 64 ((message.size / 128) / 2^64) := by rw [highAddr]; exact input.blockCountHigh
  have wLow := effect.writes.2.1
  have wHigh : (.reg (LoadSetup.countHighReg v form) : Operand 64).read t =
      Length.Shld.result
        (memLoad s.external (rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 73)) 64)
        (memLoad s.external (rspOf s + BitVec.ofNat 64 (LoadSetup.countTailOffset form + 65)) 64) := by
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact effect.writes.2.2.1
  rw [lowRead] at wLow
  rw [lowRead, highRead] at wHigh
  have wTail : t.regValue (tailRegister v form) = BitVec.ofNat 64 (message.size % 128) := by
    rw [← tailRead]
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v
    all_goals first | exact effect.writes.2.2.2.1 | exact effect.writes.2.2.2.2.2.1
  have wPad : t.regValue (paddingRegister v form) = BitVec.ofNat 64 (message.size % 128) ^^^ 127 := by
    rw [← tailRead]
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v
    all_goals first | exact effect.writes.2.2.2.2 | exact effect.writes.2.2.2.2.2.2
  refine ⟨?_, memory, ?_, ?_⟩
  · refine ⟨⟨⟨preserved, ?_, ?_⟩, ?_, ?_, wTail⟩, ?_, ?_, ?_⟩
    · rcases eligible with rfl | rfl | rfl | rfl <;>
        simpa only [HashStateAt, hashPointer, memory] using input.hashWords
    · rcases eligible with rfl | rfl | rfl | rfl
      · trivial
      · trivial
      · trivial
      · have addr : rspOf s + 384 = hashPointer initial (.traitFinalizeIntoReset false) (Form.traitFinalizeIntoReset false).finalMemory := by
          rw [Machine.Initialize.stack_address input.rsp]; rfl
        have outAddr : rspOf s + 240 = outputSavePointer initial (.traitFinalizeIntoReset false) := by
          rw [Machine.Initialize.stack_address input.rsp]; rfl
        have out := outputSaved rfl
        cases v <;> constructor
        all_goals first
          | (have h := effect.writes.2.2.2.2.1; rw [addr] at h; exact h)
          | (have h := effect.writes.2.2.2.1; rw [outAddr, out] at h; exact h)
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact wLow
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact wHigh
    · have h : t.RIP = v.pc (LoadSetup.countStartOffset v form) form + BitVec.ofNat 64 (LoadSetup.countLength form) := effect.rip
      rw [Variant.pc_add (form := form)] at h
      rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact h
    · rcases eligible with rfl | rfl | rfl | rfl <;>
        simpa only [memory, tailRegion, bufferPointer, tailData, remainderBytes] using input.tailBytes
    · rw [wPad]
      have computed : ∀ tail : Fin 128, BitVec.ofNat 64 tail.val ^^^ 127 = BitVec.ofNat 64 (127 - tail.val) := by decide +kernel
      exact computed ⟨_, Nat.mod_lt _ (by decide)⟩
  · intro hf; subst form
    have h := frame.read (n := 64) (r := 12) (by
      cases v <;> simp [LoadSetup.countEffect, Effect.components, LoadSetup.countLowReg,
        LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])
    exact h
  · intro hf; subst form
    cases v
    all_goals first
      | exact frame.read (n := 64) (r := 12) (by simp [LoadSetup.countEffect, Effect.components, LoadSetup.countLowReg, LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])
      | exact frame.read (n := 64) (r := 15) (by simp [LoadSetup.countEffect, Effect.components, LoadSetup.countLowReg, LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])


theorem loaded_of_empty_tail_effect [Bindings] {v : Variant} {form : Form}
    {initial s t : RamState} {inputs : Array Input} {fuel : Nat}
    (ctx : Context v initial inputs form) (input : Buffered v initial s ByteArray.empty form)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false)
    (finalizeEmpty : form = .finalizeIntoReset false →
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧
        s.regValue (highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : Effect.post (fun s => LoadSetup.emptyTailEffect v (v.pc (LoadSetup.emptyTailStart v form) form) s form) s t) :
    Loaded v initial t ByteArray.empty form ∧ t.external = s.external ∧
      (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
      (form = .finalizeIntoReset false →
        t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
          s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) := by
  have noMem : ∀ c ∈ (LoadSetup.emptyTailEffect v (v.pc (LoadSetup.emptyTailStart v form) form) s form).components,
      ∀ a, ¬ c.Covers a := by
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
      simp [LoadSetup.emptyTailEffect, Effect.components, Component.Covers]
  have frame := effect.agrees
  have memory := frame.external noMem
  have preserved := Absorb.preserved_of_agrees
    (keptFrameOutput := by
      intro hf; subst form; left
      cases v <;> simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countLowReg,
        LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg]) ctx input.toPreserved run ready frame
    (fun c hc a ha => (noMem c hc a ha).elim)
    (by rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
        simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countLowReg,
          LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])
    (by rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;>
        simp [LoadSetup.emptyTailEffect, Effect.components])
    (by rcases eligible with rfl | rfl | rfl | rfl <;> simp)
  have wLow : t.regValue (lowCountRegister v form) = 0 := by
    rcases eligible with rfl | rfl | rfl | rfl
    · cases v <;> exact effect.writes.1
    · cases v <;> exact effect.writes.1
    · have h := frame.read (n := 64) (r := 14) (by
        cases v <;> simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countTailReg, LoadSetup.countPadReg])
      exact h.trans (finalizeEmpty rfl).2.1
    · cases v <;> exact effect.writes.1
  have wHigh : t.regValue (highCountRegister v form) = 0 := by
    rcases eligible with rfl | rfl | rfl | rfl
    · cases v <;> exact effect.writes.2.1
    · cases v <;> exact effect.writes.2.1
    · have zero := (finalizeEmpty rfl).2.2
      cases v
      all_goals first
        | exact (frame.read (n := 64) (r := 15) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countTailReg, LoadSetup.countPadReg])).trans zero
        | exact (frame.read (n := 64) (r := 12) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countTailReg, LoadSetup.countPadReg])).trans zero
    · cases v <;> exact effect.writes.2.1
  have wTail : t.regValue (tailRegister v form) = 0 := by
    rcases eligible with rfl | rfl | rfl | rfl
    · cases v <;> exact effect.writes.2.2.2.1
    · cases v <;> exact effect.writes.2.2.2.1
    · have h := effect.writes.1
      have zero := (finalizeEmpty rfl).1
      change t.regValue .r13 = ((s.regValue .rax).setWidth 8).setWidth 64 at h
      rw [zero] at h
      exact h
    · cases v <;> exact effect.writes.2.2.2.2.1
  have wPadRaw : t.regValue (paddingRegister v form) =
      (if form = .finalizeIntoReset false then (s.regValue .rax).setWidth 8 |>.setWidth 64 else 0) ^^^ (127 : BitVec 64) := by
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v
    all_goals first
      | exact effect.writes.2
      | exact effect.writes.2.2.2.2
      | exact effect.writes.2.2.2.2.2
  have wPad : t.regValue (paddingRegister v form) = 127 := by
    rw [wPadRaw]
    by_cases hf : form = .finalizeIntoReset false
    · simp only [hf, ite_true, (finalizeEmpty hf).1]
      decide
    · simp only [hf, ite_false]
      decide
  refine ⟨?_, memory, ?_, ?_⟩
  · refine ⟨⟨⟨preserved, ?_, ?_⟩, ?_, ?_, wTail⟩, ?_, ?_, ?_⟩
    · rcases eligible with rfl | rfl | rfl | rfl <;>
        simpa only [HashStateAt, hashPointer, memory] using input.hashWords
    · rcases eligible with rfl | rfl | rfl | rfl
      · trivial
      · trivial
      · trivial
      · have addr : rspOf s + 384 = hashPointer initial (.traitFinalizeIntoReset false) (Form.traitFinalizeIntoReset false).finalMemory := by
          rw [Machine.Initialize.stack_address input.rsp]; rfl
        have out := traitOutput rfl
        cases v <;> constructor
        all_goals first
          | (have h := effect.writes.2.2.2.1; rw [addr] at h; exact h)
          | exact (frame.read (n := 64) (r := 5) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countLowReg, LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])).trans out
          | exact (frame.read (n := 64) (r := 13) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countLowReg, LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])).trans out
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact wLow
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact wHigh
    · have h : t.RIP = v.pc (LoadSetup.emptyTailStart v form) form + BitVec.ofNat 64 (LoadSetup.emptyTailLength form) := effect.rip
      rw [Variant.pc_add (form := form)] at h
      rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact h
    · rcases eligible with rfl | rfl | rfl | rfl <;>
        simpa only [memory, tailRegion, bufferPointer, tailData, remainderBytes] using input.tailBytes
    · exact wPad
  · intro hf; subst form
    have h := frame.read (n := 64) (r := 12) (by
      cases v <;> simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countLowReg,
        LoadSetup.countHighReg, LoadSetup.countTailReg, LoadSetup.countPadReg])
    exact h
  · intro hf; subst form
    cases v
    all_goals first
      | exact frame.read (n := 64) (r := 12) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countTailReg, LoadSetup.countPadReg])
      | exact frame.read (n := 64) (r := 15) (by simp [LoadSetup.emptyTailEffect, Effect.components, LoadSetup.countTailReg, LoadSetup.countPadReg])



theorem load_count_local [Bindings] {v : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context v initial inputs form) (input : Buffered v initial s message form)
    (rip : s.RIP = v.pc (v.dispatchOffset form) form)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false)
    (outputSaved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) :
    ∃ t, Loaded v initial t message form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external ∧
      (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
      (form = .finalizeIntoReset false →
        t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
          s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) := by
  have pre : LoadSetup.CountPre (v.pc (LoadSetup.countStartOffset v form) form) s form := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> exact rip
    · rw [Machine.Initialize.stack_address input.rsp]
      rcases eligible with rfl | rfl | rfl | rfl <;>
        simp only [Form.frameBytes, LoadSetup.countTailOffset, BitVec.reduceSub]
      all_goals exact Machine.Initialize.stack_readable ctx input.toState (by cases v <;> decide) (by decide)
    · rw [Machine.Initialize.stack_address input.rsp]
      rcases eligible with rfl | rfl | rfl | rfl <;>
        simp only [Form.frameBytes, LoadSetup.countTailOffset, Nat.reduceAdd, BitVec.reduceSub]
      all_goals exact Machine.Initialize.stack_readable ctx input.toState (by cases v <;> decide) (by decide)
    · rw [Machine.Initialize.stack_address input.rsp]
      rcases eligible with rfl | rfl | rfl | rfl <;>
        simp only [Form.frameBytes, LoadSetup.countTailOffset, Nat.reduceAdd, BitVec.reduceSub]
      all_goals exact Machine.Initialize.stack_readable ctx input.toState (by cases v <;> decide) (by decide)
    · by_cases hf : form = .traitFinalizeIntoReset false
      · subst form
        change MemReadable s (rspOf s + 240) 8
        rw [Machine.Initialize.stack_address input.rsp]
        change MemReadable s (stackPtr initial - 408) 8
        exact Machine.Initialize.stack_readable ctx input.toState (by cases v <;> decide) (by decide)
      · simp only [hf, ite_false]
  have inside : BlockInProgram (v.pc (LoadSetup.countStartOffset v form) form) (LoadSetup.countLength form) := by
    apply blockInProgram_of_textOffset
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide
  obtain ⟨fuel, t, run, ready, _, effect⟩ := LoadSetup.run_count v _ form (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside eligible s
    (supportedMachine_readyToStep input.machine) (LoadSetup.countCode input.loaded eligible) pre
  obtain ⟨loaded, memory, resetCount, finalCount⟩ := loaded_of_count_effect ctx input eligible outputSaved run ready effect
  exact ⟨t, loaded, ⟨fuel, run⟩, memory, resetCount, finalCount⟩
theorem load_empty_tail_local [Bindings] {v : Variant} {form : Form}
    {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs form) (input : Buffered v initial s ByteArray.empty form)
    (rip : s.RIP = v.pc (LoadSetup.emptyTailStart v form) form)
    (eligible : form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false)
    (finalizeEmpty : form = .finalizeIntoReset false →
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧ s.regValue (highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx) :
    ∃ t, Loaded v initial t ByteArray.empty form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external ∧
      (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
      (form = .finalizeIntoReset false →
        t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
          s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) := by
  have inside : BlockInProgram (v.pc (LoadSetup.emptyTailStart v form) form) (LoadSetup.emptyTailLength form) := by
    apply blockInProgram_of_textOffset
    rcases eligible with rfl | rfl | rfl | rfl <;> cases v <;> decide
  obtain ⟨fuel, t, run, ready, _, effect⟩ := LoadSetup.run_empty_tail v _ form (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside eligible s
    (supportedMachine_readyToStep input.machine) (LoadSetup.emptyTailCode input.loaded eligible) rip
  obtain ⟨loaded, memory, resetCount, finalCount⟩ := loaded_of_empty_tail_effect ctx input eligible finalizeEmpty traitOutput run ready effect
  exact ⟨t, loaded, ⟨fuel, run⟩, memory, resetCount, finalCount⟩

theorem buffered_of_empty_store_effect [Bindings] {v : Variant}
    {initial s t : RamState} {inputs : Array Input} {fuel : Nat}
    (ctx : Context v initial inputs (.reset 1))
    (input : Buffered v initial s ByteArray.empty (.reset 1))
    (rax : s.regValue .rax = hashPointer initial (.reset 1))
    (words : ∀ i < 8,
      (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s =
        v.initialHash[i]!.toBitVec)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : Effect.post (LoadSetup.emptyStoreEffect v (v.pc 0x3d5 (.reset 1))) s t) :
    Buffered v initial t ByteArray.empty (.reset 1) ∧ t.external = s.external ∧
      (∀ r : BitVec 5, (.reg r : Operand 64).read t = (.reg r : Operand 64).read s) ∧
      t.RIP = v.pc 0x3f4 (.reset 1) := by
  have stored (i : Nat) (hi : i < 8) :
      memLoad t.external (s.regValue .rax + BitVec.ofNat 64 (8*i)) 64 =
        v.initialHash[i]!.toBitVec := by
    have writes := effect.writes
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [LoadSetup.emptyStoreEffect, List.map, Write.AllHold] at writes
    · exact writes.2.2.2.2.2.2.2.trans (words 0 (by decide))
    · exact writes.2.2.2.2.2.2.1.trans (words 1 (by decide))
    · exact writes.2.2.2.2.2.1.trans (words 2 (by decide))
    · exact writes.2.2.2.2.1.trans (words 3 (by decide))
    · exact writes.2.2.2.1.trans (words 4 (by decide))
    · exact writes.2.2.1.trans (words 5 (by decide))
    · exact writes.2.1.trans (words 6 (by decide))
    · exact writes.1.trans (words 7 (by decide))
  have agreesWord (i : Nat) (hi : i < 8) :
      (Component.mem (s.regValue .rax + BitVec.ofNat 64 (8*i)) 8).Agrees s t := by
    have old := Common.Memory.bytes_of_loadBytes64 (input.hashWords.2 i hi)
    change Bytes s.external (hashPointer initial (.reset 1) + BitVec.ofNat 64 (8*i)) 8
      (storedByte (v.initialHash[i]!.toBitVec)) at old
    rw [← rax] at old
    have new := Bytes.of_memLoad (n := 64) (m := t.external)
      (a := s.regValue .rax + BitVec.ofNat 64 (8*i)) (by
        intro j hj
        apply effect.agrees.grow
        rw [old j hj]
        rfl)
    rw [stored i hi] at new
    exact fun j hj => (new j hj).trans (old j hj).symm
  have frame : AgreesExcept [.rip] s t := by
    apply effect.agrees.narrow
    intro c hc hn
    simp only [LoadSetup.emptyStoreEffect, Effect.components, List.map, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false, Write.component_mem] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact agreesWord _ (by decide) | exact (hn (by simp)).elim
  refine ⟨Absorb.buffered_of_agrees ctx input run ready frame (by simp [Component.Covers])
    (by simp), frame.external (by simp [Component.Covers]), ?_, ?_⟩
  · intro r
    exact frame.read (by simp)
  · exact effect.rip.trans (Variant.pc_add v 0x3d5 31 (.reset 1))

set_option maxRecDepth 1024 in
theorem empty_store_pre [Bindings] {v : Variant} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs (.reset 1))
    (input : Buffered v initial s ByteArray.empty (.reset 1))
    (rip : s.RIP = v.pc 0x3d5 (.reset 1))
    (rax : s.regValue .rax = hashPointer initial (.reset 1)) :
    LoadSetup.EmptyStorePre (v.pc 0x3d5 (.reset 1)) s := by
  have address (i : Nat) (hi : i < 8) :
      s.regValue .rax + BitVec.ofNat 64 (8*i) =
        stackPtr initial - BitVec.ofNat 64 (296 - 8*i) := by
    rw [rax]
    change stackPtr initial - 296 + BitVec.ofNat 64 (8*i) = _
    have h : (296 : BitVec 64) = BitVec.ofNat 64 (296 - 8*i) + BitVec.ofNat 64 (8*i) := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel (by omega)]
      rfl
    rw [h, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  refine ⟨rip, ?_, ?_⟩
  · intro i hi
    rw [address i hi]
    apply Machine.Stages.stack_slot_writable ctx input.toState
    · cases v <;> change 296 - 8*i ≤ 976 <;> omega
    · omega
  · intro i hi j n hn
    rw [address i hi]
    simp only [Variant.pc, BitVec.add_assoc, ← BitVec.ofNat_add]
    apply Machine.Stages.stack_slot_codeApart ctx
    · cases v <;> change 296 - 8*i ≤ 976 <;> omega
    · omega
    · cases v <;> simp only [Variant.textOffset] <;> omega


theorem load_empty_store_local [Bindings] {v : Variant}
    {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.reset 1))
    (input : Buffered v initial s ByteArray.empty (.reset 1))
    (rip : s.RIP = v.pc 0x3d5 (.reset 1))
    (rax : s.regValue .rax = hashPointer initial (.reset 1))
    (words : ∀ i < 8,
      (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s =
        v.initialHash[i]!.toBitVec)
 :
    ∃ t, Buffered v initial t ByteArray.empty (.reset 1) ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      t.external = s.external ∧ (∀ r, t.regValue r = s.regValue r) ∧
      t.RIP = v.pc 0x3f4 (.reset 1) := by
  have inside : BlockInProgram (v.pc 0x3d5 (.reset 1)) 31 := by
    apply blockInProgram_of_textOffset
    cases v <;> decide +kernel
  have runner := LoadSetup.run_empty_store v (v.pc 0x3d5 (.reset 1))
    (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside
  obtain ⟨fuel, t, run, ready, _, effect⟩ := runner s
    (supportedMachine_readyToStep input.machine) (LoadSetup.emptyStoreCode input.loaded)
    (empty_store_pre ctx input rip rax)
  obtain ⟨buffered, memory, regs, pc⟩ := buffered_of_empty_store_effect ctx input rax words run ready effect
  refine ⟨t, buffered, ⟨fuel, run⟩, memory, ?_, pc⟩
  intro r
  cases r
  · exact regs 0
  · exact regs 1
  · exact regs 2
  · exact regs 3
  · exact regs 4
  · exact regs 5
  · exact regs 6
  · exact regs 7
  · exact regs 8
  · exact regs 9
  · exact regs 10
  · exact regs 11
  · exact regs 12
  · exact regs 13
  · exact regs 14
  · exact regs 15


theorem load_local [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Buffered v initial s (message inputs) form)
    (rip : s.RIP = v.pc (v.dispatchOffset form inputs.isEmpty) form)
    (eligible : form.canFinalize)
    (resetEmptyPointer : form = .reset 1 → inputs.isEmpty = true →
      s.regValue .rax = hashPointer initial form form.finalMemory)
    (resetEmptyWords : form = .reset 1 → inputs.isEmpty = true → ∀ i < 8,
      (.reg (BitVec.ofNat 5 (Dispatch.Store.wordRegister v (.reset 1) i)) : Operand 64).read s = v.initialHash[i]!.toBitVec)
    (finalizeEmpty : form = .finalizeIntoReset false → inputs.isEmpty = true →
      (s.regValue .rax).setWidth 8 = 0 ∧ s.regValue .r14 = 0 ∧ s.regValue (highCountRegister v form) = 0)
    (traitOutput : form = .traitFinalizeIntoReset false →
      if inputs.isEmpty then s.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx
      else memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) :
    ∃ t, Loaded v initial t (message inputs) form ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      MemoryWriteFrame s t #v[
        (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 208⟩ : MemoryRegion),
        (⟨(stackPtr initial - BitVec.ofNat 64 (form.frameBytes + 8)).toNat, 8⟩ : MemoryRegion)] ∧
      (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
      (form = .finalizeIntoReset false →
        t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
          s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) ∧
      (form = .traitFinalizeIntoReset false →
        memLoad t.external (stackPtr initial - 640) 64 = memLoad s.external (stackPtr initial - 640) 64) ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  have forms : (form = .slices ∨ form = .digest ∨ form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true) ∨
      (form = .reset 1 ∨ form = .reset 2 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) := by
    cases form with
    | slices => exact Or.inl (Or.inl rfl)
    | digest => exact Or.inl (Or.inr (Or.inl rfl))
    | finalizeIntoReset b => cases b <;> simp
    | traitFinalizeIntoReset b => cases b <;> simp
    | reset stage =>
      have hn : stage.val ≠ 0 := eligible
      have casesStage : stage = 1 ∨ stage = 2 := by
        have hb := stage.isLt
        have hv : stage.val = 1 ∨ stage.val = 2 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases casesStage with rfl | rfl <;> simp
  rcases forms with clones | counts
  · obtain ⟨t, loaded, execution, stackFrame, frame⟩ := load_cloned_local ctx input
      (by rcases clones with rfl | rfl | rfl | rfl <;> cases h : inputs.isEmpty <;> simpa [h, Variant.dispatchOffset] using rip) clones
    refine ⟨t, loaded, execution, stackFrame, frame, ?_, ?_, ?_, ?_⟩
    all_goals rcases clones with rfl | rfl | rfl | rfl <;> simp [Form.isTerminal]
  · have result : ∃ t, Loaded v initial t (message inputs) form ∧
        (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧ t.external = s.external ∧
        (form = .reset 1 → t.regValue .r12 = s.regValue .r12) ∧
        (form = .finalizeIntoReset false →
          t.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15) =
            s.regValue (if v = .sha384 ∨ v = .sha512 then .r12 else .r15)) := by
      by_cases empty : inputs.isEmpty = true
      · have msg : message inputs = ByteArray.empty := by
          rw [Array.empty_of_isEmpty empty]
          rfl
        rw [msg] at input ⊢
        by_cases reset : form = .reset 1
        · subst form
          obtain ⟨u, buffered, before, memoryU, regs, ripU⟩ := load_empty_store_local ctx input
            (by simpa [empty, Variant.dispatchOffset, LoadSetup.emptyTailStart] using rip) (resetEmptyPointer rfl empty) (resetEmptyWords rfl empty)
          obtain ⟨t, loaded, after, memoryT, countT, _⟩ := load_empty_tail_local ctx buffered ripU
            (Or.inl rfl) (by simp) (by simp)
          refine ⟨t, loaded, ?_, memoryT.trans memoryU, fun _ => (countT rfl).trans (regs .r12), by simp⟩
          obtain ⟨a, ha⟩ := before
          obtain ⟨b, hb⟩ := after
          exact ⟨a+b, ha.trans hb⟩
        · exact load_empty_tail_local ctx input
            (by
              rcases counts with h | rfl | rfl | rfl
              · exact (reset h).elim
              all_goals cases v <;> simpa [empty, Variant.dispatchOffset, LoadSetup.emptyTailStart] using rip)
            counts (fun hf => finalizeEmpty hf empty)
            (by intro hf; simpa only [empty, ite_true] using traitOutput hf)
      · have nonempty : inputs.isEmpty = false := Bool.eq_false_iff.mpr empty
        exact load_count_local ctx input (by simpa only [nonempty] using rip) counts
          (by intro hf; simpa only [nonempty, Bool.false_eq_true, ite_false] using traitOutput hf)
    obtain ⟨t, loaded, execution, memory, resetCount, finalCount⟩ := result
    refine ⟨t, loaded, execution, ?_, ?_, resetCount, finalCount, ?_, ?_⟩
    · intro a ha
      rw [memory]
    · intro a ha
      rw [memory]
    · intro hf
      rw [memory]
    · intro nonterminal
      rcases counts with rfl | rfl | rfl | rfl
      · cases v <;> exact resetCount rfl
      · exact (nonterminal rfl).elim
      · cases v <;> exact finalCount rfl
      · cases v <;> change memLoad t.external (stackPtr initial - 640) 64 = memLoad s.external (stackPtr initial - 640) 64 <;> rw [memory]

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
