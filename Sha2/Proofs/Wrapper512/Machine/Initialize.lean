import Sha2.Proofs.Reset.Prologue
import Sha2.Proofs.Reset.Entry
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Machine.Chain.Subframe
import Sha2.Proofs.Wrapper512.Machine.Stages.Stack
import Sha2.Proofs.Wrapper512.Dispatch.StoreRun
import Sha2.Proofs.Common.Memory.LoadBytes
import Sha2.Proofs.Wrapper.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper512
open Sha2.Proofs.Wrapper512.Dispatch

namespace Initialize

theorem stack_address {initial s : RamState} {frame : BitVec 64}
    (rsp : stackPtr s = stackPtr initial - frame) (i : BitVec 64) :
    rspOf s + i = stackPtr initial - (frame - i) := by
  change stackPtr s + i = _
  rw [rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem stack_readable [Bindings] {v : Variant} {initial s : RamState} {form : Form}
    {inputs : Array Input} (ctx : Context v initial inputs form) (state : State v initial s form)
    {offset len : Nat} (low : offset ≤ (v.routine form).minStackBytes) (high : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  Common.Encoding.Serialize.readable_of_grow
    (Dispatch.stack_sub_readable512 ctx low high) state.allocated

theorem stack_writable1 [Bindings] {v : Variant} {initial s : RamState} {form : Form}
    {inputs : Array Input} (ctx : Context v initial inputs form) (state : State v initial s form)
    {offset : Nat} (low : offset ≤ (v.routine form).minStackBytes) (positive : 0 < offset) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 1 := by
  have read := stack_readable ctx state low (show 1 ≤ offset + 8 by omega)
  refine MemWritable.of_not_reserved (by decide) read.low read.mem ?_
  intro i hi reserved
  exact (ctx.separation.2 (Stack.region initial (v.routine form).minStackBytes) (by cases form <;> simp [Variant.writeRegions, Form.writeRegionCount, Form.twoOutputs, Vector.toList])).2 _
    (stackRegion_contains_sub ctx.stack.2.2.1 low (by omega) ⟨i, hi, rfl⟩)
    (.inr reserved)

theorem prefix_local_writes [Bindings] {v : Variant} {initial s : RamState} {form : Form}
    (state : State v initial s form) :
    Wrapper.LocalWrites initial (Store.prefixEffect v s form).components := by
  cases form <;> cases v <;> intro c hc a ha
  all_goals
    dsimp only [Store.prefixEffect, Store.suffixOffset] at hc
    simp only [Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hc
  all_goals first
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hc with rfl | rfl | rfl | rfl | rfl)
    | (rcases hc with rfl | rfl | rfl | rfl)
    | (rcases hc with rfl)
  all_goals try exact ha.elim
  all_goals first
    | rw [stack_address state.rsp] at ha
    | (change (Component.mem (stackPtr s) 8).Covers a at ha
       rw [state.rsp] at ha)
  all_goals simp only [Form.frameBytes, BitVec.ofNat_eq_ofNat, BitVec.reduceSub, Nat.reduceDiv] at ha
  all_goals exact Wrapper.local_memory (by decide) (by decide) (by decide) a ha

theorem pre [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {form : Form} {offset : Nat}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (rip : s.RIP = v.pc offset form) :
    Dispatch.Store.Pre v s form offset := by
  refine ⟨rip, ?_, ?_⟩
  · intro slot hs
    rw [stack_address state.rsp]
    cases form
    all_goals dsimp only [Dispatch.Store.slots, Dispatch.Store.slotOffset] at hs
    all_goals simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    all_goals first
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp only [Form.frameBytes, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub]
    all_goals first
      | exact Stages.stack_slot_writable ctx state (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
      | exact stack_writable1 ctx state (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
  · intro slot hs offset len bound
    rw [stack_address state.rsp]
    cases form
    all_goals dsimp only [Dispatch.Store.slots, Dispatch.Store.slotOffset] at hs
    all_goals simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    all_goals first
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      | (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp only [Form.frameBytes, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub]
    all_goals exact Stages.stack_slot_codeApart ctx (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide) bound

theorem local_writes [Bindings] {v : Variant} {initial s : RamState} {form : Form}
    (state : State v initial s form) :
    Wrapper.LocalWrites initial (Dispatch.Store.effectWithRegister v s form).components := by
  cases form <;> intro c hc a ha
  all_goals
    dsimp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset] at hc
    simp only [List.range_succ, List.range_zero, List.cons_append, List.nil_append, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_cons,
      List.not_mem_nil, or_false] at hc
  case slices =>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [stack_address state.rsp] at ha
    all_goals simp only [Form.frameBytes, BitVec.ofNat_eq_ofNat, BitVec.reduceSub, Nat.reduceDiv] at ha
    all_goals exact Wrapper.local_memory (by decide) (by decide) (by decide) a ha
  case digest | finalizeIntoReset | traitFinalizeIntoReset =>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try contradiction
    all_goals try exact ha.elim
    all_goals rw [stack_address state.rsp] at ha
    all_goals simp only [Form.frameBytes, Nat.reduceAdd, Nat.reduceSub, BitVec.reduceSub, Nat.reduceDiv] at ha
    all_goals exact Wrapper.local_memory (by decide) (by decide) (by decide) a ha

  case reset =>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try contradiction
    all_goals try exact ha.elim
    all_goals rw [stack_address state.rsp] at ha
    all_goals simp only [Form.frameBytes, Nat.reduceSub, BitVec.reduceSub, Nat.reduceDiv] at ha
    all_goals exact Wrapper.local_memory (by decide) (by decide) (by decide) a ha


theorem suffix_stores {s t : RamState} {v : Variant} {form : Form}
    (h : (Dispatch.Store.effectWithRegister v s form).Holds s t) :
    Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes := by
  have stores := h.writes
  cases form <;>
    simp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect,
      Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, List.cons_append,
      List.nil_append, Write.AllHold] at stores ⊢
  · exact ⟨stores.2.2.2.1, stores.2.2.2.2.1, stores.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  all_goals exact ⟨stores.1, stores.2.1, stores.2.2.1, stores.2.2.2.1,
      stores.2.2.2.2.1, stores.2.2.2.2.2.1, stores.2.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.2.1,
      stores.2.2.2.2.2.2.2.2.2.1, stores.2.2.2.2.2.2.2.2.2.2.1⟩

theorem initialized_registers {s t : RamState} {v : Variant} {stage : Fin 3}
    (h : (Store.effectWithRegister v s (.reset stage)).Holds s t)
    (j : Nat) (hj : j < 8) :
    (.reg (BitVec.ofNat 5 (Store.wordRegister v (.reset stage) j)) : Operand 64).read t =
      v.initialHash[j]!.toBitVec := by
  apply Write.allHold_iff.mp h.writes
    ⟨(.reg (BitVec.ofNat 5 (Store.wordRegister v (.reset stage) j)) : Operand 64), v.initialHash[j]!.toBitVec⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem initialized_words {s t : RamState} {v : Variant} {form : Form}
    (h : Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes) :
    ∀ j < 8, memLoad t.external (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x170) + BitVec.ofNat 64 (8*j)) 64 =
      v.initialHash[j]!.toBitVec := by
  have stores := h
  simp only [Dispatch.Store.suffixEffect, Write.AllHold, Operand.read] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul]
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.2.2.2.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.2.2.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.2.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.2.1
  · cases form <;> dsimp only [Dispatch.Store.slotOffset] at stores ⊢ <;> simpa only [rspOf, Operand.read, Nat.reduceAdd, Nat.reduceSub, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using stores.1

theorem hash_words {s t : RamState} {v : Variant} {form : Form}
    (h : Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes)
    (read : MemReadable t (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x170)) 64) :
    HashStateAt t (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x170)) v.initialHash := by
  refine ⟨Variant.initialHash_size v, ?_⟩
  intro j hj
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x170) + BitVec.ofNat 64 (8*j)) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [initialized_words h j hj] at bytes
  exact bytes.loadBytes64

theorem tail_length {s t : RamState} {v : Variant} {form : Form}
    (h : Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes)
    (read : MemReadable t (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x16f)) 1) :
    t.external[rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x16f)]? = some 0 := by
  have stores := h
  simp only [Dispatch.Store.suffixEffect, Write.AllHold, Operand.read] at stores
  have word := stores.2.2.2.2.2.2.2.2.2.2
  change memLoad t.external (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x16f)) 8 = 0 at word
  have bytes := Bytes.of_memLoad (n := 8) read.mem
  rw [word] at bytes
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using bytes 0 (by decide)

theorem blocks {s t : RamState} {v : Variant} {form : Form}
    (h : Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x1b0)) 64 = 0 := by
  have stores := h
  simp only [Dispatch.Store.suffixEffect, Write.AllHold, Operand.read] at stores
  exact stores.2.2.2.2.2.2.2.2.2.1

theorem blocks_high {s t : RamState} {v : Variant} {form : Form}
    (h : Write.AllHold t (Dispatch.Store.suffixEffect v s form).writes) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 (Dispatch.Store.slotOffset form 0x1b8)) 64 = 0 := by
  have stores := h
  simp only [Dispatch.Store.suffixEffect, Write.AllHold, Operand.read] at stores
  exact stores.2.2.2.2.2.2.2.2.1

set_option maxHeartbeats 1000000 in
theorem buffered_of_stores [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {form : Form}
    (ctx : Context v initial inputs form) (source : State v initial s form)
    (preserved : Preserved v initial t form)
    (stores : Write.AllHold t (Store.suffixEffect v s form).writes) :
    Buffered v initial t ByteArray.empty form := by
  refine ⟨preserved, ?_, ?_, ?_, ?_, ?_⟩
  · have read : MemReadable t (rspOf s + BitVec.ofNat 64 (Store.slotOffset form 0x170)) 64 := by
      rw [stack_address source.rsp]
      cases form <;> dsimp only [Form.frameBytes, Store.slotOffset]
      all_goals simp only [ Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub]
      all_goals exact stack_readable ctx preserved.toState (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
    have value := hash_words stores read
    rw [stack_address source.rsp] at value
    cases form <;> dsimp only [hashPointer, tailLengthPointer, blockCountPointer, blockCountHighPointer, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, Form.frameBytes, Store.slotOffset] at value ⊢ <;> simpa only [show ByteArray.empty.size = 0 from rfl, show compressBlocks v.initialHash ByteArray.empty = v.initialHash from rfl, Nat.zero_div, Nat.zero_mod, show UInt8.ofNat 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub] using value
  · constructor
    · rfl
    · intro i
      have impossible := i.isLt
      change i.val < 0 at impossible
      omega
  · have read : MemReadable t (rspOf s + BitVec.ofNat 64 (Store.slotOffset form 0x16f)) 1 := by
      rw [stack_address source.rsp]
      cases form <;> dsimp only [Form.frameBytes, Store.slotOffset]
      all_goals simp only [ Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub]
      all_goals exact stack_readable ctx preserved.toState (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
    have value := tail_length stores read
    rw [stack_address source.rsp] at value
    cases form <;> dsimp only [hashPointer, tailLengthPointer, blockCountPointer, blockCountHighPointer, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, Form.frameBytes, Store.slotOffset] at value ⊢ <;> simpa only [show ByteArray.empty.size = 0 from rfl, show compressBlocks v.initialHash ByteArray.empty = v.initialHash from rfl, Nat.zero_div, Nat.zero_mod, show UInt8.ofNat 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub] using value
  · have value := blocks stores
    rw [stack_address source.rsp] at value
    cases form <;> dsimp only [hashPointer, tailLengthPointer, blockCountPointer, blockCountHighPointer, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, Form.frameBytes, Store.slotOffset] at value ⊢ <;> simpa only [show ByteArray.empty.size = 0 from rfl, show compressBlocks v.initialHash ByteArray.empty = v.initialHash from rfl, Nat.zero_div, Nat.zero_mod, show UInt8.ofNat 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub] using value
  · have value := blocks_high stores
    rw [stack_address source.rsp] at value
    cases form <;> dsimp only [hashPointer, tailLengthPointer, blockCountPointer, blockCountHighPointer, Form.bufferedMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory, Form.frameBytes, Store.slotOffset] at value ⊢ <;> simpa only [show ByteArray.empty.size = 0 from rfl, show compressBlocks v.initialHash ByteArray.empty = v.initialHash from rfl, Nat.zero_div, Nat.zero_mod, show UInt8.ofNat 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0 from rfl, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub] using value

theorem store [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) (state : State v initial s)
    (arguments : ∀ r ∈ [Syntax.Reg.rcx, .rdi, .rdx, .rsi], s.regValue r = initial.regValue r)
    (rip : s.RIP = v.pc 0x11) :
    ∃ t, Buffered v initial t ByteArray.empty ∧ t.RIP = v.pc 0xd0 ∧
      t.regValue .rsi = initial.regValue .rsi := by
  obtain ⟨fuel, t, execution, ready, _, effect⟩ :=
    Dispatch.Store.run (returnBoundary initial) (Dispatch.returnBoundary_of_call ctx.machine ctx.call)
      s (supportedMachine_readyToStep state.machine) (Dispatch.Store.code state.loaded) (pre ctx state rip)
  have writes := local_writes state
  have stateT := Absorb.State.of_agrees (form := .slices) state ctx execution ready effect.agrees (by
    intro c hc a ha
    refine ⟨Stack.region initial v.routine.minStackBytes, by
      exact Vector.mem_of_getElem (i := 1) (h := by decide) rfl, ?_⟩
    rcases writes c hc a ha with low | high
    · exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide) low
    · exact stackRegion_contains_sub ctx.call.stack.2.2.1 (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide) high)
    (by dsimp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset]; simp [Effect.components,
      Write.component, Operand.component]) writes.saved
    (by dsimp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset]; simp [Effect.components,
      Write.component, Operand.component])
  have stores := effect.writes
  dsimp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset] at stores
  simp only [List.cons_append,
    List.nil_append, Write.AllHold, Operand.read] at stores
  have out : memLoad t.external (rspOf s + 8) 64 = s.regValue .rcx := stores.1
  have ptr : memLoad t.external (rspOf s + 16) 64 = s.regValue .rdi := stores.2.2.1
  have len : memLoad t.external (rspOf s + 24) 64 = s.regValue .rdx := stores.2.1
  rw [stack_address state.rsp] at out ptr len
  have preserved : Preserved v initial t :=
    ⟨stateT, out.trans (arguments .rcx (by simp)), ptr.trans (arguments .rdi (by simp)),
      len.trans (arguments .rdx (by simp))⟩
  refine ⟨t, ⟨preserved, ?_, ?_, ?_, ?_, ?_⟩, effect.rip, ?_⟩
  · have read : MemReadable t (rspOf s + 0x170) 64 := by
      rw [stack_address state.rsp]
      simp only [Form.frameBytes, BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
      exact stack_readable ctx stateT (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
    have value := hash_words (suffix_stores effect) read
    rw [stack_address state.rsp] at value
    change HashStateAt t (stackPtr initial - 264) v.initialHash
    exact value
  · constructor
    · rfl
    · intro i
      have impossible := i.isLt
      change i.val < 0 at impossible
      omega
  · have read : MemReadable t (rspOf s + 0x16f) 1 := by
      rw [stack_address state.rsp]
      simp only [Form.frameBytes, BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
      exact stack_readable ctx stateT (by cases v <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide) (by decide)
    have value := tail_length (suffix_stores effect) read
    rw [stack_address state.rsp] at value
    exact value
  · have value := blocks (suffix_stores effect)
    rw [stack_address state.rsp] at value
    exact value
  · have value := blocks_high (suffix_stores effect)
    rw [stack_address state.rsp] at value
    exact value
  · exact (effect.agrees.read (n := 64) (r := 6) (by
      dsimp only [Dispatch.Store.effectWithRegister, Dispatch.Store.registerWrites, Dispatch.Store.effect, Dispatch.Store.prefixEffect, Dispatch.Store.suffixEffect, Dispatch.Store.slotOffset]
      simp [Effect.components,
        Write.component, Operand.component])).trans (arguments .rsi (by simp))

theorem prologue_saved {p : BitVec 64} {layout : Prologue.Layout} {initial s : RamState}
    (six : layout.six = true) (effect : (Prologue.effect p layout initial).Holds initial s) :
    SavedStackAt initial s := by
  constructor
  · intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    have stores := effect.writes
    simp only [Prologue.effect, Prologue.registers, six, ite_true, List.cons_append,
      List.nil_append, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
      List.append_eq, Write.AllHold, Nat.reduceAdd, Nat.reduceMul] at stores
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact stores.1
    · exact stores.2.1
    · exact stores.2.2.1
    · exact stores.2.2.2.1
    · exact stores.2.2.2.2.1
    · exact stores.2.2.2.2.2.1
  · apply Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
    intro i hi c hc covered
    have exclude (off : BitVec 64) (apart : OffsetsApart (-off) 8 (0#64) 8)
        (cover : (Component.mem (rspOf initial - off) 8).Covers
          (stackPtr initial + BitVec.ofNat 64 i)) : False := by
      obtain ⟨j,hj,he⟩ := cover
      rw [BitVec.sub_eq_add_neg] at he
      exact OffsetsApart.ne apart (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          have rspEq : rspOf initial = stackPtr initial := by simp [rspOf, stackPtr, Operand.read]
          rw [rspEq] at he
          exact he.symm)
    simp only [Effect.components, Prologue.effect, Prologue.registers, six, ite_true,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
      List.map_nil, List.append_eq, Write.component, Operand.component, Nat.reduceDiv,
      Nat.reduceAdd, Nat.reduceMul, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact exclude _ (by unfold OffsetsApart; decide +kernel) covered
theorem prologue_state [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {form : Form} (ctx : Context v initial inputs form)
    (entryForm : form = .reset 0 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    ∃ s, State v initial s form ∧ s.RIP = v.pc 0x11 form ∧
      ∀ r : BitVec 5, r ≠ 4#5 →
        (Operand.reg r : Operand 64).read s = (Operand.reg r : Operand 64).read initial := by
  let layout : Prologue.Layout := match form with
    | .reset _ => .six376
    | .finalizeIntoReset _ => .six584
    | _ => .six600
  have six : layout.six = true := by rcases entryForm with rfl | rfl | rfl <;> rfl
  have member : (v.routine form, layout) ∈
      [(sha384Reset, Epilogue.Layout.six376), (sha384FinalizeIntoReset, .six584),
       (sha384TraitFinalizeIntoReset, .six600), (sha512Reset, .six376),
       (sha512FinalizeIntoReset, .six584), (sha512TraitFinalizeIntoReset, .six600),
       (sha512_224Reset, .six376), (sha512_224FinalizeIntoReset, .six584),
       (sha512_224TraitFinalizeIntoReset, .six600), (sha512_256Reset, .six376),
       (sha512_256FinalizeIntoReset, .six584), (sha512_256TraitFinalizeIntoReset, .six600)] := by
    rcases entryForm with rfl | rfl | rfl <;> cases v
    all_goals dsimp only [layout]
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false]
    all_goals solve_by_elim (maxDepth := 15) only [Or.inl, Or.inr, Eq.refl]
  have call : TwoOutputs.ValidCall (v.routine form) initial inputs := by
    rcases entryForm with rfl | rfl | rfl <;> exact ctx.call
  have length : (Prologue.bytes layout).length = layout.length := by
    rcases entryForm with rfl | rfl | rfl <;> rfl
  obtain ⟨s, execution, effect, rsp, rip⟩ := Reset.prologue ctx.machine call layout six
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;> decide +kernel)
    (by rw [← length]; exact Reset.prologue512_inside _ _ member)
    (Reset.prologue512_code _ _ member ctx.programLoaded)
  have execution' : ExecutionState initial s (v.writeRegions initial form) := by
    rcases entryForm with rfl | rfl | rfl <;> exact execution
  refine ⟨s, State.of_executionState execution' (prologue_saved six effect) ?_, ?_, ?_⟩
  · have frame : layout.allocation + 48 = form.frameBytes := by
      rcases entryForm with rfl | rfl | rfl <;> rfl
    simpa only [frame] using rsp
  · rw [rip]
    rcases entryForm with rfl | rfl | rfl <;> cases v <;> rfl
  · intro r hr
    exact effect.agrees.read (n := 64) (r := r) (by
      simpa [Prologue.effect, Prologue.registers, six, Effect.components] using hr)


theorem local_stack [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {form : Form} {components : List Component} (ctx : Context v initial inputs form)
    (writes : Wrapper.LocalWrites initial components) :
    WritesWithin components #v[Stack.region initial (v.routine form).minStackBytes] := by
  intro c hc a ha
  refine ⟨_, Vector.mem_of_getElem (i := 0) (h := by decide) rfl, ?_⟩
  rcases writes c hc a ha with low | high
  · exact stackRegion_contains_sub ctx.stack.2.2.1
      (by cases form <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide)
      (by decide) low
  · exact stackRegion_contains_sub ctx.stack.2.2.1
      (by cases form <;> dsimp only [Variant.routine, Form.stackBytes] <;> decide)
      (by decide) high

theorem state_of_local [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {form : Form} {components : List Component} {fuel : Nat}
    (ctx : Context v initial inputs form) (state : State v initial s form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : Wrapper.LocalWrites initial components)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components) :
    State v initial t form := by
  apply Absorb.State.of_agrees state ctx run ready frame ?_ kept4 writes.saved hdf
  intro c hc a ha
  obtain ⟨region, member, contains⟩ := local_stack ctx writes c hc a ha
  have eq : region = Stack.region initial (v.routine form).minStackBytes := by simpa using member
  subst region
  refine ⟨_, ?_, contains⟩
  cases form with
  | slices | digest => exact Vector.mem_of_getElem (i := 1) (h := by decide) rfl
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    exact Vector.mem_of_getElem (i := 2) (h := by change 2 < 3; decide) rfl

set_option maxHeartbeats 800000 in
theorem suffix_local_writes [Bindings] {v : Variant} {initial s : RamState} {form : Form}
    (state : State v initial s form)
    (entryForm : form = .reset 0 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    Absorb.LocalWrites initial (Store.effectWithRegister v s form).components form := by
  rcases entryForm with rfl | rfl | rfl
  all_goals intro c hc a ha
  all_goals
    dsimp only [Store.effectWithRegister, Store.registerWrites, Store.effect,
      Store.prefixEffect, Store.suffixEffect, Store.slotOffset] at hc
    simp only [List.range_succ, List.range_zero, List.cons_append, List.nil_append,
      Effect.components, List.map_cons, List.map_nil, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
  all_goals first
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals try contradiction
  all_goals try exact ha.elim
  all_goals rw [stack_address state.rsp] at ha
  all_goals simp only [Form.frameBytes, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub, Nat.reduceDiv] at ha
  all_goals first
    | exact Absorb.local_memory (form := .reset 0) (by decide) (by decide) (by
        simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
        intro slot hs
        rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
    | exact Absorb.local_memory (form := .finalizeIntoReset false) (by decide) (by decide) (by
        simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
        intro slot hs
        rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
    | exact Absorb.local_memory (form := .traitFinalizeIntoReset false) (by decide) (by decide) (by
        simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
        intro slot hs
        rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha

theorem prefix_preserved [Bindings] {v : Variant} {initial s t : RamState} {form : Form}
    (source : State v initial s form) (target : State v initial t form)
    (effect : (Store.prefixEffect v s form).Holds s t)
    (arguments : ∀ r ∈ [Syntax.Reg.rcx, .rdi, .rdx, .rsi, .r8], s.regValue r = initial.regValue r)
    (entryForm : form = .reset 0 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    Preserved v initial t form := by
  have arg1 := arguments .rcx (by simp)
  have arg7 := arguments .rdi (by simp)
  have arg2 := arguments .rdx (by simp)
  have arg8 := arguments .r8 (by simp)
  rcases entryForm with rfl | rfl | rfl
  · have out : memLoad t.external (rspOf s + 232) 64 = s.regValue .rcx := effect.writes.2.1
    have ptr : memLoad t.external (rspOf s + 216) 64 = s.regValue .rdi := effect.writes.2.2.2.2.1
    have len : memLoad t.external (rspOf s + 224) 64 = s.regValue .rdx := effect.writes.2.2.1
    have second : memLoad t.external (rspOf s + 240) 64 = s.regValue .r8 := effect.writes.1
    rw [stack_address source.rsp] at out ptr len second
    exact ⟨target, ⟨Or.inl (out.trans arg1), second.trans arg8⟩, ptr.trans arg7, len.trans arg2⟩
  · have out : memLoad t.external (rspOf s + 224) 64 = s.regValue .rcx := by
      cases v <;> exact effect.writes.2.1
    have ptr : memLoad t.external (rspOf s) 64 = s.regValue .rdi := by
      cases v
      · exact effect.writes.2.2.2
      · exact effect.writes.2.2.2
      · exact effect.writes.2.2.2.2
      · exact effect.writes.2.2.2.2
    have len : memLoad t.external (rspOf s + 8) 64 = s.regValue .rdx := by
      cases v <;> exact effect.writes.2.2.1
    have second : memLoad t.external (rspOf s + 232) 64 = s.regValue .r8 := by
      cases v <;> exact effect.writes.1
    rw [stack_address source.rsp] at out len second
    change memLoad t.external (stackPtr s) 64 = _ at ptr
    rw [source.rsp] at ptr
    exact ⟨target, ⟨Or.inl (out.trans arg1), second.trans arg8⟩, ptr.trans arg7, len.trans arg2⟩
  · have out : t.regValue (if v = .sha512 then .r13 else .rbp) = s.regValue .rcx := by
      cases v <;> exact effect.writes.2.1
    have ptr : memLoad t.external (rspOf s + 16) 64 = s.regValue .rdi := effect.writes.2.2.2
    have len : memLoad t.external (rspOf s + 24) 64 = s.regValue .rdx := effect.writes.2.2.1
    have second : memLoad t.external (rspOf s + 248) 64 = s.regValue .r8 := effect.writes.1
    rw [stack_address source.rsp] at ptr len second
    exact ⟨target, ⟨Or.inr ⟨rfl, out.trans arg1⟩, second.trans arg8⟩, ptr.trans arg7, len.trans arg2⟩

theorem initialized_entry [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {form : Form} (ctx : Context v initial inputs form)
    (entryForm : form = .reset 0 ∨ form = .finalizeIntoReset false ∨ form = .traitFinalizeIntoReset false) :
    ∃ p h t, State v initial p form ∧
      (∀ r ∈ [Syntax.Reg.rcx, .rdi, .rdx, .rsi, .r8], p.regValue r = initial.regValue r) ∧
      (Store.prefixEffect v p form).Holds p h ∧
      (Store.effectWithRegister v h form).Holds h t ∧ Buffered v initial t ByteArray.empty form := by
  obtain ⟨p, stateP, ripP, regs⟩ := prologue_state ctx entryForm
  have arguments : ∀ r ∈ [Syntax.Reg.rcx, .rdi, .rdx, .rsi, .r8],
      p.regValue r = initial.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact regs 1#5 (by decide)
    · exact regs 7#5 (by decide)
    · exact regs 2#5 (by decide)
    · exact regs 6#5 (by decide)
    · exact regs 8#5 (by decide)
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have code : CodeIn (codeRange (v.pc 0x11 form) (Store.prefixBytes v form)) p := by
    rcases entryForm with rfl | rfl | rfl <;> exact Store.argument_code stateP.loaded _
  obtain ⟨n, h, runH, readyH, _, prefixResult⟩ := Store.runPrefix (returnBoundary initial) outside
    p (supportedMachine_readyToStep stateP.machine) code (pre ctx stateP ripP)
  have stateH := state_of_local ctx stateP runH readyH prefixResult.agrees (prefix_local_writes stateP)
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;>
      simp [Store.prefixEffect, Effect.components, Write.component, Operand.component])
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;>
      simp [Store.prefixEffect, Effect.components, Write.component, Operand.component])
  have preservedH := prefix_preserved stateP stateH prefixResult arguments entryForm
  have ripH : h.RIP = v.pc (Store.startOffset form v) form := by
    rw [prefixResult.rip]
    rcases entryForm with rfl | rfl | rfl <;> cases v <;> rfl
  obtain ⟨m, t, runT, readyT, _, suffix⟩ := Store.run (returnBoundary initial) outside
    h readyH (Store.code stateH.loaded form (by rcases entryForm with rfl | rfl | rfl <;> rfl))
    (pre ctx stateH ripH)
  have preservedT := Absorb.preserved_of_agrees ctx preservedH runT readyT suffix.agrees
    (suffix_local_writes stateH entryForm)
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;>
      simp [Store.effectWithRegister, Store.registerWrites, Store.wordRegister, Store.effect, Store.suffixEffect,
        Effect.components, Write.component, Operand.component, List.range_succ])
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;>
      simp [Store.effectWithRegister, Store.registerWrites, Store.wordRegister, Store.effect, Store.suffixEffect,
        Effect.components, Write.component, Operand.component, List.range_succ])
    (by rcases entryForm with rfl | rfl | rfl <;> simp)
    (by rcases entryForm with rfl | rfl | rfl <;> cases v <;>
      simp [Store.effectWithRegister, Store.registerWrites, Store.wordRegister, Store.effect, Store.suffixEffect,
        Effect.components, Write.component, Operand.component, List.range_succ])
  exact ⟨p, h, t, stateP, arguments, prefixResult, suffix,
    buffered_of_stores ctx stateH preservedT (suffix_stores suffix)⟩

theorem reset_initialized [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.reset 0)) :
    ∃ t, Buffered v initial t ByteArray.empty (.reset 0) ∧
      t.RIP = v.pc 0xe9 (.reset 0) ∧ t.regValue .r12 = BitVec.ofNat 64 inputs.size ∧
      (t.regValue .rax = stackPtr initial - 296 ∧
      ∀ j < 8, t.regValue (match j with
        | 0 => .r10 | 1 => .r11 | 2 => .r8 | 3 => .r9 | 4 => .rsi | 5 => .rdi
        | 6 => if v = .sha512 then .rcx else .rdx
        | _ => if v = .sha512 then .rdx else .rcx) = (v.initialHash[j]!).toBitVec) := by
  obtain ⟨p,h,t,stateP,args,hp,ht,buffered⟩ := initialized_entry ctx (Or.inl rfl)
  have count : p.regValue .rsi = BitVec.ofNat 64 inputs.size := by
    rw [args .rsi (by simp), ← ctx.call.countArgumentMatchesInputs]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have r12h : h.regValue .r12 = p.regValue .rsi := hp.writes.2.2.2.1
  have raxh : h.regValue .rax = rspOf p + 128 := hp.writes.2.2.2.2.2
  have r12t : t.regValue .r12 = h.regValue .r12 := ht.agrees.read (n := 64) (r := 12) (by
    cases v <;> simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
      Store.registerWrites, Store.wordRegister, Effect.components, Write.component, Operand.component, List.range_succ])
  have raxt : t.regValue .rax = h.regValue .rax := ht.agrees.read (n := 64) (r := 0) (by
    cases v <;> simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
      Store.registerWrites, Store.wordRegister, Effect.components, Write.component, Operand.component, List.range_succ])
  refine ⟨t,buffered,ht.rip,r12t.trans (r12h.trans count),?_,?_⟩
  · rw [raxt, raxh, stack_address stateP.rsp]
    rfl
  · intro j hj
    have value := initialized_registers ht j hj
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases v <;> exact value

theorem finalize_initialized [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.finalizeIntoReset false)) :
    ∃ t, Buffered v initial t ByteArray.empty (.finalizeIntoReset false) ∧
      t.RIP = Dispatch.Loop.finalizeFirstSetupPC v ∧
      t.regValue .rsi = BitVec.ofNat 64 inputs.size ∧
      (Dispatch.Loop.finalizeFirstCopiesCount v = false →
        t.regValue .r15 = BitVec.ofNat 64 inputs.size) := by
  obtain ⟨p,h,t,stateP,args,hp,ht,buffered⟩ := initialized_entry ctx (Or.inr (Or.inl rfl))
  have count : p.regValue .rsi = BitVec.ofNat 64 inputs.size := by
    rw [args .rsi (by simp), ← ctx.call.countArgumentMatchesInputs]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hs : h.regValue .rsi = p.regValue .rsi := hp.agrees.read (n := 64) (r := 6) (by
    cases v <;> simp [Store.prefixEffect, Effect.components, Write.component, Operand.component])
  have ts : t.regValue .rsi = h.regValue .rsi := ht.agrees.read (n := 64) (r := 6) (by
    simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
      Store.registerWrites, Effect.components, Write.component, Operand.component])
  refine ⟨t,buffered,?_,ts.trans (hs.trans count),?_⟩
  · cases v <;> exact ht.rip
  · intro truncated
    have tr : t.regValue .r15 = h.regValue .r15 := ht.agrees.read (n := 64) (r := 15) (by
      simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
        Store.registerWrites, Effect.components, Write.component, Operand.component])
    apply tr.trans
    cases v
    · contradiction
    · contradiction
    · exact hp.writes.2.2.2.1.trans count
    · exact hp.writes.2.2.2.1.trans count

theorem trait_initialized [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset false)) :
    ∃ t, Buffered v initial t ByteArray.empty (.traitFinalizeIntoReset false) ∧
      t.RIP = Dispatch.Loop.traitSavePC v false ∧
      t.regValue .rsi = BitVec.ofNat 64 inputs.size ∧
      t.regValue (if v = .sha512 then .r13 else .rbp) = initial.regValue .rcx := by
  obtain ⟨p,h,t,stateP,args,hp,ht,buffered⟩ := initialized_entry ctx (Or.inr (Or.inr rfl))
  have count : p.regValue .rsi = BitVec.ofNat 64 inputs.size := by
    rw [args .rsi (by simp), ← ctx.call.countArgumentMatchesInputs]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hs : h.regValue .rsi = p.regValue .rsi := hp.agrees.read (n := 64) (r := 6) (by
    cases v <;> simp [Store.prefixEffect, Effect.components, Write.component, Operand.component])
  have ts : t.regValue .rsi = h.regValue .rsi := ht.agrees.read (n := 64) (r := 6) (by
    simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
      Store.registerWrites, Effect.components, Write.component, Operand.component])
  refine ⟨t,buffered,?_,ts.trans (hs.trans count),?_⟩
  · cases v <;> exact ht.rip
  · have out : h.regValue (if v = .sha512 then .r13 else .rbp) = p.regValue .rcx := by
      cases v <;> exact hp.writes.2.1
    have kept := ht.agrees.read (n := 64) (r := if v = .sha512 then 13 else 5) (by
      cases v <;> simp [Store.effectWithRegister, Store.effect, Store.suffixEffect,
        Store.registerWrites, Effect.components, Write.component, Operand.component])
    have eq : t.regValue (if v = .sha512 then .r13 else .rbp) =
        h.regValue (if v = .sha512 then .r13 else .rbp) := by
      cases v <;> exact kept
    exact eq.trans (out.trans (args .rcx (by simp)))

theorem second_preserved [Bindings] {v : Variant} {initial s : RamState} {first last : Form}
    (shape : (first = .finalizeIntoReset false ∧ last = .finalizeIntoReset true) ∨
      (first = .traitFinalizeIntoReset false ∧ last = .traitFinalizeIntoReset true))
    (state : Preserved v initial s first) : Preserved v initial s last := by
  rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    refine ⟨⟨state.execution, state.machine, state.loaded, state.allocated, state.saved,
      state.directionFlag, ?_, state.rsp⟩, ?_, state.pointerTable, state.lengthTable⟩
  all_goals first
    | (cases v <;> exact state.frame)
    | exact ⟨Or.inl state.outputPointer.2, state.outputPointer.2⟩

theorem reinitialized_of_stores [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {first last : Form} {components : List Component} {fuel : Nat}
    (shape : (first = .finalizeIntoReset false ∧ last = .finalizeIntoReset true) ∨
      (first = .traitFinalizeIntoReset false ∧ last = .traitFinalizeIntoReset true))
    (ctx : Context v initial inputs first) (state : Preserved v initial s first)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : Absorb.LocalWrites initial components last)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components)
    (stores : Write.AllHold t (Store.suffixEffect v s last).writes) :
    Buffered v initial t ByteArray.empty last ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine last).minStackBytes] := by
  have ctxLast : Context v initial inputs last := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals exact ⟨ctx.stride, ctx.machine, by cases v <;> exact ctx.call⟩
  have stateLast := second_preserved shape state
  have target := Absorb.preserved_of_agrees ctxLast stateLast run ready frame writes kept4 hdf
    (by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp)
    (by rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp)
  exact ⟨buffered_of_stores ctxLast stateLast.toState target stores,
    frame.memoryWriteFrame (writes.stack ctxLast)⟩

open Sha2.Proofs.Wrapper512.Dispatch.Loop

theorem restoration_stores {v : Variant} {p : BitVec 64} {s t : RamState} {form : Form}
    (shape : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true)
    (effect : (resetTransitionEffect v p s form).Holds s t) :
    Write.AllHold t (Store.suffixEffect v s form).writes := by
  rcases shape with rfl | rfl
  all_goals exact effect.writes.2.2

theorem restoration_local_writes [Bindings] {v : Variant} {initial s : RamState}
    {p : BitVec 64} {form : Form} (state : State v initial s form)
    (shape : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true) :
    Absorb.LocalWrites initial (resetTransitionEffect v p s form).components form := by
  rcases shape with rfl | rfl
  all_goals intro c hc a ha
  all_goals
    rw [Effect.components] at hc
    dsimp only [Store.suffixEffect, Store.slotOffset, resetTransitionEffect, resetTransitionRegister, resetTransitionHead, resetTransitionHashOffset] at hc
    simp only [
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, Write.component,
      Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals rw [stack_address state.rsp] at ha
  all_goals simp only [Form.frameBytes, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSub, Nat.reduceDiv] at ha
  all_goals first
    | exact Absorb.local_memory (form := .finalizeIntoReset true) (by decide) (by decide) (by
        simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
        intro slot hs
        rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
    | exact Absorb.local_memory (form := .traitFinalizeIntoReset true) (by decide) (by decide) (by
        simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]
        intro slot hs
        rcases hs with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a ha
theorem restoration_count [Bindings] {v : Variant} {initial s t : RamState}
    {p : BitVec 64} {form : Form} (state : State v initial s form)
    (shape : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true)
    (effect : (resetTransitionEffect v p s form).Holds s t) :
    v.countValue form initial t = v.countValue form initial s := by
  rcases shape with rfl | rfl
  · cases v
    all_goals first
      | exact effect.agrees.read (n := 64) (r := 12) (by
          simp [Effect.components, resetTransitionEffect, resetTransitionRegister, resetTransitionHead, resetTransitionBase, Write.component, Operand.component])
      | exact effect.agrees.read (n := 64) (r := 15) (by
          simp [Effect.components, resetTransitionEffect, resetTransitionRegister, resetTransitionHead, resetTransitionBase, Write.component, Operand.component])
  · have countValue (u : RamState) : v.countValue (.traitFinalizeIntoReset true) initial u =
        memLoad u.external (stackPtr initial - 640) 64 := by cases v <;> rfl
    rw [countValue, countValue]
    apply Common.Encoding.Serialize.read_mem_of_agrees effect.agrees
    intro i hi c hc covered
    have exclude (off len : Nat) (small : len ≤ 8)
        (apart : OffsetsApart (-640) 8 (-(BitVec.ofNat 64 off)) len)
        (cover : (Component.mem (stackPtr initial - BitVec.ofNat 64 off) len).Covers
          (stackPtr initial - 640 + BitVec.ofNat 64 i)) : False := by
      obtain ⟨j,hj,he⟩ := cover
      exact OffsetsApart.ne apart (stackPtr initial) hi hj (by omega)
        (by simpa only [BitVec.sub_eq_add_neg] using he)
    rw [Effect.components] at hc
    dsimp only [Store.suffixEffect, Store.slotOffset, resetTransitionEffect, resetTransitionRegister, resetTransitionHead, resetTransitionHashOffset] at hc
    simp only [
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, Write.component,
      Operand.component, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals rw [stack_address state.rsp] at covered
    all_goals simp only [Form.frameBytes, Nat.reduceAdd, BitVec.reduceSub, Nat.reduceDiv] at covered
    all_goals exact exclude _ _ (by decide) (by unfold OffsetsApart; decide +kernel) covered
theorem restoration_pre [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {p : BitVec 64} {form : Form} (ctx : Context v initial inputs form)
    (state : State v initial s form)
    (shape : form = .finalizeIntoReset true ∨ form = .traitFinalizeIntoReset true)
    (rip : s.RIP = p) (inside : BlockInProgram p 148)
    (base : (Operand.reg (BitVec.ofNat 5 (resetTransitionBase v form)) : Operand 64).read s =
      rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset form)) :
    ResetTransitionPre p s form v := by
  have avoidsPages : (Stack.region initial (v.routine form).minStackBytes).Avoids InPageTables := by
    intro a ha hp
    exact (ctx.separation.2 _ (by rcases shape with rfl | rfl <;> change _ ∈ [_, _, _] <;> simp)).2 a ha (.inr hp)
  have avoidsProgram : (Stack.region initial (v.routine form).minStackBytes).Avoids InProgram := by
    intro a ha hp
    exact (ctx.separation.2 _ (by rcases shape with rfl | rfl <;> change _ ∈ [_, _, _] <;> simp)).2 a ha (.inl hp)
  have writable (offset len : Nat) (bound : offset + len ≤ form.frameBytes) (pos : 0 < len) :
      MemWritable s (rspOf s + BitVec.ofNat 64 offset) len := by
    change MemWritable s (stackPtr s + _) len
    rw [state.rsp]
    exact stack_frame_writable (frame := form.frameBytes) ctx.stack
      (by rcases shape with rfl | rfl <;> cases v <;> decide) avoidsPages state.allocated bound pos
  have apart (offset len : Nat) (bound : offset + len ≤ form.frameBytes) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) len p 148 := by
    change RangeApart (stackPtr s + _) len _ _
    rw [state.rsp]
    exact stack_frame_codeApart (frame := form.frameBytes) ctx.stack
      (by rcases shape with rfl | rfl <;> cases v <;> decide) avoidsProgram bound
      (fun i hi => inside i (Nat.le_of_lt hi))
  refine ⟨rip,
    writable (resetTransitionHashOffset form - 1) 1 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form - 1) 1 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 0) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 0) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 8) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 8) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 16) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 16) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 24) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 24) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 32) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 32) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 40) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 40) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 48) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 48) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 56) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 56) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 64) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 64) 8 (by rcases shape with rfl | rfl <;> decide),
    writable (resetTransitionHashOffset form + 72) 8 (by rcases shape with rfl | rfl <;> decide) (by decide),
    apart (resetTransitionHashOffset form + 72) 8 (by rcases shape with rfl | rfl <;> decide),
    fun _ => base⟩

theorem restored_of_effect [Bindings] {v : Variant} {initial s t : RamState}
    {inputs : Array Input} {first last : Form} {p : BitVec 64} {fuel : Nat}
    (shape : (first = .finalizeIntoReset false ∧ last = .finalizeIntoReset true) ∨
      (first = .traitFinalizeIntoReset false ∧ last = .traitFinalizeIntoReset true))
    (ctx : Context v initial inputs first) (state : Preserved v initial s first)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (effect : (resetTransitionEffect v p s last).Holds s t) :
    Buffered v initial t ByteArray.empty last ∧
      t.RIP = p + BitVec.ofNat 64 (resetTransitionLength v last) ∧
      v.countValue last initial t = v.countValue first initial s ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine last).minStackBytes] := by
  have shapeLast : last = .finalizeIntoReset true ∨ last = .traitFinalizeIntoReset true := by
    rcases shape with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have source := second_preserved shape state
  obtain ⟨buffered, frame⟩ := reinitialized_of_stores shape ctx state run ready effect.agrees
    (restoration_local_writes source.toState shapeLast)
    (by rcases shapeLast with rfl | rfl <;> cases v <;>
      simp [resetTransitionEffect, resetTransitionRegister, resetTransitionBase,
        resetTransitionHead, Effect.components, Write.component, Operand.component])
    (by rcases shapeLast with rfl | rfl <;>
      simp [resetTransitionEffect, Effect.components, Write.component, Operand.component])
    (restoration_stores shapeLast effect)
  refine ⟨buffered, effect.rip, (restoration_count source.toState shapeLast effect).trans ?_, frame⟩
  rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases v <;> rfl

theorem reinitialize [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    {first last : Form}
    (shape : (first = .finalizeIntoReset false ∧ last = .finalizeIntoReset true) ∨
      (first = .traitFinalizeIntoReset false ∧ last = .traitFinalizeIntoReset true))
    (ctx : Context v initial inputs first) (state : Preserved v initial s first)
    (rip : s.RIP = v.pc (v.outputEndOffset first) first)
    (count : v.countValue first initial s = BitVec.ofNat 64 inputs.size)
    (base : (Operand.reg (BitVec.ofNat 5 (resetTransitionBase v last)) : Operand 64).read s =
      hashPointer initial last) :
    ∃ t, Buffered v initial t ByteArray.empty last ∧
      t.RIP = v.pc (resetTransitionOffset v last + resetTransitionLength v last) last ∧
      v.countValue last initial t = BitVec.ofNat 64 inputs.size ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine last).minStackBytes] := by
  have shapeLast : last = .finalizeIntoReset true ∨ last = .traitFinalizeIntoReset true := by
    rcases shape with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have ctxLast : Context v initial inputs last := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals exact ⟨ctx.stride, ctx.machine, by cases v <;> exact ctx.call⟩
  have source := second_preserved shape state
  have entry : s.RIP = v.pc (resetTransitionOffset v last) last := by
    rcases shape with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases v <;> exact rip
  have inside : BlockInProgram (v.pc (resetTransitionOffset v last) last) 148 := by
    apply blockInProgram_of_textOffset
    rcases shapeLast with rfl | rfl <;> cases v <;> decide +kernel
  have pointer : (Operand.reg (BitVec.ofNat 5 (resetTransitionBase v last)) : Operand 64).read s =
      rspOf s + BitVec.ofNat 64 (resetTransitionHashOffset last) := by
    rw [base, stack_address source.rsp]
    rcases shapeLast with rfl | rfl <;> rfl
  obtain ⟨fuel,t,run,ready,_,effect⟩ := reset_transition v _ (returnBoundary initial)
    (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2 inside
    (form := last) (phase := Or.inr shapeLast)
    s (supportedMachine_readyToStep state.machine)
    (resetTransition_code (form := last) (phase := Or.inr shapeLast) state.loaded)
    (restoration_pre ctxLast source.toState shapeLast entry inside pointer)
  obtain ⟨buffered,entryT,countT,frame⟩ := restored_of_effect shape ctx state run ready effect
  refine ⟨t,buffered,?_,countT.trans count,frame⟩
  simpa only [Variant.pc_add] using entryT

theorem finalize_reinitialized [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.finalizeIntoReset false))
    (state : Preserved v initial s (.finalizeIntoReset false))
    (rip : s.RIP = v.pc (v.outputEndOffset (.finalizeIntoReset false)) (.finalizeIntoReset false))
    (count : v.countValue (.finalizeIntoReset false) initial s = BitVec.ofNat 64 inputs.size)
    (pointer : s.regValue .r14 = stackPtr initial - 488) :
    ∃ t, Buffered v initial t ByteArray.empty (.finalizeIntoReset true) ∧
      t.RIP = v.pc (ResetLayout.finalizeIntoResetInitializationEnds v)[1]! (.finalizeIntoReset true) ∧
      v.countValue (.finalizeIntoReset true) initial t = BitVec.ofNat 64 inputs.size ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.finalizeIntoReset true)).minStackBytes] := by
  have result := reinitialize (Or.inl ⟨rfl,rfl⟩) ctx state rip count
    (show (Operand.reg (BitVec.ofNat 5 (resetTransitionBase v (.finalizeIntoReset true))) : Operand 64).read s =
      hashPointer initial (.finalizeIntoReset true) from pointer)
  cases v <;> exact result

theorem trait_reinitialized [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.traitFinalizeIntoReset false))
    (state : Preserved v initial s (.traitFinalizeIntoReset false))
    (rip : s.RIP = v.pc (v.outputEndOffset (.traitFinalizeIntoReset false)) (.traitFinalizeIntoReset false))
    (count : v.countValue (.traitFinalizeIntoReset false) initial s = BitVec.ofNat 64 inputs.size)
    (pointer : s.regValue (if v = .sha512 then .rbp else .rbx) = stackPtr initial - 264) :
    ∃ t, Buffered v initial t ByteArray.empty (.traitFinalizeIntoReset true) ∧
      t.RIP = v.pc (ResetLayout.traitFinalizeIntoResetInitializationEnds v)[1]! (.traitFinalizeIntoReset true) ∧
      v.countValue (.traitFinalizeIntoReset true) initial t = BitVec.ofNat 64 inputs.size ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.traitFinalizeIntoReset true)).minStackBytes] := by
  have base : (Operand.reg (BitVec.ofNat 5 (resetTransitionBase v (.traitFinalizeIntoReset true))) : Operand 64).read s =
      hashPointer initial (.traitFinalizeIntoReset true) := by cases v <;> exact pointer
  have result := reinitialize (Or.inr ⟨rfl,rfl⟩) ctx state rip count base
  cases v <;> exact result

end Initialize

theorem «initialize» [bindings : Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) :
    ∃ s, Buffered v initial s ByteArray.empty ∧
      s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size := by
  obtain ⟨s, pushed, rip⟩ := Chain.pushed ctx
  obtain ⟨t, execution, ready, loaded, ripT, rspT, agrees⟩ :=
    Stages.subframe ctx (supportedMachine_readyToStep pushed.machine) pushed.loaded rip pushed.rsp
  have external : t.external = s.external := agrees.external (by simp [Component.Covers])
  have state : State v initial t := by
    obtain ⟨fuel, previous⟩ := pushed.execution
    refine ⟨⟨fuel + 1, previous.trans execution⟩,
      supportedMachine_of_ready_agrees pushed.machine ready agrees, loaded,
      fun a ha => agrees.grow a (pushed.allocated a ha), ?_,
      agrees.directionFlagClear (by simp) pushed.directionFlag, ?_, rspT⟩
    · constructor
      · intro slot hs
        rw [external]
        exact pushed.saved.words slot hs
      · rw [external]
        exact pushed.saved.returnAddress
    · intro address outside
      rw [external]
      exact pushed.frame address outside
  have arguments : ∀ r ∈ [Syntax.Reg.rcx, .rdi, .rdx, .rsi],
      t.regValue r = initial.regValue r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals first
      | exact (agrees.read (n := 64) (r := 1) (by simp)).trans
          (pushed.agrees.read (n := 64) (r := 1) (by simp [Common.Encoding.Serialize.saveFrame]))
      | exact (agrees.read (n := 64) (r := 7) (by simp)).trans
          (pushed.agrees.read (n := 64) (r := 7) (by simp [Common.Encoding.Serialize.saveFrame]))
      | exact (agrees.read (n := 64) (r := 2) (by simp)).trans
          (pushed.agrees.read (n := 64) (r := 2) (by simp [Common.Encoding.Serialize.saveFrame]))
      | exact (agrees.read (n := 64) (r := 6) (by simp)).trans
          (pushed.agrees.read (n := 64) (r := 6) (by simp [Common.Encoding.Serialize.saveFrame]))
  obtain ⟨u, buffered, ripU, count⟩ := Initialize.store ctx state arguments ripT
  refine ⟨u, buffered, ripU, count.trans ?_⟩
  have countNat := ctx.call.countArgumentMatchesInputs
  rw [← countNat]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Sha2.Proofs.Wrapper512.Machine
