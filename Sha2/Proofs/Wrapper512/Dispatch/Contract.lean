import Sha2.Proofs.Wrapper512.Machine.Initialize
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Wrapper512.API
import Sha2.Proofs.Wrapper512.Dispatch.Run

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Dispatch

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Wrapper512

theorem contract_of_parts [bindings : Bindings] {v : Variant}
    (initializer : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs →
        ∃ s, Buffered v initial s ByteArray.empty ∧
          s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (absorb : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs → ∀ {s : RamState}, LoopState v initial s inputs 0 →
        ∃ t, Buffered v initial t (message inputs) ∧ t.RIP = v.pc 0x218) :
    DispatchContract v := by
  refine ⟨fun {initial} {inputs} ctx => ?_⟩
  obtain ⟨s, initialized, rip, count⟩ := initializer ctx
  obtain ⟨t, result⟩ := Dispatch.run ctx ⟨s, initialized, rip, count⟩
  cases result with
  | inl finalized =>
      exact ⟨t, ⟨finalized.1.toState, finalized.1, finalized.2⟩⟩
  | inr loop =>
      obtain ⟨u, buffered, urip⟩ := absorb ctx loop
      exact ⟨u, ⟨buffered.toState, buffered, urip⟩⟩


set_option maxHeartbeats 1000000 in
theorem reset_transition [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs (.reset 1))
    (positive : 0 < inputs.size)
    (state : Buffered v initial s (message inputs) (.reset 0))
    (rip : s.RIP = v.pc (v.dispatchOffset (.reset 0) inputs.isEmpty) (.reset 0))
    (count : v.countValue (.reset 0) initial s = BitVec.ofNat 64 inputs.size) :
    ∃ t, Buffered v initial t ByteArray.empty (.reset 1) ∧ t.RIP = v.pc 0x29e (.reset 1) ∧
      t.regValue .r12 = BitVec.ofNat 64 inputs.size ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine (.reset 1)).minStackBytes] := by
  have source : Preserved v initial s (.reset 1) := by
    refine ⟨⟨state.execution, state.machine, state.loaded, state.allocated,
      state.saved, state.directionFlag, ?_, state.rsp⟩, ?_, state.pointerTable, state.lengthTable⟩
    · cases v <;> exact state.frame
    · rcases state.outputPointer with ⟨pointer, saved⟩
      refine ⟨?_, saved⟩
      rcases pointer with pointer | ⟨impossible, _⟩
      · exact .inl pointer
      · cases impossible
  have empty : inputs.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt positive]
  have entry : s.RIP = v.pc 0x20a (.reset 1) := by
    rw [empty] at rip
    cases v <;> exact rip
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  have inside : BlockInProgram (v.pc 0x20a (.reset 1)) 148 := by
    have h := blockInProgram_of_textOffset ((ResetLayout.reset v).textOffset + 0x20a) 148
      (by cases v <;> decide)
    cases v <;> exact h
  have avoidsPages : (Stack.region initial (v.routine (.reset 1)).minStackBytes).Avoids InPageTables := by
    intro a ha hp
    exact (ctx.separation.2 _ (by change _ ∈ [_, _, _]; simp)).2 a ha (.inr hp)
  have avoidsProgram : (Stack.region initial (v.routine (.reset 1)).minStackBytes).Avoids InProgram := by
    intro a ha hp
    exact (ctx.separation.2 _ (by change _ ∈ [_, _, _]; simp)).2 a ha (.inl hp)
  have writable (offset len : Nat) (bound : offset + len ≤ 424) (pos : 0 < len) :
      MemWritable s (rspOf s + BitVec.ofNat 64 offset) len := by
    change MemWritable s (stackPtr s + _) len
    rw [source.rsp]
    exact stack_frame_writable (frame := 424) ctx.stack (by cases v <;> decide) avoidsPages source.allocated bound pos
  have apart (offset len : Nat) (bound : offset + len ≤ 424) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) len (v.pc 0x20a (.reset 1)) 148 := by
    change RangeApart (stackPtr s + _) len _ _
    rw [source.rsp]
    exact stack_frame_codeApart (frame := 424) ctx.stack (by cases v <;> decide) avoidsProgram bound
      (fun i hi => inside i (Nat.le_of_lt hi))
  have pre : Loop.ResetTransitionPre (v.pc 0x20a (.reset 1)) s (.reset 1) v := by
    refine ⟨entry,
      writable 127 1 (by decide) (by decide),
      apart 127 1 (by decide),
      writable 128 8 (by decide) (by decide),
      apart 128 8 (by decide),
      writable 136 8 (by decide) (by decide),
      apart 136 8 (by decide),
      writable 144 8 (by decide) (by decide),
      apart 144 8 (by decide),
      writable 152 8 (by decide) (by decide),
      apart 152 8 (by decide),
      writable 160 8 (by decide) (by decide),
      apart 160 8 (by decide),
      writable 168 8 (by decide) (by decide),
      apart 168 8 (by decide),
      writable 176 8 (by decide) (by decide),
      apart 176 8 (by decide),
      writable 184 8 (by decide) (by decide),
      apart 184 8 (by decide),
      writable 192 8 (by decide) (by decide),
      apart 192 8 (by decide),
      writable 200 8 (by decide) (by decide),
      apart 200 8 (by decide), by intro h; cases h⟩
  obtain ⟨fuel, t, run, readyT, _, post⟩ := Loop.reset_transition v _ (returnBoundary initial)
    outside inside (form := .reset 1) (phase := Or.inl rfl) s (supportedMachine_readyToStep source.machine)
      (Loop.resetTransition_code state.loaded) pre
  have rsp : rspOf s = stackPtr initial - 424 := source.rsp
  have writes : Absorb.LocalWrites initial (Loop.resetTransitionEffect v (v.pc 0x20a (.reset 1)) s).components (.reset 1) := by
    intro c hc a ha
    simp only [Loop.resetTransitionEffect, Loop.resetTransitionBase, Loop.resetTransitionHashOffset,
      Loop.resetTransitionRegister, Loop.resetTransitionHead, Loop.resetTransitionLength, Effect.components, List.map_cons,
      List.map_nil, List.append_nil, List.cons_append, List.nil_append, Write.component_reg, Write.component_mem,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals rw [rsp] at ha
    all_goals simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv, BitVec.ofNat_eq_ofNat] at ha
    · apply Absorb.local_memory (offset := 240) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 248) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 256) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 264) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 272) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 280) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 288) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 296) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 224) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 232) (len := 8) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
    · apply Absorb.local_memory (offset := 297) (len := 1) (form := .reset 1)
        (by decide) (by decide) (by
          intro slot member
          simp only [Form.metadataSlots, Form.outputSlot, Form.secondOutputSlot,
            Form.pointerSlot, Form.lengthSlot, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel) a
      simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using ha
  have preserved := Absorb.preserved_of_agrees ctx source run readyT post.agrees writes
    (by simp [Loop.resetTransitionEffect, Loop.resetTransitionBase, Loop.resetTransitionHashOffset,
      Loop.resetTransitionRegister, Loop.resetTransitionHead, Loop.resetTransitionLength, Effect.components])
    (by simp [Loop.resetTransitionEffect, Loop.resetTransitionBase, Loop.resetTransitionHashOffset,
      Loop.resetTransitionRegister, Loop.resetTransitionHead, Loop.resetTransitionLength, Effect.components])
  have stores : Write.AllHold t (Store.suffixEffect v s (.reset 1)).writes := by
    have h := post.writes.2.2
    exact h
  have buffered := Machine.Initialize.buffered_of_stores ctx source.toState preserved stores
  refine ⟨t, buffered, ?_, ?_, ⟨_, run⟩, post.agrees.memoryWriteFrame (writes.stack ctx)⟩
  · have h := post.rip
    cases v <;> exact h
  · have h := post.agrees.read (n := 64) (r := 12) (by simp [Loop.resetTransitionEffect, Loop.resetTransitionBase, Loop.resetTransitionHashOffset,
      Loop.resetTransitionRegister, Loop.resetTransitionHead, Loop.resetTransitionLength, Effect.components])
    cases v <;> exact h.trans count

end Sha2.Proofs.Wrapper512.Dispatch
