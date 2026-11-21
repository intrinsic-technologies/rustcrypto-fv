import Sha2.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import Sha2.Proofs.Reset.Inputs
import Sha2.Proofs.Reset.Layouts
import Sha2.Proofs.Reset.Entry
import Sha2.Proofs.Reset.Prologue
import Sha2.Proofs.Reset.Header
import Sha2.Proofs.Reset.Dispatch
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.SHA256.Instances.Initialize
import Sha2.Proofs.Common.SHA256.Initialize.Correctness

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256
open Sha2.Proofs.Common.SHA256.Instances Sha2.Proofs.Common.Instructions

def resetRoutine : Wrapper.Variant → Routine
  | .sha224 => sha224Reset
  | .sha256 => sha256Reset

theorem resetRoutine_stack (v : Wrapper.Variant) : (resetRoutine v).minStackBytes = 720 := by
  cases v <;> rfl

private theorem initialization_word_inside (v : Wrapper.Variant) (occ : Initialization)
    (i : Fin 4) : BlockInProgram ((occ.layout v).wordPC i.val)
      ((occ.layout v).words[i]).bytes.length := by
  have pc : (occ.layout v).wordPC i.val = Extracted.textAddress +
      BitVec.ofNat 64 (((occ.layout v).wordPC i.val).toNat - 0x100000) := by
    rcases i with ⟨i, hi⟩
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals cases v <;> cases occ <;> decide +kernel +revert
  rw [pc]
  apply blockInProgram_of_textOffset
  rcases i with ⟨i, hi⟩
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals cases v <;> cases occ <;> decide +kernel +revert

private theorem initialization_clear_inside (v : Wrapper.Variant) (occ : Initialization) :
    BlockInProgram ((occ.layout v).wordPC 4) (occ.layout v).clear.bytes.length := by
  have pc : (occ.layout v).wordPC 4 = Extracted.textAddress +
      BitVec.ofNat 64 (((occ.layout v).wordPC 4).toNat - 0x100000) := by
    cases v <;> cases occ <;> decide +kernel
  rw [pc]
  exact blockInProgram_of_textOffset _ _ (by cases v <;> cases occ <;> decide +kernel)

theorem initialize_pre_at (v : Wrapper.Variant) {initial s : RamState}
    {occ : Initialization} {reserve frame : Nat}
    (stack : Stack.Valid initial reserve)
    (avoids : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 frame)
    (rip : s.RIP = (occ.layout v).start)
    (capacity : frame ≤ reserve)
    (fits : occ.bufferOffset + 104 ≤ frame)
    (base : occ.hashBase ≠ 4 →
      (.reg (occ.hashBase.setWidth 5) : Operand 64).read s = rspOf s + BitVec.ofNat 64 (occ.bufferOffset + 64) := by
        intro impossible; exact (impossible rfl).elim) :
    Initialize.Pre (occ.layout v) (rspOf s + BitVec.ofNat 64 occ.bufferOffset) s := by
  have write (t : RamState) (memory : t.external = s.external) (offset len : Nat)
      (bound : offset + len ≤ frame) (pos : 0 < len) :
      MemWritable t (rspOf s + BitVec.ofNat 64 offset) len := by
    rw [rsp]
    exact stack_frame_writable stack capacity
      (fun a ha h => avoids a ha (.inr h))
      (by simpa only [memory] using grow) bound pos
  have apart (offset len : Nat) (bound : offset + len ≤ frame)
      (p : BitVec 64) (size : Nat) (inside : BlockInProgram p size) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) len p size := by
    rw [rsp]
    exact stack_frame_codeApart stack capacity (fun a ha h => avoids a ha (.inl h))
      bound (fun j hj => inside j (Nat.le_of_lt hj))
  have addresses (i : Fin 4) : (occ.layout v).words[i].destination.read s =
      rspOf s + BitVec.ofNat 64 (occ.bufferOffset + 64 + 8 * (3-i.val)) := by
    rcases i with ⟨i, hi⟩
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals cases occ
    all_goals first
      | rfl
      | (have hb := base (by decide)
         first
         | change (Operand.reg 0#5 : Operand 64).read s = _ at hb
         | change (Operand.reg 3#5 : Operand 64).read s = _ at hb
         | change (Operand.reg 5#5 : Operand 64).read s = _ at hb
         first
         | change (Operand.reg 0#5 : Operand 64).read s + _ = _
         | change (Operand.reg 3#5 : Operand 64).read s + _ = _
         | change (Operand.reg 5#5 : Operand 64).read s + _ = _
         rw [hb, BitVec.add_assoc]
         rfl)
  have counters : (occ.layout v).clear.counter.read s =
      rspOf s + BitVec.ofNat 64 (occ.bufferOffset + 96) ∧
      (occ.layout v).clear.tail.read s = rspOf s + BitVec.ofNat 64 (occ.bufferOffset + 63) := by
    cases occ <;> exact ⟨rfl, rfl⟩
  have valid := Initialization.valid occ v
  refine ⟨rip, valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rsp]
    exact stack_frame_readable stack capacity grow fits
  · intro i
    have addr : (occ.layout v).words[i].destination.read
        {s with RIP := (occ.layout v).wordPC i.val} =
        rspOf s + BitVec.ofNat 64 (occ.bufferOffset + 64 + 8 * (3-i.val)) := addresses i
    have load : (occ.layout v).words[i].loadConstant = true := by
      rcases i with ⟨i, hi⟩
      obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rfl
    refine ⟨rfl, valid.addressing i, valid.independentWords i i, ?_, ?_, ?_⟩
    · rw [load]; intro impossible; contradiction
    · rw [addr]
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (occ.layout v).wordPC i.val} rfl _ 8 (by omega) (by decide))
    · rw [addr]
      exact apart _ 8 (by omega) _ _ (initialization_word_inside v occ i)
  · intro i
    rw [addresses i, valid.order i, BitVec.add_assoc, BitVec.ofNat_add]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using counters.1
  · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using counters.2
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (
      cases occ <;> cases v <;> decide +kernel +revert)
    · change CrossPageStore.Writable {s with RIP := (occ.layout v).wordPC 4}
        ((occ.layout v).clear.counter.read s) 8
      rw [counters.1]
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (occ.layout v).wordPC 4} rfl (occ.bufferOffset + 96) 8 (by omega) (by decide))
    · change RangeApart ((occ.layout v).clear.counter.read s) 8 _ _
      rw [counters.1]
      exact apart (occ.bufferOffset + 96) 8 (by omega) _ _ (initialization_clear_inside v occ)
    · change MemWritable {s with RIP := (occ.layout v).wordPC 4}
        ((occ.layout v).clear.tail.read s) 1
      rw [counters.2]
      exact write {s with RIP := (occ.layout v).wordPC 4} rfl (occ.bufferOffset + 63) 1 (by omega) (by decide)
    · change RangeApart ((occ.layout v).clear.tail.read s) 1 _ _
      rw [counters.2]
      exact apart (occ.bufferOffset + 63) 1 (by omega) _ _ (initialization_clear_inside v occ)
    · change RangeApart ((occ.layout v).clear.counter.read s) 8
        ((occ.layout v).clear.tail.read s) 1
      rw [counters.1, counters.2]
      cases occ <;> intro i hi j hj he
      all_goals exact OffsetsApart.ne (by unfold OffsetsApart; decide +kernel) (rspOf s) hi hj (by decide) he
  · exact apart occ.bufferOffset 104 fits _ _ (Initialization.inside occ v)

theorem initialize_pre (v : Wrapper.Variant) {initial s : RamState}
    {occ : Initialization}
    (stack : Stack.Valid initial 720)
    (avoids : (Stack.region initial 720).Avoids (fun a => InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = (occ.layout v).start)
    (allowed : occ ∈ [Initialization.resetInitial, .resetDiscarded, .resetOutput] := by simp)
    (base : occ.hashBase ≠ 4 →
      (.reg (occ.hashBase.setWidth 5) : Operand 64).read s = rspOf s + 64#64 := by
        intro impossible; exact (impossible rfl).elim) :
    Initialize.Pre (occ.layout v) (rspOf s) s := by
  have offset : occ.bufferOffset = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl <;> rfl
  simpa only [offset, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    initialize_pre_at v stack avoids grow rsp rip (by decide) (by rw [offset]; decide) (by simpa only [offset, Nat.zero_add] using base)

private theorem regions_avoid {routine : Routine} {initial : RamState} {inputs : Array Input}
    (call : TwoOutputs.ValidCall routine initial inputs) :
    ∀ region ∈ regions routine initial, region.Avoids InProgram := by
  intro region member a ha hp
  have mem : region ∈ [TwoOutputs.outputRegion routine initial,
      TwoOutputs.secondOutputRegion routine initial, Stack.region initial routine.minStackBytes] := by
    simpa only [regions, Vector.mem_mk, List.mem_toArray] using member
  exact (call.separation.2 region mem).2 a ha (.inl hp)

theorem branch_state [bindings : Bindings] {routine : Routine} {initial u : RamState}
    {inputs : Array Input} {p : BitVec 64} {displacement : BitVec 32} {count : BitVec 4}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial u (regions routine initial))
    (rip : u.RIP = p)
    (code : CodeIn (codeRange p (Dispatch.branchBytes displacement count)) u)
    (inside : BlockInProgram p 9)
    (target : InProgram (p + 9 + displacement.signExtend 64)) :
    ∃ b, ExecutionState initial b (regions routine initial) ∧
      (Dispatch.branchEffect p u displacement count).Holds u b := by
  obtain ⟨fuel, b, run, ready, _, result⟩ := Dispatch.branch p
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside target u (supportedMachine_readyToStep state.machine) code rip
  refine ⟨b, state.of_agrees (regions_avoid call) run ready result.agrees ?_ ?_, result⟩
  · intro c hc a ha
    simp [Dispatch.branchEffect, Effect.components, Component.Covers] at hc ha
    rcases hc with rfl | rfl <;> exact ha.elim
  · simp [Dispatch.branchEffect, Effect.components]

theorem header_at [bindings : Bindings] (layout : Header.Layout) (v : Wrapper.Variant)
    {routine : Routine} {frame : Nat} {initial p : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial p (regions routine initial))
    (rsp : stackPtr p = stackPtr initial - BitVec.ofNat 64 frame)
    (rip : p.RIP = layout.pc v)
    (capacity : frame ≤ routine.minStackBytes)
    (bound : layout.countSlot + 8 ≤ frame) :
    ∃ h, ExecutionState initial h (regions routine initial) ∧
      (Header.effectAt layout (layout.pc v) p).Holds p h := by
  have stack := call.stack
  have avoid : (Stack.region initial routine.minStackBytes).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [InPageTables] using (call.separation.2 _ (by simp)).2
  have inside := Header.inside layout v
  have write (offset : Nat) (bound : offset + 8 ≤ frame) :
      MemWritable p (rspOf p + BitVec.ofNat 64 offset) 8 := by
    change rspOf p = stackPtr initial - BitVec.ofNat 64 frame at rsp
    rw [rsp]
    exact stack_frame_writable stack capacity (fun a ha h => avoid a ha (.inr h))
      state.allocated bound (by decide)
  have apart (offset : Nat) (bound : offset + 8 ≤ frame) :
      RangeApart (rspOf p + BitVec.ofNat 64 offset) 8 (layout.pc v) layout.size := by
    change rspOf p = stackPtr initial - BitVec.ofNat 64 frame at rsp
    rw [rsp]
    exact stack_frame_codeApart stack capacity (fun a ha h => avoid a ha (.inl h))
      bound (fun j hj => inside j (by cases layout <;> simp_all [Header.bytesAt, Header.Layout.size] <;> omega))
  have lengthBound : layout.lengthSlot + 8 ≤ frame := by cases layout <;> simp_all [Header.Layout.lengthSlot, Header.Layout.countSlot] <;> omega
  have inputBound : layout.inputSlot + 8 ≤ frame := by cases layout <;> simp_all [Header.Layout.inputSlot, Header.Layout.countSlot] <;> omega
  obtain ⟨fuel, h, run, ready, _, result⟩ := Header.runAt layout (layout.pc v)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    inside p (supportedMachine_readyToStep state.machine) (Header.code layout v state.loaded)
    ⟨rip, write _ bound, apart _ bound, write _ lengthBound, apart _ lengthBound,
      write _ inputBound, apart _ inputBound⟩
  refine ⟨h, state.of_agrees (regions_avoid call) run ready result.agrees ?_ ?_, result⟩
  · intro c hc a ha
    have slots : c = .mem (rspOf p + BitVec.ofNat 64 layout.countSlot) 8 ∨
        c = .mem (rspOf p + BitVec.ofNat 64 layout.lengthSlot) 8 ∨
        c = .mem (rspOf p + BitVec.ofNat 64 layout.inputSlot) 8 := by
      cases layout <;> simp only [Header.effectAt, Effect.components,
        List.map_cons, List.map_nil, Write.component, Operand.component,
        List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false, reduceIte] at hc
      all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ha.elim | simp
    rcases slots with rfl | rfl | rfl
    all_goals refine ⟨Stack.region initial routine.minStackBytes, by simp [regions], ?_⟩
    all_goals change rspOf p = stackPtr initial - BitVec.ofNat 64 frame at rsp
    all_goals rw [rsp] at ha
    · exact stack_frame_contains stack capacity bound ha
    · exact stack_frame_contains stack capacity lengthBound ha
    · exact stack_frame_contains stack capacity inputBound ha
  · cases layout <;> simp [Header.effectAt, Effect.components]

theorem header [bindings : Bindings] (v : Wrapper.Variant) {initial p : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial p (regions (resetRoutine v) initial))
    (rsp : stackPtr p = stackPtr initial - 248#64)
    (rip : p.RIP = (resetRoutine v).entryAddress + 17#64) :
    ∃ h, ExecutionState initial h (regions (resetRoutine v) initial) ∧
      (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h := by
  have pc : (resetRoutine v).entryAddress + 17#64 = Header.Layout.reset.pc v := by cases v <;> rfl
  simpa [← pc, Header.effectAt, Header.effect, Header.Layout.size,
    Header.Layout.countSlot, Header.Layout.lengthSlot, Header.Layout.inputSlot,
    List.cons_append, List.nil_append, List.append_nil, reduceIte] using
    header_at .reset v machine call state rsp (rip.trans pc)
      (by rw [resetRoutine_stack]; decide) (by decide)

theorem initialize_state_at [bindings : Bindings] (v : Wrapper.Variant) {occ : Initialization} {routine : Routine} {frame : Nat} {initial h : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial h (regions routine initial))
    (rsp : stackPtr h = stackPtr initial - BitVec.ofNat 64 frame)
    (rip : h.RIP = (occ.layout v).start)
    (capacity : frame ≤ routine.minStackBytes)
    (fits : occ.bufferOffset + 104 ≤ frame)
    (base : occ.hashBase ≠ 4 →
      (.reg (occ.hashBase.setWidth 5) : Operand 64).read h = rspOf h + BitVec.ofNat 64 (occ.bufferOffset + 64) := by
        intro impossible; exact (impossible rfl).elim) :
    ∃ u, ExecutionState initial u (regions routine initial) ∧
      Initialize.Post (occ.layout v) (rspOf h + BitVec.ofNat 64 occ.bufferOffset) h u := by
  have stack := call.stack
  have avoid : (Stack.region initial routine.minStackBytes).Avoids
      (fun a => InProgram a ∨ InPageTables a) := by
    simpa only [InPageTables] using
      (call.separation.2 _ (by simp)).2
  obtain ⟨fuel, u, run, ready, _, result⟩ := Initialize.correct (returnBoundary initial)
    (occ.layout v)
    (valid_return_boundary machine call.stack call.returnAddress).2.2
    (Initialization.inside occ v) (rspOf h + BitVec.ofNat 64 occ.bufferOffset) h
    (supportedMachine_readyToStep state.machine) (Initialization.code occ state.loaded v)
    (initialize_pre_at v stack avoid state.allocated rsp rip capacity fits base)
  refine ⟨u, state.of_agrees (regions_avoid call) run ready result.frame ?_ ?_, result⟩
  · intro c hc a ha
    rw [Initialize.Layout.components] at hc
    rcases List.mem_append.mp hc with reg | hc
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp reg
      exact ha.elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial routine.minStackBytes, by simp [regions], ?_⟩
    all_goals change rspOf h = stackPtr initial - BitVec.ofNat 64 frame at rsp
    all_goals rw [rsp] at ha
    · apply stack_frame_contains stack (frame := frame) (offset := occ.bufferOffset + 64) (len := 32) capacity (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using ha
    · apply stack_frame_contains stack (frame := frame) (offset := occ.bufferOffset + 96) (len := 8) capacity (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using ha
    · apply stack_frame_contains stack (frame := frame) (offset := occ.bufferOffset + 63) (len := 1) capacity (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using ha
  · simp [Initialize.Layout.components]

theorem initialize_state [bindings : Bindings] (v : Wrapper.Variant) {occ : Initialization} {initial h : RamState}
    {inputs : Array Input} (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial h (regions (resetRoutine v) initial))
    (rsp : stackPtr h = stackPtr initial - 248#64)
    (rip : h.RIP = (occ.layout v).start)
    (allowed : occ ∈ [Initialization.resetInitial, .resetDiscarded, .resetOutput] := by simp)
    (base : occ.hashBase ≠ 4 →
      (.reg (occ.hashBase.setWidth 5) : Operand 64).read h = rspOf h + 64#64 := by
        intro impossible; exact (impossible rfl).elim) :
    ∃ u, ExecutionState initial u (regions (resetRoutine v) initial) ∧
      Initialize.Post (occ.layout v) (rspOf h) h u := by
  have offset : occ.bufferOffset = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
    rcases allowed with rfl | rfl | rfl <;> rfl
  simpa only [offset, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    initialize_state_at v machine call state rsp rip
      (by rw [resetRoutine_stack]; decide) (by rw [offset]; decide) (by simpa only [offset, Nat.zero_add] using base)

def Header.Layout.routine (layout : Header.Layout) (v : Wrapper.Variant) : Routine :=
  match layout, v with
  | .reset, _ => resetRoutine v
  | .finalize, .sha224 => sha224FinalizeIntoReset
  | .finalize, .sha256 => sha256FinalizeIntoReset
  | .trait, .sha224 => sha224TraitFinalizeIntoReset
  | .trait, .sha256 => sha256TraitFinalizeIntoReset

def Header.Layout.prologue : Header.Layout → Prologue.Layout
  | .reset => .six200
  | _ => .six312

def Header.Layout.initialization : Header.Layout → Initialization
  | .reset => .resetInitial
  | .finalize => .finalizeInitial
  | .trait => .traitInitial

def Header.Layout.frame (layout : Header.Layout) : Nat := layout.prologue.allocation + 48

theorem initialized_at [bindings : Bindings] {initial : RamState} {inputs : Array Input}
    (layout : Header.Layout) (v : Wrapper.Variant) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (layout.routine v) initial inputs) :
    ∃ p h u, ExecutionState initial u (regions (layout.routine v) initial) ∧
      (Prologue.effect (layout.routine v).entryAddress layout.prologue initial).Holds initial p ∧
      (Header.effectAt layout (layout.pc v) p).Holds p h ∧
      Initialize.Post (layout.initialization.layout v)
        (rspOf h + BitVec.ofNat 64 layout.initialization.bufferOffset) h u ∧
      stackPtr p = stackPtr initial - BitVec.ofNat 64 layout.frame ∧
      stackPtr h = stackPtr initial - BitVec.ofNat 64 layout.frame ∧
      stackPtr u = stackPtr initial - BitVec.ofNat 64 layout.frame := by
  have member : (layout.routine v, layout.prologue) ∈
      [(sha224Reset, Epilogue.Layout.six200), (sha256Reset, .six200),
       (sha224FinalizeIntoReset, .six312), (sha256FinalizeIntoReset, .six312),
       (sha224TraitFinalizeIntoReset, .six312), (sha256TraitFinalizeIntoReset, .six312)] := by
    cases layout <;> cases v <;> simp [Header.Layout.routine, Header.Layout.prologue, resetRoutine]
  obtain ⟨p, stateP, push, rspP, ripP⟩ := prologue machine call layout.prologue
    (by cases layout <;> rfl)
    (by cases layout <;> cases v <;> decide +kernel)
    (by simpa only [show (Prologue.bytes layout.prologue).length = layout.prologue.length by cases layout <;> rfl] using prologue256_inside _ _ member) (prologue256_code _ _ member call.programLoaded)
  have pc : (layout.routine v).entryAddress + BitVec.ofNat 64 layout.prologue.length = layout.pc v := by
    cases layout <;> cases v <;> decide +kernel
  obtain ⟨h, stateH, args⟩ := header_at layout v machine call stateP rspP (ripP.trans pc)
    (by cases layout <;> cases v <;> decide +kernel) (by cases layout <;> decide +kernel)
  have rspH : stackPtr h = stackPtr initial - BitVec.ofNat 64 layout.frame :=
    (args.agrees.read (n := 64) (r := 4)
      (by cases layout <;> simp [Header.effectAt, Effect.components])).trans rspP
  have ripH : h.RIP = (layout.initialization.layout v).start := by
    rw [args.rip]
    change layout.pc v + BitVec.ofNat 64 layout.size = _
    cases layout <;> cases v <;> decide +kernel
  obtain ⟨u, stateU, init⟩ := initialize_state_at v machine call stateH rspH ripH
    (by cases layout <;> cases v <;> decide +kernel)
    (by cases layout <;> decide +kernel)
    (by cases layout <;> intro impossible <;> exact (impossible rfl).elim)
  exact ⟨p, h, u, stateU, push, args, init, rspP, rspH, init.rsp.trans rspH⟩

theorem initialized [bindings : Bindings] {initial : RamState} {inputs : Array Input}
    (v : Wrapper.Variant) (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs) :
    ∃ p h u, ExecutionState initial u (regions (resetRoutine v) initial) ∧
      (Prologue.effect (resetRoutine v).entryAddress .six200 initial).Holds initial p ∧
      (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h ∧
      Initialize.Post (Initialization.resetInitial.layout v) (rspOf h) h u ∧
      stackPtr p = stackPtr initial - 248#64 ∧
      stackPtr h = stackPtr initial - 248#64 ∧ stackPtr u = stackPtr initial - 248#64 := by
  obtain ⟨p,h,u,state,push,args,init,rspP,rspH,rspU⟩ := initialized_at .reset v machine call
  have base : rspOf h + BitVec.ofNat 64 Header.Layout.reset.initialization.bufferOffset = rspOf h :=
    BitVec.add_zero _
  rw [base] at init
  have pc : Header.Layout.reset.pc v = (resetRoutine v).entryAddress + 17#64 := by cases v <;> rfl
  refine ⟨p,h,u,state,push,?_,init,rspP,rspH,rspU⟩
  simpa [pc, Header.effectAt, Header.effect, Header.Layout.size, Header.Layout.countSlot,
    Header.Layout.lengthSlot, Header.Layout.inputSlot] using args

def Header.Layout.countRegister : Header.Layout → BitVec 5
  | .reset => 12
  | .finalize => 15
  | .trait => 6

def Header.Layout.outputRegister : Header.Layout → BitVec 5
  | .trait => 12
  | _ => 13

set_option maxHeartbeats 800000 in
theorem initialized_arguments_at {layout : Header.Layout} {v : Wrapper.Variant}
    {initial p h u : RamState}
    (push : (Prologue.effect (layout.routine v).entryAddress layout.prologue initial).Holds initial p)
    (args : (Header.effectAt layout (layout.pc v) p).Holds p h)
    (init : Initialize.Post (layout.initialization.layout v)
      (rspOf h + BitVec.ofNat 64 layout.initialization.bufferOffset) h u) :
    memLoad u.external (rspOf u + BitVec.ofNat 64 layout.inputSlot) 64 = initial.regValue .rdi ∧
    memLoad u.external (rspOf u + BitVec.ofNat 64 layout.lengthSlot) 64 = initial.regValue .rdx ∧
    memLoad u.external (rspOf u + BitVec.ofNat 64 layout.countSlot) 64 = initial.regValue .r8 ∧
    (.reg layout.countRegister : Operand 64).read u = initial.regValue .rsi ∧
    (.reg layout.outputRegister : Operand 64).read u = initial.regValue .rcx ∧
    (layout ≠ .reset → u.regValue .rsi = initial.regValue .rsi) := by
  have rspH : rspOf h = rspOf p := args.agrees.read (n := 64) (r := 4)
    (by cases layout <;> simp [Header.effectAt, Effect.components])
  have rspU : rspOf u = rspOf h := init.rsp
  have saved (slot : Nat) (member : slot ∈ [layout.inputSlot, layout.lengthSlot, layout.countSlot]) :
      memLoad u.external (rspOf u + BitVec.ofNat 64 slot) 64 =
        memLoad h.external (rspOf p + BitVec.ofNat 64 slot) 64 := by
    rw [rspU, ← rspH]
    apply Common.Encoding.Serialize.read_mem_of_agrees init.frame
    intro i hi c hc covered
    rw [Initialize.Layout.components] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
      exact covered.elim
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc member
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j, hj, he⟩ := covered
    · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (layout.initialization.bufferOffset + 64))
        (c₂ := BitVec.ofNat 64 slot) (len₁ := 32) (len₂ := 8) ?_ (rspOf h) hj hi (by decide) ?_
      · rcases member with rfl | rfl | rfl <;> cases layout <;> unfold OffsetsApart <;> decide +kernel
      · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm
    · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (layout.initialization.bufferOffset + 96))
        (c₂ := BitVec.ofNat 64 slot) (len₁ := 8) (len₂ := 8) ?_ (rspOf h) hj hi (by decide) ?_
      · rcases member with rfl | rfl | rfl <;> cases layout <;> unfold OffsetsApart <;> decide +kernel
      · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm
    · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (layout.initialization.bufferOffset + 63))
        (c₂ := BitVec.ofNat 64 slot) (len₁ := 1) (len₂ := 8) ?_ (rspOf h) hj hi (by decide) ?_
      · rcases member with rfl | rfl | rfl <;> cases layout <;> unfold OffsetsApart <;> decide +kernel
      · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm
  have regs (r : BitVec 5)
      (member : r ∈ [layout.countRegister, layout.outputRegister] ∨
        (layout ≠ .reset ∧ r = 6)) :
      (.reg r : Operand 64).read u = (.reg r : Operand 64).read h := by
    apply init.frame.read
    cases layout <;> simp only [Header.Layout.countRegister, Header.Layout.outputRegister,
      List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals rcases member with (rfl | rfl) | ⟨hne, rfl⟩
    all_goals first | exact (hne rfl).elim | simp [Header.Layout.initialization, Initialize.Layout.components, Initialization.layout, Initialization.word, Initialization.temporary]
  have original (r : BitVec 5) (ne : r ≠ 4#5) :
      (.reg r : Operand 64).read p = (.reg r : Operand 64).read initial := by
    apply push.agrees.read
    cases layout <;> simpa [Header.Layout.prologue, Prologue.effect, Prologue.registers,
      Epilogue.Layout.six, Effect.components, List.zipIdx_cons, List.zipIdx_nil,
      Write.component, Operand.component] using ne
  have writes := args.writes
  have ptr : memLoad h.external (rspOf p + BitVec.ofNat 64 layout.inputSlot) 64 = p.regValue .rdi := by
    cases layout with
    | reset => exact writes.2.2.2.2.1
    | finalize => exact writes.2.2.2.2
    | trait => exact writes.2.2.2
  have len : memLoad h.external (rspOf p + BitVec.ofNat 64 layout.lengthSlot) 64 = p.regValue .rdx := by
    cases layout <;> exact writes.2.2.1
  have out : memLoad h.external (rspOf p + BitVec.ofNat 64 layout.countSlot) 64 = p.regValue .r8 := by
    cases layout <;> exact writes.1
  have output : (.reg layout.outputRegister : Operand 64).read h = p.regValue .rcx := by
    cases layout <;> exact writes.2.1
  have count : (.reg layout.countRegister : Operand 64).read h = p.regValue .rsi := by
    cases layout with
    | reset => exact writes.2.2.2.1
    | finalize => exact writes.2.2.2.1
    | trait => exact args.agrees.read (n := 64) (r := 6) (by simp [Header.effectAt, Effect.components])
  refine ⟨(saved _ (by simp)).trans (ptr.trans (original 7 (by decide))),
    (saved _ (by simp)).trans (len.trans (original 2 (by decide))),
    (saved _ (by simp)).trans (out.trans (original 8 (by decide))),
    (regs _ (.inl (by simp))).trans (count.trans (original 6 (by decide))),
    (regs _ (.inl (by simp))).trans (output.trans (original 1 (by decide))), ?_⟩
  intro nonreset
  exact (regs 6 (.inr ⟨nonreset, rfl⟩)).trans
    ((args.agrees.read (n := 64) (r := 6)
      (by cases layout <;> simp_all [Header.effectAt, Effect.components])).trans
      (original 6 (by decide)))

theorem initialized_arguments {v : Wrapper.Variant} {initial p h u : RamState}
    (push : (Prologue.effect (resetRoutine v).entryAddress .six200 initial).Holds initial p)
    (args : (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h)
    (init : Initialize.Post (Initialization.resetInitial.layout v) (rspOf h) h u) :
    memLoad u.external (rspOf u + 168#64) 64 = initial.regValue .rdi ∧
    memLoad u.external (rspOf u + 176#64) 64 = initial.regValue .rdx ∧
    memLoad u.external (rspOf u + 192#64) 64 = initial.regValue .r8 ∧
    u.regValue .r12 = initial.regValue .rsi ∧ u.regValue .r13 = initial.regValue .rcx := by
  have pc : (resetRoutine v).entryAddress + 17#64 = Header.Layout.reset.pc v := by cases v <;> rfl
  have argAt : (Header.effectAt .reset (Header.Layout.reset.pc v) p).Holds p h := by
    simpa [← pc, Header.effectAt, Header.effect, Header.Layout.size,
      Header.Layout.countSlot, Header.Layout.lengthSlot, Header.Layout.inputSlot,
      List.cons_append, List.nil_append, List.append_nil, reduceIte] using args
  have result := initialized_arguments_at (layout := .reset) (v := v) push argAt (by
    change Initialize.Post _ (rspOf h + 0#64) h u
    rw [show rspOf h + 0#64 = rspOf h from BitVec.add_zero _]
    exact init)
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1, result.2.2.2.2.1⟩

theorem initialized_table [Bindings] {v : Wrapper.Variant} {initial p h u : RamState}
    {inputs : Array Input} (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial u (regions (resetRoutine v) initial))
    (push : (Prologue.effect (resetRoutine v).entryAddress .six200 initial).Holds initial p)
    (args : (Header.effect ((resetRoutine v).entryAddress + 17#64) p).Holds p h)
    (init : Initialize.Post (Initialization.resetInitial.layout v) (rspOf h) h u)
    (rsp : stackPtr u = stackPtr initial - 248#64) :
    Absorb.Table.InputData (resetDiscarded v) ((resetDiscarded v).chunk.sp initial) inputs u ∧
    Absorb.Table.Separation (resetDiscarded v) initial u 720 inputs := by
  obtain ⟨pointer, length, _, _, _⟩ := initialized_arguments push args init
  have sp : (resetDiscarded v).chunk.sp initial = rspOf u := by
    rw [show rspOf u = stackPtr initial - 248#64 from rsp]
    cases v <;> rfl
  have ptr : memLoad u.external
      ((resetDiscarded v).chunk.sp initial + BitVec.ofNat 64 (resetDiscarded v).pointerSlot) 64 =
      initial.regValue .rdi := by
    rw [sp]
    exact pointer
  have len : memLoad u.external
      ((resetDiscarded v).chunk.sp initial + BitVec.ofNat 64 (resetDiscarded v).lengthSlot) 64 =
      initial.regValue .rdx := by
    rw [sp]
    exact length
  exact ⟨table_inputData call state.frame (resetDiscarded v) _ ptr len,
    by simpa only [resetRoutine_stack] using table_separation call (resetDiscarded v) ptr len⟩

theorem initialize_saved {v : Wrapper.Variant} {occ : Initialization} {s t : RamState}
    (init : Initialize.Post (occ.layout v) (rspOf s + BitVec.ofNat 64 occ.bufferOffset) s t)
    (slot : Nat) (apart : slot + 8 ≤ occ.bufferOffset + 63 ∨ occ.bufferOffset + 104 ≤ slot)
    (high : slot ≤ 360) :
    memLoad t.external (rspOf s + BitVec.ofNat 64 slot) 64 =
      memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 := by
  apply Common.Encoding.Serialize.read_mem_of_agrees init.frame
  intro i hi c hc covered
  rw [Initialize.Layout.components] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hc
    exact covered.elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨j,hj,he⟩ := covered
  · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (occ.bufferOffset + 64))
      (c₂ := BitVec.ofNat 64 slot) (len₁ := 32) (len₂ := 8) ?_ (rspOf s) hj hi (by decide) ?_
    · cases occ <;> simp only [Initialization.bufferOffset] at apart ⊢
      all_goals simp only [OffsetsApart, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod, Nat.reduceAdd]
      all_goals omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm
  · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (occ.bufferOffset + 96))
      (c₂ := BitVec.ofNat 64 slot) (len₁ := 8) (len₂ := 8) ?_ (rspOf s) hj hi (by decide) ?_
    · cases occ <;> simp only [Initialization.bufferOffset] at apart ⊢
      all_goals simp only [OffsetsApart, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod, Nat.reduceAdd]
      all_goals omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm
  · refine OffsetsApart.ne (c₁ := BitVec.ofNat 64 (occ.bufferOffset + 63))
      (c₂ := BitVec.ofNat 64 slot) (len₁ := 1) (len₂ := 8) ?_ (rspOf s) hj hi (by decide) ?_
    · cases occ <;> simp only [Initialization.bufferOffset] at apart ⊢
      all_goals simp only [OffsetsApart, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod, Nat.reduceAdd]
      all_goals omega
    · simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he.symm

theorem initialized_abi (layout : Header.Layout) {v : Wrapper.Variant} {initial p h u : RamState}
    (push : (Prologue.effect (layout.routine v).entryAddress layout.prologue initial).Holds initial p)
    (args : (Header.effectAt layout (layout.pc v) p).Holds p h)
    (init : Initialize.Post (layout.initialization.layout v) (rspOf h + BitVec.ofNat 64 layout.initialization.bufferOffset) h u) :
    (∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad u.external (rspOf u + BitVec.ofNat 64 (layout.prologue.allocation + offset)) 64 =
        (Operand.reg r : Operand 64).read initial) ∧
    memLoad u.external (rspOf u + BitVec.ofNat 64 layout.frame) 64 = memLoad initial.external (stackPtr initial) 64 := by
  have rspP : rspOf p = stackPtr initial - BitVec.ofNat 64 layout.frame := by
    have w := push.writes
    cases layout <;> exact w.2.2.2.2.2.2
  have rspH : rspOf h = rspOf p := args.agrees.read (n := 64) (r := 4)
    (by cases layout <;> simp [Header.effectAt, Effect.components])
  have rspU : rspOf u = rspOf p := init.rsp.trans rspH
  have saved (slot : Nat) (lo : layout.prologue.allocation ≤ slot) (upper : slot ≤ layout.frame) :
      memLoad u.external (rspOf u + BitVec.ofNat 64 slot) 64 =
        memLoad p.external (rspOf p + BitVec.ofNat 64 slot) 64 := by
    rw [rspU]
    apply Eq.trans (b := memLoad h.external (rspOf p + BitVec.ofNat 64 slot) 64)
    · rw [← rspH]
      exact initialize_saved init slot (by
        cases layout <;> simp only [Header.Layout.prologue, Epilogue.Layout.allocation] at lo
        all_goals right; change _ ≤ slot; dsimp [Header.Layout.initialization, Initialization.bufferOffset]; omega)
        (by cases layout <;> simp only [Header.Layout.frame, Header.Layout.prologue, Epilogue.Layout.allocation] at upper <;> omega)
    · apply Common.Encoding.Serialize.read_mem_of_agrees args.agrees
      intro i hi c hc covered
      cases layout
      all_goals simp only [Header.Layout.prologue, Header.Layout.frame, Epilogue.Layout.allocation] at lo upper
      all_goals simp only [Header.effectAt, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false, reduceIte] at hc
      all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      all_goals obtain ⟨j,hj,he⟩ := covered
      all_goals
        exact OffsetsApart.ne (by simp only [Header.Layout.countSlot, Header.Layout.lengthSlot, Header.Layout.inputSlot, OffsetsApart, Nat.reduceDiv, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod]; omega)
          (rspOf p) hj hi (by decide) he.symm
  constructor
  · intro r offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals rw [saved _ (by cases layout <;> decide) (by cases layout <;> decide), rspP]
    all_goals
      have w : memLoad p.external (rspOf initial - 8#64) 64 = initial.regValue .rbp ∧
          memLoad p.external (rspOf initial - 16#64) 64 = initial.regValue .r15 ∧
          memLoad p.external (rspOf initial - 24#64) 64 = initial.regValue .r14 ∧
          memLoad p.external (rspOf initial - 32#64) 64 = initial.regValue .r13 ∧
          memLoad p.external (rspOf initial - 40#64) 64 = initial.regValue .r12 ∧
          memLoad p.external (rspOf initial - 48#64) 64 = initial.regValue .rbx ∧
          rspOf p = rspOf initial - BitVec.ofNat 64 layout.frame := by cases layout <;> exact push.writes
      cases layout
      all_goals simp only [Header.Layout.prologue, Header.Layout.frame, Epilogue.Layout.allocation, BitVec.sub_eq_add_neg, BitVec.add_assoc] at w ⊢
      all_goals simp_all [rspOf, stackPtr]
      all_goals rfl
  · rw [saved layout.frame (by cases layout <;> decide) (Nat.le_refl _), rspP, BitVec.sub_add_cancel]
    apply Common.Encoding.Serialize.read_mem_of_agrees push.agrees
    intro i hi c hc covered
    have six : layout.prologue.six = true := by cases layout <;> rfl
    simp only [Effect.components, Prologue.effect, Operand.read_reg64, Int.reduceToNat,
      BitVec.ofNat_eq_ofNat, Fin.getElem_fin, Prologue.registers, six,
      ↓reduceIte, List.cons_append, List.nil_append, List.zipIdx_cons, Nat.zero_add,
      Nat.reduceAdd, List.zipIdx_nil, List.map_cons, Nat.mul_one, Nat.reduceMul,
      List.map_nil, List.append_eq, Write.component, Operand.component, Nat.reduceDiv,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,he⟩ := covered
    all_goals rw [BitVec.sub_eq_add_neg] at he
    · exact OffsetsApart.ne (c₁ := -8) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)
    · exact OffsetsApart.ne (c₁ := -16) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)
    · exact OffsetsApart.ne (c₁ := -24) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)
    · exact OffsetsApart.ne (c₁ := -32) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)
    · exact OffsetsApart.ne (c₁ := -40) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 8) (len₂ := 8) (c₂ := 0#64)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
        (by
          rw [show stackPtr initial + 0#64 = stackPtr initial from BitVec.add_zero _]
          exact he.symm)

theorem initialized_abi_after (layout : Header.Layout) {v : Wrapper.Variant}
    {initial p h u s : RamState} {cs : List Component}
    (push : (Prologue.effect (layout.routine v).entryAddress layout.prologue initial).Holds initial p)
    (args : (Header.effectAt layout (layout.pc v) p).Holds p h)
    (init : Initialize.Post (layout.initialization.layout v)
      (rspOf h + BitVec.ofNat 64 layout.initialization.bufferOffset) h u)
    (rsp : rspOf s = rspOf u) (frame : AgreesExcept cs u s)
    (below : ∀ c ∈ cs, ∀ a, c.Covers a →
      ∃ i < layout.prologue.allocation, a = rspOf u + BitVec.ofNat 64 i) :
    (∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32),(5,40)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.prologue.allocation + offset)) 64 =
        (Operand.reg r : Operand 64).read initial) ∧
    memLoad s.external (rspOf s + BitVec.ofNat 64 layout.frame) 64 =
      memLoad initial.external (stackPtr initial) 64 := by
  have abi := initialized_abi layout push args init
  have saved (slot : Nat) (low : layout.prologue.allocation ≤ slot) (high : slot ≤ layout.frame) :
      memLoad s.external (rspOf s + BitVec.ofNat 64 slot) 64 =
        memLoad u.external (rspOf u + BitVec.ofNat 64 slot) 64 := by
    rw [rsp]
    apply Common.Encoding.Serialize.read_mem_of_agrees frame
    intro i hi c hc cover
    obtain ⟨j,hj,he⟩ := below c hc _ cover
    refine OffsetsApart.ne (c₁ := 0#64) (len₁ := layout.prologue.allocation)
      (c₂ := BitVec.ofNat 64 slot) (len₂ := 8) ?_ (rspOf u) hj hi ?_ ?_
    · cases layout <;> simp only [Header.Layout.prologue, Header.Layout.frame,
        Epilogue.Layout.allocation] at low high ⊢
      all_goals simp only [OffsetsApart, BitVec.toNat_sub, Nat.reducePow, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reduceSub, Nat.add_mod_mod]
      all_goals omega
    · cases layout <;> decide +kernel
    · simpa only [BitVec.add_zero] using he.symm
  constructor
  · intro r offset member
    rw [saved _ (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
      all_goals cases layout <;> decide +kernel)]
    exact abi.1 r offset member
  · rw [saved _ (by cases layout <;> decide +kernel) (Nat.le_refl _)]
    exact abi.2

end Sha2.Proofs.Reset
