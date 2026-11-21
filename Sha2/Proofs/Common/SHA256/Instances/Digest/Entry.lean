import Sha2.Proofs.Common.SHA256.Instances.Digest.Code
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def regions (initial : RamState) (v : Wrapper.Variant := .sha256) : Vector MemoryRegion 2 :=
  #v[OneShot.outputRegion (routine v) initial, Stack.region initial 784]

theorem prologue {v : Wrapper.Variant} [bindings : Bindings] {initial : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data) :
    ∃ s, ExecutionState initial s (regions initial v) ∧
      (Prologue.effect (Segment.prologue.pc v) .five272 initial).Holds initial s ∧
      stackPtr s = stackPtr initial - 312 ∧ s.RIP = (Segment.header.pc v) := by
  have avoid : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have write (offset : Nat) (low : offset ≤ 784) (high : 8 ≤ offset) :
      MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
    stack_valid_sub_writable call.stack (fun a ha h => avoid a ha (.inr h)) low (by omega) (by (try dsimp only [routine]); decide +kernel)
  have apart (offset : Nat) (low : offset ≤ 784) (high : 8 ≤ offset) :
      RangeApart (stackPtr initial - BitVec.ofNat 64 offset) 8 (Segment.prologue.pc v) 16 := by
    intro i hi j hj equal
    apply avoid _ (stackRegion_contains_sub call.stack.2.2.1 low high ⟨i, hi, rfl⟩)
    left
    rw [equal]
    exact Segment.inside .prologue (v := v) j (Nat.le_of_lt hj)
  have pre : Prologue.Pre (Segment.prologue.pc v) .five272 initial := by
    refine ⟨call.entry, ?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using write 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using write 16 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using write 24 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using write 32 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using write 40 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using apart 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using apart 16 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using apart 24 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using apart 32 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, Epilogue.Layout.length, Epilogue.Layout.six] using apart 40 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
  obtain ⟨fuel, s, run, ready, _, result⟩ := Prologue.run (Segment.prologue.pc v) .five272
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (Segment.inside .prologue (v := v)) initial (supportedMachine_readyToStep machine)
    (Segment.code .prologue (v := v) call.programLoaded) pre
  have frame : MemoryWriteFrame initial s (regions initial v) := by
    apply result.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [Prologue.effect, Prologue.registers, Epilogue.Layout.six,
      Bool.false_eq_true, ite_false, List.nil_append, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.append, List.cons_append, Effect.components,
      Write.component, Operand.component] at hc
    change c ∈ [Component.mem (rspOf initial - 8) 8,
      .mem (rspOf initial - 16) 8, .mem (rspOf initial - 24) 8,
      .mem (rspOf initial - 32) 8, .mem (rspOf initial - 40) 8,
      .reg 4, .flags, .rip] at hc
    have rspeq : rspOf initial = stackPtr initial := by simp [rspOf, stackPtr, Operand.read]
    rw [rspeq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial 784, by simp [regions], ?_⟩
    all_goals apply stackRegion_contains_sub call.stack.2.2.1 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
  have state : ExecutionState initial s (regions initial v) := by
    refine ⟨⟨fuel, run⟩, supportedMachine_of_ready_agrees machine ready result.agrees,
      ?_, result.agrees.grow, ?_, frame⟩
    · intro address byte program
      rw [frame address]
      · exact call.programLoaded address byte program
      · intro region member contains
        have mem : region ∈ [OneShot.outputRegion (routine v) initial, Stack.region initial 784] := by
          simpa [regions] using member
        exact (call.separation.2 region mem).2 address contains (.inl ⟨byte, program⟩)
    · exact result.agrees.directionFlagClear (by simp [Prologue.effect, Effect.components,
        Prologue.registers, Epilogue.Layout.six]) call.directionFlagUnset
  have nextPC : (Segment.prologue.pc v) + 16 = Segment.header.pc v := by
    cases v <;> decide +kernel
  refine ⟨s, state, result, ?_, result.rip.trans nextPC⟩
  have hold := Write.allHold_iff.mp result.writes
    (⟨(.reg 4 : Operand 64), stackPtr initial - 312⟩ : Write)
    (by simp [Prologue.effect, Epilogue.Layout.allocation, Epilogue.Layout.six]; rfl)
  exact hold

theorem header {v : Wrapper.Variant} [Bindings] {initial s : RamState} {data : ByteArray}
    (machine : SupportedMachine ‹Bindings› initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (state : ExecutionState initial s (regions initial v))
    (rip : s.RIP = (Segment.header.pc v)) :
    ∃ t, ExecutionState initial t (regions initial v) ∧
      (Blocks.Digest.Header.effect (Segment.header.pc v) s).Holds s t := by
  obtain ⟨fuel, t, run, ready, _, result⟩ := Blocks.Digest.Header.run (Segment.header.pc v)
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (Segment.inside .header (v := v)) s (supportedMachine_readyToStep state.machine)
    (Segment.code .header (v := v) state.loaded) rip
  refine ⟨t, state.of_agrees ?_ run ready result.agrees ?_ ?_, result⟩
  · intro region member a ha h
    have mem : region ∈ [OneShot.outputRegion (routine v) initial,
        Stack.region initial (routine v).minStackBytes] := by
      have stackSize : (routine v).minStackBytes = 784 := by cases v <;> rfl
      simpa only [regions, List.mem_cons, List.mem_singleton, Vector.mem_mk, List.mem_toArray, stackSize] using member
    exact (call.separation.2 region mem).2 a ha (.inl h)
  · intro c hc a ha
    have member : c ∈ [.reg 3, .reg 14, .reg 6, .rip] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact ha.elim
  · simp [Blocks.Digest.Header.effect, Effect.components, Write.component, Operand.component]

end Sha2.Proofs.Common.SHA256.Instances.Digest
