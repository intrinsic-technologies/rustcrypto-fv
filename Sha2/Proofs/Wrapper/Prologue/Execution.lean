import Sha2.Proofs.Common.Machine.Prologue
import Sha2.Proofs.Common.Machine.ExecutionState
import Sha2.Proofs.Common.Machine.FrameMemory

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem prologue_execution [bindings : Bindings] {initial : RamState} {n : Nat}
    (regions : Vector MemoryRegion n) (layout : Prologue.Layout) (six : layout.six = true)
    (reserve : Nat) (machine : SupportedMachine bindings initial)
    (stack : Stack.Valid initial reserve) (capacity : 48 ≤ reserve)
    (avoid : (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
    (stackMember : Stack.region initial reserve ∈ regions)
    (regionAvoid : ∀ region ∈ regions, region.Avoids InProgram)
    (loaded : ProgramLoaded initial) (df : DirectionFlagUnset initial)
    (ret : ValidReturnAddress initial) (p : BitVec 64) (entry : initial.RIP = p)
    (inside : BlockInProgram p layout.length)
    (code : CodeIn (codeRange p (Prologue.bytes layout)) initial) :
    ∃ s, ExecutionState initial s regions ∧ (Prologue.effect p layout initial).Holds initial s ∧
      stackPtr s = stackPtr initial - BitVec.ofNat 64 (layout.allocation + 48) ∧
      s.RIP = p + BitVec.ofNat 64 layout.length := by
  have write (offset : Nat) (low : offset ≤ reserve) (high : 8 ≤ offset) :
      MemWritable initial (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
    stack_valid_sub_writable stack (fun a ha h => avoid a ha (.inr h)) low (by omega) (by omega)
  have apart (offset : Nat) (low : offset ≤ reserve) (high : 8 ≤ offset) :
      RangeApart (stackPtr initial - BitVec.ofNat 64 offset) 8 p layout.length := by
    intro i hi j hj equal
    apply avoid _ (stackRegion_contains_sub stack.2.2.1 low high ⟨i, hi, rfl⟩)
    left
    rw [equal]
    exact inside j (Nat.le_of_lt hj)
  have pre : Prologue.Pre p layout initial := by
    refine ⟨entry, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 8 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 16 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 24 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 32 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 40 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using write 48 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 8 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 16 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 24 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 32 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 40 (by omega) (by omega)
    · simpa [BitVec.sub_eq_add_neg, rspOf, stackPtr, Operand.read, six] using apart 48 (by omega) (by omega)
  obtain ⟨fuel, s, run, ready, _, result⟩ := Prologue.run p layout
    (returnBoundary initial) (valid_return_boundary machine stack ret).2.2
    inside initial (supportedMachine_readyToStep machine)
    code pre
  have frame : MemoryWriteFrame initial s regions := by
    apply result.agrees.memoryWriteFrame
    intro c hc a ha
    simp only [Prologue.effect, Prologue.registers, six,
      ite_true, List.nil_append, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.append, List.cons_append, Effect.components,
      Write.component, Operand.component] at hc
    change c ∈ [Component.mem (rspOf initial - 8) 8,
      .mem (rspOf initial - 16) 8, .mem (rspOf initial - 24) 8,
      .mem (rspOf initial - 32) 8, .mem (rspOf initial - 40) 8, .mem (rspOf initial - 48) 8,
      .reg 4, .flags, .rip] at hc
    have rspeq : rspOf initial = stackPtr initial := by simp [rspOf, stackPtr, Operand.read]
    rw [rspeq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial reserve, stackMember, ?_⟩
    all_goals apply stackRegion_contains_sub stack.2.2.1 (by simp only; omega) (by simp only; omega) ha
  have state : ExecutionState initial s regions := by
    refine ⟨⟨fuel, run⟩, supportedMachine_of_ready_agrees machine ready result.agrees,
      ?_, result.agrees.grow, ?_, frame⟩
    · intro address byte program
      rw [frame address]
      · exact loaded address byte program
      · intro region member contains
        exact regionAvoid region member address contains ⟨byte, program⟩
    · exact result.agrees.directionFlagClear (by simp [Prologue.effect, Effect.components,
        Prologue.registers, six]) df
  refine ⟨s, state, result, ?_, result.rip⟩
  have hold := Write.allHold_iff.mp result.writes
    (⟨(.reg 4 : Operand 64), stackPtr initial - BitVec.ofNat 64 (layout.allocation + 48)⟩ : Write)
    (by simp [Prologue.effect, Epilogue.Layout.allocation, six]; rfl)
  exact hold


end Sha2.Proofs.Wrapper
