import P256.Proofs.Projective.Multiply.Machine.Radix.Prologue
import P256.Proofs.Projective.Multiply.Machine.Radix.Memory
import P256.Proofs.Projective.Multiply.Machine.Radix.Code

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

theorem initialize_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (rip : t.RIP = 0x10b728) : InitializePre t := by
  refine ⟨rip,?_,?_,?_⟩
  · have w := state.stack_writable pre (offset := 72) (len := 1) (by decide)
      (by decide) (by decide)
    exact ⟨w.low, w.mem, w.tables⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact state.stack_writable pre (by decide) (by decide) (by decide)
  · intro i n hi pc len bound
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with h|h|h|h|h|h|h|h|h
    all_goals cases h
    all_goals exact state.stack_code pre (by decide) (by decide) bound

theorem initialize_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t)
    (rip : t.RIP = 0x10b728) :
    ∃ u fuel, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x10b77a ∧
      (initializeEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := initialize_block boundary pre.outerBoundary
    t state.ready (programText_slice (programLoaded_codeIn (state.loaded pre))
      0xb728 _ (by decide) initializeBytes_code) (initialize_pre pre state rip)
  refine ⟨u,fuel,run,?_,effect.rip,effect⟩
  apply state.after_stack pre ready effect.agrees
  · intro c hc hm
    simp only [initializeEffect,Effect.components,List.map_cons,List.map_nil,List.append_nil,
      List.cons_append,List.nil_append,Write.component,Operand.component,Nat.reduceDiv,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp_all [Component.isMem,registers]
  · intro p n hc
    simp only [initializeEffect,Effect.components,List.map_cons,List.map_nil,List.append_nil,
      List.cons_append,List.nil_append,Write.component,Operand.component,Nat.reduceDiv,
      List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,false_or,Component.mem.injEq] at hc
    rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    all_goals refine ⟨_,?_,?_,ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)⟩
    all_goals decide
  · exact (effect.agrees.read (n := 64) (r := 4) (by simp [initializeEffect,Effect.components])).trans state.rsp

end P256.Proofs.Projective.Multiply.Machine.Radix
