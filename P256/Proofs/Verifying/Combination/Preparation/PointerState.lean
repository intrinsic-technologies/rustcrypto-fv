import P256.Proofs.Verifying.Combination.Preparation.Pointer
import P256.Proofs.Verifying.Combination.Prologue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines

theorem pointer_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {ip : BitVec 64}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = ip) : PointerPre ip t := by
  refine ⟨rip, ?_, ?_⟩
  · intro k hk
    change MemWritable t (stackPtr t + BitVec.ofNat 64 (32 + 8*k)) 8
    rw [scalar_stack_address (frameOffset := 6552) state.rsp (by decide) (by omega)]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids (Stack.region s 8808) (by simp) a ha (.inr hp)) (by omega) (by omega)) state.allocated
  · intro k hk offset len bound
    change RangeApart (stackPtr t + BitVec.ofNat 64 (32 + 8*k)) 8 _ _
    exact stack_code (frameOffset := 6552) pre state (by decide) (by omega) bound

structure PointerState [Bindings] (s t : RamState) (pointerRegister : BitVec 5) : Prop
    extends FrameState s t 96 8808 6552 where
  cursorPointer : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496
  pointPointer : memLoad t.external (stackPtr s - 6496) 64 = stackPtr s - 5472
  input : t.regValue .rsi = stackPtr s - 6520
  output : t.regValue .rdi = stackPtr s - 4656
  temporary : (Operand.reg pointerRegister : Operand 64).read t = stackPtr s - 4656
  iterator : t.regValue .r15 = stackPtr s - 6520

theorem pointer_state [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {ip : BitVec 64} {r : BitVec 5}
    (pre : Pre s boundary) (state : State s t) (ready : ReadyToStep u)
    (effect : (pointerEffect ip r t).Holds t u) (hr : r ≠ 4)
    (rbx : t.regValue .rbx = stackPtr s - 5472) :
    PointerState s u r ∧ AgreesExcept [.mem (stackPtr s - 6496) 8, .mem (stackPtr s - 6480) 8,
      .mem (stackPtr s - 6488) 8, .mem (stackPtr s - 6520) 8,
      .reg 0, .reg r, .reg 15, .reg 6, .reg 7, .rip] t u := by
  have a16 : (Operand.reg 4 : Operand 64).read t + 32 = stackPtr s - 6520 :=
    scalar_stack_address (frameOffset := 6552) state.rsp (offset := 32) (by decide) (by decide)
  have a24 : (Operand.reg 4 : Operand 64).read t + 56 = stackPtr s - 6496 :=
    scalar_stack_address (frameOffset := 6552) state.rsp (offset := 56) (by decide) (by decide)
  have a32 : (Operand.reg 4 : Operand 64).read t + 64 = stackPtr s - 6488 :=
    scalar_stack_address (frameOffset := 6552) state.rsp (offset := 64) (by decide) (by decide)
  have a40 : (Operand.reg 4 : Operand 64).read t + 72 = stackPtr s - 6480 :=
    scalar_stack_address (frameOffset := 6552) state.rsp (offset := 72) (by decide) (by decide)
  have a3928 : (Operand.reg 4 : Operand 64).read t + 1896 = stackPtr s - 4656 :=
    scalar_stack_address (frameOffset := 6552) state.rsp (offset := 1896) (by decide) (by decide)
  have agrees : AgreesExcept [.mem (stackPtr s - 6496) 8, .mem (stackPtr s - 6480) 8,
      .mem (stackPtr s - 6488) 8, .mem (stackPtr s - 6520) 8,
      .reg 0, .reg r, .reg 15, .reg 6, .reg 7, .rip] t u := by
    have h := effect.agrees
    simp only [pointerEffect, Effect.components, List.map_cons, List.map_nil, Write.component_reg, Write.component_mem, List.cons_append, List.nil_append] at h
    change AgreesExcept [.mem ((Operand.reg 4 : Operand 64).read t + 56) 8,
      .mem ((Operand.reg 4 : Operand 64).read t + 72) 8,
      .mem ((Operand.reg 4 : Operand 64).read t + 64) 8,
      .mem ((Operand.reg 4 : Operand 64).read t + 32) 8,
      .reg 0, .reg r, .reg 15, .reg 6, .reg 7, .rip] t u at h
    simpa only [a16, a24, a32, a40] using h
  have stateU : State s u := by
    apply FrameState.after_effect pre (by decide) state ready agrees ?_ (by simp; exact Ne.symm hr)
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals exact ⟨workRegion s 8808, by simp, work_contains pre (by decide) (by decide) covered⟩
  have writes := effect.writes
  change (Operand.mem ((Operand.reg 4 : Operand 64).read t + 56) : Operand 64).read u = t.regValue .rbx ∧
    (Operand.mem ((Operand.reg 4 : Operand 64).read t + 72) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 4 : Operand 64).read t + 64) : Operand 64).read u = _ ∧
    (Operand.mem ((Operand.reg 4 : Operand 64).read t + 32) : Operand 64).read u = _ ∧
    u.regValue .rax = _ ∧ (Operand.reg r : Operand 64).read u = _ ∧ u.regValue .r15 = _ ∧ u.regValue .rsi = _ ∧ u.regValue .rdi = _ at writes
  rw [a16, a24, a32, a40, a3928] at writes
  exact ⟨⟨stateU, writes.2.2.2.1, writes.1.trans rbx, writes.2.2.2.2.2.2.2.1,
      writes.2.2.2.2.2.2.2.2, writes.2.2.2.2.2.1, writes.2.2.2.2.2.2.1⟩, agrees⟩


theorem table_pointer [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x106544)
    (rbx : t.regValue .rbx = stackPtr s - 5472) :
    ∃ fuel u, Advances boundary fuel t u ∧ PointerState s u 5 ∧ u.RIP = 0x10657d ∧
      AgreesExcept [.mem (stackPtr s - 6496) 8, .mem (stackPtr s - 6480) 8,
        .mem (stackPtr s - 6488) 8, .mem (stackPtr s - 6520) 8,
        .reg 0, .reg 5, .reg 15, .reg 6, .reg 7, .rip] t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := tablePointer_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6544 tablePointerBytes
      (by decide) (by decide +kernel)) (pointer_pre pre state rip)
  obtain ⟨stateU, agrees⟩ := pointer_state pre state ready effect (by decide) rbx
  exact ⟨fuel, u, run, stateU, effect.rip, agrees⟩


end P256.Proofs.Verifying.Combination.Preparation
