import P256.Proofs.Verifying.Combination.TableSetup.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.TableSetup

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines Preparation

def leftTableCopy1Site : CopyCallSite 768 :=
  ⟨0x6597, by decide, by decide +kernel,
    ⟨6560, 4656, 6240, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def leftTableCopy2Site : CopyCallSite 768 :=
  ⟨0x65ad, by decide, by decide +kernel,
    ⟨6560, 6240, 3888, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def leftTableCopy3Site : CopyCallSite 768 :=
  ⟨0x65c3, by decide, by decide +kernel,
    ⟨6560, 3888, 3120, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def leftTableCopy4Site : CopyCallSite 768 :=
  ⟨0x65d6, by decide, by decide +kernel,
    ⟨6560, 3120, 1584, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

theorem left_table_copies [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {values : Fin 8 → Projective}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x106584)
    (table : Table.TableAt t (stackPtr s - 4656) values)
    (input : t.regValue .r15 = stackPtr s - 6520)
    (target : t.regValue .r14 = 0x11c930)
    (temporary : t.regValue .rbp = stackPtr s - 4656) :
    ∃ fuel u, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x1065d9 ∧
      Table.TableAt u (stackPtr s - 1584) values ∧ CopyRegisters s u 4656 ∧
      CopiesKept s t u [6240, 3888, 3120, 1584] := by
  obtain ⟨n1, t1, run1, step1⟩ := copy_after_setup pre state
    leftTableCopy1Site 0x6584 leftTableCopy1Bytes leftTableCopy1Effect
    (by decide) (by decide +kernel) (leftTableCopy1_correct boundary pre.outerBoundary) rip
    (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component])).trans target,
        h.writes.2.1, h.writes.2.2.2.trans temporary,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) state.rsp (offset := 312) (by decide) (by decide))⟩)
  have r12_1 : t1.regValue .r15 = stackPtr s - 6520 :=
    step1.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component])).trans input)
  have r15_1 : t1.regValue .r14 = 0x11c930 :=
    step1.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component])).trans target)
  have r14_1 : t1.regValue .rbp = stackPtr s - 4656 :=
    step1.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [leftTableCopy1Effect, Effect.components, Write.component, Operand.component])).trans temporary)
  have r13_1 : t1.regValue .rbx = stackPtr s - 6240 :=
    step1.registers .rbx (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) state.rsp (offset := 312) (by decide) (by decide)))
  have table1 : Table.TableAt t1 (stackPtr s - 6240) values :=
    table.of_copy step1.bytes
  obtain ⟨n2, t2, run2, step2⟩ := copy_after_setup pre step1.toFrameState
    leftTableCopy2Site 0x659a leftTableCopy2Bytes leftTableCopy2Effect
    (by decide) (by decide +kernel) (leftTableCopy2_correct boundary pre.outerBoundary) step1.rip
    (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1,
        h.writes.2.1, h.writes.2.2.2.trans r13_1,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) step1.toFrameState.rsp (offset := 2664) (by decide) (by decide))⟩)
  have r12_2 : t2.regValue .r15 = stackPtr s - 6520 :=
    step2.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component])).trans r12_1)
  have r15_2 : t2.regValue .r14 = 0x11c930 :=
    step2.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1)
  have r14_2 : t2.regValue .rbp = stackPtr s - 4656 :=
    step2.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component])).trans r14_1)
  have r13_2 : t2.regValue .rbx = stackPtr s - 6240 :=
    step2.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [leftTableCopy2Effect, Effect.components, Write.component, Operand.component])).trans r13_1)
  have r5_2 : t2.regValue .r12 = stackPtr s - 3888 :=
    step2.registers .r12 (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step1.toFrameState.rsp (offset := 2664) (by decide) (by decide)))
  have table2 : Table.TableAt t2 (stackPtr s - 3888) values :=
    table1.of_copy step2.bytes
  obtain ⟨n3, t3, run3, step3⟩ := copy_after_setup pre step2.toFrameState
    leftTableCopy3Site 0x65b0 leftTableCopy3Bytes leftTableCopy3Effect
    (by decide) (by decide +kernel) (leftTableCopy3_correct boundary pre.outerBoundary) step2.rip
    (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2,
        h.writes.2.1, h.writes.2.2.2.trans r5_2,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) step2.toFrameState.rsp (offset := 3432) (by decide) (by decide))⟩)
  have r12_3 : t3.regValue .r15 = stackPtr s - 6520 :=
    step3.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r12_2)
  have r15_3 : t3.regValue .r14 = 0x11c930 :=
    step3.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2)
  have r14_3 : t3.regValue .rbp = stackPtr s - 4656 :=
    step3.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r14_2)
  have r13_3 : t3.regValue .rbx = stackPtr s - 6240 :=
    step3.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r13_2)
  have r5_3 : t3.regValue .r12 = stackPtr s - 3888 :=
    step3.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [leftTableCopy3Effect, Effect.components, Write.component, Operand.component])).trans r5_2)
  have r3_3 : t3.regValue .r13 = stackPtr s - 3120 :=
    step3.registers .r13 (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step2.toFrameState.rsp (offset := 3432) (by decide) (by decide)))
  have table3 : Table.TableAt t3 (stackPtr s - 3120) values :=
    table2.of_copy step3.bytes
  obtain ⟨n4, t4, run4, step4⟩ := copy_after_setup pre step3.toFrameState
    leftTableCopy4Site 0x65c6 leftTableCopy4Bytes leftTableCopy4Effect
    (by decide) (by decide +kernel) (leftTableCopy4_correct boundary pre.outerBoundary) step3.rip
    (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3,
        h.writes.2.1, h.writes.2.2.trans r3_3,
        h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step3.toFrameState.rsp (offset := 4968) (by decide) (by decide))⟩)
  have r12_4 : t4.regValue .r15 = stackPtr s - 6520 :=
    step4.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r12_3)
  have r15_4 : t4.regValue .r14 = 0x11c930 :=
    step4.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3)
  have r14_4 : t4.regValue .rbp = stackPtr s - 4656 :=
    step4.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r14_3)
  have r13_4 : t4.regValue .rbx = stackPtr s - 6240 :=
    step4.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r13_3)
  have r5_4 : t4.regValue .r12 = stackPtr s - 3888 :=
    step4.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r5_3)
  have r3_4 : t4.regValue .r13 = stackPtr s - 3120 :=
    step4.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [leftTableCopy4Effect, Effect.components, Write.component, Operand.component])).trans r3_3)
  have table4 : Table.TableAt t4 (stackPtr s - 1584) values :=
    table3.of_copy step4.bytes
  refine ⟨n1+n2+n3+n4, t4, ((run1.trans run2).trans run3).trans run4,
    step4.toFrameState, step4.rip, table4,
    ⟨r12_4, r15_4, r13_4, r5_4, r3_4, r14_4⟩, ?_⟩
  intro off len ho hl apart i hi
  exact (step4.kept off len ho hl (apart 1584 (by simp)) i hi).trans
    ((step3.kept off len ho hl (apart 3120 (by simp)) i hi).trans
      ((step2.kept off len ho hl (apart 3888 (by simp)) i hi).trans
        (step1.kept off len ho hl (apart 6240 (by simp)) i hi)))

end P256.Proofs.Verifying.Combination.TableSetup
