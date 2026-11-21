import P256.Proofs.Verifying.Combination.TableSetup.Copy
import P256.Proofs.Verifying.Combination.Preparation.Naf.Setup
import P256.Proofs.Verifying.Combination.Naf.Output

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines TableSetup

structure NafCopyRegisters (s t : RamState) : Prop where
  input : t.regValue .rbp = stackPtr s - 6528
  target : t.regValue .r14 = 0x11c930
  first : t.regValue .r12 = stackPtr s - 3888
  second : t.regValue .r13 = stackPtr s - 5472
  third : t.regValue .r15 = stackPtr s - 4656
  temporary : t.regValue .rbx = stackPtr s - 6240

def firstCopy1Site : CopyCallSite 272 :=
  ⟨0x669c, by decide, by decide +kernel,
    ⟨6560, 6240, 3888, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def firstCopy2Site : CopyCallSite 272 :=
  ⟨0x66b2, by decide, by decide +kernel,
    ⟨6560, 3888, 5472, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def firstCopy3Site : CopyCallSite 272 :=
  ⟨0x66c8, by decide, by decide +kernel,
    ⟨6560, 5472, 4656, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def firstCopy4Site : CopyCallSite 272 :=
  ⟨0x66db, by decide, by decide +kernel,
    ⟨6560, 4656, 5200, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

theorem first_copies [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {values : Nat}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x106689)
    (table : Combination.Naf.NafAt t (stackPtr s - 6240) values)
    (input : t.regValue .rbp = stackPtr s - 6528)
    (target : t.regValue .r14 = 0x11c930)
    (temporary : t.regValue .rbx = stackPtr s - 6240) :
    ∃ fuel u, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x1066de ∧
      Combination.Naf.NafAt u (stackPtr s - 5200) values ∧ NafCopyRegisters s u ∧
      CopiesKept s t u [3888, 5472, 4656, 5200] 272 := by
  obtain ⟨n1, t1, run1, step1⟩ := copy_after_setup pre state
    firstCopy1Site 0x6689 firstCopy1Bytes firstCopy1Effect
    (by decide) (by decide +kernel) (firstCopy1_correct boundary pre.outerBoundary) rip
    (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component])).trans target,
        h.writes.2.1, h.writes.2.2.2.trans temporary,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) state.rsp (offset := 2664) (by decide) (by decide))⟩)
  have r12_1 : t1.regValue .rbp = stackPtr s - 6528 :=
    step1.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component])).trans input)
  have r15_1 : t1.regValue .r14 = 0x11c930 :=
    step1.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component])).trans target)
  have r14_1 : t1.regValue .rbx = stackPtr s - 6240 :=
    step1.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [firstCopy1Effect, Effect.components, Write.component, Operand.component])).trans temporary)
  have r13_1 : t1.regValue .r12 = stackPtr s - 3888 :=
    step1.registers .r12 (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) state.rsp (offset := 2664) (by decide) (by decide)))
  have table1 : Combination.Naf.NafAt t1 (stackPtr s - 3888) values :=
    table.of_copy step1.bytes
  obtain ⟨n2, t2, run2, step2⟩ := copy_after_setup pre step1.toFrameState
    firstCopy2Site 0x669f firstCopy2Bytes firstCopy2Effect
    (by decide) (by decide +kernel) (firstCopy2_correct boundary pre.outerBoundary) step1.rip
    (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1,
        h.writes.2.1, h.writes.2.2.2.trans r13_1,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) step1.toFrameState.rsp (offset := 1080) (by decide) (by decide))⟩)
  have r12_2 : t2.regValue .rbp = stackPtr s - 6528 :=
    step2.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component])).trans r12_1)
  have r15_2 : t2.regValue .r14 = 0x11c930 :=
    step2.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1)
  have r14_2 : t2.regValue .rbx = stackPtr s - 6240 :=
    step2.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component])).trans r14_1)
  have r13_2 : t2.regValue .r12 = stackPtr s - 3888 :=
    step2.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [firstCopy2Effect, Effect.components, Write.component, Operand.component])).trans r13_1)
  have r5_2 : t2.regValue .r13 = stackPtr s - 5472 :=
    step2.registers .r13 (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step1.toFrameState.rsp (offset := 1080) (by decide) (by decide)))
  have table2 : Combination.Naf.NafAt t2 (stackPtr s - 5472) values :=
    table1.of_copy step2.bytes
  obtain ⟨n3, t3, run3, step3⟩ := copy_after_setup pre step2.toFrameState
    firstCopy3Site 0x66b5 firstCopy3Bytes firstCopy3Effect
    (by decide) (by decide +kernel) (firstCopy3_correct boundary pre.outerBoundary) step2.rip
    (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2,
        h.writes.2.1, h.writes.2.2.2.trans r5_2,
        h.writes.2.2.1.trans (scalar_stack_address (frameOffset := 6552) step2.toFrameState.rsp (offset := 1896) (by decide) (by decide))⟩)
  have r12_3 : t3.regValue .rbp = stackPtr s - 6528 :=
    step3.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r12_2)
  have r15_3 : t3.regValue .r14 = 0x11c930 :=
    step3.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2)
  have r14_3 : t3.regValue .rbx = stackPtr s - 6240 :=
    step3.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r14_2)
  have r13_3 : t3.regValue .r12 = stackPtr s - 3888 :=
    step3.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r13_2)
  have r5_3 : t3.regValue .r13 = stackPtr s - 5472 :=
    step3.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [firstCopy3Effect, Effect.components, Write.component, Operand.component])).trans r5_2)
  have r3_3 : t3.regValue .r15 = stackPtr s - 4656 :=
    step3.registers .r15 (by simp) _ (by
      intro a h
      exact h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step2.toFrameState.rsp (offset := 1896) (by decide) (by decide)))
  have table3 : Combination.Naf.NafAt t3 (stackPtr s - 4656) values :=
    table2.of_copy step3.bytes
  obtain ⟨n4, t4, run4, step4⟩ := copy_after_setup pre step3.toFrameState
    firstCopy4Site 0x66cb firstCopy4Bytes firstCopy4Effect
    (by decide) (by decide +kernel) (firstCopy4_correct boundary pre.outerBoundary) step3.rip
    (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3,
        h.writes.2.1, h.writes.2.2.trans r3_3,
        h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step3.toFrameState.rsp (offset := 1352) (by decide) (by decide))⟩)
  have r12_4 : t4.regValue .rbp = stackPtr s - 6528 :=
    step4.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r12_3)
  have r15_4 : t4.regValue .r14 = 0x11c930 :=
    step4.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3)
  have r14_4 : t4.regValue .rbx = stackPtr s - 6240 :=
    step4.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r14_3)
  have r13_4 : t4.regValue .r12 = stackPtr s - 3888 :=
    step4.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r13_3)
  have r5_4 : t4.regValue .r13 = stackPtr s - 5472 :=
    step4.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r5_3)
  have r3_4 : t4.regValue .r15 = stackPtr s - 4656 :=
    step4.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [firstCopy4Effect, Effect.components, Write.component, Operand.component])).trans r3_3)
  have table4 : Combination.Naf.NafAt t4 (stackPtr s - 5200) values :=
    table3.of_copy step4.bytes
  refine ⟨n1+n2+n3+n4, t4, ((run1.trans run2).trans run3).trans run4,
    step4.toFrameState, step4.rip, table4,
    ⟨r12_4, r15_4, r13_4, r5_4, r3_4, r14_4⟩, ?_⟩
  intro off len ho hl apart i hi
  exact (step4.kept off len ho hl (apart 5200 (by simp)) i hi).trans
    ((step3.kept off len ho hl (apart 4656 (by simp)) i hi).trans
      ((step2.kept off len ho hl (apart 5472 (by simp)) i hi).trans
        (step1.kept off len ho hl (apart 3888 (by simp)) i hi)))

end P256.Proofs.Verifying.Combination.Preparation.Naf
