import P256.Proofs.Verifying.Combination.Preparation.Naf.FirstCopy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation.Naf

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Spec.Program.Routines TableSetup

def secondCopy1Site : CopyCallSite 272 :=
  ⟨0x66f9, by decide, by decide +kernel,
    ⟨6560, 6240, 3888, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def secondCopy2Site : CopyCallSite 272 :=
  ⟨0x6707, by decide, by decide +kernel,
    ⟨6560, 3888, 5472, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def secondCopy3Site : CopyCallSite 272 :=
  ⟨0x6715, by decide, by decide +kernel,
    ⟨6560, 5472, 4656, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

def secondCopy4Site : CopyCallSite 272 :=
  ⟨0x6728, by decide, by decide +kernel,
    ⟨6560, 4656, 4928, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩, rfl, by decide⟩

theorem second_copies [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {values : Nat}
    (pre : Pre s boundary) (state : State s t) (rip : t.RIP = 0x1066ee)
    (table : Combination.Naf.NafAt t (stackPtr s - 6240) values)
    (registers : NafCopyRegisters s t) :
    ∃ fuel u, Advances boundary fuel t u ∧ State s u ∧ u.RIP = 0x10672b ∧
      Combination.Naf.NafAt u (stackPtr s - 4928) values ∧ NafCopyRegisters s u ∧
      CopiesKept s t u [3888, 5472, 4656, 4928] 272 := by
  obtain ⟨n1, t1, run1, step1⟩ := copy_after_setup pre state
    secondCopy1Site 0x66ee secondCopy1Bytes secondCopy1Effect
    (by decide) (by decide +kernel) (secondCopy1_correct boundary pre.outerBoundary) rip
    (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.target,
        h.writes.1, h.writes.2.2.trans registers.temporary,
        h.writes.2.1.trans registers.first⟩)
  have r12_1 : t1.regValue .rbp = stackPtr s - 6528 :=
    step1.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.input)
  have r15_1 : t1.regValue .r14 = 0x11c930 :=
    step1.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.target)
  have r14_1 : t1.regValue .rbx = stackPtr s - 6240 :=
    step1.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.temporary)
  have r13_1 : t1.regValue .r12 = stackPtr s - 3888 :=
    step1.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.first)
  have r5_1 : t1.regValue .r13 = stackPtr s - 5472 :=
    step1.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.second)
  have r3_1 : t1.regValue .r15 = stackPtr s - 4656 :=
    step1.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [secondCopy1Effect, Effect.components, Write.component, Operand.component])).trans registers.third)
  have table1 : Combination.Naf.NafAt t1 (stackPtr s - 3888) values :=
    table.of_copy step1.bytes
  obtain ⟨n2, t2, run2, step2⟩ := copy_after_setup pre step1.toFrameState
    secondCopy2Site 0x66fc secondCopy2Bytes secondCopy2Effect
    (by decide) (by decide +kernel) (secondCopy2_correct boundary pre.outerBoundary) step1.rip
    (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1,
        h.writes.1, h.writes.2.2.trans r13_1,
        h.writes.2.1.trans r5_1⟩)
  have r12_2 : t2.regValue .rbp = stackPtr s - 6528 :=
    step2.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r12_1)
  have r15_2 : t2.regValue .r14 = 0x11c930 :=
    step2.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r15_1)
  have r14_2 : t2.regValue .rbx = stackPtr s - 6240 :=
    step2.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r14_1)
  have r13_2 : t2.regValue .r12 = stackPtr s - 3888 :=
    step2.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r13_1)
  have r5_2 : t2.regValue .r13 = stackPtr s - 5472 :=
    step2.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r5_1)
  have r3_2 : t2.regValue .r15 = stackPtr s - 4656 :=
    step2.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [secondCopy2Effect, Effect.components, Write.component, Operand.component])).trans r3_1)
  have table2 : Combination.Naf.NafAt t2 (stackPtr s - 5472) values :=
    table1.of_copy step2.bytes
  obtain ⟨n3, t3, run3, step3⟩ := copy_after_setup pre step2.toFrameState
    secondCopy3Site 0x670a secondCopy3Bytes secondCopy3Effect
    (by decide) (by decide +kernel) (secondCopy3_correct boundary pre.outerBoundary) step2.rip
    (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2,
        h.writes.1, h.writes.2.2.trans r5_2,
        h.writes.2.1.trans r3_2⟩)
  have r12_3 : t3.regValue .rbp = stackPtr s - 6528 :=
    step3.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r12_2)
  have r15_3 : t3.regValue .r14 = 0x11c930 :=
    step3.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r15_2)
  have r14_3 : t3.regValue .rbx = stackPtr s - 6240 :=
    step3.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r14_2)
  have r13_3 : t3.regValue .r12 = stackPtr s - 3888 :=
    step3.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r13_2)
  have r5_3 : t3.regValue .r13 = stackPtr s - 5472 :=
    step3.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r5_2)
  have r3_3 : t3.regValue .r15 = stackPtr s - 4656 :=
    step3.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [secondCopy3Effect, Effect.components, Write.component, Operand.component])).trans r3_2)
  have table3 : Combination.Naf.NafAt t3 (stackPtr s - 4656) values :=
    table2.of_copy step3.bytes
  obtain ⟨n4, t4, run4, step4⟩ := copy_after_setup pre step3.toFrameState
    secondCopy4Site 0x6718 secondCopy4Bytes secondCopy4Effect
    (by decide) (by decide +kernel) (secondCopy4_correct boundary pre.outerBoundary) step3.rip
    (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component, Component.Covers])
    (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component]) rfl (by
      intro a h
      exact ⟨(h.agrees.read (n := 64) (r := 14) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3,
        h.writes.2.1, h.writes.2.2.trans r3_3,
        h.writes.1.trans (scalar_stack_address (frameOffset := 6552) step3.toFrameState.rsp (offset := 1624) (by decide) (by decide))⟩)
  have r12_4 : t4.regValue .rbp = stackPtr s - 6528 :=
    step4.registers .rbp (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 5) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r12_3)
  have r15_4 : t4.regValue .r14 = 0x11c930 :=
    step4.registers .r14 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 14) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r15_3)
  have r14_4 : t4.regValue .rbx = stackPtr s - 6240 :=
    step4.registers .rbx (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 3) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r14_3)
  have r13_4 : t4.regValue .r12 = stackPtr s - 3888 :=
    step4.registers .r12 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 12) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r13_3)
  have r5_4 : t4.regValue .r13 = stackPtr s - 5472 :=
    step4.registers .r13 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 13) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r5_3)
  have r3_4 : t4.regValue .r15 = stackPtr s - 4656 :=
    step4.registers .r15 (by simp) _ (by
      intro a h
      exact (h.agrees.read (n := 64) (r := 15) (by simp [secondCopy4Effect, Effect.components, Write.component, Operand.component])).trans r3_3)
  have table4 : Combination.Naf.NafAt t4 (stackPtr s - 4928) values :=
    table3.of_copy step4.bytes
  refine ⟨n1+n2+n3+n4, t4, ((run1.trans run2).trans run3).trans run4,
    step4.toFrameState, step4.rip, table4,
    ⟨r12_4, r15_4, r13_4, r5_4, r3_4, r14_4⟩, ?_⟩
  intro off len ho hl apart i hi
  exact (step4.kept off len ho hl (apart 4928 (by simp)) i hi).trans
    ((step3.kept off len ho hl (apart 4656 (by simp)) i hi).trans
      ((step2.kept off len ho hl (apart 5472 (by simp)) i hi).trans
        (step1.kept off len ho hl (apart 3888 (by simp)) i hi)))

end P256.Proofs.Verifying.Combination.Preparation.Naf
