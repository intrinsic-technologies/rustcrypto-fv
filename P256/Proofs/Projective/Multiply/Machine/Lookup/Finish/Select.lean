import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareSelectX
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareSelectY
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareSelectZ
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareCopyBack
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.State

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Scanning

def selectNegatedXSite : BinaryCallSite 0x114380 128 :=
  { codeOffset := 0x490a
    disp := 0xfa71
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,344,248,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 144
    rightAbove := by decide
    rightEnd := by decide
    rightApart := by decide }

def selectNegatedYSite : BinaryCallSite 0x114380 128 :=
  { codeOffset := 0x4921
    disp := 0xfa5a
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,312,216,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 112
    rightAbove := by decide
    rightEnd := by decide
    rightApart := by decide }

def selectNegatedZSite : BinaryCallSite 0x114380 128 :=
  { codeOffset := 0x4938
    disp := 0xfa43
    codeBound := by decide
    bytes := by decide +kernel
    target := by decide +kernel
    entryLow := by decide
    entryProgram := inProgram_of_textOffset 0x14380 (by decide)
    layout := ⟨368,280,184,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
    stack := rfl
    outputSaved := by decide
    rightOffset := 80
    rightAbove := by decide
    rightEnd := by decide
    rightApart := by decide }

set_option maxHeartbeats 1600000 in
theorem select_negated [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {negative : Bool}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (state : NegatedState s t point negative) :
    ∃ fuel u, Advances boundary fuel t u ∧
      SelectedState s u (if negative then point.negate else point) := by
  obtain ⟨n1,t1,run1,f1,e1,mem1⟩ := registers state.toFrameState 0x48f1
    prepareSelectX0Bytes prepareSelectX0Effect (by decide) (by decide +kernel)
    (prepareSelectX0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareSelectX0Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareSelectX0Effect, Effect.components]) state.rip
  have w1 := e1.writes
  simp only [prepareSelectX0Effect, Write.AllHold] at w1
  have rbp1 : t1.regValue .rbp = if negative then 1 else 0 := by
    have h := w1.1
    change t1.regValue .rbp = ((t.regValue .rbp).setWidth 8).setWidth 64 at h
    rw [state.rbp] at h
    exact h.trans (by cases negative <;> rfl)
  have r121 : t1.regValue .r12 = stackPtr s - 248 :=
    w1.2.1.trans (stack_address state.rsp (by decide))
  have r141 : t1.regValue .r14 = stackPtr s - 344 :=
    (e1.agrees.read (n := 64) (r := 14) (by simp [prepareSelectX0Effect, Effect.components])).trans state.r14
  have r151 : t1.regValue .r15 = stackPtr s - 112 :=
    (e1.agrees.read (n := 64) (r := 15) (by simp [prepareSelectX0Effect, Effect.components])).trans state.r15
  have rbx1 : t1.regValue .rbx = stackPtr s - 80 :=
    (e1.agrees.read (n := 64) (r := 3) (by simp [prepareSelectX0Effect, Effect.components])).trans state.rbx
  have src1 : t1.regValue .rsi = stackPtr s - 344 := w1.2.2.2.2.1.trans state.r14
  have right1 : t1.regValue .rdx = stackPtr s - 144 :=
    w1.2.2.1.trans (stack_address state.rsp (by decide))
  have dst1 : t1.regValue .rdi = stackPtr s - 248 :=
    w1.2.2.2.1.trans (stack_address state.rsp (by decide))
  have choice1 : t1.regValue .rcx = if negative then 1 else 0 := by
    have h := w1.2.2.2.2.2
    change t1.regValue .rcx = ((((t.regValue .rbp).setWidth 8).setWidth 64).setWidth 32).setWidth 64 at h
    rw [state.rbp] at h
    exact h.trans (by cases negative <;> rfl)
  have point1 := projective_mem state.value mem1
  have negated1 := projective_mem state.negated mem1
  have output1 : (Operand.mem (stackPtr s - 152) : Operand 64).read t1 = s.regValue .rdi := by
    change memLoad t1.external _ _ = _
    rw [mem1]
    exact state.output
  obtain ⟨n2,t2,run2,f2,rip2,x2,regs2,mem2⟩ := select_stack pre f1 selectNegatedXSite
    e1.rip src1 right1 dst1 point1.1 negated1.1 choice1
  change MontgomeryAt t2 (stackPtr s - 248) _ at x2
  have rbp2 := (regs2 .rbp (by simp)).trans rbp1
  have r122 := (regs2 .r12 (by simp)).trans r121
  have r142 := (regs2 .r14 (by simp)).trans r141
  have r152 := (regs2 .r15 (by simp)).trans r151
  have rbx2 := (regs2 .rbx (by simp)).trans rbx1
  have point2 := point1.of_bytes_eq (mem2 344 96 (by decide) (by decide) (by decide))
  have negated2 := negated1.of_bytes_eq (mem2 144 96 (by decide) (by decide) (by decide))
  have output2 := (read_bytes (mem2 152 8 (by decide) (by decide) (by decide))).trans output1
  obtain ⟨n3,t3,run3,f3,e3,mem3⟩ := registers f2 0x490f
    prepareSelectY0Bytes prepareSelectY0Effect (by decide) (by decide +kernel)
    (prepareSelectY0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareSelectY0Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareSelectY0Effect, Effect.components]) rip2
  have w3 := e3.writes
  simp only [prepareSelectY0Effect, Write.AllHold] at w3
  have rbp3 : t3.regValue .rbp = if negative then 1 else 0 :=
    (e3.agrees.read (n := 64) (r := 5) (by simp [prepareSelectY0Effect, Effect.components])).trans rbp2
  have r123 : t3.regValue .r12 = stackPtr s - 248 :=
    (e3.agrees.read (n := 64) (r := 12) (by simp [prepareSelectY0Effect, Effect.components])).trans r122
  have r143 : t3.regValue .r14 = stackPtr s - 344 :=
    (e3.agrees.read (n := 64) (r := 14) (by simp [prepareSelectY0Effect, Effect.components])).trans r142
  have rbx3 : t3.regValue .rbx = stackPtr s - 80 :=
    (e3.agrees.read (n := 64) (r := 3) (by simp [prepareSelectY0Effect, Effect.components])).trans rbx2
  have src3 : t3.regValue .rsi = stackPtr s - 312 :=
    w3.2.1.trans (stack_address f2.rsp (by decide))
  have right3 : t3.regValue .rdx = stackPtr s - 112 := w3.2.2.1.trans r152
  have dst3 : t3.regValue .rdi = stackPtr s - 216 :=
    w3.1.trans (stack_address f2.rsp (by decide))
  have choice3 : t3.regValue .rcx = if negative then 1 else 0 := by
    have h := w3.2.2.2
    change t3.regValue .rcx = ((t2.regValue .rbp).setWidth 32).setWidth 64 at h
    rw [rbp2] at h
    exact h.trans (by cases negative <;> rfl)
  have point3 := projective_mem point2 mem3
  have negated3 := projective_mem negated2 mem3
  have left3 : MontgomeryAt t3 (stackPtr s - 312) point.y := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using point3.2.1
  have rightValue3 : MontgomeryAt t3 (stackPtr s - 112) point.negate.y := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using negated3.2.1
  have x3 := montgomery_mem x2 mem3
  have output3 : (Operand.mem (stackPtr s - 152) : Operand 64).read t3 = s.regValue .rdi := by
    change memLoad t3.external _ _ = _
    rw [mem3]
    exact output2
  obtain ⟨n4,t4,run4,f4,rip4,y4,regs4,mem4⟩ := select_stack pre f3 selectNegatedYSite
    e3.rip src3 right3 dst3 left3 rightValue3 choice3
  change MontgomeryAt t4 (stackPtr s - 216) _ at y4
  have rbp4 := (regs4 .rbp (by simp)).trans rbp3
  have r124 := (regs4 .r12 (by simp)).trans r123
  have r144 := (regs4 .r14 (by simp)).trans r143
  have rbx4 := (regs4 .rbx (by simp)).trans rbx3
  have point4 := point3.of_bytes_eq (mem4 344 96 (by decide) (by decide) (by decide))
  have negated4 := negated3.of_bytes_eq (mem4 144 96 (by decide) (by decide) (by decide))
  have x4 := Field.MontgomeryAt.of_bytes_eq x3 (mem4 248 32 (by decide) (by decide) (by decide))
  have output4 := (read_bytes (mem4 152 8 (by decide) (by decide) (by decide))).trans output3
  obtain ⟨n5,t5,run5,f5,e5,mem5⟩ := registers f4 0x4926
    prepareSelectZ0Bytes prepareSelectZ0Effect (by decide) (by decide +kernel)
    (prepareSelectZ0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareSelectZ0Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareSelectZ0Effect, Effect.components]) rip4
  have w5 := e5.writes
  simp only [prepareSelectZ0Effect, Write.AllHold] at w5
  have r125 : t5.regValue .r12 = stackPtr s - 248 :=
    (e5.agrees.read (n := 64) (r := 12) (by simp [prepareSelectZ0Effect, Effect.components])).trans r124
  have r145 : t5.regValue .r14 = stackPtr s - 344 :=
    (e5.agrees.read (n := 64) (r := 14) (by simp [prepareSelectZ0Effect, Effect.components])).trans r144
  have src5 : t5.regValue .rsi = stackPtr s - 280 :=
    w5.2.1.trans (stack_address f4.rsp (by decide))
  have right5 : t5.regValue .rdx = stackPtr s - 80 := w5.2.2.1.trans rbx4
  have dst5 : t5.regValue .rdi = stackPtr s - 184 :=
    w5.1.trans (stack_address f4.rsp (by decide))
  have choice5 : t5.regValue .rcx = if negative then 1 else 0 := by
    have h := w5.2.2.2
    change t5.regValue .rcx = ((t4.regValue .rbp).setWidth 32).setWidth 64 at h
    rw [rbp4] at h
    exact h.trans (by cases negative <;> rfl)
  have point5 := projective_mem point4 mem5
  have negated5 := projective_mem negated4 mem5
  have left5 : MontgomeryAt t5 (stackPtr s - 280) point.z := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using point5.2.2
  have rightValue5 : MontgomeryAt t5 (stackPtr s - 80) point.negate.z := by
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using negated5.2.2
  have x5 := montgomery_mem x4 mem5
  have y5 := montgomery_mem y4 mem5
  have output5 : (Operand.mem (stackPtr s - 152) : Operand 64).read t5 = s.regValue .rdi := by
    change memLoad t5.external _ _ = _
    rw [mem5]
    exact output4
  obtain ⟨n6,t6,run6,f6,rip6,z6,regs6,mem6⟩ := select_stack pre f5 selectNegatedZSite
    e5.rip src5 right5 dst5 left5 rightValue5 choice5
  change MontgomeryAt t6 (stackPtr s - 184) _ at z6
  have r126 := (regs6 .r12 (by simp)).trans r125
  have r146 := (regs6 .r14 (by simp)).trans r145
  have x6 := Field.MontgomeryAt.of_bytes_eq x5 (mem6 248 32 (by decide) (by decide) (by decide))
  have y6 := Field.MontgomeryAt.of_bytes_eq y5 (mem6 216 32 (by decide) (by decide) (by decide))
  have output6 := (read_bytes (mem6 152 8 (by decide) (by decide) (by decide))).trans output5
  obtain ⟨n7,t7,run7,f7,e7,mem7⟩ := registers f6 0x493d
    prepareCopyBack0Bytes prepareCopyBack0Effect (by decide) (by decide +kernel)
    (prepareCopyBack0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareCopyBack0Effect, Effect.components, Component.Covers])
    (by intro v; simp [prepareCopyBack0Effect, Effect.components]) rip6
  have w7 := e7.writes
  simp only [prepareCopyBack0Effect, Write.AllHold] at w7
  have r147 : t7.regValue .r14 = stackPtr s - 344 :=
    (e7.agrees.read (n := 64) (r := 14) (by simp [prepareCopyBack0Effect, Effect.components])).trans r146
  have src7 : t7.regValue .rsi = stackPtr s - 248 := w7.2.2.trans r126
  have dst7 : t7.regValue .rdi = stackPtr s - 344 := w7.2.1.trans r146
  have x7 := montgomery_mem x6 mem7
  have y7 := montgomery_mem y6 mem7
  have z7 := montgomery_mem z6 mem7
  have selected7 : ProjectiveAt t7 (stackPtr s - 248) (if negative then point.negate else point) := by
    apply selected_point x7
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using y7
    · simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] using z7
  have output7 : (Operand.mem (stackPtr s - 152) : Operand 64).read t7 = s.regValue .rdi := by
    change memLoad t7.external _ _ = _
    rw [mem7]
    exact output6
  have readable : MemReadable t7 (t7.regValue .rsi) 96 := by
    rw [src7]
    have h := stack_readable pre f7 (offset := 112) (len := 96) (by decide)
    exact (stack_address f7.rsp (by decide) : stackPtr t7 + 112 = stackPtr s - 248) ▸ h
  obtain ⟨u,run8,f8,rip8,point8,agr8⟩ := copy_to_stack pre f7
    0x4948 (by decide) (by decide +kernel) e7.rip
    344 (by decide) (by decide) dst7 w7.1 readable
    (stack_sources_disjoint pre (by decide) (by decide) src7 dst7 (by decide))
    (src7 ▸ selected7)
  refine ⟨n1+n2+n3+n4+n5+n6+n7+12,u,?_,f8,rip8,point8,?_,?_⟩
  · exact (((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8)
  · exact (agr8.read (n := 64) (r := 14) (by simp)).trans r147
  · apply Eq.trans (read_bytes (t := t7) ?_) output7
    intro i hi
    apply agr8.byte
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact id
    rintro ⟨j,hj,he⟩
    apply OffsetsApart.ne (c₁ := -344) (len₁ := 96) (c₂ := -152) (len₂ := 8)
      (by unfold OffsetsApart; decide +kernel) (stackPtr s) hj hi (by decide)
    simpa only [BitVec.sub_eq_add_neg, BitVec.reduceNeg] using he.symm

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
