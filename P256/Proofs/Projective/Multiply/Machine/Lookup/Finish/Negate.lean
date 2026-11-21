import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Sign
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.CopyStack
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.CopyY
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.CopyZ
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.CopyX
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareSignSave
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareNegArgs
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.PrepareZBase
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Projective.Multiply.Machine.Lookup.Call.Choice
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Correct

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Scanning

set_option maxHeartbeats 1200000 in
theorem negate [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (hdigit : (s.regValue .rdx).setWidth 8 = digit) (state : SignState s t table digit) :
    ∃ fuel u, Advances boundary fuel t u ∧
      NegatedState s u (selectMagnitude table (digitMagnitude digit)) digit.msb := by
  let point := selectMagnitude table (digitMagnitude digit)
  have point0 : ProjectiveAt t (stackPtr s-344) point := state.value
  have r140 := state.r14
  have output0 := state.output
  obtain ⟨t1,run1,f1,rip1,choice1,agr1⟩ := extract_sign pre state.toFrameState state.rip state.digit hdigit
  have mem1 : t1.external = t.external := agr1.external (by simp [Component.Covers])
  have point1 := projective_mem point0 mem1
  have r141 := (agr1.read (n := 64) (r := 14) (by simp)).trans r140
  change t1.regValue .r14 = _ at r141
  have output1 : (Operand.mem (stackPtr s-152) : Operand 64).read t1 = s.regValue .rdi := by
    change memLoad t1.external _ _ = _
    rw [mem1]; exact output0
  obtain ⟨n2,t2,run2,f2,rip2,rax2,regs2,mem2⟩ := choice_call pre f1
    0x4837 0x14834 (by decide) (by decide +kernel) (by decide +kernel) rip1
  have choice2 : t2.regValue .rax = if digit.msb then 1 else 0 := by
    rw [rax2,choice1]; cases digit.msb <;> rfl
  have r142 := (regs2 .r14 (by simp)).trans r141
  have point2 := point1.of_bytes_eq (mem2 344 96 (by decide) (by decide))
  have output2 := (read_bytes (mem2 152 8 (by decide) (by decide))).trans output1
  obtain ⟨n3,t3,run3,f3,e3,mem3⟩ := registers f2 0x483c
    prepareSignSave0Bytes prepareSignSave0Effect (by decide) (by decide +kernel)
    (prepareSignSave0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareSignSave0Effect,Effect.components,Component.Covers])
    (by intro v; simp [prepareSignSave0Effect,Effect.components]) rip2
  have r143 := (e3.agrees.read (n := 64) (r := 14) (by simp [prepareSignSave0Effect,Effect.components])).trans r142
  change t3.regValue .r14 = _ at r143
  have point3 := projective_mem point2 mem3
  have output3 : (Operand.mem (stackPtr s-152) : Operand 64).read t3 = s.regValue .rdi := by
    change memLoad t3.external _ _ = _
    rw [mem3]; exact output2
  have rbp3 : t3.regValue .rbp = if digit.msb then 1 else 0 := by
    have h := e3.writes
    change t3.regValue .rbp = ((t2.regValue .rax).setWidth 32).setWidth 64 at h
    rw [choice2] at h
    exact h.trans (by cases digit.msb <;> rfl)
  obtain ⟨n4,t4,run4,f4,rip4,value4,agr4⟩ := execute_copy (entryOffset := 0x483e) (src := 48) (dst := 112) (x := point.y) pre f3
    (copyY_correct boundary pre.outerBoundary) (by decide) (by decide +kernel)
    (by decide) (by decide) (by unfold OffsetsApart; decide +kernel) e3.rip
    (by
      change MontgomeryAt t3 (stackPtr s-312) point.y
      simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using point3.2.1)
  have r144 := (agr4.read (n := 64) (r := 14) (by simp)).trans r143
  change t4.regValue .r14 = _ at r144
  have rbp4 := (agr4.read (n := 64) (r := 5) (by simp)).trans rbp3
  change t4.regValue .rbp = _ at rbp4
  have point4 := point3.of_bytes_eq (copy_bytes (offset := 344) (len := 96) agr4 (by unfold OffsetsApart; decide +kernel) (by decide))
  have output4 := (read_bytes (copy_bytes (offset := 152) (len := 8) agr4 (by unfold OffsetsApart; decide +kernel) (by decide))).trans output3
  have y4 : MontgomeryAt t4 (stackPtr s-248) point.y := value4
  obtain ⟨n5,t5,run5,f5,e5,mem5⟩ := registers f4 0x486c
    prepareNegArgs0Bytes prepareNegArgs0Effect (by decide) (by decide +kernel)
    (prepareNegArgs0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareNegArgs0Effect,Effect.components,Component.Covers])
    (by intro v; simp [prepareNegArgs0Effect,Effect.components]) rip4
  have r145 := (e5.agrees.read (n := 64) (r := 14) (by simp [prepareNegArgs0Effect,Effect.components])).trans r144
  change t5.regValue .r14 = _ at r145
  have rbp5 := (e5.agrees.read (n := 64) (r := 5) (by simp [prepareNegArgs0Effect,Effect.components])).trans rbp4
  change t5.regValue .rbp = _ at rbp5
  have point5 := projective_mem point4 mem5
  have output5 : (Operand.mem (stackPtr s-152) : Operand 64).read t5 = s.regValue .rdi := by
    change memLoad t5.external _ _ = _
    rw [mem5]; exact output4
  have y5 := montgomery_mem y4 mem5
  have w5 := e5.writes
  change t5.regValue .r15 = stackPtr t4+248 ∧ t5.regValue .rsi = stackPtr t4+112 ∧
    t5.regValue .rdi = stackPtr t4+248 at w5
  have a5 : stackPtr t4+248 = stackPtr s-112 := stack_address f4.rsp (by decide)
  have b5 : stackPtr t4+112 = stackPtr s-248 := stack_address f4.rsp (by decide)
  have r155 := w5.1.trans a5
  have src5 := w5.2.1.trans b5
  have dst5 := w5.2.2.trans a5
  let layout : StackCallLayout 496 32 32 24 :=
    ⟨368,248,112,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  obtain ⟨n6,t6,run6,f6,rip6,value6,regs6,mem6,_⟩ := Program.FieldCall.unary_call (frameOffset := 360) (entry := 0x1137d0) (x := point.y) (resultAt := fun u a => MontgomeryAt u a point.negate.y) pre f5 layout rfl (by decide)
    0x487c 0xef4f (by decide) (by decide +kernel) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x137d0 (by decide))
    (fun v hp hx => by
      obtain ⟨u,result,value⟩ := Negate.negate_correct (value := point.y) hp hx
      refine ⟨u,result,?_⟩
      simpa only [Projective.negate, Standards.SECG.ECC.Curve.fieldSub, Nat.zero_mod, Nat.zero_add,
        Nat.mod_eq_of_lt hx.1] using value) e5.rip src5 dst5 y5
  have neg6 : MontgomeryAt t6 (stackPtr s-112) point.negate.y := value6
  have r146 := (regs6 .r14 (by simp)).trans r145
  have rbp6 := (regs6 .rbp (by simp)).trans rbp5
  have r156 := (regs6 .r15 (by simp)).trans r155
  have point6 := point5.of_bytes_eq (mem6 344 96 (by decide) (by decide) (by decide))
  have output6 := (read_bytes (mem6 152 8 (by decide) (by decide) (by decide))).trans output5
  obtain ⟨n7,t7,run7,f7,e7,mem7⟩ := registers f6 0x4881
    prepareZBase0Bytes prepareZBase0Effect (by decide) (by decide +kernel)
    (prepareZBase0_correct boundary pre.outerBoundary)
    (by intro v; simp [prepareZBase0Effect,Effect.components,Component.Covers])
    (by intro v; simp [prepareZBase0Effect,Effect.components]) rip6
  have r147 := (e7.agrees.read (n := 64) (r := 14) (by simp [prepareZBase0Effect,Effect.components])).trans r146
  change t7.regValue .r14 = _ at r147
  have rbp7 := (e7.agrees.read (n := 64) (r := 5) (by simp [prepareZBase0Effect,Effect.components])).trans rbp6
  change t7.regValue .rbp = _ at rbp7
  have r157 := (e7.agrees.read (n := 64) (r := 15) (by simp [prepareZBase0Effect,Effect.components])).trans r156
  change t7.regValue .r15 = _ at r157
  have point7 := projective_mem point6 mem7
  have output7 : (Operand.mem (stackPtr s-152) : Operand 64).read t7 = s.regValue .rdi := by
    change memLoad t7.external _ _ = _
    rw [mem7]; exact output6
  have neg7 := montgomery_mem neg6 mem7
  have rbx7 : t7.regValue .rbx = stackPtr s-80 := by
    have h := e7.writes
    change t7.regValue .rbx = stackPtr t6+280 at h
    exact h.trans (stack_address f6.rsp (by decide))
  obtain ⟨n8,t8,run8,f8,rip8,value8,agr8⟩ := execute_copy (entryOffset := 0x4889) (src := 80) (dst := 280) (x := point.z) pre f7
    (copyZ_correct boundary pre.outerBoundary) (by decide) (by decide +kernel)
    (by decide) (by decide) (by unfold OffsetsApart; decide +kernel) e7.rip
    (by
      change MontgomeryAt t7 (stackPtr s-280) point.z
      simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using point7.2.2)
  have r148 := (agr8.read (n := 64) (r := 14) (by simp)).trans r147
  change t8.regValue .r14 = _ at r148
  have rbp8 := (agr8.read (n := 64) (r := 5) (by simp)).trans rbp7
  change t8.regValue .rbp = _ at rbp8
  have r158 := (agr8.read (n := 64) (r := 15) (by simp)).trans r157
  change t8.regValue .r15 = _ at r158
  have rbx8 := (agr8.read (n := 64) (r := 3) (by simp)).trans rbx7
  change t8.regValue .rbx = _ at rbx8
  have point8 := point7.of_bytes_eq (copy_bytes (offset := 344) (len := 96) agr8 (by unfold OffsetsApart; decide +kernel) (by decide))
  have output8 := (read_bytes (copy_bytes (offset := 152) (len := 8) agr8 (by unfold OffsetsApart; decide +kernel) (by decide))).trans output7
  have neg8 := Field.MontgomeryAt.of_bytes_eq neg7 (copy_bytes (offset := 112) (len := 32) agr8 (by unfold OffsetsApart; decide +kernel) (by decide))
  have z8 : MontgomeryAt t8 (stackPtr s-80) point.z := value8
  obtain ⟨n9,t9,run9,f9,rip9,value9,agr9⟩ := execute_copy (entryOffset := 0x48bd) (src := 16) (dst := 216) (x := point.x) pre f8
    (copyX_correct boundary pre.outerBoundary) (by decide) (by decide +kernel)
    (by decide) (by decide) (by unfold OffsetsApart; decide +kernel) rip8
    (point8.1)
  have r149 := (agr9.read (n := 64) (r := 14) (by simp)).trans r148
  change t9.regValue .r14 = _ at r149
  have rbp9 := (agr9.read (n := 64) (r := 5) (by simp)).trans rbp8
  change t9.regValue .rbp = _ at rbp9
  have r159 := (agr9.read (n := 64) (r := 15) (by simp)).trans r158
  change t9.regValue .r15 = _ at r159
  have rbx9 := (agr9.read (n := 64) (r := 3) (by simp)).trans rbx8
  change t9.regValue .rbx = _ at rbx9
  have point9 := point8.of_bytes_eq (copy_bytes (offset := 344) (len := 96) agr9 (by unfold OffsetsApart; decide +kernel) (by decide))
  have output9 := (read_bytes (copy_bytes (offset := 152) (len := 8) agr9 (by unfold OffsetsApart; decide +kernel) (by decide))).trans output8
  have neg9 := Field.MontgomeryAt.of_bytes_eq neg8 (copy_bytes (offset := 112) (len := 32) agr9 (by unfold OffsetsApart; decide +kernel) (by decide))
  have z9 := Field.MontgomeryAt.of_bytes_eq z8 (copy_bytes (offset := 80) (len := 32) agr9 (by unfold OffsetsApart; decide +kernel) (by decide))
  refine ⟨3+n2+n3+n4+n5+n6+n7+n8+n9,t9,?_,f9,rip9,point9,?_,rbp9,r149,r159,rbx9,output9⟩
  · exact (((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9
  · refine ⟨value9,?_,?_⟩
    · simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using neg9
    · change MontgomeryAt t9 (stackPtr s-144+64) point.z
      simpa only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd] using z9

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
