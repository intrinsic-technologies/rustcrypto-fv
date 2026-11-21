import P256.Proofs.Projective.Double.Values
import P256.Proofs.Projective.Double.CrossTerms.Sites
import P256.Proofs.Field.Constants
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Field.Montgomery
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
import P256.Proofs.Field.Double
import P256.Proofs.Projective.Double.CrossTerms.CopyXY
import P256.Proofs.Projective.Double.CrossTerms.DoubleXY
import P256.Proofs.Projective.Double.CrossTerms.CopyXZ
import P256.Proofs.Projective.Double.CrossTerms.DoubleXZ
import P256.Proofs.Projective.Double.CrossTerms.BZZ
import P256.Proofs.Projective.Double.CrossTerms.Subtract
import P256.Proofs.Projective.Double.CrossTerms.DoubleDifference
import P256.Proofs.Projective.Double.CrossTerms.Triple

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CrossTerms

structure PairProductsAt (s t : RamState) (point : Projective) : Prop extends SquaresAt s t point where
  r14 : t.regValue .r14 = stackPtr s - 176
  xy2 : MontgomeryAt t (stackPtr s - 176) (values point).xy2
  xz : MontgomeryAt t (stackPtr s - 656) (point.x * point.z % P256.Spec.Operations.domain.p)
  xz2 : MontgomeryAt t (stackPtr s - 528) (values point).xz2

theorem pair_products_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x105dc3)
    (input : SquaresAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x105ea2 ∧ PairProductsAt s u point := by
  have point0 := input.pointAt
  have reg0_3 := input.rbx
  have mem0_104 : MontgomeryAt t (stackSlot s 104) (values point).xx := by
    rw [stackSlot_eq s (by decide)]
    exact input.xx
  have mem0_136 : MontgomeryAt t (stackSlot s 136) (values point).yy := by
    rw [stackSlot_eq s (by decide)]
    exact input.yy
  have mem0_168 : MontgomeryAt t (stackSlot s 168) (values point).zz := by
    rw [stackSlot_eq s (by decide)]
    exact input.zz
  obtain ⟨t1, run1, frame1, rip1, frameScratch1, arg1_15, arg1_6, arg1_2, arg1_7, word1_8, word1_16, word1_24, word1_32, word1_40, word1_48, word1_56, word1_64⟩ :=
    copyXY pre state rip reg0_3
  have reg1_3 : t1.regValue .rbx = s.regValue .rdi :=
    (frameScratch1.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg0_3
  have reg1_15 : t1.regValue .r15 = stackSlot s 72 := arg1_15
  have reg1_6 : t1.regValue .rsi = stackSlot s 40 := arg1_6
  have reg1_2 : t1.regValue .rdx = stackSlot s 8 := arg1_2
  have reg1_7 : t1.regValue .rdi = stackSlot s 72 := arg1_7
  have point1 := scratch_point pre frameScratch1 (by decide) point0
  have mem1_104 : MontgomeryAt t1 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch1 (slots_apart (by decide) (by decide) (by decide)) mem0_104
  have mem1_136 : MontgomeryAt t1 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch1 (slots_apart (by decide) (by decide) (by decide)) mem0_136
  have mem1_168 : MontgomeryAt t1 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch1 (slots_apart (by decide) (by decide) (by decide)) mem0_168
  have mem1_8 : MontgomeryAt t1 (stackSlot s 8) (point.y) := by
    apply copied (dst := 8) pre frame1 (by decide) point0.2.1
    · exact word1_8
    · rw [BitVec.add_assoc]
      exact word1_16
    · rw [BitVec.add_assoc]
      exact word1_24
    · rw [BitVec.add_assoc]
      exact word1_32
  have mem1_40 : MontgomeryAt t1 (stackSlot s 40) (point.x) := by
    apply copied (dst := 40) pre frame1 (by decide) point0.1
    · exact word1_40.trans (congrArg (fun addr => memLoad t.external addr 64) (BitVec.add_zero _))
    · exact word1_48
    · exact word1_56
    · exact word1_64
  have input1_6 : t1.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 := by
    have h := reg1_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input1_7 : t1.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg1_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input1_2 : t1.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have h := reg1_2
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value1_40 : MontgomeryAt t1 (stackPtr s - BitVec.ofNat 64 688) (point.x) := by
    have h := mem1_40
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value1_8 : MontgomeryAt t1 (stackPtr s - BitVec.ofNat 64 720) (point.y) := by
    have h := mem1_8
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n2, t2, run2, frame2, rip2, value2, regs2, bytes2, work2⟩ :=
    binary_call pre frame1 mulXYSite (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) rip1
      input1_6 input1_2 input1_7 value1_40 value1_8
  have point2 := point_of_stack pre (work_stack_frame pre work2) point1
  have reg2_3 : t2.regValue .rbx = s.regValue .rdi :=
    (regs2 .rbx (by decide)).trans reg1_3
  have reg2_15 : t2.regValue .r15 = stackSlot s 72 :=
    (regs2 .r15 (by decide)).trans reg1_15
  have mem2_104 : MontgomeryAt t2 (stackSlot s 104) ((values point).xx) := by
    have h := mem1_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes2 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem2_136 : MontgomeryAt t2 (stackSlot s 136) ((values point).yy) := by
    have h := mem1_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes2 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem2_168 : MontgomeryAt t2 (stackSlot s 168) ((values point).zz) := by
    have h := mem1_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes2 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem2_8 : MontgomeryAt t2 (stackSlot s 8) (point.y) := by
    have h := mem1_8
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes2 720 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem2_40 : MontgomeryAt t2 (stackSlot s 40) (point.x) := by
    have h := mem1_40
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes2 688 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem2_72 : MontgomeryAt t2 (stackSlot s 72) ((point.x*point.y) % P256.Spec.Operations.domain.p) := by
    rw [stackSlot_eq s (by decide)]
    exact value2
  obtain ⟨t3, run3, frame3, rip3, frameScratch3, arg3_14, arg3_7, arg3_6⟩ :=
    doubleXY pre frame2 rip2
  have reg3_3 : t3.regValue .rbx = s.regValue .rdi :=
    (frameScratch3.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg2_3
  have reg3_15 : t3.regValue .r15 = stackSlot s 72 :=
    (frameScratch3.read (n := 64) (r := 15) (by simp [scratchComponents])).trans reg2_15
  have reg3_14 : t3.regValue .r14 = stackSlot s 552 := arg3_14
  have reg3_7 : t3.regValue .rdi = stackSlot s 552 := arg3_7
  have reg3_6 : t3.regValue .rsi = stackSlot s 72 := arg3_6.trans reg2_15
  have point3 := scratch_point pre frameScratch3 (by decide) point2
  have mem3_104 : MontgomeryAt t3 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch3 (slots_apart (by decide) (by decide) (by decide)) mem2_104
  have mem3_136 : MontgomeryAt t3 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch3 (slots_apart (by decide) (by decide) (by decide)) mem2_136
  have mem3_168 : MontgomeryAt t3 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch3 (slots_apart (by decide) (by decide) (by decide)) mem2_168
  have mem3_72 : MontgomeryAt t3 (stackSlot s 72) ((point.x*point.y) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch3 (slots_apart (by decide) (by decide) (by decide)) mem2_72
  have input3_6 : t3.regValue .rsi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg3_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input3_7 : t3.regValue .rdi = stackPtr s - BitVec.ofNat 64 176 := by
    have h := reg3_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value3_72 : MontgomeryAt t3 (stackPtr s - BitVec.ofNat 64 656) ((point.x*point.y) % P256.Spec.Operations.domain.p) := by
    have h := mem3_72
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n4, t4, run4, frame4, rip4, value4, regs4, bytes4, work4⟩ :=
    unary_call pre frame3 (entry := 0x1137f0) (outputBytes := 32) (reserve := 16)
      (x := (point.x*point.y) % P256.Spec.Operations.domain.p) (resultAt := fun u ptr => MontgomeryAt u ptr (((point.x*point.y) % P256.Spec.Operations.domain.p+(point.x*point.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p))
      (⟨736, 656, 176, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ : StackCallLayout 1016 32 32 16)
      rfl (by decide) 0x5e2f 0xd9bc (by decide) (by decide +kernel)
      (by decide) (by decide) (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx) rip3 input3_6 input3_7 value3_72
  have point4 := point_of_stack pre (work_stack_frame pre work4) point3
  have reg4_3 : t4.regValue .rbx = s.regValue .rdi :=
    (regs4 .rbx (by decide)).trans reg3_3
  have reg4_15 : t4.regValue .r15 = stackSlot s 72 :=
    (regs4 .r15 (by decide)).trans reg3_15
  have reg4_14 : t4.regValue .r14 = stackSlot s 552 :=
    (regs4 .r14 (by decide)).trans reg3_14
  have mem4_104 : MontgomeryAt t4 (stackSlot s 104) ((values point).xx) := by
    have h := mem3_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes4 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem4_136 : MontgomeryAt t4 (stackSlot s 136) ((values point).yy) := by
    have h := mem3_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes4 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem4_168 : MontgomeryAt t4 (stackSlot s 168) ((values point).zz) := by
    have h := mem3_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes4 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem4_72 : MontgomeryAt t4 (stackSlot s 72) ((point.x*point.y) % P256.Spec.Operations.domain.p) := by
    have h := mem3_72
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes4 656 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem4_552 : MontgomeryAt t4 (stackSlot s 552) ((values point).xy2) := by
    rw [stackSlot_eq s (by decide)]
    exact value4
  obtain ⟨t5, run5, frame5, rip5, frameScratch5, arg5_15, arg5_6, arg5_2, arg5_7, word5_8, word5_16, word5_24, word5_32, word5_40, word5_48, word5_56, word5_64⟩ :=
    copyXZ pre frame4 rip4 reg4_3
  have reg5_3 : t5.regValue .rbx = s.regValue .rdi :=
    (frameScratch5.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg4_3
  have reg5_14 : t5.regValue .r14 = stackSlot s 552 :=
    (frameScratch5.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg4_14
  have reg5_15 : t5.regValue .r15 = stackSlot s 72 := arg5_15
  have reg5_6 : t5.regValue .rsi = stackSlot s 40 := arg5_6
  have reg5_2 : t5.regValue .rdx = stackSlot s 8 := arg5_2
  have reg5_7 : t5.regValue .rdi = stackSlot s 72 := arg5_7
  have point5 := scratch_point pre frameScratch5 (by decide) point4
  have mem5_104 : MontgomeryAt t5 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch5 (slots_apart (by decide) (by decide) (by decide)) mem4_104
  have mem5_136 : MontgomeryAt t5 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch5 (slots_apart (by decide) (by decide) (by decide)) mem4_136
  have mem5_168 : MontgomeryAt t5 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch5 (slots_apart (by decide) (by decide) (by decide)) mem4_168
  have mem5_72 : MontgomeryAt t5 (stackSlot s 72) ((point.x*point.y) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch5 (slots_apart (by decide) (by decide) (by decide)) mem4_72
  have mem5_552 : MontgomeryAt t5 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch5 (slots_apart (by decide) (by decide) (by decide)) mem4_552
  have mem5_8 : MontgomeryAt t5 (stackSlot s 8) (point.z) := by
    apply copied (dst := 8) pre frame5 (by decide) point4.2.2
    · exact word5_8
    · rw [BitVec.add_assoc]
      exact word5_16
    · rw [BitVec.add_assoc]
      exact word5_24
    · rw [BitVec.add_assoc]
      exact word5_32
  have mem5_40 : MontgomeryAt t5 (stackSlot s 40) (point.x) := by
    apply copied (dst := 40) pre frame5 (by decide) point4.1
    · exact word5_40.trans (congrArg (fun addr => memLoad t4.external addr 64) (BitVec.add_zero _))
    · exact word5_48
    · exact word5_56
    · exact word5_64
  have input5_6 : t5.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 := by
    have h := reg5_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input5_7 : t5.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg5_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input5_2 : t5.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have h := reg5_2
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value5_40 : MontgomeryAt t5 (stackPtr s - BitVec.ofNat 64 688) (point.x) := by
    have h := mem5_40
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value5_8 : MontgomeryAt t5 (stackPtr s - BitVec.ofNat 64 720) (point.z) := by
    have h := mem5_8
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n6, t6, run6, frame6, rip6, value6, regs6, bytes6, work6⟩ :=
    binary_call pre frame5 mulXZSite (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) rip5
      input5_6 input5_2 input5_7 value5_40 value5_8
  have point6 := point_of_stack pre (work_stack_frame pre work6) point5
  have reg6_3 : t6.regValue .rbx = s.regValue .rdi :=
    (regs6 .rbx (by decide)).trans reg5_3
  have reg6_15 : t6.regValue .r15 = stackSlot s 72 :=
    (regs6 .r15 (by decide)).trans reg5_15
  have reg6_14 : t6.regValue .r14 = stackSlot s 552 :=
    (regs6 .r14 (by decide)).trans reg5_14
  have mem6_104 : MontgomeryAt t6 (stackSlot s 104) ((values point).xx) := by
    have h := mem5_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_136 : MontgomeryAt t6 (stackSlot s 136) ((values point).yy) := by
    have h := mem5_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_168 : MontgomeryAt t6 (stackSlot s 168) ((values point).zz) := by
    have h := mem5_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_552 : MontgomeryAt t6 (stackSlot s 552) ((values point).xy2) := by
    have h := mem5_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_8 : MontgomeryAt t6 (stackSlot s 8) (point.z) := by
    have h := mem5_8
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 720 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_40 : MontgomeryAt t6 (stackSlot s 40) (point.x) := by
    have h := mem5_40
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes6 688 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem6_72 : MontgomeryAt t6 (stackSlot s 72) ((point.x*point.z) % P256.Spec.Operations.domain.p) := by
    rw [stackSlot_eq s (by decide)]
    exact value6
  obtain ⟨t7, run7, frame7, rip7, frameScratch7, arg7_7, arg7_6⟩ :=
    doubleXZ pre frame6 rip6
  have reg7_3 : t7.regValue .rbx = s.regValue .rdi :=
    (frameScratch7.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg6_3
  have reg7_15 : t7.regValue .r15 = stackSlot s 72 :=
    (frameScratch7.read (n := 64) (r := 15) (by simp [scratchComponents])).trans reg6_15
  have reg7_14 : t7.regValue .r14 = stackSlot s 552 :=
    (frameScratch7.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg6_14
  have reg7_7 : t7.regValue .rdi = stackSlot s 200 := arg7_7
  have reg7_6 : t7.regValue .rsi = stackSlot s 72 := arg7_6.trans reg6_15
  have point7 := scratch_point pre frameScratch7 (by decide) point6
  have mem7_104 : MontgomeryAt t7 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch7 (slots_apart (by decide) (by decide) (by decide)) mem6_104
  have mem7_136 : MontgomeryAt t7 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch7 (slots_apart (by decide) (by decide) (by decide)) mem6_136
  have mem7_168 : MontgomeryAt t7 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch7 (slots_apart (by decide) (by decide) (by decide)) mem6_168
  have mem7_72 : MontgomeryAt t7 (stackSlot s 72) ((point.x*point.z) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch7 (slots_apart (by decide) (by decide) (by decide)) mem6_72
  have mem7_552 : MontgomeryAt t7 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch7 (slots_apart (by decide) (by decide) (by decide)) mem6_552
  have input7_6 : t7.regValue .rsi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg7_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input7_7 : t7.regValue .rdi = stackPtr s - BitVec.ofNat 64 528 := by
    have h := reg7_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value7_72 : MontgomeryAt t7 (stackPtr s - BitVec.ofNat 64 656) ((point.x*point.z) % P256.Spec.Operations.domain.p) := by
    have h := mem7_72
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n8, t8, run8, frame8, rip8, value8, regs8, bytes8, work8⟩ :=
    unary_call pre frame7 (entry := 0x1137f0) (outputBytes := 32) (reserve := 16)
      (x := (point.x*point.z) % P256.Spec.Operations.domain.p) (resultAt := fun u ptr => MontgomeryAt u ptr (((point.x*point.z) % P256.Spec.Operations.domain.p+(point.x*point.z) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p))
      (⟨736, 656, 528, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ : StackCallLayout 1016 32 32 16)
      rfl (by decide) 0x5e9d 0xd94e (by decide) (by decide +kernel)
      (by decide) (by decide) (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx) rip7 input7_6 input7_7 value7_72
  have point8 := point_of_stack pre (work_stack_frame pre work8) point7
  have reg8_3 : t8.regValue .rbx = s.regValue .rdi :=
    (regs8 .rbx (by decide)).trans reg7_3
  have reg8_15 : t8.regValue .r15 = stackSlot s 72 :=
    (regs8 .r15 (by decide)).trans reg7_15
  have reg8_14 : t8.regValue .r14 = stackSlot s 552 :=
    (regs8 .r14 (by decide)).trans reg7_14
  have mem8_104 : MontgomeryAt t8 (stackSlot s 104) ((values point).xx) := by
    have h := mem7_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes8 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem8_136 : MontgomeryAt t8 (stackSlot s 136) ((values point).yy) := by
    have h := mem7_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes8 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem8_168 : MontgomeryAt t8 (stackSlot s 168) ((values point).zz) := by
    have h := mem7_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes8 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem8_72 : MontgomeryAt t8 (stackSlot s 72) ((point.x*point.z) % P256.Spec.Operations.domain.p) := by
    have h := mem7_72
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes8 656 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem8_552 : MontgomeryAt t8 (stackSlot s 552) ((values point).xy2) := by
    have h := mem7_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes8 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem8_200 : MontgomeryAt t8 (stackSlot s 200) ((values point).xz2) := by
    rw [stackSlot_eq s (by decide)]
    exact value8
  refine ⟨_, t8, ((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8,
    frame8, rip8, ⟨point8, reg8_3, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h := mem8_104
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem8_136
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem8_168
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := reg8_14
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem8_552
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem8_72
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem8_200
    rw [stackSlot_eq s (by decide)] at h
    exact h

end P256.Proofs.Projective.Double
