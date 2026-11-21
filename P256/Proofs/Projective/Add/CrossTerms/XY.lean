import P256.Proofs.Projective.Add.CrossTerms.Blocks

set_option autoImplicit false


namespace P256.Proofs.Projective.Add.CrossTerms

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Call
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem xy_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left right : Projective}
    (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (state : FrameState s t 96 920 632) (rip : t.RIP = 0x10531f)
    (input : ProductsAt s t left right)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105480 ∧ ProductsAt s u left right ∧
      MontgomeryAt u (stackPtr s - 400) (values left right).xy := by
  obtain ⟨n1, t1, run1, frame1, rip1, value1, agrees1⟩ :=
    Copy.execute_stack pre state (entryOffset := 0x531f) (offset := 40)
      (leftXY0_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre state (by decide) rfl rip (by change MemReadable t (t.regValue .rbx + 0) 32; rw [input.rbx]; exact Copy.point_readable pre state .rdi (by simp) (by decide)) (by change RangeApart (stackPtr t + 40) 32 (t.regValue .rbx + 0) 32; rw [input.rbx]; exact Copy.stack_point_apart pre state .rdi (by simp) (by decide) (by decide))) (by change MontgomeryAt t (t.regValue .rbx + 0) left.x; rw [input.rbx]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using input.leftPoint.1)
  have mem1 := copy_stack_frame pre state (by decide) agrees1
  have r3_1 : t1.regValue .rbx = s.regValue .rdi := (agrees1.read (n := 64) (r := 3) (by simp [Copy32.components])).trans input.rbx
  have r5_1 : t1.regValue .rbp = stackPtr s - 528 := (agrees1.read (n := 64) (r := 5) (by simp [Copy32.components])).trans input.rbp
  have r14_1 : t1.regValue .r14 = s.regValue .rsi := (agrees1.read (n := 64) (r := 14) (by simp [Copy32.components])).trans input.r14
  have v560_1 : MontgomeryAt t1 (stackPtr s - 560) (values left right).xx := copy_stack_value pre state (by decide) (by decide) (by decide) (by decide) agrees1 input.xx
  have v464_1 : MontgomeryAt t1 (stackPtr s - 464) (values left right).yy := copy_stack_value pre state (by decide) (by decide) (by decide) (by decide) agrees1 input.yy
  have v528_1 : MontgomeryAt t1 (stackPtr s - 528) (values left right).zz := copy_stack_value pre state (by decide) (by decide) (by decide) (by decide) agrees1 input.zz
  have left1 : ProjectiveAt t1 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem1 input.leftPoint
  have right1 : ProjectiveAt t1 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem1 input.rightPoint
  have v592_1 : MontgomeryAt t1 (stackPtr s - 592) left.x := by
    have h := value1
    change MontgomeryAt t1 (stackPtr t + 40) left.x at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide)] at h
    exact h
  obtain ⟨n2, t2, run2, frame2, rip2, value2, agrees2⟩ :=
    Copy.execute_stack pre frame1 (entryOffset := 0x5342) (offset := 8)
      (leftXY1_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre frame1 (by decide) rfl rip1 (by change MemReadable t1 (t1.regValue .rbx + 32) 32; rw [r3_1]; exact Copy.point_readable pre frame1 .rdi (by simp) (by decide)) (by change RangeApart (stackPtr t1 + 8) 32 (t1.regValue .rbx + 32) 32; rw [r3_1]; exact Copy.stack_point_apart pre frame1 .rdi (by simp) (by decide) (by decide))) (by change MontgomeryAt t1 (t1.regValue .rbx + 32) left.y; rw [r3_1]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using left1.2.1)
  have mem2 := copy_stack_frame pre frame1 (by decide) agrees2
  have r3_2 : t2.regValue .rbx = s.regValue .rdi := (agrees2.read (n := 64) (r := 3) (by simp [Copy32.components])).trans r3_1
  have r5_2 : t2.regValue .rbp = stackPtr s - 528 := (agrees2.read (n := 64) (r := 5) (by simp [Copy32.components])).trans r5_1
  have r14_2 : t2.regValue .r14 = s.regValue .rsi := (agrees2.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r14_1
  have v560_2 : MontgomeryAt t2 (stackPtr s - 560) (values left right).xx := copy_stack_value pre frame1 (by decide) (by decide) (by decide) (by decide) agrees2 v560_1
  have v464_2 : MontgomeryAt t2 (stackPtr s - 464) (values left right).yy := copy_stack_value pre frame1 (by decide) (by decide) (by decide) (by decide) agrees2 v464_1
  have v528_2 : MontgomeryAt t2 (stackPtr s - 528) (values left right).zz := copy_stack_value pre frame1 (by decide) (by decide) (by decide) (by decide) agrees2 v528_1
  have v592_2 : MontgomeryAt t2 (stackPtr s - 592) left.x := copy_stack_value pre frame1 (by decide) (by decide) (by decide) (by decide) agrees2 v592_1
  have left2 : ProjectiveAt t2 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem2 left1
  have right2 : ProjectiveAt t2 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem2 right1
  have v624_2 : MontgomeryAt t2 (stackPtr s - 624) left.y := by
    have h := value2
    change MontgomeryAt t2 (stackPtr t1 + 8) left.y at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) frame1.rsp (by decide) (offset := 8) (by decide)] at h
    exact h
  obtain ⟨n3, t3, run3, frame3, effect3, ext3⟩ :=
    register_block pre frame2 (offset := 0x5366) (leftXY_registers boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip2
      (by simp [leftXYRegisterEffect, Effect.components, Component.Covers])
      (by simp [leftXYRegisterEffect, Effect.components])
  have rip3 : t3.RIP = 0x10537b := effect3.rip
  have r3_3 : t3.regValue .rbx = s.regValue .rdi := (effect3.agrees.read (n := 64) (r := 3) (by simp [leftXYRegisterEffect, Effect.components])).trans r3_2
  have r5_3 : t3.regValue .rbp = stackPtr s - 528 := (effect3.agrees.read (n := 64) (r := 5) (by simp [leftXYRegisterEffect, Effect.components])).trans r5_2
  have r14_3 : t3.regValue .r14 = s.regValue .rsi := (effect3.agrees.read (n := 64) (r := 14) (by simp [leftXYRegisterEffect, Effect.components])).trans r14_2
  have v560_3 : MontgomeryAt t3 (stackPtr s - 560) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using v560_2
  have v464_3 : MontgomeryAt t3 (stackPtr s - 464) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using v464_2
  have v528_3 : MontgomeryAt t3 (stackPtr s - 528) (values left right).zz := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using v528_2
  have v592_3 : MontgomeryAt t3 (stackPtr s - 592) left.x := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using v592_2
  have v624_3 : MontgomeryAt t3 (stackPtr s - 624) left.y := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using v624_2
  have left3 : ProjectiveAt t3 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using left2
  have right3 : ProjectiveAt t3 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext3] using right2
  have r15_3 : t3.regValue .r15 = stackPtr s - 80 := by
    have h : t3.regValue .r15 = stackPtr t2 + 552 := effect3.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame2.rsp (by decide) (offset := 552) (by decide))
  have r6_3 : t3.regValue .rsi = stackPtr s - 592 := by
    have h : t3.regValue .rsi = stackPtr t2 + 40 := effect3.writes.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame2.rsp (by decide) (offset := 40) (by decide))
  have r2_3 : t3.regValue .rdx = stackPtr s - 624 := by
    have h : t3.regValue .rdx = stackPtr t2 + 8 := effect3.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame2.rsp (by decide) (offset := 8) (by decide))
  have r7_3 : t3.regValue .rdi = stackPtr s - 80 := by
    have h : t3.regValue .rdi = stackPtr t2 + 552 := effect3.writes.2.2.2
    exact h.trans (scalar_stack_address (frameOffset := 632) frame2.rsp (by decide) (offset := 552) (by decide))
  obtain ⟨n4, t4, run4, frame4, rip4, value4, regs4, bytes4, work4⟩ :=
    Call.binary_call pre frame3 (x := left.x) (y := left.y) (op := fun x y => (x + y) % P256.Spec.Operations.domain.p) Call.Sites.call_10302b (fun _ hp hx hy => P256.Proofs.Field.field_add_correct hp hx hy)
      rip3 r6_3 r2_3 r7_3 v592_3 v624_3
  have mem4 := Copy.work_stack_frame pre work4
  have r3_4 : t4.regValue .rbx = s.regValue .rdi := (regs4 .rbx (by decide)).trans r3_3
  have r5_4 : t4.regValue .rbp = stackPtr s - 528 := (regs4 .rbp (by decide)).trans r5_3
  have r14_4 : t4.regValue .r14 = s.regValue .rsi := (regs4 .r14 (by decide)).trans r14_3
  have r15_4 : t4.regValue .r15 = stackPtr s - 80 := (regs4 .r15 (by decide)).trans r15_3
  have v560_4 : MontgomeryAt t4 (stackPtr s - 560) (values left right).xx := v560_3.of_bytes_eq (fun i hi => (bytes4 560 32 (by decide) (by decide) (by decide) i hi))
  have v464_4 : MontgomeryAt t4 (stackPtr s - 464) (values left right).yy := v464_3.of_bytes_eq (fun i hi => (bytes4 464 32 (by decide) (by decide) (by decide) i hi))
  have v528_4 : MontgomeryAt t4 (stackPtr s - 528) (values left right).zz := v528_3.of_bytes_eq (fun i hi => (bytes4 528 32 (by decide) (by decide) (by decide) i hi))
  have v592_4 : MontgomeryAt t4 (stackPtr s - 592) left.x := v592_3.of_bytes_eq (fun i hi => (bytes4 592 32 (by decide) (by decide) (by decide) i hi))
  have v624_4 : MontgomeryAt t4 (stackPtr s - 624) left.y := v624_3.of_bytes_eq (fun i hi => (bytes4 624 32 (by decide) (by decide) (by decide) i hi))
  have left4 : ProjectiveAt t4 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem4 left3
  have right4 : ProjectiveAt t4 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem4 right3
  have v80_4 : MontgomeryAt t4 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := value4
  obtain ⟨n5, t5, run5, frame5, rip5, value5, agrees5⟩ :=
    Copy.execute_stack pre frame4 (entryOffset := 0x5380) (offset := 40)
      (rightXY0_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre frame4 (by decide) rfl rip4 (by change MemReadable t4 (t4.regValue .r14 + 0) 32; rw [r14_4]; exact Copy.point_readable pre frame4 .rsi (by simp) (by decide)) (by change RangeApart (stackPtr t4 + 40) 32 (t4.regValue .r14 + 0) 32; rw [r14_4]; exact Copy.stack_point_apart pre frame4 .rsi (by simp) (by decide) (by decide))) (by change MontgomeryAt t4 (t4.regValue .r14 + 0) right.x; rw [r14_4]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using right4.1)
  have mem5 := copy_stack_frame pre frame4 (by decide) agrees5
  have r3_5 : t5.regValue .rbx = s.regValue .rdi := (agrees5.read (n := 64) (r := 3) (by simp [Copy32.components])).trans r3_4
  have r5_5 : t5.regValue .rbp = stackPtr s - 528 := (agrees5.read (n := 64) (r := 5) (by simp [Copy32.components])).trans r5_4
  have r14_5 : t5.regValue .r14 = s.regValue .rsi := (agrees5.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r14_4
  have r15_5 : t5.regValue .r15 = stackPtr s - 80 := (agrees5.read (n := 64) (r := 15) (by simp [Copy32.components])).trans r15_4
  have v560_5 : MontgomeryAt t5 (stackPtr s - 560) (values left right).xx := copy_stack_value pre frame4 (by decide) (by decide) (by decide) (by decide) agrees5 v560_4
  have v464_5 : MontgomeryAt t5 (stackPtr s - 464) (values left right).yy := copy_stack_value pre frame4 (by decide) (by decide) (by decide) (by decide) agrees5 v464_4
  have v528_5 : MontgomeryAt t5 (stackPtr s - 528) (values left right).zz := copy_stack_value pre frame4 (by decide) (by decide) (by decide) (by decide) agrees5 v528_4
  have v624_5 : MontgomeryAt t5 (stackPtr s - 624) left.y := copy_stack_value pre frame4 (by decide) (by decide) (by decide) (by decide) agrees5 v624_4
  have v80_5 : MontgomeryAt t5 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame4 (by decide) (by decide) (by decide) (by decide) agrees5 v80_4
  have left5 : ProjectiveAt t5 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem5 left4
  have right5 : ProjectiveAt t5 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem5 right4
  have v592_5 : MontgomeryAt t5 (stackPtr s - 592) right.x := by
    have h := value5
    change MontgomeryAt t5 (stackPtr t4 + 40) right.x at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) frame4.rsp (by decide) (offset := 40) (by decide)] at h
    exact h
  obtain ⟨n6, t6, run6, frame6, rip6, value6, agrees6⟩ :=
    Copy.execute_stack pre frame5 (entryOffset := 0x53a3) (offset := 8)
      (rightXY1_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre frame5 (by decide) rfl rip5 (by change MemReadable t5 (t5.regValue .r14 + 32) 32; rw [r14_5]; exact Copy.point_readable pre frame5 .rsi (by simp) (by decide)) (by change RangeApart (stackPtr t5 + 8) 32 (t5.regValue .r14 + 32) 32; rw [r14_5]; exact Copy.stack_point_apart pre frame5 .rsi (by simp) (by decide) (by decide))) (by change MontgomeryAt t5 (t5.regValue .r14 + 32) right.y; rw [r14_5]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using right5.2.1)
  have mem6 := copy_stack_frame pre frame5 (by decide) agrees6
  have r3_6 : t6.regValue .rbx = s.regValue .rdi := (agrees6.read (n := 64) (r := 3) (by simp [Copy32.components])).trans r3_5
  have r5_6 : t6.regValue .rbp = stackPtr s - 528 := (agrees6.read (n := 64) (r := 5) (by simp [Copy32.components])).trans r5_5
  have r14_6 : t6.regValue .r14 = s.regValue .rsi := (agrees6.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r14_5
  have r15_6 : t6.regValue .r15 = stackPtr s - 80 := (agrees6.read (n := 64) (r := 15) (by simp [Copy32.components])).trans r15_5
  have v560_6 : MontgomeryAt t6 (stackPtr s - 560) (values left right).xx := copy_stack_value pre frame5 (by decide) (by decide) (by decide) (by decide) agrees6 v560_5
  have v464_6 : MontgomeryAt t6 (stackPtr s - 464) (values left right).yy := copy_stack_value pre frame5 (by decide) (by decide) (by decide) (by decide) agrees6 v464_5
  have v528_6 : MontgomeryAt t6 (stackPtr s - 528) (values left right).zz := copy_stack_value pre frame5 (by decide) (by decide) (by decide) (by decide) agrees6 v528_5
  have v80_6 : MontgomeryAt t6 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame5 (by decide) (by decide) (by decide) (by decide) agrees6 v80_5
  have v592_6 : MontgomeryAt t6 (stackPtr s - 592) right.x := copy_stack_value pre frame5 (by decide) (by decide) (by decide) (by decide) agrees6 v592_5
  have left6 : ProjectiveAt t6 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem6 left5
  have right6 : ProjectiveAt t6 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem6 right5
  have v624_6 : MontgomeryAt t6 (stackPtr s - 624) right.y := by
    have h := value6
    change MontgomeryAt t6 (stackPtr t5 + 8) right.y at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) frame5.rsp (by decide) (offset := 8) (by decide)] at h
    exact h
  obtain ⟨n7, t7, run7, frame7, effect7, ext7⟩ :=
    register_block pre frame6 (offset := 0x53c7) (rightXY_registers boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip6
      (by simp [rightXYRegisterEffect, Effect.components, Component.Covers])
      (by simp [rightXYRegisterEffect, Effect.components])
  have rip7 : t7.RIP = 0x1053dc := effect7.rip
  have r3_7 : t7.regValue .rbx = s.regValue .rdi := (effect7.agrees.read (n := 64) (r := 3) (by simp [rightXYRegisterEffect, Effect.components])).trans r3_6
  have r5_7 : t7.regValue .rbp = stackPtr s - 528 := (effect7.agrees.read (n := 64) (r := 5) (by simp [rightXYRegisterEffect, Effect.components])).trans r5_6
  have r14_7 : t7.regValue .r14 = s.regValue .rsi := (effect7.agrees.read (n := 64) (r := 14) (by simp [rightXYRegisterEffect, Effect.components])).trans r14_6
  have r15_7 : t7.regValue .r15 = stackPtr s - 80 := (effect7.agrees.read (n := 64) (r := 15) (by simp [rightXYRegisterEffect, Effect.components])).trans r15_6
  have v560_7 : MontgomeryAt t7 (stackPtr s - 560) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v560_6
  have v464_7 : MontgomeryAt t7 (stackPtr s - 464) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v464_6
  have v528_7 : MontgomeryAt t7 (stackPtr s - 528) (values left right).zz := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v528_6
  have v80_7 : MontgomeryAt t7 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v80_6
  have v592_7 : MontgomeryAt t7 (stackPtr s - 592) right.x := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v592_6
  have v624_7 : MontgomeryAt t7 (stackPtr s - 624) right.y := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using v624_6
  have left7 : ProjectiveAt t7 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using left6
  have right7 : ProjectiveAt t7 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext7] using right6
  have r13_7 : t7.regValue .r13 = stackPtr s - 496 := by
    have h : t7.regValue .r13 = stackPtr t6 + 136 := effect7.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame6.rsp (by decide) (offset := 136) (by decide))
  have r6_7 : t7.regValue .rsi = stackPtr s - 592 := by
    have h : t7.regValue .rsi = stackPtr t6 + 40 := effect7.writes.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame6.rsp (by decide) (offset := 40) (by decide))
  have r2_7 : t7.regValue .rdx = stackPtr s - 624 := by
    have h : t7.regValue .rdx = stackPtr t6 + 8 := effect7.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame6.rsp (by decide) (offset := 8) (by decide))
  have r7_7 : t7.regValue .rdi = stackPtr s - 496 := by
    have h : t7.regValue .rdi = stackPtr t6 + 136 := effect7.writes.2.2.2
    exact h.trans (scalar_stack_address (frameOffset := 632) frame6.rsp (by decide) (offset := 136) (by decide))
  obtain ⟨n8, t8, run8, frame8, rip8, value8, regs8, bytes8, work8⟩ :=
    Call.binary_call pre frame7 (x := right.x) (y := right.y) (op := fun x y => (x + y) % P256.Spec.Operations.domain.p) Call.Sites.call_10308c (fun _ hp hx hy => P256.Proofs.Field.field_add_correct hp hx hy)
      rip7 r6_7 r2_7 r7_7 v592_7 v624_7
  have mem8 := Copy.work_stack_frame pre work8
  have r3_8 : t8.regValue .rbx = s.regValue .rdi := (regs8 .rbx (by decide)).trans r3_7
  have r5_8 : t8.regValue .rbp = stackPtr s - 528 := (regs8 .rbp (by decide)).trans r5_7
  have r14_8 : t8.regValue .r14 = s.regValue .rsi := (regs8 .r14 (by decide)).trans r14_7
  have r15_8 : t8.regValue .r15 = stackPtr s - 80 := (regs8 .r15 (by decide)).trans r15_7
  have r13_8 : t8.regValue .r13 = stackPtr s - 496 := (regs8 .r13 (by decide)).trans r13_7
  have v560_8 : MontgomeryAt t8 (stackPtr s - 560) (values left right).xx := v560_7.of_bytes_eq (fun i hi => (bytes8 560 32 (by decide) (by decide) (by decide) i hi))
  have v464_8 : MontgomeryAt t8 (stackPtr s - 464) (values left right).yy := v464_7.of_bytes_eq (fun i hi => (bytes8 464 32 (by decide) (by decide) (by decide) i hi))
  have v528_8 : MontgomeryAt t8 (stackPtr s - 528) (values left right).zz := v528_7.of_bytes_eq (fun i hi => (bytes8 528 32 (by decide) (by decide) (by decide) i hi))
  have v80_8 : MontgomeryAt t8 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := v80_7.of_bytes_eq (fun i hi => (bytes8 80 32 (by decide) (by decide) (by decide) i hi))
  have v592_8 : MontgomeryAt t8 (stackPtr s - 592) right.x := v592_7.of_bytes_eq (fun i hi => (bytes8 592 32 (by decide) (by decide) (by decide) i hi))
  have v624_8 : MontgomeryAt t8 (stackPtr s - 624) right.y := v624_7.of_bytes_eq (fun i hi => (bytes8 624 32 (by decide) (by decide) (by decide) i hi))
  have left8 : ProjectiveAt t8 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem8 left7
  have right8 : ProjectiveAt t8 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem8 right7
  have v496_8 : MontgomeryAt t8 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := value8
  obtain ⟨n9, t9, run9, frame9, effect9, ext9⟩ :=
    register_block pre frame8 (offset := 0x53e1) (productXY_registers boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip8
      (by simp [productXYRegisterEffect, Effect.components, Component.Covers])
      (by simp [productXYRegisterEffect, Effect.components])
  have rip9 : t9.RIP = 0x1053f2 := effect9.rip
  have r3_9 : t9.regValue .rbx = s.regValue .rdi := (effect9.agrees.read (n := 64) (r := 3) (by simp [productXYRegisterEffect, Effect.components])).trans r3_8
  have r5_9 : t9.regValue .rbp = stackPtr s - 528 := (effect9.agrees.read (n := 64) (r := 5) (by simp [productXYRegisterEffect, Effect.components])).trans r5_8
  have r14_9 : t9.regValue .r14 = s.regValue .rsi := (effect9.agrees.read (n := 64) (r := 14) (by simp [productXYRegisterEffect, Effect.components])).trans r14_8
  have r15_9 : t9.regValue .r15 = stackPtr s - 80 := (effect9.agrees.read (n := 64) (r := 15) (by simp [productXYRegisterEffect, Effect.components])).trans r15_8
  have r13_9 : t9.regValue .r13 = stackPtr s - 496 := (effect9.agrees.read (n := 64) (r := 13) (by simp [productXYRegisterEffect, Effect.components])).trans r13_8
  have v560_9 : MontgomeryAt t9 (stackPtr s - 560) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v560_8
  have v464_9 : MontgomeryAt t9 (stackPtr s - 464) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v464_8
  have v528_9 : MontgomeryAt t9 (stackPtr s - 528) (values left right).zz := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v528_8
  have v80_9 : MontgomeryAt t9 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v80_8
  have v592_9 : MontgomeryAt t9 (stackPtr s - 592) right.x := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v592_8
  have v624_9 : MontgomeryAt t9 (stackPtr s - 624) right.y := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v624_8
  have v496_9 : MontgomeryAt t9 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using v496_8
  have left9 : ProjectiveAt t9 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using left8
  have right9 : ProjectiveAt t9 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext9] using right8
  have r12_9 : t9.regValue .r12 = stackPtr s - 432 := by
    have h : t9.regValue .r12 = stackPtr t8 + 200 := effect9.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame8.rsp (by decide) (offset := 200) (by decide))
  have r7_9 : t9.regValue .rdi = stackPtr s - 432 := by
    have h : t9.regValue .rdi = stackPtr t8 + 200 := effect9.writes.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame8.rsp (by decide) (offset := 200) (by decide))
  have r6_9 : t9.regValue .rsi = stackPtr s - 80 := by
    have h : t9.regValue .rsi = t8.regValue .r15 := effect9.writes.2.2.1
    exact h.trans r15_8
  have r2_9 : t9.regValue .rdx = stackPtr s - 496 := by
    have h : t9.regValue .rdx = t8.regValue .r13 := effect9.writes.2.2.2
    exact h.trans r13_8
  obtain ⟨n10, t10, run10, frame10, rip10, value10, regs10, bytes10, work10⟩ :=
    Call.binary_call pre frame9 (x := ((left.x + left.y) % P256.Spec.Operations.domain.p)) (y := ((right.x + right.y) % P256.Spec.Operations.domain.p)) (op := fun x y => x * y % P256.Spec.Operations.domain.p) Call.Sites.call_1030a2 (fun _ hp hx hy => P256.Proofs.Field.field_mul_correct hp hx hy)
      rip9 r6_9 r2_9 r7_9 v80_9 v496_9
  have mem10 := Copy.work_stack_frame pre work10
  have r3_10 : t10.regValue .rbx = s.regValue .rdi := (regs10 .rbx (by decide)).trans r3_9
  have r5_10 : t10.regValue .rbp = stackPtr s - 528 := (regs10 .rbp (by decide)).trans r5_9
  have r14_10 : t10.regValue .r14 = s.regValue .rsi := (regs10 .r14 (by decide)).trans r14_9
  have r15_10 : t10.regValue .r15 = stackPtr s - 80 := (regs10 .r15 (by decide)).trans r15_9
  have r13_10 : t10.regValue .r13 = stackPtr s - 496 := (regs10 .r13 (by decide)).trans r13_9
  have r12_10 : t10.regValue .r12 = stackPtr s - 432 := (regs10 .r12 (by decide)).trans r12_9
  have v560_10 : MontgomeryAt t10 (stackPtr s - 560) (values left right).xx := v560_9.of_bytes_eq (fun i hi => (bytes10 560 32 (by decide) (by decide) (by decide) i hi))
  have v464_10 : MontgomeryAt t10 (stackPtr s - 464) (values left right).yy := v464_9.of_bytes_eq (fun i hi => (bytes10 464 32 (by decide) (by decide) (by decide) i hi))
  have v528_10 : MontgomeryAt t10 (stackPtr s - 528) (values left right).zz := v528_9.of_bytes_eq (fun i hi => (bytes10 528 32 (by decide) (by decide) (by decide) i hi))
  have v80_10 : MontgomeryAt t10 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := v80_9.of_bytes_eq (fun i hi => (bytes10 80 32 (by decide) (by decide) (by decide) i hi))
  have v592_10 : MontgomeryAt t10 (stackPtr s - 592) right.x := v592_9.of_bytes_eq (fun i hi => (bytes10 592 32 (by decide) (by decide) (by decide) i hi))
  have v624_10 : MontgomeryAt t10 (stackPtr s - 624) right.y := v624_9.of_bytes_eq (fun i hi => (bytes10 624 32 (by decide) (by decide) (by decide) i hi))
  have v496_10 : MontgomeryAt t10 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := v496_9.of_bytes_eq (fun i hi => (bytes10 496 32 (by decide) (by decide) (by decide) i hi))
  have left10 : ProjectiveAt t10 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem10 left9
  have right10 : ProjectiveAt t10 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem10 right9
  have v432_10 : MontgomeryAt t10 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := value10
  obtain ⟨n11, t11, run11, frame11, rip11, value11, agrees11⟩ :=
    Copy.execute_stack pre frame10 (entryOffset := 0x53f7) (offset := 40)
      (sumXXYY0_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre frame10 (by decide) rfl rip10 (by exact stack_readable (frameOffset := 632) pre frame10 (by decide) (by decide)) (by exact RangeApart.offsets (stackPtr t10) (by decide) (by decide) (by decide))) (by change MontgomeryAt t10 (stackPtr t10 + 72) (values left right).xx; simp only [BitVec.ofNat_eq_ofNat]; rw [scalar_stack_address (frameOffset := 632) frame10.rsp (by decide) (offset := 72) (by decide)]; exact v560_10)
  have mem11 := copy_stack_frame pre frame10 (by decide) agrees11
  have r3_11 : t11.regValue .rbx = s.regValue .rdi := (agrees11.read (n := 64) (r := 3) (by simp [Copy32.components])).trans r3_10
  have r5_11 : t11.regValue .rbp = stackPtr s - 528 := (agrees11.read (n := 64) (r := 5) (by simp [Copy32.components])).trans r5_10
  have r14_11 : t11.regValue .r14 = s.regValue .rsi := (agrees11.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r14_10
  have r15_11 : t11.regValue .r15 = stackPtr s - 80 := (agrees11.read (n := 64) (r := 15) (by simp [Copy32.components])).trans r15_10
  have r13_11 : t11.regValue .r13 = stackPtr s - 496 := (agrees11.read (n := 64) (r := 13) (by simp [Copy32.components])).trans r13_10
  have r12_11 : t11.regValue .r12 = stackPtr s - 432 := (agrees11.read (n := 64) (r := 12) (by simp [Copy32.components])).trans r12_10
  have v560_11 : MontgomeryAt t11 (stackPtr s - 560) (values left right).xx := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v560_10
  have v464_11 : MontgomeryAt t11 (stackPtr s - 464) (values left right).yy := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v464_10
  have v528_11 : MontgomeryAt t11 (stackPtr s - 528) (values left right).zz := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v528_10
  have v80_11 : MontgomeryAt t11 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v80_10
  have v624_11 : MontgomeryAt t11 (stackPtr s - 624) right.y := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v624_10
  have v496_11 : MontgomeryAt t11 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v496_10
  have v432_11 : MontgomeryAt t11 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame10 (by decide) (by decide) (by decide) (by decide) agrees11 v432_10
  have left11 : ProjectiveAt t11 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem11 left10
  have right11 : ProjectiveAt t11 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem11 right10
  have v592_11 : MontgomeryAt t11 (stackPtr s - 592) (values left right).xx := by
    have h := value11
    change MontgomeryAt t11 (stackPtr t10 + 40) (values left right).xx at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) frame10.rsp (by decide) (offset := 40) (by decide)] at h
    exact h
  obtain ⟨n12, t12, run12, frame12, rip12, value12, agrees12⟩ :=
    Copy.execute_stack pre frame11 (entryOffset := 0x541f) (offset := 8)
      (sumXXYY1_copy boundary pre.outerBoundary) (by decide) (by decide +kernel) (by decide) rfl
      (Copy.stack_pre pre frame11 (by decide) rfl rip11 (by exact stack_readable (frameOffset := 632) pre frame11 (by decide) (by decide)) (by exact RangeApart.offsets (stackPtr t11) (by decide) (by decide) (by decide))) (by change MontgomeryAt t11 (stackPtr t11 + 168) (values left right).yy; simp only [BitVec.ofNat_eq_ofNat]; rw [scalar_stack_address (frameOffset := 632) frame11.rsp (by decide) (offset := 168) (by decide)]; exact v464_11)
  have mem12 := copy_stack_frame pre frame11 (by decide) agrees12
  have r3_12 : t12.regValue .rbx = s.regValue .rdi := (agrees12.read (n := 64) (r := 3) (by simp [Copy32.components])).trans r3_11
  have r5_12 : t12.regValue .rbp = stackPtr s - 528 := (agrees12.read (n := 64) (r := 5) (by simp [Copy32.components])).trans r5_11
  have r14_12 : t12.regValue .r14 = s.regValue .rsi := (agrees12.read (n := 64) (r := 14) (by simp [Copy32.components])).trans r14_11
  have r15_12 : t12.regValue .r15 = stackPtr s - 80 := (agrees12.read (n := 64) (r := 15) (by simp [Copy32.components])).trans r15_11
  have r13_12 : t12.regValue .r13 = stackPtr s - 496 := (agrees12.read (n := 64) (r := 13) (by simp [Copy32.components])).trans r13_11
  have r12_12 : t12.regValue .r12 = stackPtr s - 432 := (agrees12.read (n := 64) (r := 12) (by simp [Copy32.components])).trans r12_11
  have v560_12 : MontgomeryAt t12 (stackPtr s - 560) (values left right).xx := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v560_11
  have v464_12 : MontgomeryAt t12 (stackPtr s - 464) (values left right).yy := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v464_11
  have v528_12 : MontgomeryAt t12 (stackPtr s - 528) (values left right).zz := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v528_11
  have v80_12 : MontgomeryAt t12 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v80_11
  have v496_12 : MontgomeryAt t12 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v496_11
  have v432_12 : MontgomeryAt t12 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v432_11
  have v592_12 : MontgomeryAt t12 (stackPtr s - 592) (values left right).xx := copy_stack_value pre frame11 (by decide) (by decide) (by decide) (by decide) agrees12 v592_11
  have left12 : ProjectiveAt t12 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem12 left11
  have right12 : ProjectiveAt t12 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem12 right11
  have v624_12 : MontgomeryAt t12 (stackPtr s - 624) (values left right).yy := by
    have h := value12
    change MontgomeryAt t12 (stackPtr t11 + 8) (values left right).yy at h
    simp only [BitVec.ofNat_eq_ofNat] at h
    rw [scalar_stack_address (frameOffset := 632) frame11.rsp (by decide) (offset := 8) (by decide)] at h
    exact h
  obtain ⟨n13, t13, run13, frame13, effect13, ext13⟩ :=
    register_block pre frame12 (offset := 0x5453) (sumXXYY_registers boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip12
      (by simp [sumXXYYRegisterEffect, Effect.components, Component.Covers])
      (by simp [sumXXYYRegisterEffect, Effect.components])
  have rip13 : t13.RIP = 0x105468 := effect13.rip
  have r3_13 : t13.regValue .rbx = s.regValue .rdi := (effect13.agrees.read (n := 64) (r := 3) (by simp [sumXXYYRegisterEffect, Effect.components])).trans r3_12
  have r5_13 : t13.regValue .rbp = stackPtr s - 528 := (effect13.agrees.read (n := 64) (r := 5) (by simp [sumXXYYRegisterEffect, Effect.components])).trans r5_12
  have r14_13 : t13.regValue .r14 = s.regValue .rsi := (effect13.agrees.read (n := 64) (r := 14) (by simp [sumXXYYRegisterEffect, Effect.components])).trans r14_12
  have r13_13 : t13.regValue .r13 = stackPtr s - 496 := (effect13.agrees.read (n := 64) (r := 13) (by simp [sumXXYYRegisterEffect, Effect.components])).trans r13_12
  have r12_13 : t13.regValue .r12 = stackPtr s - 432 := (effect13.agrees.read (n := 64) (r := 12) (by simp [sumXXYYRegisterEffect, Effect.components])).trans r12_12
  have v560_13 : MontgomeryAt t13 (stackPtr s - 560) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v560_12
  have v464_13 : MontgomeryAt t13 (stackPtr s - 464) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v464_12
  have v528_13 : MontgomeryAt t13 (stackPtr s - 528) (values left right).zz := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v528_12
  have v80_13 : MontgomeryAt t13 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v80_12
  have v496_13 : MontgomeryAt t13 (stackPtr s - 496) ((right.x + right.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v496_12
  have v432_13 : MontgomeryAt t13 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v432_12
  have v592_13 : MontgomeryAt t13 (stackPtr s - 592) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v592_12
  have v624_13 : MontgomeryAt t13 (stackPtr s - 624) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using v624_12
  have left13 : ProjectiveAt t13 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using left12
  have right13 : ProjectiveAt t13 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext13] using right12
  have r15_13 : t13.regValue .r15 = stackPtr s - 496 := by
    have h : t13.regValue .r15 = stackPtr t12 + 136 := effect13.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame12.rsp (by decide) (offset := 136) (by decide))
  have r6_13 : t13.regValue .rsi = stackPtr s - 592 := by
    have h : t13.regValue .rsi = stackPtr t12 + 40 := effect13.writes.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame12.rsp (by decide) (offset := 40) (by decide))
  have r2_13 : t13.regValue .rdx = stackPtr s - 624 := by
    have h : t13.regValue .rdx = stackPtr t12 + 8 := effect13.writes.2.2.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame12.rsp (by decide) (offset := 8) (by decide))
  have r7_13 : t13.regValue .rdi = stackPtr s - 496 := by
    have h : t13.regValue .rdi = stackPtr t12 + 136 := effect13.writes.2.2.2
    exact h.trans (scalar_stack_address (frameOffset := 632) frame12.rsp (by decide) (offset := 136) (by decide))
  obtain ⟨n14, t14, run14, frame14, rip14, value14, regs14, bytes14, work14⟩ :=
    Call.binary_call pre frame13 (x := (values left right).xx) (y := (values left right).yy) (op := fun x y => (x + y) % P256.Spec.Operations.domain.p) Call.Sites.call_103118 (fun _ hp hx hy => P256.Proofs.Field.field_add_correct hp hx hy)
      rip13 r6_13 r2_13 r7_13 v592_13 v624_13
  have mem14 := Copy.work_stack_frame pre work14
  have r3_14 : t14.regValue .rbx = s.regValue .rdi := (regs14 .rbx (by decide)).trans r3_13
  have r5_14 : t14.regValue .rbp = stackPtr s - 528 := (regs14 .rbp (by decide)).trans r5_13
  have r14_14 : t14.regValue .r14 = s.regValue .rsi := (regs14 .r14 (by decide)).trans r14_13
  have r13_14 : t14.regValue .r13 = stackPtr s - 496 := (regs14 .r13 (by decide)).trans r13_13
  have r12_14 : t14.regValue .r12 = stackPtr s - 432 := (regs14 .r12 (by decide)).trans r12_13
  have r15_14 : t14.regValue .r15 = stackPtr s - 496 := (regs14 .r15 (by decide)).trans r15_13
  have v560_14 : MontgomeryAt t14 (stackPtr s - 560) (values left right).xx := v560_13.of_bytes_eq (fun i hi => (bytes14 560 32 (by decide) (by decide) (by decide) i hi))
  have v464_14 : MontgomeryAt t14 (stackPtr s - 464) (values left right).yy := v464_13.of_bytes_eq (fun i hi => (bytes14 464 32 (by decide) (by decide) (by decide) i hi))
  have v528_14 : MontgomeryAt t14 (stackPtr s - 528) (values left right).zz := v528_13.of_bytes_eq (fun i hi => (bytes14 528 32 (by decide) (by decide) (by decide) i hi))
  have v80_14 : MontgomeryAt t14 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := v80_13.of_bytes_eq (fun i hi => (bytes14 80 32 (by decide) (by decide) (by decide) i hi))
  have v432_14 : MontgomeryAt t14 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := v432_13.of_bytes_eq (fun i hi => (bytes14 432 32 (by decide) (by decide) (by decide) i hi))
  have v592_14 : MontgomeryAt t14 (stackPtr s - 592) (values left right).xx := v592_13.of_bytes_eq (fun i hi => (bytes14 592 32 (by decide) (by decide) (by decide) i hi))
  have v624_14 : MontgomeryAt t14 (stackPtr s - 624) (values left right).yy := v624_13.of_bytes_eq (fun i hi => (bytes14 624 32 (by decide) (by decide) (by decide) i hi))
  have left14 : ProjectiveAt t14 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem14 left13
  have right14 : ProjectiveAt t14 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem14 right13
  have v496_14 : MontgomeryAt t14 (stackPtr s - 496) (((values left right).xx + (values left right).yy) % P256.Spec.Operations.domain.p) := value14
  obtain ⟨n15, t15, run15, frame15, effect15, ext15⟩ :=
    register_block pre frame14 (offset := 0x546d) (xy_registers boundary pre.outerBoundary)
      (by decide) (by decide +kernel) rip14
      (by simp [xyRegisterEffect, Effect.components, Component.Covers])
      (by simp [xyRegisterEffect, Effect.components])
  have rip15 : t15.RIP = 0x10547b := effect15.rip
  have r3_15 : t15.regValue .rbx = s.regValue .rdi := (effect15.agrees.read (n := 64) (r := 3) (by simp [xyRegisterEffect, Effect.components])).trans r3_14
  have r5_15 : t15.regValue .rbp = stackPtr s - 528 := (effect15.agrees.read (n := 64) (r := 5) (by simp [xyRegisterEffect, Effect.components])).trans r5_14
  have r14_15 : t15.regValue .r14 = s.regValue .rsi := (effect15.agrees.read (n := 64) (r := 14) (by simp [xyRegisterEffect, Effect.components])).trans r14_14
  have r13_15 : t15.regValue .r13 = stackPtr s - 496 := (effect15.agrees.read (n := 64) (r := 13) (by simp [xyRegisterEffect, Effect.components])).trans r13_14
  have r12_15 : t15.regValue .r12 = stackPtr s - 432 := (effect15.agrees.read (n := 64) (r := 12) (by simp [xyRegisterEffect, Effect.components])).trans r12_14
  have r15_15 : t15.regValue .r15 = stackPtr s - 496 := (effect15.agrees.read (n := 64) (r := 15) (by simp [xyRegisterEffect, Effect.components])).trans r15_14
  have v560_15 : MontgomeryAt t15 (stackPtr s - 560) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v560_14
  have v464_15 : MontgomeryAt t15 (stackPtr s - 464) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v464_14
  have v528_15 : MontgomeryAt t15 (stackPtr s - 528) (values left right).zz := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v528_14
  have v80_15 : MontgomeryAt t15 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v80_14
  have v432_15 : MontgomeryAt t15 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v432_14
  have v592_15 : MontgomeryAt t15 (stackPtr s - 592) (values left right).xx := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v592_14
  have v624_15 : MontgomeryAt t15 (stackPtr s - 624) (values left right).yy := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v624_14
  have v496_15 : MontgomeryAt t15 (stackPtr s - 496) (((values left right).xx + (values left right).yy) % P256.Spec.Operations.domain.p) := by simpa only [MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using v496_14
  have left15 : ProjectiveAt t15 (s.regValue .rdi) left := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using left14
  have right15 : ProjectiveAt t15 (s.regValue .rsi) right := by simpa only [ProjectiveAt, MontgomeryAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, ext15] using right14
  have r7_15 : t15.regValue .rdi = stackPtr s - 400 := by
    have h : t15.regValue .rdi = stackPtr t14 + 232 := effect15.writes.1
    exact h.trans (scalar_stack_address (frameOffset := 632) frame14.rsp (by decide) (offset := 232) (by decide))
  have r6_15 : t15.regValue .rsi = stackPtr s - 432 := by
    have h : t15.regValue .rsi = t14.regValue .r12 := effect15.writes.2.1
    exact h.trans r12_14
  have r2_15 : t15.regValue .rdx = stackPtr s - 496 := by
    have h : t15.regValue .rdx = t14.regValue .r15 := effect15.writes.2.2
    exact h.trans r15_14
  obtain ⟨n16, t16, run16, frame16, rip16, value16, regs16, bytes16, work16⟩ :=
    Call.binary_call pre frame15 (x := (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p)) (y := (((values left right).xx + (values left right).yy) % P256.Spec.Operations.domain.p)) (op := fun x y => Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p x y) Call.Sites.call_10312b (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      rip15 r6_15 r2_15 r7_15 v432_15 v496_15
  have mem16 := Copy.work_stack_frame pre work16
  have r3_16 : t16.regValue .rbx = s.regValue .rdi := (regs16 .rbx (by decide)).trans r3_15
  have r5_16 : t16.regValue .rbp = stackPtr s - 528 := (regs16 .rbp (by decide)).trans r5_15
  have r14_16 : t16.regValue .r14 = s.regValue .rsi := (regs16 .r14 (by decide)).trans r14_15
  have r13_16 : t16.regValue .r13 = stackPtr s - 496 := (regs16 .r13 (by decide)).trans r13_15
  have r12_16 : t16.regValue .r12 = stackPtr s - 432 := (regs16 .r12 (by decide)).trans r12_15
  have r15_16 : t16.regValue .r15 = stackPtr s - 496 := (regs16 .r15 (by decide)).trans r15_15
  have v560_16 : MontgomeryAt t16 (stackPtr s - 560) (values left right).xx := v560_15.of_bytes_eq (fun i hi => (bytes16 560 32 (by decide) (by decide) (by decide) i hi))
  have v464_16 : MontgomeryAt t16 (stackPtr s - 464) (values left right).yy := v464_15.of_bytes_eq (fun i hi => (bytes16 464 32 (by decide) (by decide) (by decide) i hi))
  have v528_16 : MontgomeryAt t16 (stackPtr s - 528) (values left right).zz := v528_15.of_bytes_eq (fun i hi => (bytes16 528 32 (by decide) (by decide) (by decide) i hi))
  have v80_16 : MontgomeryAt t16 (stackPtr s - 80) ((left.x + left.y) % P256.Spec.Operations.domain.p) := v80_15.of_bytes_eq (fun i hi => (bytes16 80 32 (by decide) (by decide) (by decide) i hi))
  have v432_16 : MontgomeryAt t16 (stackPtr s - 432) (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) := v432_15.of_bytes_eq (fun i hi => (bytes16 432 32 (by decide) (by decide) (by decide) i hi))
  have v592_16 : MontgomeryAt t16 (stackPtr s - 592) (values left right).xx := v592_15.of_bytes_eq (fun i hi => (bytes16 592 32 (by decide) (by decide) (by decide) i hi))
  have v624_16 : MontgomeryAt t16 (stackPtr s - 624) (values left right).yy := v624_15.of_bytes_eq (fun i hi => (bytes16 624 32 (by decide) (by decide) (by decide) i hi))
  have v496_16 : MontgomeryAt t16 (stackPtr s - 496) (((values left right).xx + (values left right).yy) % P256.Spec.Operations.domain.p) := v496_15.of_bytes_eq (fun i hi => (bytes16 496 32 (by decide) (by decide) (by decide) i hi))
  have left16 : ProjectiveAt t16 (s.regValue .rdi) left := Copy.point_of_stack pre .rdi (by simp) mem16 left15
  have right16 : ProjectiveAt t16 (s.regValue .rsi) right := Copy.point_of_stack pre .rsi (by simp) mem16 right15
  have v400_16 : MontgomeryAt t16 (stackPtr s - 400) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p (((left.x + left.y) % P256.Spec.Operations.domain.p) * ((right.x + right.y) % P256.Spec.Operations.domain.p) % P256.Spec.Operations.domain.p) (((values left right).xx + (values left right).yy) % P256.Spec.Operations.domain.p)) := value16
  refine ⟨_, t16, (((((((((((((((run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16, frame16, rip16, ?_⟩
  refine ⟨⟨left16, right16, r3_16, r14_16, r5_16, v560_16, v464_16, v528_16⟩,  ?_⟩
  exact v400_16

end P256.Proofs.Projective.Add.CrossTerms
