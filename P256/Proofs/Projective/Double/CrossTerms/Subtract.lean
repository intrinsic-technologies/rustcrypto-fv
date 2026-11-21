import P256.Proofs.Projective.Double.CrossTerms.Memory

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem subtract [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x105f29) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u 96 1016 728 ∧ u.RIP = 0x105f70 ∧
      AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t u ∧
      u.regValue .r12 = stackSlot s 264 ∧
      u.regValue .rdx = stackSlot s 8 ∧
      u.regValue .rdi = stackSlot s 264 ∧
      u.regValue .rsi = t.regValue .r15 ∧
      memLoad u.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 ∧
      memLoad u.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 ∧
      memLoad u.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 ∧
      memLoad u.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x5f29) (mov_r64_m64_effect_step 0x105f29 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 224)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨rip, ?_⟩; exact stack_readable (frameOffset := 728) pre state (by decide) (by decide))
    (inProgram_of_textOffset 0x5f31 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree1 : AgreesExcept [.reg 0, .rip] t t1 := effect1.agrees
  have part1 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t t1 :=
    scratch_reg agree1 (by decide)
  have reg1_0 : t1.regValue .rax = memLoad t.external (stackSlot s 224) 64 := by
    have h : t1.regValue .rax = memLoad t.external (stackPtr t + 224) 64 := effect1.writes
    rw [state.rsp] at h
    exact h
  have all1 := part1
  obtain ⟨t2, run2, frame2, effect2⟩ := step pre frame1 (by decide)
    (offset := 0x5f31) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105f31 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect1.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame1 (by decide) (offset := 32) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame1 (by decide) (offset := 32) (len := 8) (codeOffset := 0x5f31) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5f36 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame1 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree2 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t1 t2 := by
    have h : AgreesExcept [.mem (stackPtr t1 + 32) 8, .rip] t1 t2 := by have h := effect2.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame1.rsp] at h
    exact h
  have part2 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t1 t2 :=
    scratch_store agree2 (by decide) (by decide)
  have mem2_32 : memLoad t2.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    have h : memLoad t2.external (stackPtr t1 + 32) 64 = t1.regValue .rax := effect2.writes
    rw [frame1.rsp] at h
    exact h.trans reg1_0
  have all2 := scratch_trans all1 part2
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x5f36) (mov_r64_m64_effect_step 0x105f36 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 216)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect2.rip, ?_⟩; exact stack_readable (frameOffset := 728) pre frame2 (by decide) (by decide))
    (inProgram_of_textOffset 0x5f3e (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree3 : AgreesExcept [.reg 0, .rip] t2 t3 := effect3.agrees
  have part3 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t2 t3 :=
    scratch_reg agree3 (by decide)
  have reg3_0 : t3.regValue .rax = memLoad t.external (stackSlot s 216) 64 := by
    have h : t3.regValue .rax = memLoad t2.external (stackPtr t2 + 216) 64 := effect3.writes
    rw [frame2.rsp] at h
    exact h.trans (scratch_read all2 (slots_apart (by decide) (by decide) (by decide)))
  have all3 := scratch_trans all2 part3
  obtain ⟨t4, run4, frame4, effect4⟩ := step pre frame3 (by decide)
    (offset := 0x5f3e) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105f3e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect3.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame3 (by decide) (offset := 24) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame3 (by decide) (offset := 24) (len := 8) (codeOffset := 0x5f3e) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5f43 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame3 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree4 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t3 t4 := by
    have h : AgreesExcept [.mem (stackPtr t3 + 24) 8, .rip] t3 t4 := by have h := effect4.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame3.rsp] at h
    exact h
  have part4 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t3 t4 :=
    scratch_store agree4 (by decide) (by decide)
  have mem4_24 : memLoad t4.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    have h : memLoad t4.external (stackPtr t3 + 24) 64 = t3.regValue .rax := effect4.writes
    rw [frame3.rsp] at h
    exact h.trans reg3_0
  have all4 := scratch_trans all3 part4
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x5f43) (mov_r64_m64_effect_step 0x105f43 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect4.rip, ?_⟩; exact stack_readable (frameOffset := 728) pre frame4 (by decide) (by decide))
    (inProgram_of_textOffset 0x5f4b (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree5 : AgreesExcept [.reg 0, .rip] t4 t5 := effect5.agrees
  have part5 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t4 t5 :=
    scratch_reg agree5 (by decide)
  have reg5_0 : t5.regValue .rax = memLoad t.external (stackSlot s 200) 64 := by
    have h : t5.regValue .rax = memLoad t4.external (stackPtr t4 + 200) 64 := effect5.writes
    rw [frame4.rsp] at h
    exact h.trans (scratch_read all4 (slots_apart (by decide) (by decide) (by decide)))
  have all5 := scratch_trans all4 part5
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x5f4b) (mov_r64_m64_effect_step 0x105f4b 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 208)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect5.rip, ?_⟩; exact stack_readable (frameOffset := 728) pre frame5 (by decide) (by decide))
    (inProgram_of_textOffset 0x5f53 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 1, .rip]; decide)
  have agree6 : AgreesExcept [.reg 1, .rip] t5 t6 := effect6.agrees
  have part6 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t5 t6 :=
    scratch_reg agree6 (by decide)
  have reg6_1 : t6.regValue .rcx = memLoad t.external (stackSlot s 208) 64 := by
    have h : t6.regValue .rcx = memLoad t5.external (stackPtr t5 + 208) 64 := effect6.writes
    rw [frame5.rsp] at h
    exact h.trans (scratch_read all5 (slots_apart (by decide) (by decide) (by decide)))
  have all6 := scratch_trans all5 part6
  obtain ⟨t7, run7, frame7, effect7⟩ := step pre frame6 (by decide)
    (offset := 0x5f53) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105f53 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect6.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame6 (by decide) (offset := 16) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame6 (by decide) (offset := 16) (len := 8) (codeOffset := 0x5f53) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5f58 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame6 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree7 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t6 t7 := by
    have h : AgreesExcept [.mem (stackPtr t6 + 16) 8, .rip] t6 t7 := by have h := effect7.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame6.rsp] at h
    exact h
  have part7 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t6 t7 :=
    scratch_store agree7 (by decide) (by decide)
  have mem7_16 : memLoad t7.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 := by
    have h : memLoad t7.external (stackPtr t6 + 16) 64 = t6.regValue .rcx := effect7.writes
    rw [frame6.rsp] at h
    exact h.trans reg6_1
  have all7 := scratch_trans all6 part7
  have reg6_0 : t6.regValue .rax = memLoad t.external (stackSlot s 200) 64 :=
    (agree6.read (n := 64) (r := 0) (by simp)).trans reg5_0
  have reg7_0 : t7.regValue .rax = memLoad t.external (stackSlot s 200) 64 :=
    (agree7.read (n := 64) (r := 0) (by simp)).trans reg6_0
  obtain ⟨t8, run8, frame8, effect8⟩ := step pre frame7 (by decide)
    (offset := 0x5f58) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105f58 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect7.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame7 (by decide) (offset := 8) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame7 (by decide) (offset := 8) (len := 8) (codeOffset := 0x5f58) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5f5d (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame7 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree8 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t7 t8 := by
    have h : AgreesExcept [.mem (stackPtr t7 + 8) 8, .rip] t7 t8 := by have h := effect8.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame7.rsp] at h
    exact h
  have part8 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t7 t8 :=
    scratch_store agree8 (by decide) (by decide)
  have mem8_8 : memLoad t8.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 := by
    have h : memLoad t8.external (stackPtr t7 + 8) 64 = t7.regValue .rax := effect8.writes
    rw [frame7.rsp] at h
    exact h.trans reg7_0
  have all8 := scratch_trans all7 part8
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x5f5d) (lea_r64_effect_step 0x105f5d 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect8.rip
    (inProgram_of_textOffset 0x5f65 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 12, .rip]; decide)
  have agree9 : AgreesExcept [.reg 12, .rip] t8 t9 := effect9.agrees
  have part9 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t8 t9 :=
    scratch_reg agree9 (by decide)
  have reg9_12 : t9.regValue .r12 = stackSlot s 264 := by
    have h : t9.regValue .r12 = stackPtr t8 + 264 := effect9.writes
    rw [frame8.rsp] at h
    exact h
  have all9 := scratch_trans all8 part9
  obtain ⟨t10, run10, frame10, effect10⟩ := step_registers pre frame9
    (offset := 0x5f65) (lea_r64_effect_step 0x105f65 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect9.rip
    (inProgram_of_textOffset 0x5f6a (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 2, .rip]; decide)
  have agree10 : AgreesExcept [.reg 2, .rip] t9 t10 := effect10.agrees
  have part10 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t9 t10 :=
    scratch_reg agree10 (by decide)
  have reg10_2 : t10.regValue .rdx = stackSlot s 8 := by
    have h : t10.regValue .rdx = stackPtr t9 + 8 := effect10.writes
    rw [frame9.rsp] at h
    exact h
  have all10 := scratch_trans all9 part10
  have reg10_12 : t10.regValue .r12 = stackSlot s 264 :=
    (agree10.read (n := 64) (r := 12) (by simp)).trans reg9_12
  obtain ⟨t11, run11, frame11, effect11⟩ := step_registers pre frame10
    (offset := 0x5f6a) (mov_r64_r64_effect_step 0x105f6a 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect10.rip
    (inProgram_of_textOffset 0x5f6d (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 7, .rip]; decide)
  have agree11 : AgreesExcept [.reg 7, .rip] t10 t11 := effect11.agrees
  have part11 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t10 t11 :=
    scratch_reg agree11 (by decide)
  have reg11_7 : t11.regValue .rdi = stackSlot s 264 := by
    exact effect11.writes.trans reg10_12
  have all11 := scratch_trans all10 part11
  have reg1_15 : t1.regValue .r15 = t.regValue .r15 :=
    (agree1.read (n := 64) (r := 15) (by simp)).trans (rfl)
  have reg2_15 : t2.regValue .r15 = t.regValue .r15 :=
    (agree2.read (n := 64) (r := 15) (by simp)).trans reg1_15
  have reg3_15 : t3.regValue .r15 = t.regValue .r15 :=
    (agree3.read (n := 64) (r := 15) (by simp)).trans reg2_15
  have reg4_15 : t4.regValue .r15 = t.regValue .r15 :=
    (agree4.read (n := 64) (r := 15) (by simp)).trans reg3_15
  have reg5_15 : t5.regValue .r15 = t.regValue .r15 :=
    (agree5.read (n := 64) (r := 15) (by simp)).trans reg4_15
  have reg6_15 : t6.regValue .r15 = t.regValue .r15 :=
    (agree6.read (n := 64) (r := 15) (by simp)).trans reg5_15
  have reg7_15 : t7.regValue .r15 = t.regValue .r15 :=
    (agree7.read (n := 64) (r := 15) (by simp)).trans reg6_15
  have reg8_15 : t8.regValue .r15 = t.regValue .r15 :=
    (agree8.read (n := 64) (r := 15) (by simp)).trans reg7_15
  have reg9_15 : t9.regValue .r15 = t.regValue .r15 :=
    (agree9.read (n := 64) (r := 15) (by simp)).trans reg8_15
  have reg10_15 : t10.regValue .r15 = t.regValue .r15 :=
    (agree10.read (n := 64) (r := 15) (by simp)).trans reg9_15
  have reg11_15 : t11.regValue .r15 = t.regValue .r15 :=
    (agree11.read (n := 64) (r := 15) (by simp)).trans reg10_15
  obtain ⟨t12, run12, frame12, effect12⟩ := step_registers pre frame11
    (offset := 0x5f6d) (mov_r64_r64_effect_step 0x105f6d 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect11.rip
    (inProgram_of_textOffset 0x5f70 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 6, .rip]; decide)
  have agree12 : AgreesExcept [.reg 6, .rip] t11 t12 := effect12.agrees
  have part12 : AgreesExcept (scratchComponents s [0, 1, 12, 2, 7, 6] 32) t11 t12 :=
    scratch_reg agree12 (by decide)
  have reg12_6 : t12.regValue .rsi = t.regValue .r15 := by
    exact effect12.writes.trans reg11_15
  have all12 := scratch_trans all11 part12
  have reg11_12 : t11.regValue .r12 = stackSlot s 264 :=
    (agree11.read (n := 64) (r := 12) (by simp)).trans reg10_12
  have reg12_12 : t12.regValue .r12 = stackSlot s 264 :=
    (agree12.read (n := 64) (r := 12) (by simp)).trans reg11_12
  have reg11_2 : t11.regValue .rdx = stackSlot s 8 :=
    (agree11.read (n := 64) (r := 2) (by simp)).trans reg10_2
  have reg12_2 : t12.regValue .rdx = stackSlot s 8 :=
    (agree12.read (n := 64) (r := 2) (by simp)).trans reg11_2
  have reg12_7 : t12.regValue .rdi = stackSlot s 264 :=
    (agree12.read (n := 64) (r := 7) (by simp)).trans reg11_7
  have mem9_8 : memLoad t9.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_8
  have mem10_8 : memLoad t10.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 := by
    rw [agree10.external (by simp [Component.Covers])]
    exact mem9_8
  have mem11_8 : memLoad t11.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_8
  have mem12_8 : memLoad t12.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 200) 64 := by
    rw [agree12.external (by simp [Component.Covers])]
    exact mem11_8
  have mem8_16 : memLoad t8.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_16
  have mem9_16 : memLoad t9.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_16
  have mem10_16 : memLoad t10.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 := by
    rw [agree10.external (by simp [Component.Covers])]
    exact mem9_16
  have mem11_16 : memLoad t11.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_16
  have mem12_16 : memLoad t12.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 208) 64 := by
    rw [agree12.external (by simp [Component.Covers])]
    exact mem11_16
  have mem5_24 : memLoad t5.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree5.external (by simp [Component.Covers])]
    exact mem4_24
  have mem6_24 : memLoad t6.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree6.external (by simp [Component.Covers])]
    exact mem5_24
  have mem7_24 : memLoad t7.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 :=
    (read_of_store agree7 (slots_apart (by decide) (by decide) (by decide))).trans mem6_24
  have mem8_24 : memLoad t8.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_24
  have mem9_24 : memLoad t9.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_24
  have mem10_24 : memLoad t10.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree10.external (by simp [Component.Covers])]
    exact mem9_24
  have mem11_24 : memLoad t11.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_24
  have mem12_24 : memLoad t12.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 216) 64 := by
    rw [agree12.external (by simp [Component.Covers])]
    exact mem11_24
  have mem3_32 : memLoad t3.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree3.external (by simp [Component.Covers])]
    exact mem2_32
  have mem4_32 : memLoad t4.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 :=
    (read_of_store agree4 (slots_apart (by decide) (by decide) (by decide))).trans mem3_32
  have mem5_32 : memLoad t5.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree5.external (by simp [Component.Covers])]
    exact mem4_32
  have mem6_32 : memLoad t6.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree6.external (by simp [Component.Covers])]
    exact mem5_32
  have mem7_32 : memLoad t7.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 :=
    (read_of_store agree7 (slots_apart (by decide) (by decide) (by decide))).trans mem6_32
  have mem8_32 : memLoad t8.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_32
  have mem9_32 : memLoad t9.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_32
  have mem10_32 : memLoad t10.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree10.external (by simp [Component.Covers])]
    exact mem9_32
  have mem11_32 : memLoad t11.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_32
  have mem12_32 : memLoad t12.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 224) 64 := by
    rw [agree12.external (by simp [Component.Covers])]
    exact mem11_32
  exact ⟨t12, (((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12), frame12, effect12.rip, all12, reg12_12, reg12_2, reg12_7, reg12_6, mem12_8, mem12_16, mem12_24, mem12_32⟩

end P256.Proofs.Projective.Double.CrossTerms
