import P256.Proofs.Projective.Double.CrossTerms.Memory

set_option autoImplicit false



namespace P256.Proofs.Projective.Double.CrossTerms

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem copyXY [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister) (state : FrameState s t 96 1016 728)
    (rip : t.RIP = 0x105dc3) (bx : t.regValue .rbx = s.regValue .rdi) :
    ∃ u, Advances boundary 20 t u ∧ FrameState s u 96 1016 728 ∧ u.RIP = 0x105e1c ∧
      AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t u ∧
      u.regValue .r15 = stackSlot s 72 ∧
      u.regValue .rsi = stackSlot s 40 ∧
      u.regValue .rdx = stackSlot s 8 ∧
      u.regValue .rdi = stackSlot s 72 ∧
      memLoad u.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 ∧
      memLoad u.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 ∧
      memLoad u.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 ∧
      memLoad u.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 ∧
      memLoad u.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 ∧
      memLoad u.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 ∧
      memLoad u.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 ∧
      memLoad u.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x5dc3) (mov_r64_m64_effect_step 0x105dc3 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨rip, ?_⟩; change MemReadable t (t.regValue .rbx + BitVec.ofNat 64 24) 8; rw [bx]; exact point_readable pre state (by decide))
    (inProgram_of_textOffset 0x5dc7 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree1 : AgreesExcept [.reg 0, .rip] t t1 := effect1.agrees
  have part1 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t t1 :=
    scratch_reg agree1 (by decide)
  have reg1_0 : t1.regValue .rax = memLoad t.external (s.regValue .rdi + 24) 64 := by
    have h : t1.regValue .rax = memLoad t.external (t.regValue .rbx + 24) 64 := effect1.writes
    rw [bx] at h
    exact h
  have all1 := part1
  obtain ⟨t2, run2, frame2, effect2⟩ := step pre frame1 (by decide)
    (offset := 0x5dc7) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105dc7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect1.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame1 (by decide) (offset := 64) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame1 (by decide) (offset := 64) (len := 8) (codeOffset := 0x5dc7) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5dcc (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame1 (offset := 64) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree2 : AgreesExcept [.mem (stackSlot s 64) 8, .rip] t1 t2 := by
    have h : AgreesExcept [.mem (stackPtr t1 + 64) 8, .rip] t1 t2 := by have h := effect2.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame1.rsp] at h
    exact h
  have part2 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t1 t2 :=
    scratch_store agree2 (by decide) (by decide)
  have mem2_64 : memLoad t2.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    have h : memLoad t2.external (stackPtr t1 + 64) 64 = t1.regValue .rax := effect2.writes
    rw [frame1.rsp] at h
    exact h.trans reg1_0
  have all2 := scratch_trans all1 part2
  have reg1_3 : t1.regValue .rbx = s.regValue .rdi :=
    (agree1.read (n := 64) (r := 3) (by simp)).trans (bx)
  have reg2_3 : t2.regValue .rbx = s.regValue .rdi :=
    (agree2.read (n := 64) (r := 3) (by simp)).trans reg1_3
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x5dcc) (mov_r64_m64_effect_step 0x105dcc 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect2.rip, ?_⟩; change MemReadable t2 (t2.regValue .rbx + BitVec.ofNat 64 16) 8; rw [reg2_3]; exact point_readable pre frame2 (by decide))
    (inProgram_of_textOffset 0x5dd0 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree3 : AgreesExcept [.reg 0, .rip] t2 t3 := effect3.agrees
  have part3 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t2 t3 :=
    scratch_reg agree3 (by decide)
  have reg3_0 : t3.regValue .rax = memLoad t.external (s.regValue .rdi + 16) 64 := by
    have h : t3.regValue .rax = memLoad t2.external (t2.regValue .rbx + 16) 64 := effect3.writes
    rw [reg2_3] at h
    exact h.trans (scratch_read all2 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 16) (plen := 8) (by decide) (by decide)))
  have all3 := scratch_trans all2 part3
  obtain ⟨t4, run4, frame4, effect4⟩ := step pre frame3 (by decide)
    (offset := 0x5dd0) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105dd0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect3.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame3 (by decide) (offset := 56) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame3 (by decide) (offset := 56) (len := 8) (codeOffset := 0x5dd0) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5dd5 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame3 (offset := 56) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree4 : AgreesExcept [.mem (stackSlot s 56) 8, .rip] t3 t4 := by
    have h : AgreesExcept [.mem (stackPtr t3 + 56) 8, .rip] t3 t4 := by have h := effect4.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame3.rsp] at h
    exact h
  have part4 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t3 t4 :=
    scratch_store agree4 (by decide) (by decide)
  have mem4_56 : memLoad t4.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    have h : memLoad t4.external (stackPtr t3 + 56) 64 = t3.regValue .rax := effect4.writes
    rw [frame3.rsp] at h
    exact h.trans reg3_0
  have all4 := scratch_trans all3 part4
  have reg3_3 : t3.regValue .rbx = s.regValue .rdi :=
    (agree3.read (n := 64) (r := 3) (by simp)).trans reg2_3
  have reg4_3 : t4.regValue .rbx = s.regValue .rdi :=
    (agree4.read (n := 64) (r := 3) (by simp)).trans reg3_3
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x5dd5) (mov_r64_m64_effect_step 0x105dd5 0x48 (by simp [RexWPrefix]) 0 (.base 3 .none) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect4.rip, ?_⟩; change MemReadable t4 (t4.regValue .rbx + BitVec.ofNat 64 0) 8; rw [reg4_3]; exact point_readable pre frame4 (by decide))
    (inProgram_of_textOffset 0x5dd8 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree5 : AgreesExcept [.reg 0, .rip] t4 t5 := effect5.agrees
  have part5 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t4 t5 :=
    scratch_reg agree5 (by decide)
  have reg5_0 : t5.regValue .rax = memLoad t.external (s.regValue .rdi + 0) 64 := by
    have h : t5.regValue .rax = memLoad t4.external (t4.regValue .rbx + 0) 64 := effect5.writes
    rw [reg4_3] at h
    exact h.trans (scratch_read all4 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 0) (plen := 8) (by decide) (by decide)))
  have all5 := scratch_trans all4 part5
  have reg5_3 : t5.regValue .rbx = s.regValue .rdi :=
    (agree5.read (n := 64) (r := 3) (by simp)).trans reg4_3
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x5dd8) (mov_r64_m64_effect_step 0x105dd8 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect5.rip, ?_⟩; change MemReadable t5 (t5.regValue .rbx + BitVec.ofNat 64 8) 8; rw [reg5_3]; exact point_readable pre frame5 (by decide))
    (inProgram_of_textOffset 0x5ddc (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 1, .rip]; decide)
  have agree6 : AgreesExcept [.reg 1, .rip] t5 t6 := effect6.agrees
  have part6 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t5 t6 :=
    scratch_reg agree6 (by decide)
  have reg6_1 : t6.regValue .rcx = memLoad t.external (s.regValue .rdi + 8) 64 := by
    have h : t6.regValue .rcx = memLoad t5.external (t5.regValue .rbx + 8) 64 := effect6.writes
    rw [reg5_3] at h
    exact h.trans (scratch_read all5 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 8) (plen := 8) (by decide) (by decide)))
  have all6 := scratch_trans all5 part6
  obtain ⟨t7, run7, frame7, effect7⟩ := step pre frame6 (by decide)
    (offset := 0x5ddc) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105ddc 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect6.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame6 (by decide) (offset := 48) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame6 (by decide) (offset := 48) (len := 8) (codeOffset := 0x5ddc) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5de1 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame6 (offset := 48) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree7 : AgreesExcept [.mem (stackSlot s 48) 8, .rip] t6 t7 := by
    have h : AgreesExcept [.mem (stackPtr t6 + 48) 8, .rip] t6 t7 := by have h := effect7.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame6.rsp] at h
    exact h
  have part7 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t6 t7 :=
    scratch_store agree7 (by decide) (by decide)
  have mem7_48 : memLoad t7.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    have h : memLoad t7.external (stackPtr t6 + 48) 64 = t6.regValue .rcx := effect7.writes
    rw [frame6.rsp] at h
    exact h.trans reg6_1
  have all7 := scratch_trans all6 part7
  have reg6_0 : t6.regValue .rax = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (agree6.read (n := 64) (r := 0) (by simp)).trans reg5_0
  have reg7_0 : t7.regValue .rax = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (agree7.read (n := 64) (r := 0) (by simp)).trans reg6_0
  obtain ⟨t8, run8, frame8, effect8⟩ := step pre frame7 (by decide)
    (offset := 0x5de1) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105de1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect7.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame7 (by decide) (offset := 40) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame7 (by decide) (offset := 40) (len := 8) (codeOffset := 0x5de1) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5de6 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame7 (offset := 40) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree8 : AgreesExcept [.mem (stackSlot s 40) 8, .rip] t7 t8 := by
    have h : AgreesExcept [.mem (stackPtr t7 + 40) 8, .rip] t7 t8 := by have h := effect8.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame7.rsp] at h
    exact h
  have part8 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t7 t8 :=
    scratch_store agree8 (by decide) (by decide)
  have mem8_40 : memLoad t8.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    have h : memLoad t8.external (stackPtr t7 + 40) 64 = t7.regValue .rax := effect8.writes
    rw [frame7.rsp] at h
    exact h.trans reg7_0
  have all8 := scratch_trans all7 part8
  have reg6_3 : t6.regValue .rbx = s.regValue .rdi :=
    (agree6.read (n := 64) (r := 3) (by simp)).trans reg5_3
  have reg7_3 : t7.regValue .rbx = s.regValue .rdi :=
    (agree7.read (n := 64) (r := 3) (by simp)).trans reg6_3
  have reg8_3 : t8.regValue .rbx = s.regValue .rdi :=
    (agree8.read (n := 64) (r := 3) (by simp)).trans reg7_3
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x5de6) (mov_r64_m64_effect_step 0x105de6 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 56)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect8.rip, ?_⟩; change MemReadable t8 (t8.regValue .rbx + BitVec.ofNat 64 56) 8; rw [reg8_3]; exact point_readable pre frame8 (by decide))
    (inProgram_of_textOffset 0x5dea (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree9 : AgreesExcept [.reg 0, .rip] t8 t9 := effect9.agrees
  have part9 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t8 t9 :=
    scratch_reg agree9 (by decide)
  have reg9_0 : t9.regValue .rax = memLoad t.external (s.regValue .rdi + 56) 64 := by
    have h : t9.regValue .rax = memLoad t8.external (t8.regValue .rbx + 56) 64 := effect9.writes
    rw [reg8_3] at h
    exact h.trans (scratch_read all8 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 56) (plen := 8) (by decide) (by decide)))
  have all9 := scratch_trans all8 part9
  obtain ⟨t10, run10, frame10, effect10⟩ := step pre frame9 (by decide)
    (offset := 0x5dea) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105dea 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect9.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame9 (by decide) (offset := 32) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame9 (by decide) (offset := 32) (len := 8) (codeOffset := 0x5dea) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5def (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame9 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree10 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t9 t10 := by
    have h : AgreesExcept [.mem (stackPtr t9 + 32) 8, .rip] t9 t10 := by have h := effect10.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame9.rsp] at h
    exact h
  have part10 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t9 t10 :=
    scratch_store agree10 (by decide) (by decide)
  have mem10_32 : memLoad t10.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    have h : memLoad t10.external (stackPtr t9 + 32) 64 = t9.regValue .rax := effect10.writes
    rw [frame9.rsp] at h
    exact h.trans reg9_0
  have all10 := scratch_trans all9 part10
  have reg9_3 : t9.regValue .rbx = s.regValue .rdi :=
    (agree9.read (n := 64) (r := 3) (by simp)).trans reg8_3
  have reg10_3 : t10.regValue .rbx = s.regValue .rdi :=
    (agree10.read (n := 64) (r := 3) (by simp)).trans reg9_3
  obtain ⟨t11, run11, frame11, effect11⟩ := step_registers pre frame10
    (offset := 0x5def) (mov_r64_m64_effect_step 0x105def 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 48)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect10.rip, ?_⟩; change MemReadable t10 (t10.regValue .rbx + BitVec.ofNat 64 48) 8; rw [reg10_3]; exact point_readable pre frame10 (by decide))
    (inProgram_of_textOffset 0x5df3 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree11 : AgreesExcept [.reg 0, .rip] t10 t11 := effect11.agrees
  have part11 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t10 t11 :=
    scratch_reg agree11 (by decide)
  have reg11_0 : t11.regValue .rax = memLoad t.external (s.regValue .rdi + 48) 64 := by
    have h : t11.regValue .rax = memLoad t10.external (t10.regValue .rbx + 48) 64 := effect11.writes
    rw [reg10_3] at h
    exact h.trans (scratch_read all10 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 48) (plen := 8) (by decide) (by decide)))
  have all11 := scratch_trans all10 part11
  obtain ⟨t12, run12, frame12, effect12⟩ := step pre frame11 (by decide)
    (offset := 0x5df3) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105df3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect11.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame11 (by decide) (offset := 24) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame11 (by decide) (offset := 24) (len := 8) (codeOffset := 0x5df3) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5df8 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame11 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree12 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t11 t12 := by
    have h : AgreesExcept [.mem (stackPtr t11 + 24) 8, .rip] t11 t12 := by have h := effect12.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame11.rsp] at h
    exact h
  have part12 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t11 t12 :=
    scratch_store agree12 (by decide) (by decide)
  have mem12_24 : memLoad t12.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    have h : memLoad t12.external (stackPtr t11 + 24) 64 = t11.regValue .rax := effect12.writes
    rw [frame11.rsp] at h
    exact h.trans reg11_0
  have all12 := scratch_trans all11 part12
  have reg11_3 : t11.regValue .rbx = s.regValue .rdi :=
    (agree11.read (n := 64) (r := 3) (by simp)).trans reg10_3
  have reg12_3 : t12.regValue .rbx = s.regValue .rdi :=
    (agree12.read (n := 64) (r := 3) (by simp)).trans reg11_3
  obtain ⟨t13, run13, frame13, effect13⟩ := step_registers pre frame12
    (offset := 0x5df8) (mov_r64_m64_effect_step 0x105df8 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect12.rip, ?_⟩; change MemReadable t12 (t12.regValue .rbx + BitVec.ofNat 64 32) 8; rw [reg12_3]; exact point_readable pre frame12 (by decide))
    (inProgram_of_textOffset 0x5dfc (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 0, .rip]; decide)
  have agree13 : AgreesExcept [.reg 0, .rip] t12 t13 := effect13.agrees
  have part13 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t12 t13 :=
    scratch_reg agree13 (by decide)
  have reg13_0 : t13.regValue .rax = memLoad t.external (s.regValue .rdi + 32) 64 := by
    have h : t13.regValue .rax = memLoad t12.external (t12.regValue .rbx + 32) 64 := effect13.writes
    rw [reg12_3] at h
    exact h.trans (scratch_read all12 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 32) (plen := 8) (by decide) (by decide)))
  have all13 := scratch_trans all12 part13
  have reg13_3 : t13.regValue .rbx = s.regValue .rdi :=
    (agree13.read (n := 64) (r := 3) (by simp)).trans reg12_3
  obtain ⟨t14, run14, frame14, effect14⟩ := step_registers pre frame13
    (offset := 0x5dfc) (mov_r64_m64_effect_step 0x105dfc 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect13.rip, ?_⟩; change MemReadable t13 (t13.regValue .rbx + BitVec.ofNat 64 40) 8; rw [reg13_3]; exact point_readable pre frame13 (by decide))
    (inProgram_of_textOffset 0x5e00 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 1, .rip]; decide)
  have agree14 : AgreesExcept [.reg 1, .rip] t13 t14 := effect14.agrees
  have part14 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t13 t14 :=
    scratch_reg agree14 (by decide)
  have reg14_1 : t14.regValue .rcx = memLoad t.external (s.regValue .rdi + 40) 64 := by
    have h : t14.regValue .rcx = memLoad t13.external (t13.regValue .rbx + 40) 64 := effect14.writes
    rw [reg13_3] at h
    exact h.trans (scratch_read all13 (stack_point_apart pre (offset := 8) (len := 64) (poffset := 40) (plen := 8) (by decide) (by decide)))
  have all14 := scratch_trans all13 part14
  obtain ⟨t15, run15, frame15, effect15⟩ := step pre frame14 (by decide)
    (offset := 0x5e00) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105e00 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect14.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame14 (by decide) (offset := 16) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame14 (by decide) (offset := 16) (len := 8) (codeOffset := 0x5e00) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5e05 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame14 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree15 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t14 t15 := by
    have h : AgreesExcept [.mem (stackPtr t14 + 16) 8, .rip] t14 t15 := by have h := effect15.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame14.rsp] at h
    exact h
  have part15 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t14 t15 :=
    scratch_store agree15 (by decide) (by decide)
  have mem15_16 : memLoad t15.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 := by
    have h : memLoad t15.external (stackPtr t14 + 16) 64 = t14.regValue .rcx := effect15.writes
    rw [frame14.rsp] at h
    exact h.trans reg14_1
  have all15 := scratch_trans all14 part15
  have reg14_0 : t14.regValue .rax = memLoad t.external (s.regValue .rdi + 32) 64 :=
    (agree14.read (n := 64) (r := 0) (by simp)).trans reg13_0
  have reg15_0 : t15.regValue .rax = memLoad t.external (s.regValue .rdi + 32) 64 :=
    (agree15.read (n := 64) (r := 0) (by simp)).trans reg14_0
  obtain ⟨t16, run16, frame16, effect16⟩ := step pre frame15 (by decide)
    (offset := 0x5e05) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105e05 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) (by refine ⟨effect15.rip, ?_, ?_⟩; exact stack_writable (frameOffset := 728) pre frame15 (by decide) (offset := 8) (len := 8) (by decide) (by decide); exact stack_code (frameOffset := 728) pre frame15 (by decide) (offset := 8) (len := 8) (codeOffset := 0x5e05) (codeLen := 5) (by decide) (by decide))
    (inProgram_of_textOffset 0x5e0a (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame15 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have agree16 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t15 t16 := by
    have h : AgreesExcept [.mem (stackPtr t15 + 8) 8, .rip] t15 t16 := by have h := effect16.agrees; rw [movM64R64Effect_components] at h; exact h
    rw [frame15.rsp] at h
    exact h
  have part16 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t15 t16 :=
    scratch_store agree16 (by decide) (by decide)
  have mem16_8 : memLoad t16.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 := by
    have h : memLoad t16.external (stackPtr t15 + 8) 64 = t15.regValue .rax := effect16.writes
    rw [frame15.rsp] at h
    exact h.trans reg15_0
  have all16 := scratch_trans all15 part16
  obtain ⟨t17, run17, frame17, effect17⟩ := step_registers pre frame16
    (offset := 0x5e0a) (lea_r64_effect_step 0x105e0a 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect16.rip
    (inProgram_of_textOffset 0x5e0f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 15, .rip]; decide)
  have agree17 : AgreesExcept [.reg 15, .rip] t16 t17 := effect17.agrees
  have part17 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t16 t17 :=
    scratch_reg agree17 (by decide)
  have reg17_15 : t17.regValue .r15 = stackSlot s 72 := by
    have h : t17.regValue .r15 = stackPtr t16 + 72 := effect17.writes
    rw [frame16.rsp] at h
    exact h
  have all17 := scratch_trans all16 part17
  obtain ⟨t18, run18, frame18, effect18⟩ := step_registers pre frame17
    (offset := 0x5e0f) (lea_r64_effect_step 0x105e0f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect17.rip
    (inProgram_of_textOffset 0x5e14 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 6, .rip]; decide)
  have agree18 : AgreesExcept [.reg 6, .rip] t17 t18 := effect18.agrees
  have part18 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t17 t18 :=
    scratch_reg agree18 (by decide)
  have reg18_6 : t18.regValue .rsi = stackSlot s 40 := by
    have h : t18.regValue .rsi = stackPtr t17 + 40 := effect18.writes
    rw [frame17.rsp] at h
    exact h
  have all18 := scratch_trans all17 part18
  obtain ⟨t19, run19, frame19, effect19⟩ := step_registers pre frame18
    (offset := 0x5e14) (lea_r64_effect_step 0x105e14 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel) effect18.rip
    (inProgram_of_textOffset 0x5e19 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 2, .rip]; decide)
  have agree19 : AgreesExcept [.reg 2, .rip] t18 t19 := effect19.agrees
  have part19 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t18 t19 :=
    scratch_reg agree19 (by decide)
  have reg19_2 : t19.regValue .rdx = stackSlot s 8 := by
    have h : t19.regValue .rdx = stackPtr t18 + 8 := effect19.writes
    rw [frame18.rsp] at h
    exact h
  have all19 := scratch_trans all18 part19
  have reg18_15 : t18.regValue .r15 = stackSlot s 72 :=
    (agree18.read (n := 64) (r := 15) (by simp)).trans reg17_15
  have reg19_15 : t19.regValue .r15 = stackSlot s 72 :=
    (agree19.read (n := 64) (r := 15) (by simp)).trans reg18_15
  obtain ⟨t20, run20, frame20, effect20⟩ := step_registers pre frame19
    (offset := 0x5e19) (mov_r64_r64_effect_step 0x105e19 0x4c 0xff (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel) effect19.rip
    (inProgram_of_textOffset 0x5e1c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [.reg 7, .rip]; decide)
  have agree20 : AgreesExcept [.reg 7, .rip] t19 t20 := effect20.agrees
  have part20 : AgreesExcept (scratchComponents s [0, 1, 15, 6, 2, 7]) t19 t20 :=
    scratch_reg agree20 (by decide)
  have reg20_7 : t20.regValue .rdi = stackSlot s 72 := by
    exact effect20.writes.trans reg19_15
  have all20 := scratch_trans all19 part20
  have reg20_15 : t20.regValue .r15 = stackSlot s 72 :=
    (agree20.read (n := 64) (r := 15) (by simp)).trans reg19_15
  have reg19_6 : t19.regValue .rsi = stackSlot s 40 :=
    (agree19.read (n := 64) (r := 6) (by simp)).trans reg18_6
  have reg20_6 : t20.regValue .rsi = stackSlot s 40 :=
    (agree20.read (n := 64) (r := 6) (by simp)).trans reg19_6
  have reg20_2 : t20.regValue .rdx = stackSlot s 8 :=
    (agree20.read (n := 64) (r := 2) (by simp)).trans reg19_2
  have mem17_8 : memLoad t17.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_8
  have mem18_8 : memLoad t18.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_8
  have mem19_8 : memLoad t19.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_8
  have mem20_8 : memLoad t20.external (stackSlot s 8) 64 = memLoad t.external (s.regValue .rdi + 32) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_8
  have mem16_16 : memLoad t16.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_16
  have mem17_16 : memLoad t17.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_16
  have mem18_16 : memLoad t18.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_16
  have mem19_16 : memLoad t19.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_16
  have mem20_16 : memLoad t20.external (stackSlot s 16) 64 = memLoad t.external (s.regValue .rdi + 40) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_16
  have mem13_24 : memLoad t13.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_24
  have mem14_24 : memLoad t14.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_24
  have mem15_24 : memLoad t15.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_24
  have mem16_24 : memLoad t16.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_24
  have mem17_24 : memLoad t17.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_24
  have mem18_24 : memLoad t18.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_24
  have mem19_24 : memLoad t19.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_24
  have mem20_24 : memLoad t20.external (stackSlot s 24) 64 = memLoad t.external (s.regValue .rdi + 48) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_24
  have mem11_32 : memLoad t11.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_32
  have mem12_32 : memLoad t12.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 :=
    (read_of_store agree12 (slots_apart (by decide) (by decide) (by decide))).trans mem11_32
  have mem13_32 : memLoad t13.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_32
  have mem14_32 : memLoad t14.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_32
  have mem15_32 : memLoad t15.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_32
  have mem16_32 : memLoad t16.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_32
  have mem17_32 : memLoad t17.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_32
  have mem18_32 : memLoad t18.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_32
  have mem19_32 : memLoad t19.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_32
  have mem20_32 : memLoad t20.external (stackSlot s 32) 64 = memLoad t.external (s.regValue .rdi + 56) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_32
  have mem9_40 : memLoad t9.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_40
  have mem10_40 : memLoad t10.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (read_of_store agree10 (slots_apart (by decide) (by decide) (by decide))).trans mem9_40
  have mem11_40 : memLoad t11.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_40
  have mem12_40 : memLoad t12.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (read_of_store agree12 (slots_apart (by decide) (by decide) (by decide))).trans mem11_40
  have mem13_40 : memLoad t13.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_40
  have mem14_40 : memLoad t14.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_40
  have mem15_40 : memLoad t15.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_40
  have mem16_40 : memLoad t16.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_40
  have mem17_40 : memLoad t17.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_40
  have mem18_40 : memLoad t18.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_40
  have mem19_40 : memLoad t19.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_40
  have mem20_40 : memLoad t20.external (stackSlot s 40) 64 = memLoad t.external (s.regValue .rdi + 0) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_40
  have mem8_48 : memLoad t8.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_48
  have mem9_48 : memLoad t9.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_48
  have mem10_48 : memLoad t10.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 :=
    (read_of_store agree10 (slots_apart (by decide) (by decide) (by decide))).trans mem9_48
  have mem11_48 : memLoad t11.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_48
  have mem12_48 : memLoad t12.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 :=
    (read_of_store agree12 (slots_apart (by decide) (by decide) (by decide))).trans mem11_48
  have mem13_48 : memLoad t13.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_48
  have mem14_48 : memLoad t14.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_48
  have mem15_48 : memLoad t15.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_48
  have mem16_48 : memLoad t16.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_48
  have mem17_48 : memLoad t17.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_48
  have mem18_48 : memLoad t18.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_48
  have mem19_48 : memLoad t19.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_48
  have mem20_48 : memLoad t20.external (stackSlot s 48) 64 = memLoad t.external (s.regValue .rdi + 8) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_48
  have mem5_56 : memLoad t5.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree5.external (by simp [Component.Covers])]
    exact mem4_56
  have mem6_56 : memLoad t6.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree6.external (by simp [Component.Covers])]
    exact mem5_56
  have mem7_56 : memLoad t7.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree7 (slots_apart (by decide) (by decide) (by decide))).trans mem6_56
  have mem8_56 : memLoad t8.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_56
  have mem9_56 : memLoad t9.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_56
  have mem10_56 : memLoad t10.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree10 (slots_apart (by decide) (by decide) (by decide))).trans mem9_56
  have mem11_56 : memLoad t11.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_56
  have mem12_56 : memLoad t12.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree12 (slots_apart (by decide) (by decide) (by decide))).trans mem11_56
  have mem13_56 : memLoad t13.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_56
  have mem14_56 : memLoad t14.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_56
  have mem15_56 : memLoad t15.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_56
  have mem16_56 : memLoad t16.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_56
  have mem17_56 : memLoad t17.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_56
  have mem18_56 : memLoad t18.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_56
  have mem19_56 : memLoad t19.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_56
  have mem20_56 : memLoad t20.external (stackSlot s 56) 64 = memLoad t.external (s.regValue .rdi + 16) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_56
  have mem3_64 : memLoad t3.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree3.external (by simp [Component.Covers])]
    exact mem2_64
  have mem4_64 : memLoad t4.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree4 (slots_apart (by decide) (by decide) (by decide))).trans mem3_64
  have mem5_64 : memLoad t5.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree5.external (by simp [Component.Covers])]
    exact mem4_64
  have mem6_64 : memLoad t6.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree6.external (by simp [Component.Covers])]
    exact mem5_64
  have mem7_64 : memLoad t7.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree7 (slots_apart (by decide) (by decide) (by decide))).trans mem6_64
  have mem8_64 : memLoad t8.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree8 (slots_apart (by decide) (by decide) (by decide))).trans mem7_64
  have mem9_64 : memLoad t9.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree9.external (by simp [Component.Covers])]
    exact mem8_64
  have mem10_64 : memLoad t10.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree10 (slots_apart (by decide) (by decide) (by decide))).trans mem9_64
  have mem11_64 : memLoad t11.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree11.external (by simp [Component.Covers])]
    exact mem10_64
  have mem12_64 : memLoad t12.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree12 (slots_apart (by decide) (by decide) (by decide))).trans mem11_64
  have mem13_64 : memLoad t13.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree13.external (by simp [Component.Covers])]
    exact mem12_64
  have mem14_64 : memLoad t14.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree14.external (by simp [Component.Covers])]
    exact mem13_64
  have mem15_64 : memLoad t15.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree15 (slots_apart (by decide) (by decide) (by decide))).trans mem14_64
  have mem16_64 : memLoad t16.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 :=
    (read_of_store agree16 (slots_apart (by decide) (by decide) (by decide))).trans mem15_64
  have mem17_64 : memLoad t17.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree17.external (by simp [Component.Covers])]
    exact mem16_64
  have mem18_64 : memLoad t18.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree18.external (by simp [Component.Covers])]
    exact mem17_64
  have mem19_64 : memLoad t19.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree19.external (by simp [Component.Covers])]
    exact mem18_64
  have mem20_64 : memLoad t20.external (stackSlot s 64) 64 = memLoad t.external (s.regValue .rdi + 24) 64 := by
    rw [agree20.external (by simp [Component.Covers])]
    exact mem19_64
  exact ⟨t20, (((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20), frame20, effect20.rip, all20, reg20_15, reg20_6, reg20_2, reg20_7, mem20_8, mem20_16, mem20_24, mem20_32, mem20_40, mem20_48, mem20_56, mem20_64⟩

end P256.Proofs.Projective.Double.CrossTerms
