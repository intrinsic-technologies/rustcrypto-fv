import P256.Proofs.Projective.Double.Combinations.State

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

structure Combinations.ZZSumAt (s t : RamState) (point : Projective) : Prop
    extends BProductAt s t point where
  rbp : t.regValue .rbp = stackSlot s 72
  sum : MontgomeryAt t (stackSlot s 72)
    ((tripleZZ point + (values point).xx) % Operations.domain.p)

set_option maxRecDepth 2048 in
theorem Combinations.difference_prepare [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x1061ae)
    (input : BProductAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x106224 ∧ ZZSumAt s u point := by
  have r0_rbx : t.regValue .rbx = s.regValue .rdi := input.rbx
  have r0_r15 : t.regValue .r15 = stackSlot s 616 := input.r15
  have r0_r12 : t.regValue .r12 = stackSlot s 360 := input.r12
  have r0_r14 : t.regValue .r14 = stackSlot s 232 := input.r14
  have m0_104 : MontgomeryAt t (stackSlot s 104) ((values point).xx) := input.xx
  have m0_136 : MontgomeryAt t (stackSlot s 136) ((values point).yy) := input.yy
  have m0_520 : MontgomeryAt t (stackSlot s 520) ((values point).xProduct) := input.xProduct
  have m0_616 : MontgomeryAt t (stackSlot s 616) ((values point).yProduct) := input.yProduct
  have m0_360 : MontgomeryAt t (stackSlot s 360) (tripleZZ point) := input.zz3
  have m0_232 : MontgomeryAt t (stackSlot s 232) (bXZ point) := input.bxz
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x61ae) (mov_r64_m64_effect_step 0x1061ae 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip, stack_readable (frameOffset := 728) pre state (by decide) (offset := 128) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61b6 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag1 : AgreesExcept [.reg 0, .rip] t t1 := effect1.agrees
  have ext1 : t1.external = t.external := ag1.external (by simp [Component.Covers])
  have rip1 : t1.RIP = 0x1061b6 := effect1.rip
  have write1 : t1.regValue .rax = memLoad t.external (stackPtr t + 128#64) 64 := effect1.writes
  rw [state.rsp] at write1
  have r1_rax : t1.regValue .rax = memLoad t.external (stackSlot s 128) 64 := write1.trans (Eq.refl _)
  obtain ⟨t2, run2, frame2, effect2⟩ := step pre frame1 (by decide)
    (offset := 0x61b6) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061b6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip1, stack_writable (frameOffset := 728) pre frame1 (by decide) (offset := 64) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame1 (by decide) (offset := 64) (len := 8) (codeOffset := 0x61b6) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61bb (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame1 (offset := 64) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag2 : AgreesExcept [.mem (stackSlot s 64) 8, .rip] t1 t2 := by
    have h : AgreesExcept [.mem (stackPtr t1 + 64#64) 8, .rip] t1 t2 := by
      have h := effect2.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame1.rsp] at h
    exact h
  have rip2 : t2.RIP = 0x1061bb := effect2.rip
  have write2 : memLoad t2.external (stackPtr t1 + 64#64) 64 = t1.regValue .rax := effect2.writes
  rw [frame1.rsp] at write2
  have sw2 : memLoad t2.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 := write2.trans r1_rax
  have w1_120_0 : memLoad t1.external (stackSlot s 120) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by rw [ext1]
  have w2_120_0 : memLoad t2.external (stackSlot s 120) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_120_0
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x61bb) (mov_r64_m64_effect_step 0x1061bb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip2, stack_readable (frameOffset := 728) pre frame2 (by decide) (offset := 120) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61c0 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag3 : AgreesExcept [.reg 0, .rip] t2 t3 := effect3.agrees
  have ext3 : t3.external = t2.external := ag3.external (by simp [Component.Covers])
  have rip3 : t3.RIP = 0x1061c0 := effect3.rip
  have write3 : t3.regValue .rax = memLoad t2.external (stackPtr t2 + 120#64) 64 := effect3.writes
  rw [frame2.rsp] at write3
  have r3_rax : t3.regValue .rax = memLoad t.external (stackSlot s 120) 64 := write3.trans w2_120_0
  obtain ⟨t4, run4, frame4, effect4⟩ := step pre frame3 (by decide)
    (offset := 0x61c0) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061c0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip3, stack_writable (frameOffset := 728) pre frame3 (by decide) (offset := 56) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame3 (by decide) (offset := 56) (len := 8) (codeOffset := 0x61c0) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61c5 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame3 (offset := 56) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag4 : AgreesExcept [.mem (stackSlot s 56) 8, .rip] t3 t4 := by
    have h : AgreesExcept [.mem (stackPtr t3 + 56#64) 8, .rip] t3 t4 := by
      have h := effect4.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame3.rsp] at h
    exact h
  have rip4 : t4.RIP = 0x1061c5 := effect4.rip
  have write4 : memLoad t4.external (stackPtr t3 + 56#64) 64 = t3.regValue .rax := effect4.writes
  rw [frame3.rsp] at write4
  have sw4 : memLoad t4.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 := write4.trans r3_rax
  have w1_104_0 : memLoad t1.external (stackSlot s 104) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by rw [ext1]
  have w2_104_0 : memLoad t2.external (stackSlot s 104) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_104_0
  have w3_104_0 : memLoad t3.external (stackSlot s 104) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext3] using w2_104_0
  have w4_104_0 : memLoad t4.external (stackSlot s 104) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_104_0
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x61c5) (mov_r64_m64_effect_step 0x1061c5 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip4, stack_readable (frameOffset := 728) pre frame4 (by decide) (offset := 104) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61ca (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag5 : AgreesExcept [.reg 0, .rip] t4 t5 := effect5.agrees
  have ext5 : t5.external = t4.external := ag5.external (by simp [Component.Covers])
  have rip5 : t5.RIP = 0x1061ca := effect5.rip
  have write5 : t5.regValue .rax = memLoad t4.external (stackPtr t4 + 104#64) 64 := effect5.writes
  rw [frame4.rsp] at write5
  have r5_rax : t5.regValue .rax = memLoad t.external (stackSlot s 104) 64 := write5.trans w4_104_0
  have w1_112_0 : memLoad t1.external (stackSlot s 112) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by rw [ext1]
  have w2_112_0 : memLoad t2.external (stackSlot s 112) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_112_0
  have w3_112_0 : memLoad t3.external (stackSlot s 112) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext3] using w2_112_0
  have w4_112_0 : memLoad t4.external (stackSlot s 112) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_112_0
  have w5_112_0 : memLoad t5.external (stackSlot s 112) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext5] using w4_112_0
  obtain ⟨t6, run6, frame6, effect6⟩ := step_registers pre frame5
    (offset := 0x61ca) (mov_r64_m64_effect_step 0x1061ca 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip5, stack_readable (frameOffset := 728) pre frame5 (by decide) (offset := 112) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61cf (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide +kernel)
  have ag6 : AgreesExcept [.reg 1, .rip] t5 t6 := effect6.agrees
  have ext6 : t6.external = t5.external := ag6.external (by simp [Component.Covers])
  have rip6 : t6.RIP = 0x1061cf := effect6.rip
  have write6 : t6.regValue .rcx = memLoad t5.external (stackPtr t5 + 112#64) 64 := effect6.writes
  rw [frame5.rsp] at write6
  have r6_rcx : t6.regValue .rcx = memLoad t.external (stackSlot s 112) 64 := write6.trans w5_112_0
  obtain ⟨t7, run7, frame7, effect7⟩ := step pre frame6 (by decide)
    (offset := 0x61cf) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061cf 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip6, stack_writable (frameOffset := 728) pre frame6 (by decide) (offset := 48) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame6 (by decide) (offset := 48) (len := 8) (codeOffset := 0x61cf) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61d4 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame6 (offset := 48) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag7 : AgreesExcept [.mem (stackSlot s 48) 8, .rip] t6 t7 := by
    have h : AgreesExcept [.mem (stackPtr t6 + 48#64) 8, .rip] t6 t7 := by
      have h := effect7.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame6.rsp] at h
    exact h
  have rip7 : t7.RIP = 0x1061d4 := effect7.rip
  have write7 : memLoad t7.external (stackPtr t6 + 48#64) 64 = t6.regValue .rcx := effect7.writes
  rw [frame6.rsp] at write7
  have sw7 : memLoad t7.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 := write7.trans r6_rcx
  have r6_rax : t6.regValue .rax = memLoad t.external (stackSlot s 104) 64 :=
    (ag6.read (n := 64) (r := 0) (by simp)).trans r5_rax
  have r7_rax : t7.regValue .rax = memLoad t.external (stackSlot s 104) 64 :=
    (ag7.read (n := 64) (r := 0) (by simp)).trans r6_rax
  obtain ⟨t8, run8, frame8, effect8⟩ := step pre frame7 (by decide)
    (offset := 0x61d4) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061d4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip7, stack_writable (frameOffset := 728) pre frame7 (by decide) (offset := 40) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame7 (by decide) (offset := 40) (len := 8) (codeOffset := 0x61d4) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61d9 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame7 (offset := 40) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag8 : AgreesExcept [.mem (stackSlot s 40) 8, .rip] t7 t8 := by
    have h : AgreesExcept [.mem (stackPtr t7 + 40#64) 8, .rip] t7 t8 := by
      have h := effect8.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame7.rsp] at h
    exact h
  have rip8 : t8.RIP = 0x1061d9 := effect8.rip
  have write8 : memLoad t8.external (stackPtr t7 + 40#64) 64 = t7.regValue .rax := effect8.writes
  rw [frame7.rsp] at write8
  have sw8 : memLoad t8.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 := write8.trans r7_rax
  have w1_384_0 : memLoad t1.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by rw [ext1]
  have w2_384_0 : memLoad t2.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_384_0
  have w3_384_0 : memLoad t3.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext3] using w2_384_0
  have w4_384_0 : memLoad t4.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_384_0
  have w5_384_0 : memLoad t5.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext5] using w4_384_0
  have w6_384_0 : memLoad t6.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext6] using w5_384_0
  have w7_384_0 : memLoad t7.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_384_0
  have w8_384_0 : memLoad t8.external (stackSlot s 384) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_384_0
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x61d9) (mov_r64_m64_effect_step 0x1061d9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 384)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip8, stack_readable (frameOffset := 728) pre frame8 (by decide) (offset := 384) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61e1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag9 : AgreesExcept [.reg 0, .rip] t8 t9 := effect9.agrees
  have ext9 : t9.external = t8.external := ag9.external (by simp [Component.Covers])
  have rip9 : t9.RIP = 0x1061e1 := effect9.rip
  have write9 : t9.regValue .rax = memLoad t8.external (stackPtr t8 + 384#64) 64 := effect9.writes
  rw [frame8.rsp] at write9
  have r9_rax : t9.regValue .rax = memLoad t.external (stackSlot s 384) 64 := write9.trans w8_384_0
  obtain ⟨t10, run10, frame10, effect10⟩ := step pre frame9 (by decide)
    (offset := 0x61e1) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061e1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip9, stack_writable (frameOffset := 728) pre frame9 (by decide) (offset := 32) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame9 (by decide) (offset := 32) (len := 8) (codeOffset := 0x61e1) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61e6 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame9 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag10 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t9 t10 := by
    have h : AgreesExcept [.mem (stackPtr t9 + 32#64) 8, .rip] t9 t10 := by
      have h := effect10.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame9.rsp] at h
    exact h
  have rip10 : t10.RIP = 0x1061e6 := effect10.rip
  have write10 : memLoad t10.external (stackPtr t9 + 32#64) 64 = t9.regValue .rax := effect10.writes
  rw [frame9.rsp] at write10
  have sw10 : memLoad t10.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 := write10.trans r9_rax
  have w1_376_0 : memLoad t1.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by rw [ext1]
  have w2_376_0 : memLoad t2.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_376_0
  have w3_376_0 : memLoad t3.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext3] using w2_376_0
  have w4_376_0 : memLoad t4.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_376_0
  have w5_376_0 : memLoad t5.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext5] using w4_376_0
  have w6_376_0 : memLoad t6.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext6] using w5_376_0
  have w7_376_0 : memLoad t7.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_376_0
  have w8_376_0 : memLoad t8.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_376_0
  have w9_376_0 : memLoad t9.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext9] using w8_376_0
  have w10_376_0 : memLoad t10.external (stackSlot s 376) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_376_0
  obtain ⟨t11, run11, frame11, effect11⟩ := step_registers pre frame10
    (offset := 0x61e6) (mov_r64_m64_effect_step 0x1061e6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 376)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip10, stack_readable (frameOffset := 728) pre frame10 (by decide) (offset := 376) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61ee (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag11 : AgreesExcept [.reg 0, .rip] t10 t11 := effect11.agrees
  have ext11 : t11.external = t10.external := ag11.external (by simp [Component.Covers])
  have rip11 : t11.RIP = 0x1061ee := effect11.rip
  have write11 : t11.regValue .rax = memLoad t10.external (stackPtr t10 + 376#64) 64 := effect11.writes
  rw [frame10.rsp] at write11
  have r11_rax : t11.regValue .rax = memLoad t.external (stackSlot s 376) 64 := write11.trans w10_376_0
  obtain ⟨t12, run12, frame12, effect12⟩ := step pre frame11 (by decide)
    (offset := 0x61ee) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1061ee 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip11, stack_writable (frameOffset := 728) pre frame11 (by decide) (offset := 24) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame11 (by decide) (offset := 24) (len := 8) (codeOffset := 0x61ee) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x61f3 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame11 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag12 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t11 t12 := by
    have h : AgreesExcept [.mem (stackPtr t11 + 24#64) 8, .rip] t11 t12 := by
      have h := effect12.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame11.rsp] at h
    exact h
  have rip12 : t12.RIP = 0x1061f3 := effect12.rip
  have write12 : memLoad t12.external (stackPtr t11 + 24#64) 64 = t11.regValue .rax := effect12.writes
  rw [frame11.rsp] at write12
  have sw12 : memLoad t12.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 := write12.trans r11_rax
  have w1_360_0 : memLoad t1.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by rw [ext1]
  have w2_360_0 : memLoad t2.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_360_0
  have w3_360_0 : memLoad t3.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext3] using w2_360_0
  have w4_360_0 : memLoad t4.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_360_0
  have w5_360_0 : memLoad t5.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext5] using w4_360_0
  have w6_360_0 : memLoad t6.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext6] using w5_360_0
  have w7_360_0 : memLoad t7.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_360_0
  have w8_360_0 : memLoad t8.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_360_0
  have w9_360_0 : memLoad t9.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext9] using w8_360_0
  have w10_360_0 : memLoad t10.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_360_0
  have w11_360_0 : memLoad t11.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext11] using w10_360_0
  have w12_360_0 : memLoad t12.external (stackSlot s 360) 64 = memLoad t.external (stackSlot s 360) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_360_0
  obtain ⟨t13, run13, frame13, effect13⟩ := step_registers pre frame12
    (offset := 0x61f3) (mov_r64_m64_effect_step 0x1061f3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 360)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip12, stack_readable (frameOffset := 728) pre frame12 (by decide) (offset := 360) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x61fb (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag13 : AgreesExcept [.reg 0, .rip] t12 t13 := effect13.agrees
  have ext13 : t13.external = t12.external := ag13.external (by simp [Component.Covers])
  have rip13 : t13.RIP = 0x1061fb := effect13.rip
  have write13 : t13.regValue .rax = memLoad t12.external (stackPtr t12 + 360#64) 64 := effect13.writes
  rw [frame12.rsp] at write13
  have r13_rax : t13.regValue .rax = memLoad t.external (stackSlot s 360) 64 := write13.trans w12_360_0
  have w1_368_0 : memLoad t1.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by rw [ext1]
  have w2_368_0 : memLoad t2.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag2 (by decide) (by decide) (by decide)).trans w1_368_0
  have w3_368_0 : memLoad t3.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext3] using w2_368_0
  have w4_368_0 : memLoad t4.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_368_0
  have w5_368_0 : memLoad t5.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext5] using w4_368_0
  have w6_368_0 : memLoad t6.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext6] using w5_368_0
  have w7_368_0 : memLoad t7.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_368_0
  have w8_368_0 : memLoad t8.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_368_0
  have w9_368_0 : memLoad t9.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext9] using w8_368_0
  have w10_368_0 : memLoad t10.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_368_0
  have w11_368_0 : memLoad t11.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext11] using w10_368_0
  have w12_368_0 : memLoad t12.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_368_0
  have w13_368_0 : memLoad t13.external (stackSlot s 368) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext13] using w12_368_0
  obtain ⟨t14, run14, frame14, effect14⟩ := step_registers pre frame13
    (offset := 0x61fb) (mov_r64_m64_effect_step 0x1061fb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip13, stack_readable (frameOffset := 728) pre frame13 (by decide) (offset := 368) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6203 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide +kernel)
  have ag14 : AgreesExcept [.reg 1, .rip] t13 t14 := effect14.agrees
  have ext14 : t14.external = t13.external := ag14.external (by simp [Component.Covers])
  have rip14 : t14.RIP = 0x106203 := effect14.rip
  have write14 : t14.regValue .rcx = memLoad t13.external (stackPtr t13 + 368#64) 64 := effect14.writes
  rw [frame13.rsp] at write14
  have r14_rcx : t14.regValue .rcx = memLoad t.external (stackSlot s 368) 64 := write14.trans w13_368_0
  obtain ⟨t15, run15, frame15, effect15⟩ := step pre frame14 (by decide)
    (offset := 0x6203) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106203 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip14, stack_writable (frameOffset := 728) pre frame14 (by decide) (offset := 16) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame14 (by decide) (offset := 16) (len := 8) (codeOffset := 0x6203) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6208 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame14 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag15 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t14 t15 := by
    have h : AgreesExcept [.mem (stackPtr t14 + 16#64) 8, .rip] t14 t15 := by
      have h := effect15.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame14.rsp] at h
    exact h
  have rip15 : t15.RIP = 0x106208 := effect15.rip
  have write15 : memLoad t15.external (stackPtr t14 + 16#64) 64 = t14.regValue .rcx := effect15.writes
  rw [frame14.rsp] at write15
  have sw15 : memLoad t15.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 := write15.trans r14_rcx
  have r14_rax : t14.regValue .rax = memLoad t.external (stackSlot s 360) 64 :=
    (ag14.read (n := 64) (r := 0) (by simp)).trans r13_rax
  have r15_rax : t15.regValue .rax = memLoad t.external (stackSlot s 360) 64 :=
    (ag15.read (n := 64) (r := 0) (by simp)).trans r14_rax
  obtain ⟨t16, run16, frame16, effect16⟩ := step pre frame15 (by decide)
    (offset := 0x6208) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106208 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip15, stack_writable (frameOffset := 728) pre frame15 (by decide) (offset := 8) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame15 (by decide) (offset := 8) (len := 8) (codeOffset := 0x6208) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x620d (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame15 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag16 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t15 t16 := by
    have h : AgreesExcept [.mem (stackPtr t15 + 8#64) 8, .rip] t15 t16 := by
      have h := effect16.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame15.rsp] at h
    exact h
  have rip16 : t16.RIP = 0x10620d := effect16.rip
  have write16 : memLoad t16.external (stackPtr t15 + 8#64) 64 = t15.regValue .rax := effect16.writes
  rw [frame15.rsp] at write16
  have sw16 : memLoad t16.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 360) 64 := write16.trans r15_rax
  obtain ⟨t17, run17, frame17, effect17⟩ := step_registers pre frame16
    (offset := 0x620d) (lea_r64_effect_step 0x10620d 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip16
    (inProgram_of_textOffset 0x6212 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 5, .rip]; decide +kernel)
  have ag17 : AgreesExcept [.reg 5, .rip] t16 t17 := effect17.agrees
  have ext17 : t17.external = t16.external := ag17.external (by simp [Component.Covers])
  have rip17 : t17.RIP = 0x106212 := effect17.rip
  have write17 : t17.regValue .rbp = stackPtr t16 + 72#64 := effect17.writes
  rw [frame16.rsp] at write17
  have r17_rbp : t17.regValue .rbp = stackSlot s 72 := write17
  obtain ⟨t18, run18, frame18, effect18⟩ := step_registers pre frame17
    (offset := 0x6212) (lea_r64_effect_step 0x106212 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip17
    (inProgram_of_textOffset 0x6217 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag18 : AgreesExcept [.reg 6, .rip] t17 t18 := effect18.agrees
  have ext18 : t18.external = t17.external := ag18.external (by simp [Component.Covers])
  have rip18 : t18.RIP = 0x106217 := effect18.rip
  have write18 : t18.regValue .rsi = stackPtr t17 + 8#64 := effect18.writes
  rw [frame17.rsp] at write18
  have r18_rsi : t18.regValue .rsi = stackSlot s 8 := write18
  obtain ⟨t19, run19, frame19, effect19⟩ := step_registers pre frame18
    (offset := 0x6217) (lea_r64_effect_step 0x106217 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip18
    (inProgram_of_textOffset 0x621c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag19 : AgreesExcept [.reg 2, .rip] t18 t19 := effect19.agrees
  have ext19 : t19.external = t18.external := ag19.external (by simp [Component.Covers])
  have rip19 : t19.RIP = 0x10621c := effect19.rip
  have write19 : t19.regValue .rdx = stackPtr t18 + 40#64 := effect19.writes
  rw [frame18.rsp] at write19
  have r19_rdx : t19.regValue .rdx = stackSlot s 40 := write19
  have r18_rbp : t18.regValue .rbp = stackSlot s 72 :=
    (ag18.read (n := 64) (r := 5) (by simp)).trans r17_rbp
  have r19_rbp : t19.regValue .rbp = stackSlot s 72 :=
    (ag19.read (n := 64) (r := 5) (by simp)).trans r18_rbp
  obtain ⟨t20, run20, frame20, effect20⟩ := step_registers pre frame19
    (offset := 0x621c) (mov_r64_r64_effect_step 0x10621c 0x48 0xef (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip19
    (inProgram_of_textOffset 0x621f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag20 : AgreesExcept [.reg 7, .rip] t19 t20 := effect20.agrees
  have ext20 : t20.external = t19.external := ag20.external (by simp [Component.Covers])
  have rip20 : t20.RIP = 0x10621f := effect20.rip
  have write20 : t20.regValue .rdi = t19.regValue .rbp := effect20.writes
  have r20_rdi : t20.regValue .rdi = stackSlot s 72 := write20.trans r19_rbp
  have r19_rsi : t19.regValue .rsi = stackSlot s 8 :=
    (ag19.read (n := 64) (r := 6) (by simp)).trans r18_rsi
  have r20_rsi : t20.regValue .rsi = stackSlot s 8 :=
    (ag20.read (n := 64) (r := 6) (by simp)).trans r19_rsi
  have w17_8_0 : memLoad t17.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext17] using sw16
  have w18_8_0 : memLoad t18.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext18] using w17_8_0
  have w19_8_0 : memLoad t19.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext19] using w18_8_0
  have w20_8_0 : memLoad t20.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 360) 64 :=
    by simpa only [ext20] using w19_8_0
  have w16_16_0 : memLoad t16.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans sw15
  have w17_16_0 : memLoad t17.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext17] using w16_16_0
  have w18_16_0 : memLoad t18.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext18] using w17_16_0
  have w19_16_0 : memLoad t19.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext19] using w18_16_0
  have w20_16_0 : memLoad t20.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 368) 64 :=
    by simpa only [ext20] using w19_16_0
  have w13_24_0 : memLoad t13.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext13] using sw12
  have w14_24_0 : memLoad t14.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext14] using w13_24_0
  have w15_24_0 : memLoad t15.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_24_0
  have w16_24_0 : memLoad t16.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_24_0
  have w17_24_0 : memLoad t17.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext17] using w16_24_0
  have w18_24_0 : memLoad t18.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext18] using w17_24_0
  have w19_24_0 : memLoad t19.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext19] using w18_24_0
  have w20_24_0 : memLoad t20.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 376) 64 :=
    by simpa only [ext20] using w19_24_0
  have w11_32_0 : memLoad t11.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext11] using sw10
  have w12_32_0 : memLoad t12.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_32_0
  have w13_32_0 : memLoad t13.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext13] using w12_32_0
  have w14_32_0 : memLoad t14.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext14] using w13_32_0
  have w15_32_0 : memLoad t15.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_32_0
  have w16_32_0 : memLoad t16.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_32_0
  have w17_32_0 : memLoad t17.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext17] using w16_32_0
  have w18_32_0 : memLoad t18.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext18] using w17_32_0
  have w19_32_0 : memLoad t19.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext19] using w18_32_0
  have w20_32_0 : memLoad t20.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 384) 64 :=
    by simpa only [ext20] using w19_32_0
  have copy20_8 : MontgomeryAt t20 (stackSlot s 8) (tripleZZ point) :=
    CrossTerms.copied pre frame20 (by decide) m0_360
      w20_8_0 (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_16_0) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_24_0) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_32_0)
  have r20_rdx : t20.regValue .rdx = stackSlot s 40 :=
    (ag20.read (n := 64) (r := 2) (by simp)).trans r19_rdx
  have w9_40_0 : memLoad t9.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext9] using sw8
  have w10_40_0 : memLoad t10.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_40_0
  have w11_40_0 : memLoad t11.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext11] using w10_40_0
  have w12_40_0 : memLoad t12.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_40_0
  have w13_40_0 : memLoad t13.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext13] using w12_40_0
  have w14_40_0 : memLoad t14.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext14] using w13_40_0
  have w15_40_0 : memLoad t15.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_40_0
  have w16_40_0 : memLoad t16.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_40_0
  have w17_40_0 : memLoad t17.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext17] using w16_40_0
  have w18_40_0 : memLoad t18.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext18] using w17_40_0
  have w19_40_0 : memLoad t19.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext19] using w18_40_0
  have w20_40_0 : memLoad t20.external (stackSlot s 40) 64 = memLoad t.external (stackSlot s 104) 64 :=
    by simpa only [ext20] using w19_40_0
  have w8_48_0 : memLoad t8.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans sw7
  have w9_48_0 : memLoad t9.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext9] using w8_48_0
  have w10_48_0 : memLoad t10.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_48_0
  have w11_48_0 : memLoad t11.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext11] using w10_48_0
  have w12_48_0 : memLoad t12.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_48_0
  have w13_48_0 : memLoad t13.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext13] using w12_48_0
  have w14_48_0 : memLoad t14.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext14] using w13_48_0
  have w15_48_0 : memLoad t15.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_48_0
  have w16_48_0 : memLoad t16.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_48_0
  have w17_48_0 : memLoad t17.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext17] using w16_48_0
  have w18_48_0 : memLoad t18.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext18] using w17_48_0
  have w19_48_0 : memLoad t19.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext19] using w18_48_0
  have w20_48_0 : memLoad t20.external (stackSlot s 48) 64 = memLoad t.external (stackSlot s 112) 64 :=
    by simpa only [ext20] using w19_48_0
  have w5_56_0 : memLoad t5.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext5] using sw4
  have w6_56_0 : memLoad t6.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext6] using w5_56_0
  have w7_56_0 : memLoad t7.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_56_0
  have w8_56_0 : memLoad t8.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_56_0
  have w9_56_0 : memLoad t9.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext9] using w8_56_0
  have w10_56_0 : memLoad t10.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_56_0
  have w11_56_0 : memLoad t11.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext11] using w10_56_0
  have w12_56_0 : memLoad t12.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_56_0
  have w13_56_0 : memLoad t13.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext13] using w12_56_0
  have w14_56_0 : memLoad t14.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext14] using w13_56_0
  have w15_56_0 : memLoad t15.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_56_0
  have w16_56_0 : memLoad t16.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_56_0
  have w17_56_0 : memLoad t17.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext17] using w16_56_0
  have w18_56_0 : memLoad t18.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext18] using w17_56_0
  have w19_56_0 : memLoad t19.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext19] using w18_56_0
  have w20_56_0 : memLoad t20.external (stackSlot s 56) 64 = memLoad t.external (stackSlot s 120) 64 :=
    by simpa only [ext20] using w19_56_0
  have w3_64_0 : memLoad t3.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext3] using sw2
  have w4_64_0 : memLoad t4.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag4 (by decide) (by decide) (by decide)).trans w3_64_0
  have w5_64_0 : memLoad t5.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext5] using w4_64_0
  have w6_64_0 : memLoad t6.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext6] using w5_64_0
  have w7_64_0 : memLoad t7.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag7 (by decide) (by decide) (by decide)).trans w6_64_0
  have w8_64_0 : memLoad t8.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_64_0
  have w9_64_0 : memLoad t9.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext9] using w8_64_0
  have w10_64_0 : memLoad t10.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag10 (by decide) (by decide) (by decide)).trans w9_64_0
  have w11_64_0 : memLoad t11.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext11] using w10_64_0
  have w12_64_0 : memLoad t12.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_64_0
  have w13_64_0 : memLoad t13.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext13] using w12_64_0
  have w14_64_0 : memLoad t14.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext14] using w13_64_0
  have w15_64_0 : memLoad t15.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag15 (by decide) (by decide) (by decide)).trans w14_64_0
  have w16_64_0 : memLoad t16.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    (store_read ag16 (by decide) (by decide) (by decide)).trans w15_64_0
  have w17_64_0 : memLoad t17.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext17] using w16_64_0
  have w18_64_0 : memLoad t18.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext18] using w17_64_0
  have w19_64_0 : memLoad t19.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext19] using w18_64_0
  have w20_64_0 : memLoad t20.external (stackSlot s 64) 64 = memLoad t.external (stackSlot s 128) 64 :=
    by simpa only [ext20] using w19_64_0
  have copy20_40 : MontgomeryAt t20 (stackSlot s 40) ((values point).xx) :=
    CrossTerms.copied pre frame20 (by decide) m0_104
      w20_40_0 (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_48_0) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_56_0) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w20_64_0)
  let v21 : Nat := ((tripleZZ point) + ((values point).xx)) % P256.Spec.Operations.domain.p
  let site21 : BinaryCallSite 1016 728 0x1137c0 16 :=
    { codeOffset := 0x621f, disp := 0xd59c, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x137c0 (by decide),
      layout := ⟨736, 720, 656, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 688, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n21, t21, run21, frame21, rip21, value21, regs21, bytes21, work21⟩ :=
    binary_call pre frame20 (x := tripleZZ point) (y := (values point).xx)
      (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) site21
      (fun _ hp hx hy => field_add_correct hp hx hy)
      rip20
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using r20_rsi)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using r20_rdx)
      (by simpa only [stackSlot_eq s (show 72 ≤ 728 by decide)] using r20_rdi)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using copy20_8)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using copy20_40)
  have m21_72 : MontgomeryAt t21 (stackSlot s 72) v21 := by
    rw [stackSlot_eq s (show 72 ≤ 728 by decide)]
    exact value21
  have r1_r14 : t1.regValue .r14 = stackSlot s 232 :=
    (ag1.read (n := 64) (r := 14) (by simp)).trans r0_r14
  have r2_r14 : t2.regValue .r14 = stackSlot s 232 :=
    (ag2.read (n := 64) (r := 14) (by simp)).trans r1_r14
  have r3_r14 : t3.regValue .r14 = stackSlot s 232 :=
    (ag3.read (n := 64) (r := 14) (by simp)).trans r2_r14
  have r4_r14 : t4.regValue .r14 = stackSlot s 232 :=
    (ag4.read (n := 64) (r := 14) (by simp)).trans r3_r14
  have r5_r14 : t5.regValue .r14 = stackSlot s 232 :=
    (ag5.read (n := 64) (r := 14) (by simp)).trans r4_r14
  have r6_r14 : t6.regValue .r14 = stackSlot s 232 :=
    (ag6.read (n := 64) (r := 14) (by simp)).trans r5_r14
  have r7_r14 : t7.regValue .r14 = stackSlot s 232 :=
    (ag7.read (n := 64) (r := 14) (by simp)).trans r6_r14
  have r8_r14 : t8.regValue .r14 = stackSlot s 232 :=
    (ag8.read (n := 64) (r := 14) (by simp)).trans r7_r14
  have r9_r14 : t9.regValue .r14 = stackSlot s 232 :=
    (ag9.read (n := 64) (r := 14) (by simp)).trans r8_r14
  have r10_r14 : t10.regValue .r14 = stackSlot s 232 :=
    (ag10.read (n := 64) (r := 14) (by simp)).trans r9_r14
  have r11_r14 : t11.regValue .r14 = stackSlot s 232 :=
    (ag11.read (n := 64) (r := 14) (by simp)).trans r10_r14
  have r12_r14 : t12.regValue .r14 = stackSlot s 232 :=
    (ag12.read (n := 64) (r := 14) (by simp)).trans r11_r14
  have r13_r14 : t13.regValue .r14 = stackSlot s 232 :=
    (ag13.read (n := 64) (r := 14) (by simp)).trans r12_r14
  have r14_r14 : t14.regValue .r14 = stackSlot s 232 :=
    (ag14.read (n := 64) (r := 14) (by simp)).trans r13_r14
  have r15_r14 : t15.regValue .r14 = stackSlot s 232 :=
    (ag15.read (n := 64) (r := 14) (by simp)).trans r14_r14
  have r16_r14 : t16.regValue .r14 = stackSlot s 232 :=
    (ag16.read (n := 64) (r := 14) (by simp)).trans r15_r14
  have r17_r14 : t17.regValue .r14 = stackSlot s 232 :=
    (ag17.read (n := 64) (r := 14) (by simp)).trans r16_r14
  have r18_r14 : t18.regValue .r14 = stackSlot s 232 :=
    (ag18.read (n := 64) (r := 14) (by simp)).trans r17_r14
  have r19_r14 : t19.regValue .r14 = stackSlot s 232 :=
    (ag19.read (n := 64) (r := 14) (by simp)).trans r18_r14
  have r20_r14 : t20.regValue .r14 = stackSlot s 232 :=
    (ag20.read (n := 64) (r := 14) (by simp)).trans r19_r14
  have r21_r14 : t21.regValue .r14 = stackSlot s 232 :=
    (regs21 .r14 (by decide)).trans r20_r14
  have r20_rbp : t20.regValue .rbp = stackSlot s 72 :=
    (ag20.read (n := 64) (r := 5) (by simp)).trans r19_rbp
  have r21_rbp : t21.regValue .rbp = stackSlot s 72 :=
    (regs21 .rbp (by decide)).trans r20_rbp
  have m1_0_232 : MontgomeryAt t1 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_232
  have m2_0_232 : MontgomeryAt t2 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_232
  have m3_0_232 : MontgomeryAt t3 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_232
  have m4_0_232 : MontgomeryAt t4 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_232
  have m5_0_232 : MontgomeryAt t5 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_232
  have m6_0_232 : MontgomeryAt t6 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_232
  have m7_0_232 : MontgomeryAt t7 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_232
  have m8_0_232 : MontgomeryAt t8 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_232
  have m9_0_232 : MontgomeryAt t9 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_232
  have m10_0_232 : MontgomeryAt t10 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_232
  have m11_0_232 : MontgomeryAt t11 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_232
  have m12_0_232 : MontgomeryAt t12 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_232
  have m13_0_232 : MontgomeryAt t13 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_232
  have m14_0_232 : MontgomeryAt t14 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_232
  have m15_0_232 : MontgomeryAt t15 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_232
  have m16_0_232 : MontgomeryAt t16 (stackSlot s 232) (bXZ point) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_232
  have m17_0_232 : MontgomeryAt t17 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_232
  have m18_0_232 : MontgomeryAt t18 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_232
  have m19_0_232 : MontgomeryAt t19 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_232
  have m20_0_232 : MontgomeryAt t20 (stackSlot s 232) (bXZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_232
  have m21_0_232 : MontgomeryAt t21 (stackSlot s 232) (bXZ point) :=
    by
    refine ⟨m20_0_232.1, m20_0_232.2.1, fun j hj => ?_⟩
    have h := (bytes21 496 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_232.2.2 j hj
    rw [stackSlot_eq s (show 232 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have point1 : ProjectiveAt t1 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using input.pointAt
  have point2 : ProjectiveAt t2 (s.regValue .rdi) point :=
    store_point pre ag2 (by decide) point1
  have point3 : ProjectiveAt t3 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using point2
  have point4 : ProjectiveAt t4 (s.regValue .rdi) point :=
    store_point pre ag4 (by decide) point3
  have point5 : ProjectiveAt t5 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using point4
  have point6 : ProjectiveAt t6 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using point5
  have point7 : ProjectiveAt t7 (s.regValue .rdi) point :=
    store_point pre ag7 (by decide) point6
  have point8 : ProjectiveAt t8 (s.regValue .rdi) point :=
    store_point pre ag8 (by decide) point7
  have point9 : ProjectiveAt t9 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using point8
  have point10 : ProjectiveAt t10 (s.regValue .rdi) point :=
    store_point pre ag10 (by decide) point9
  have point11 : ProjectiveAt t11 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using point10
  have point12 : ProjectiveAt t12 (s.regValue .rdi) point :=
    store_point pre ag12 (by decide) point11
  have point13 : ProjectiveAt t13 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using point12
  have point14 : ProjectiveAt t14 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using point13
  have point15 : ProjectiveAt t15 (s.regValue .rdi) point :=
    store_point pre ag15 (by decide) point14
  have point16 : ProjectiveAt t16 (s.regValue .rdi) point :=
    store_point pre ag16 (by decide) point15
  have point17 : ProjectiveAt t17 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using point16
  have point18 : ProjectiveAt t18 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using point17
  have point19 : ProjectiveAt t19 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using point18
  have point20 : ProjectiveAt t20 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using point19
  have point21 : ProjectiveAt t21 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work21) point20
  have r1_rbx : t1.regValue .rbx = s.regValue .rdi :=
    (ag1.read (n := 64) (r := 3) (by simp)).trans r0_rbx
  have r2_rbx : t2.regValue .rbx = s.regValue .rdi :=
    (ag2.read (n := 64) (r := 3) (by simp)).trans r1_rbx
  have r3_rbx : t3.regValue .rbx = s.regValue .rdi :=
    (ag3.read (n := 64) (r := 3) (by simp)).trans r2_rbx
  have r4_rbx : t4.regValue .rbx = s.regValue .rdi :=
    (ag4.read (n := 64) (r := 3) (by simp)).trans r3_rbx
  have r5_rbx : t5.regValue .rbx = s.regValue .rdi :=
    (ag5.read (n := 64) (r := 3) (by simp)).trans r4_rbx
  have r6_rbx : t6.regValue .rbx = s.regValue .rdi :=
    (ag6.read (n := 64) (r := 3) (by simp)).trans r5_rbx
  have r7_rbx : t7.regValue .rbx = s.regValue .rdi :=
    (ag7.read (n := 64) (r := 3) (by simp)).trans r6_rbx
  have r8_rbx : t8.regValue .rbx = s.regValue .rdi :=
    (ag8.read (n := 64) (r := 3) (by simp)).trans r7_rbx
  have r9_rbx : t9.regValue .rbx = s.regValue .rdi :=
    (ag9.read (n := 64) (r := 3) (by simp)).trans r8_rbx
  have r10_rbx : t10.regValue .rbx = s.regValue .rdi :=
    (ag10.read (n := 64) (r := 3) (by simp)).trans r9_rbx
  have r11_rbx : t11.regValue .rbx = s.regValue .rdi :=
    (ag11.read (n := 64) (r := 3) (by simp)).trans r10_rbx
  have r12_rbx : t12.regValue .rbx = s.regValue .rdi :=
    (ag12.read (n := 64) (r := 3) (by simp)).trans r11_rbx
  have r13_rbx : t13.regValue .rbx = s.regValue .rdi :=
    (ag13.read (n := 64) (r := 3) (by simp)).trans r12_rbx
  have r14_rbx : t14.regValue .rbx = s.regValue .rdi :=
    (ag14.read (n := 64) (r := 3) (by simp)).trans r13_rbx
  have r15_rbx : t15.regValue .rbx = s.regValue .rdi :=
    (ag15.read (n := 64) (r := 3) (by simp)).trans r14_rbx
  have r16_rbx : t16.regValue .rbx = s.regValue .rdi :=
    (ag16.read (n := 64) (r := 3) (by simp)).trans r15_rbx
  have r17_rbx : t17.regValue .rbx = s.regValue .rdi :=
    (ag17.read (n := 64) (r := 3) (by simp)).trans r16_rbx
  have r18_rbx : t18.regValue .rbx = s.regValue .rdi :=
    (ag18.read (n := 64) (r := 3) (by simp)).trans r17_rbx
  have r19_rbx : t19.regValue .rbx = s.regValue .rdi :=
    (ag19.read (n := 64) (r := 3) (by simp)).trans r18_rbx
  have r20_rbx : t20.regValue .rbx = s.regValue .rdi :=
    (ag20.read (n := 64) (r := 3) (by simp)).trans r19_rbx
  have r21_rbx : t21.regValue .rbx = s.regValue .rdi :=
    (regs21 .rbx (by decide)).trans r20_rbx
  have r1_r15 : t1.regValue .r15 = stackSlot s 616 :=
    (ag1.read (n := 64) (r := 15) (by simp)).trans r0_r15
  have r2_r15 : t2.regValue .r15 = stackSlot s 616 :=
    (ag2.read (n := 64) (r := 15) (by simp)).trans r1_r15
  have r3_r15 : t3.regValue .r15 = stackSlot s 616 :=
    (ag3.read (n := 64) (r := 15) (by simp)).trans r2_r15
  have r4_r15 : t4.regValue .r15 = stackSlot s 616 :=
    (ag4.read (n := 64) (r := 15) (by simp)).trans r3_r15
  have r5_r15 : t5.regValue .r15 = stackSlot s 616 :=
    (ag5.read (n := 64) (r := 15) (by simp)).trans r4_r15
  have r6_r15 : t6.regValue .r15 = stackSlot s 616 :=
    (ag6.read (n := 64) (r := 15) (by simp)).trans r5_r15
  have r7_r15 : t7.regValue .r15 = stackSlot s 616 :=
    (ag7.read (n := 64) (r := 15) (by simp)).trans r6_r15
  have r8_r15 : t8.regValue .r15 = stackSlot s 616 :=
    (ag8.read (n := 64) (r := 15) (by simp)).trans r7_r15
  have r9_r15 : t9.regValue .r15 = stackSlot s 616 :=
    (ag9.read (n := 64) (r := 15) (by simp)).trans r8_r15
  have r10_r15 : t10.regValue .r15 = stackSlot s 616 :=
    (ag10.read (n := 64) (r := 15) (by simp)).trans r9_r15
  have r11_r15 : t11.regValue .r15 = stackSlot s 616 :=
    (ag11.read (n := 64) (r := 15) (by simp)).trans r10_r15
  have r12_r15 : t12.regValue .r15 = stackSlot s 616 :=
    (ag12.read (n := 64) (r := 15) (by simp)).trans r11_r15
  have r13_r15 : t13.regValue .r15 = stackSlot s 616 :=
    (ag13.read (n := 64) (r := 15) (by simp)).trans r12_r15
  have r14_r15 : t14.regValue .r15 = stackSlot s 616 :=
    (ag14.read (n := 64) (r := 15) (by simp)).trans r13_r15
  have r15_r15 : t15.regValue .r15 = stackSlot s 616 :=
    (ag15.read (n := 64) (r := 15) (by simp)).trans r14_r15
  have r16_r15 : t16.regValue .r15 = stackSlot s 616 :=
    (ag16.read (n := 64) (r := 15) (by simp)).trans r15_r15
  have r17_r15 : t17.regValue .r15 = stackSlot s 616 :=
    (ag17.read (n := 64) (r := 15) (by simp)).trans r16_r15
  have r18_r15 : t18.regValue .r15 = stackSlot s 616 :=
    (ag18.read (n := 64) (r := 15) (by simp)).trans r17_r15
  have r19_r15 : t19.regValue .r15 = stackSlot s 616 :=
    (ag19.read (n := 64) (r := 15) (by simp)).trans r18_r15
  have r20_r15 : t20.regValue .r15 = stackSlot s 616 :=
    (ag20.read (n := 64) (r := 15) (by simp)).trans r19_r15
  have r21_r15 : t21.regValue .r15 = stackSlot s 616 :=
    (regs21 .r15 (by decide)).trans r20_r15
  have r1_r12 : t1.regValue .r12 = stackSlot s 360 :=
    (ag1.read (n := 64) (r := 12) (by simp)).trans r0_r12
  have r2_r12 : t2.regValue .r12 = stackSlot s 360 :=
    (ag2.read (n := 64) (r := 12) (by simp)).trans r1_r12
  have r3_r12 : t3.regValue .r12 = stackSlot s 360 :=
    (ag3.read (n := 64) (r := 12) (by simp)).trans r2_r12
  have r4_r12 : t4.regValue .r12 = stackSlot s 360 :=
    (ag4.read (n := 64) (r := 12) (by simp)).trans r3_r12
  have r5_r12 : t5.regValue .r12 = stackSlot s 360 :=
    (ag5.read (n := 64) (r := 12) (by simp)).trans r4_r12
  have r6_r12 : t6.regValue .r12 = stackSlot s 360 :=
    (ag6.read (n := 64) (r := 12) (by simp)).trans r5_r12
  have r7_r12 : t7.regValue .r12 = stackSlot s 360 :=
    (ag7.read (n := 64) (r := 12) (by simp)).trans r6_r12
  have r8_r12 : t8.regValue .r12 = stackSlot s 360 :=
    (ag8.read (n := 64) (r := 12) (by simp)).trans r7_r12
  have r9_r12 : t9.regValue .r12 = stackSlot s 360 :=
    (ag9.read (n := 64) (r := 12) (by simp)).trans r8_r12
  have r10_r12 : t10.regValue .r12 = stackSlot s 360 :=
    (ag10.read (n := 64) (r := 12) (by simp)).trans r9_r12
  have r11_r12 : t11.regValue .r12 = stackSlot s 360 :=
    (ag11.read (n := 64) (r := 12) (by simp)).trans r10_r12
  have r12_r12 : t12.regValue .r12 = stackSlot s 360 :=
    (ag12.read (n := 64) (r := 12) (by simp)).trans r11_r12
  have r13_r12 : t13.regValue .r12 = stackSlot s 360 :=
    (ag13.read (n := 64) (r := 12) (by simp)).trans r12_r12
  have r14_r12 : t14.regValue .r12 = stackSlot s 360 :=
    (ag14.read (n := 64) (r := 12) (by simp)).trans r13_r12
  have r15_r12 : t15.regValue .r12 = stackSlot s 360 :=
    (ag15.read (n := 64) (r := 12) (by simp)).trans r14_r12
  have r16_r12 : t16.regValue .r12 = stackSlot s 360 :=
    (ag16.read (n := 64) (r := 12) (by simp)).trans r15_r12
  have r17_r12 : t17.regValue .r12 = stackSlot s 360 :=
    (ag17.read (n := 64) (r := 12) (by simp)).trans r16_r12
  have r18_r12 : t18.regValue .r12 = stackSlot s 360 :=
    (ag18.read (n := 64) (r := 12) (by simp)).trans r17_r12
  have r19_r12 : t19.regValue .r12 = stackSlot s 360 :=
    (ag19.read (n := 64) (r := 12) (by simp)).trans r18_r12
  have r20_r12 : t20.regValue .r12 = stackSlot s 360 :=
    (ag20.read (n := 64) (r := 12) (by simp)).trans r19_r12
  have r21_r12 : t21.regValue .r12 = stackSlot s 360 :=
    (regs21 .r12 (by decide)).trans r20_r12
  have m1_0_104 : MontgomeryAt t1 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_104
  have m2_0_104 : MontgomeryAt t2 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_104
  have m3_0_104 : MontgomeryAt t3 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_104
  have m4_0_104 : MontgomeryAt t4 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_104
  have m5_0_104 : MontgomeryAt t5 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_104
  have m6_0_104 : MontgomeryAt t6 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_104
  have m7_0_104 : MontgomeryAt t7 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_104
  have m8_0_104 : MontgomeryAt t8 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_104
  have m9_0_104 : MontgomeryAt t9 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_104
  have m10_0_104 : MontgomeryAt t10 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_104
  have m11_0_104 : MontgomeryAt t11 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_104
  have m12_0_104 : MontgomeryAt t12 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_104
  have m13_0_104 : MontgomeryAt t13 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_104
  have m14_0_104 : MontgomeryAt t14 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_104
  have m15_0_104 : MontgomeryAt t15 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_104
  have m16_0_104 : MontgomeryAt t16 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_104
  have m17_0_104 : MontgomeryAt t17 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_104
  have m18_0_104 : MontgomeryAt t18 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_104
  have m19_0_104 : MontgomeryAt t19 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_104
  have m20_0_104 : MontgomeryAt t20 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_104
  have m21_0_104 : MontgomeryAt t21 (stackSlot s 104) ((values point).xx) :=
    by
    refine ⟨m20_0_104.1, m20_0_104.2.1, fun j hj => ?_⟩
    have h := (bytes21 624 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_104.2.2 j hj
    rw [stackSlot_eq s (show 104 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_136 : MontgomeryAt t1 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_136
  have m2_0_136 : MontgomeryAt t2 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_136
  have m3_0_136 : MontgomeryAt t3 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_136
  have m4_0_136 : MontgomeryAt t4 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_136
  have m5_0_136 : MontgomeryAt t5 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_136
  have m6_0_136 : MontgomeryAt t6 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_136
  have m7_0_136 : MontgomeryAt t7 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_136
  have m8_0_136 : MontgomeryAt t8 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_136
  have m9_0_136 : MontgomeryAt t9 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_136
  have m10_0_136 : MontgomeryAt t10 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_136
  have m11_0_136 : MontgomeryAt t11 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_136
  have m12_0_136 : MontgomeryAt t12 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_136
  have m13_0_136 : MontgomeryAt t13 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_136
  have m14_0_136 : MontgomeryAt t14 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_136
  have m15_0_136 : MontgomeryAt t15 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_136
  have m16_0_136 : MontgomeryAt t16 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_136
  have m17_0_136 : MontgomeryAt t17 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_136
  have m18_0_136 : MontgomeryAt t18 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_136
  have m19_0_136 : MontgomeryAt t19 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_136
  have m20_0_136 : MontgomeryAt t20 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_136
  have m21_0_136 : MontgomeryAt t21 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m20_0_136.1, m20_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes21 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_520 : MontgomeryAt t1 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_520
  have m2_0_520 : MontgomeryAt t2 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_520
  have m3_0_520 : MontgomeryAt t3 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_520
  have m4_0_520 : MontgomeryAt t4 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_520
  have m5_0_520 : MontgomeryAt t5 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_520
  have m6_0_520 : MontgomeryAt t6 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_520
  have m7_0_520 : MontgomeryAt t7 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_520
  have m8_0_520 : MontgomeryAt t8 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_520
  have m9_0_520 : MontgomeryAt t9 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_520
  have m10_0_520 : MontgomeryAt t10 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_520
  have m11_0_520 : MontgomeryAt t11 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_520
  have m12_0_520 : MontgomeryAt t12 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_520
  have m13_0_520 : MontgomeryAt t13 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_520
  have m14_0_520 : MontgomeryAt t14 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_520
  have m15_0_520 : MontgomeryAt t15 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_520
  have m16_0_520 : MontgomeryAt t16 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_520
  have m17_0_520 : MontgomeryAt t17 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_520
  have m18_0_520 : MontgomeryAt t18 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_520
  have m19_0_520 : MontgomeryAt t19 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_520
  have m20_0_520 : MontgomeryAt t20 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_520
  have m21_0_520 : MontgomeryAt t21 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m20_0_520.1, m20_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes21 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_616 : MontgomeryAt t1 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_616
  have m2_0_616 : MontgomeryAt t2 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_616
  have m3_0_616 : MontgomeryAt t3 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_616
  have m4_0_616 : MontgomeryAt t4 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_616
  have m5_0_616 : MontgomeryAt t5 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_616
  have m6_0_616 : MontgomeryAt t6 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_616
  have m7_0_616 : MontgomeryAt t7 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_616
  have m8_0_616 : MontgomeryAt t8 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_616
  have m9_0_616 : MontgomeryAt t9 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_616
  have m10_0_616 : MontgomeryAt t10 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_616
  have m11_0_616 : MontgomeryAt t11 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_616
  have m12_0_616 : MontgomeryAt t12 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_616
  have m13_0_616 : MontgomeryAt t13 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_616
  have m14_0_616 : MontgomeryAt t14 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_616
  have m15_0_616 : MontgomeryAt t15 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_616
  have m16_0_616 : MontgomeryAt t16 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_616
  have m17_0_616 : MontgomeryAt t17 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_616
  have m18_0_616 : MontgomeryAt t18 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_616
  have m19_0_616 : MontgomeryAt t19 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_616
  have m20_0_616 : MontgomeryAt t20 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_616
  have m21_0_616 : MontgomeryAt t21 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m20_0_616.1, m20_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes21 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_360 : MontgomeryAt t1 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_360
  have m2_0_360 : MontgomeryAt t2 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag2 (by decide) (by decide) (by decide) m1_0_360
  have m3_0_360 : MontgomeryAt t3 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_360
  have m4_0_360 : MontgomeryAt t4 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag4 (by decide) (by decide) (by decide) m3_0_360
  have m5_0_360 : MontgomeryAt t5 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_360
  have m6_0_360 : MontgomeryAt t6 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext6] using m5_0_360
  have m7_0_360 : MontgomeryAt t7 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag7 (by decide) (by decide) (by decide) m6_0_360
  have m8_0_360 : MontgomeryAt t8 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_360
  have m9_0_360 : MontgomeryAt t9 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_360
  have m10_0_360 : MontgomeryAt t10 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag10 (by decide) (by decide) (by decide) m9_0_360
  have m11_0_360 : MontgomeryAt t11 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext11] using m10_0_360
  have m12_0_360 : MontgomeryAt t12 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_360
  have m13_0_360 : MontgomeryAt t13 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_360
  have m14_0_360 : MontgomeryAt t14 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_360
  have m15_0_360 : MontgomeryAt t15 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag15 (by decide) (by decide) (by decide) m14_0_360
  have m16_0_360 : MontgomeryAt t16 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag16 (by decide) (by decide) (by decide) m15_0_360
  have m17_0_360 : MontgomeryAt t17 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext17] using m16_0_360
  have m18_0_360 : MontgomeryAt t18 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_360
  have m19_0_360 : MontgomeryAt t19 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext19] using m18_0_360
  have m20_0_360 : MontgomeryAt t20 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_360
  have m21_0_360 : MontgomeryAt t21 (stackSlot s 360) (tripleZZ point) :=
    by
    refine ⟨m20_0_360.1, m20_0_360.2.1, fun j hj => ?_⟩
    have h := (bytes21 368 32 (by decide) (by decide) (by decide) j hj)
    have hx := m20_0_360.2.2 j hj
    rw [stackSlot_eq s (show 360 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  refine ⟨_, t21, ((((((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17).trans run18).trans run19).trans run20).trans run21), frame21, rip21, ?_⟩
  exact ⟨⟨⟨point21, r21_rbx, r21_r15, m21_0_104, m21_0_136, m21_0_520,
    m21_0_616, r21_r12, m21_0_360⟩, r21_r14, m21_0_232⟩, r21_rbp, m21_72⟩

end P256.Proofs.Projective.Double
