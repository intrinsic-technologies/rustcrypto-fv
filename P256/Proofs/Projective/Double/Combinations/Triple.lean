import P256.Proofs.Projective.Double.Combinations.State

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

set_option maxRecDepth 2048 in
theorem Combinations.triple [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x10623a)
    (input : DifferenceAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x106296 ∧ TripledAt s u point := by
  have r0_rbx : t.regValue .rbx = s.regValue .rdi := input.rbx
  have r0_r15 : t.regValue .r15 = stackSlot s 616 := input.r15
  have r0_r12 : t.regValue .r12 = stackSlot s 360 := input.r12
  have r0_r13 : t.regValue .r13 = stackSlot s 392 := input.r13
  have m0_104 : MontgomeryAt t (stackSlot s 104) ((values point).xx) := input.xx
  have m0_136 : MontgomeryAt t (stackSlot s 136) ((values point).yy) := input.yy
  have m0_520 : MontgomeryAt t (stackSlot s 520) ((values point).xProduct) := input.xProduct
  have m0_616 : MontgomeryAt t (stackSlot s 616) ((values point).yProduct) := input.yProduct
  have m0_360 : MontgomeryAt t (stackSlot s 360) (tripleZZ point) := input.zz3
  have m0_392 : MontgomeryAt t (stackSlot s 392) (bXZDifference point) := input.difference
  obtain ⟨t1, run1, frame1, effect1⟩ := step_registers pre state
    (offset := 0x623a) (lea_r64_effect_step 0x10623a 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip
    (inProgram_of_textOffset 0x623f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 5, .rip]; decide +kernel)
  have ag1 : AgreesExcept [.reg 5, .rip] t t1 := effect1.agrees
  have ext1 : t1.external = t.external := ag1.external (by simp [Component.Covers])
  have rip1 : t1.RIP = 0x10623f := effect1.rip
  have write1 : t1.regValue .rbp = stackPtr t + 40#64 := effect1.writes
  rw [state.rsp] at write1
  have r1_rbp : t1.regValue .rbp = stackSlot s 40 := write1
  obtain ⟨t2, run2, frame2, effect2⟩ := step_registers pre frame1
    (offset := 0x623f) (mov_r64_r64_effect_step 0x10623f 0x48 0xef (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip1
    (inProgram_of_textOffset 0x6242 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag2 : AgreesExcept [.reg 7, .rip] t1 t2 := effect2.agrees
  have ext2 : t2.external = t1.external := ag2.external (by simp [Component.Covers])
  have rip2 : t2.RIP = 0x106242 := effect2.rip
  have write2 : t2.regValue .rdi = t1.regValue .rbp := effect2.writes
  have r2_rdi : t2.regValue .rdi = stackSlot s 40 := write2.trans r1_rbp
  have r1_r13 : t1.regValue .r13 = stackSlot s 392 :=
    (ag1.read (n := 64) (r := 13) (by simp)).trans r0_r13
  have r2_r13 : t2.regValue .r13 = stackSlot s 392 :=
    (ag2.read (n := 64) (r := 13) (by simp)).trans r1_r13
  obtain ⟨t3, run3, frame3, effect3⟩ := step_registers pre frame2
    (offset := 0x6242) (mov_r64_r64_effect_step 0x106242 0x4c 0xee (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip2
    (inProgram_of_textOffset 0x6245 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag3 : AgreesExcept [.reg 6, .rip] t2 t3 := effect3.agrees
  have ext3 : t3.external = t2.external := ag3.external (by simp [Component.Covers])
  have rip3 : t3.RIP = 0x106245 := effect3.rip
  have write3 : t3.regValue .rsi = t2.regValue .r13 := effect3.writes
  have r3_rsi : t3.regValue .rsi = stackSlot s 392 := write3.trans r2_r13
  have r3_rdi : t3.regValue .rdi = stackSlot s 40 :=
    (ag3.read (n := 64) (r := 7) (by simp)).trans r2_rdi
  have m1_0_392 : MontgomeryAt t1 (stackSlot s 392) (bXZDifference point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_392
  have m2_0_392 : MontgomeryAt t2 (stackSlot s 392) (bXZDifference point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_392
  have m3_0_392 : MontgomeryAt t3 (stackSlot s 392) (bXZDifference point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_392
  let v4 : Nat := ((bXZDifference point) + (bXZDifference point)) % P256.Spec.Operations.domain.p
  obtain ⟨n4, t4, run4, frame4, rip4, value4, regs4, bytes4, work4⟩ :=
    unary_call pre frame3 (entry := 0x1137f0) (reserve := 16)
      (resultAt := fun u a => MontgomeryAt u a v4)
      (⟨736, 336, 688, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ : StackCallLayout 1016 32 32 16) rfl (by decide)
      0x6245 0xd5a6 (by decide) (by decide +kernel) (by decide +kernel)
      (by decide) (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx)
      rip3
      (by simpa only [stackSlot_eq s (show 392 ≤ 728 by decide)] using r3_rsi)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using r3_rdi)
      (by simpa only [stackSlot_eq s (show 392 ≤ 728 by decide)] using m3_0_392)
  have m4_40 : MontgomeryAt t4 (stackSlot s 40) v4 := by
    rw [stackSlot_eq s (show 40 ≤ 728 by decide)]
    exact value4
  obtain ⟨t5, run5, frame5, effect5⟩ := step_registers pre frame4
    (offset := 0x624a) (mov_r64_m64_effect_step 0x10624a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 416)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip4, stack_readable (frameOffset := 728) pre frame4 (by decide) (offset := 416) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6252 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag5 : AgreesExcept [.reg 0, .rip] t4 t5 := effect5.agrees
  have ext5 : t5.external = t4.external := ag5.external (by simp [Component.Covers])
  have rip5 : t5.RIP = 0x106252 := effect5.rip
  have write5 : t5.regValue .rax = memLoad t4.external (stackPtr t4 + 416#64) 64 := effect5.writes
  rw [frame4.rsp] at write5
  have r5_rax : t5.regValue .rax = memLoad t4.external (stackSlot s 416) 64 := write5.trans (Eq.refl _)
  obtain ⟨t6, run6, frame6, effect6⟩ := step pre frame5 (by decide)
    (offset := 0x6252) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106252 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip5, stack_writable (frameOffset := 728) pre frame5 (by decide) (offset := 32) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame5 (by decide) (offset := 32) (len := 8) (codeOffset := 0x6252) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6257 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame5 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag6 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t5 t6 := by
    have h : AgreesExcept [.mem (stackPtr t5 + 32#64) 8, .rip] t5 t6 := by
      have h := effect6.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame5.rsp] at h
    exact h
  have rip6 : t6.RIP = 0x106257 := effect6.rip
  have write6 : memLoad t6.external (stackPtr t5 + 32#64) 64 = t5.regValue .rax := effect6.writes
  rw [frame5.rsp] at write6
  have sw6 : memLoad t6.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 := write6.trans r5_rax
  have w5_408_4 : memLoad t5.external (stackSlot s 408) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by rw [ext5]
  have w6_408_4 : memLoad t6.external (stackSlot s 408) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    (store_read ag6 (by decide) (by decide) (by decide)).trans w5_408_4
  obtain ⟨t7, run7, frame7, effect7⟩ := step_registers pre frame6
    (offset := 0x6257) (mov_r64_m64_effect_step 0x106257 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 408)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip6, stack_readable (frameOffset := 728) pre frame6 (by decide) (offset := 408) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x625f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag7 : AgreesExcept [.reg 0, .rip] t6 t7 := effect7.agrees
  have ext7 : t7.external = t6.external := ag7.external (by simp [Component.Covers])
  have rip7 : t7.RIP = 0x10625f := effect7.rip
  have write7 : t7.regValue .rax = memLoad t6.external (stackPtr t6 + 408#64) 64 := effect7.writes
  rw [frame6.rsp] at write7
  have r7_rax : t7.regValue .rax = memLoad t4.external (stackSlot s 408) 64 := write7.trans w6_408_4
  obtain ⟨t8, run8, frame8, effect8⟩ := step pre frame7 (by decide)
    (offset := 0x625f) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10625f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip7, stack_writable (frameOffset := 728) pre frame7 (by decide) (offset := 24) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame7 (by decide) (offset := 24) (len := 8) (codeOffset := 0x625f) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6264 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame7 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag8 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t7 t8 := by
    have h : AgreesExcept [.mem (stackPtr t7 + 24#64) 8, .rip] t7 t8 := by
      have h := effect8.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame7.rsp] at h
    exact h
  have rip8 : t8.RIP = 0x106264 := effect8.rip
  have write8 : memLoad t8.external (stackPtr t7 + 24#64) 64 = t7.regValue .rax := effect8.writes
  rw [frame7.rsp] at write8
  have sw8 : memLoad t8.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 := write8.trans r7_rax
  have w5_392_4 : memLoad t5.external (stackSlot s 392) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by rw [ext5]
  have w6_392_4 : memLoad t6.external (stackSlot s 392) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    (store_read ag6 (by decide) (by decide) (by decide)).trans w5_392_4
  have w7_392_4 : memLoad t7.external (stackSlot s 392) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by simpa only [ext7] using w6_392_4
  have w8_392_4 : memLoad t8.external (stackSlot s 392) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_392_4
  obtain ⟨t9, run9, frame9, effect9⟩ := step_registers pre frame8
    (offset := 0x6264) (mov_r64_m64_effect_step 0x106264 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip8, stack_readable (frameOffset := 728) pre frame8 (by decide) (offset := 392) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x626c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag9 : AgreesExcept [.reg 0, .rip] t8 t9 := effect9.agrees
  have ext9 : t9.external = t8.external := ag9.external (by simp [Component.Covers])
  have rip9 : t9.RIP = 0x10626c := effect9.rip
  have write9 : t9.regValue .rax = memLoad t8.external (stackPtr t8 + 392#64) 64 := effect9.writes
  rw [frame8.rsp] at write9
  have r9_rax : t9.regValue .rax = memLoad t4.external (stackSlot s 392) 64 := write9.trans w8_392_4
  have w5_400_4 : memLoad t5.external (stackSlot s 400) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by rw [ext5]
  have w6_400_4 : memLoad t6.external (stackSlot s 400) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    (store_read ag6 (by decide) (by decide) (by decide)).trans w5_400_4
  have w7_400_4 : memLoad t7.external (stackSlot s 400) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext7] using w6_400_4
  have w8_400_4 : memLoad t8.external (stackSlot s 400) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_400_4
  have w9_400_4 : memLoad t9.external (stackSlot s 400) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext9] using w8_400_4
  obtain ⟨t10, run10, frame10, effect10⟩ := step_registers pre frame9
    (offset := 0x626c) (mov_r64_m64_effect_step 0x10626c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip9, stack_readable (frameOffset := 728) pre frame9 (by decide) (offset := 400) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6274 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide +kernel)
  have ag10 : AgreesExcept [.reg 1, .rip] t9 t10 := effect10.agrees
  have ext10 : t10.external = t9.external := ag10.external (by simp [Component.Covers])
  have rip10 : t10.RIP = 0x106274 := effect10.rip
  have write10 : t10.regValue .rcx = memLoad t9.external (stackPtr t9 + 400#64) 64 := effect10.writes
  rw [frame9.rsp] at write10
  have r10_rcx : t10.regValue .rcx = memLoad t4.external (stackSlot s 400) 64 := write10.trans w9_400_4
  obtain ⟨t11, run11, frame11, effect11⟩ := step pre frame10 (by decide)
    (offset := 0x6274) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106274 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip10, stack_writable (frameOffset := 728) pre frame10 (by decide) (offset := 16) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame10 (by decide) (offset := 16) (len := 8) (codeOffset := 0x6274) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6279 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame10 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag11 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t10 t11 := by
    have h : AgreesExcept [.mem (stackPtr t10 + 16#64) 8, .rip] t10 t11 := by
      have h := effect11.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame10.rsp] at h
    exact h
  have rip11 : t11.RIP = 0x106279 := effect11.rip
  have write11 : memLoad t11.external (stackPtr t10 + 16#64) 64 = t10.regValue .rcx := effect11.writes
  rw [frame10.rsp] at write11
  have sw11 : memLoad t11.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 := write11.trans r10_rcx
  have r10_rax : t10.regValue .rax = memLoad t4.external (stackSlot s 392) 64 :=
    (ag10.read (n := 64) (r := 0) (by simp)).trans r9_rax
  have r11_rax : t11.regValue .rax = memLoad t4.external (stackSlot s 392) 64 :=
    (ag11.read (n := 64) (r := 0) (by simp)).trans r10_rax
  obtain ⟨t12, run12, frame12, effect12⟩ := step pre frame11 (by decide)
    (offset := 0x6279) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106279 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip11, stack_writable (frameOffset := 728) pre frame11 (by decide) (offset := 8) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame11 (by decide) (offset := 8) (len := 8) (codeOffset := 0x6279) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x627e (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame11 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag12 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t11 t12 := by
    have h : AgreesExcept [.mem (stackPtr t11 + 8#64) 8, .rip] t11 t12 := by
      have h := effect12.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame11.rsp] at h
    exact h
  have rip12 : t12.RIP = 0x10627e := effect12.rip
  have write12 : memLoad t12.external (stackPtr t11 + 8#64) 64 = t11.regValue .rax := effect12.writes
  rw [frame11.rsp] at write12
  have sw12 : memLoad t12.external (stackSlot s 8) 64 = memLoad t4.external (stackSlot s 392) 64 := write12.trans r11_rax
  obtain ⟨t13, run13, frame13, effect13⟩ := step_registers pre frame12
    (offset := 0x627e) (lea_r64_effect_step 0x10627e 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip12
    (inProgram_of_textOffset 0x6286 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 14, .rip]; decide +kernel)
  have ag13 : AgreesExcept [.reg 14, .rip] t12 t13 := effect13.agrees
  have ext13 : t13.external = t12.external := ag13.external (by simp [Component.Covers])
  have rip13 : t13.RIP = 0x106286 := effect13.rip
  have write13 : t13.regValue .r14 = stackPtr t12 + 424#64 := effect13.writes
  rw [frame12.rsp] at write13
  have r13_r14 : t13.regValue .r14 = stackSlot s 424 := write13
  obtain ⟨t14, run14, frame14, effect14⟩ := step_registers pre frame13
    (offset := 0x6286) (lea_r64_effect_step 0x106286 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip13
    (inProgram_of_textOffset 0x628b (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag14 : AgreesExcept [.reg 2, .rip] t13 t14 := effect14.agrees
  have ext14 : t14.external = t13.external := ag14.external (by simp [Component.Covers])
  have rip14 : t14.RIP = 0x10628b := effect14.rip
  have write14 : t14.regValue .rdx = stackPtr t13 + 8#64 := effect14.writes
  rw [frame13.rsp] at write14
  have r14_rdx : t14.regValue .rdx = stackSlot s 8 := write14
  have r14_r14 : t14.regValue .r14 = stackSlot s 424 :=
    (ag14.read (n := 64) (r := 14) (by simp)).trans r13_r14
  obtain ⟨t15, run15, frame15, effect15⟩ := step_registers pre frame14
    (offset := 0x628b) (mov_r64_r64_effect_step 0x10628b 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip14
    (inProgram_of_textOffset 0x628e (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag15 : AgreesExcept [.reg 7, .rip] t14 t15 := effect15.agrees
  have ext15 : t15.external = t14.external := ag15.external (by simp [Component.Covers])
  have rip15 : t15.RIP = 0x10628e := effect15.rip
  have write15 : t15.regValue .rdi = t14.regValue .r14 := effect15.writes
  have r15_rdi : t15.regValue .rdi = stackSlot s 424 := write15.trans r14_r14
  have r2_rbp : t2.regValue .rbp = stackSlot s 40 :=
    (ag2.read (n := 64) (r := 5) (by simp)).trans r1_rbp
  have r3_rbp : t3.regValue .rbp = stackSlot s 40 :=
    (ag3.read (n := 64) (r := 5) (by simp)).trans r2_rbp
  have r4_rbp : t4.regValue .rbp = stackSlot s 40 :=
    (regs4 .rbp (by decide)).trans r3_rbp
  have r5_rbp : t5.regValue .rbp = stackSlot s 40 :=
    (ag5.read (n := 64) (r := 5) (by simp)).trans r4_rbp
  have r6_rbp : t6.regValue .rbp = stackSlot s 40 :=
    (ag6.read (n := 64) (r := 5) (by simp)).trans r5_rbp
  have r7_rbp : t7.regValue .rbp = stackSlot s 40 :=
    (ag7.read (n := 64) (r := 5) (by simp)).trans r6_rbp
  have r8_rbp : t8.regValue .rbp = stackSlot s 40 :=
    (ag8.read (n := 64) (r := 5) (by simp)).trans r7_rbp
  have r9_rbp : t9.regValue .rbp = stackSlot s 40 :=
    (ag9.read (n := 64) (r := 5) (by simp)).trans r8_rbp
  have r10_rbp : t10.regValue .rbp = stackSlot s 40 :=
    (ag10.read (n := 64) (r := 5) (by simp)).trans r9_rbp
  have r11_rbp : t11.regValue .rbp = stackSlot s 40 :=
    (ag11.read (n := 64) (r := 5) (by simp)).trans r10_rbp
  have r12_rbp : t12.regValue .rbp = stackSlot s 40 :=
    (ag12.read (n := 64) (r := 5) (by simp)).trans r11_rbp
  have r13_rbp : t13.regValue .rbp = stackSlot s 40 :=
    (ag13.read (n := 64) (r := 5) (by simp)).trans r12_rbp
  have r14_rbp : t14.regValue .rbp = stackSlot s 40 :=
    (ag14.read (n := 64) (r := 5) (by simp)).trans r13_rbp
  have r15_rbp : t15.regValue .rbp = stackSlot s 40 :=
    (ag15.read (n := 64) (r := 5) (by simp)).trans r14_rbp
  obtain ⟨t16, run16, frame16, effect16⟩ := step_registers pre frame15
    (offset := 0x628e) (mov_r64_r64_effect_step 0x10628e 0x48 0xee (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip15
    (inProgram_of_textOffset 0x6291 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag16 : AgreesExcept [.reg 6, .rip] t15 t16 := effect16.agrees
  have ext16 : t16.external = t15.external := ag16.external (by simp [Component.Covers])
  have rip16 : t16.RIP = 0x106291 := effect16.rip
  have write16 : t16.regValue .rsi = t15.regValue .rbp := effect16.writes
  have r16_rsi : t16.regValue .rsi = stackSlot s 40 := write16.trans r15_rbp
  have r16_rdi : t16.regValue .rdi = stackSlot s 424 :=
    (ag16.read (n := 64) (r := 7) (by simp)).trans r15_rdi
  have m5_4_40 : MontgomeryAt t5 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_40
  have m6_4_40 : MontgomeryAt t6 (stackSlot s 40) (v4) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_4_40
  have m7_4_40 : MontgomeryAt t7 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_4_40
  have m8_4_40 : MontgomeryAt t8 (stackSlot s 40) (v4) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_4_40
  have m9_4_40 : MontgomeryAt t9 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_4_40
  have m10_4_40 : MontgomeryAt t10 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_4_40
  have m11_4_40 : MontgomeryAt t11 (stackSlot s 40) (v4) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_4_40
  have m12_4_40 : MontgomeryAt t12 (stackSlot s 40) (v4) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_4_40
  have m13_4_40 : MontgomeryAt t13 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_4_40
  have m14_4_40 : MontgomeryAt t14 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_4_40
  have m15_4_40 : MontgomeryAt t15 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_4_40
  have m16_4_40 : MontgomeryAt t16 (stackSlot s 40) (v4) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_4_40
  have r15_rdx : t15.regValue .rdx = stackSlot s 8 :=
    (ag15.read (n := 64) (r := 2) (by simp)).trans r14_rdx
  have r16_rdx : t16.regValue .rdx = stackSlot s 8 :=
    (ag16.read (n := 64) (r := 2) (by simp)).trans r15_rdx
  have w13_8_4 : memLoad t13.external (stackSlot s 8) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by simpa only [ext13] using sw12
  have w14_8_4 : memLoad t14.external (stackSlot s 8) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by simpa only [ext14] using w13_8_4
  have w15_8_4 : memLoad t15.external (stackSlot s 8) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by simpa only [ext15] using w14_8_4
  have w16_8_4 : memLoad t16.external (stackSlot s 8) 64 = memLoad t4.external (stackSlot s 392) 64 :=
    by simpa only [ext16] using w15_8_4
  have w12_16_4 : memLoad t12.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans sw11
  have w13_16_4 : memLoad t13.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext13] using w12_16_4
  have w14_16_4 : memLoad t14.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext14] using w13_16_4
  have w15_16_4 : memLoad t15.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext15] using w14_16_4
  have w16_16_4 : memLoad t16.external (stackSlot s 16) 64 = memLoad t4.external (stackSlot s 400) 64 :=
    by simpa only [ext16] using w15_16_4
  have w9_24_4 : memLoad t9.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext9] using sw8
  have w10_24_4 : memLoad t10.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext10] using w9_24_4
  have w11_24_4 : memLoad t11.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    (store_read ag11 (by decide) (by decide) (by decide)).trans w10_24_4
  have w12_24_4 : memLoad t12.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_24_4
  have w13_24_4 : memLoad t13.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext13] using w12_24_4
  have w14_24_4 : memLoad t14.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext14] using w13_24_4
  have w15_24_4 : memLoad t15.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext15] using w14_24_4
  have w16_24_4 : memLoad t16.external (stackSlot s 24) 64 = memLoad t4.external (stackSlot s 408) 64 :=
    by simpa only [ext16] using w15_24_4
  have w7_32_4 : memLoad t7.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext7] using sw6
  have w8_32_4 : memLoad t8.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    (store_read ag8 (by decide) (by decide) (by decide)).trans w7_32_4
  have w9_32_4 : memLoad t9.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext9] using w8_32_4
  have w10_32_4 : memLoad t10.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext10] using w9_32_4
  have w11_32_4 : memLoad t11.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    (store_read ag11 (by decide) (by decide) (by decide)).trans w10_32_4
  have w12_32_4 : memLoad t12.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    (store_read ag12 (by decide) (by decide) (by decide)).trans w11_32_4
  have w13_32_4 : memLoad t13.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext13] using w12_32_4
  have w14_32_4 : memLoad t14.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext14] using w13_32_4
  have w15_32_4 : memLoad t15.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext15] using w14_32_4
  have w16_32_4 : memLoad t16.external (stackSlot s 32) 64 = memLoad t4.external (stackSlot s 416) 64 :=
    by simpa only [ext16] using w15_32_4
  have m4_0_392 : MontgomeryAt t4 (stackSlot s 392) (bXZDifference point) :=
    by
    refine ⟨m3_0_392.1, m3_0_392.2.1, fun j hj => ?_⟩
    have h := (bytes4 336 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_392.2.2 j hj
    rw [stackSlot_eq s (show 392 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have copy16_8 : MontgomeryAt t16 (stackSlot s 8) (bXZDifference point) :=
    CrossTerms.copied pre frame16 (by decide) m4_0_392
      w16_8_4 (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w16_16_4) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w16_24_4) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w16_32_4)
  let v17 : Nat := ((v4) + (bXZDifference point)) % P256.Spec.Operations.domain.p
  let site17 : BinaryCallSite 1016 728 0x1137c0 16 :=
    { codeOffset := 0x6291, disp := 0xd52a, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x137c0 (by decide),
      layout := ⟨736, 688, 304, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 720, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n17, t17, run17, frame17, rip17, value17, regs17, bytes17, work17⟩ :=
    binary_call pre frame16 (x := v4) (y := bXZDifference point)
      (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) site17
      (fun _ hp hx hy => field_add_correct hp hx hy)
      rip16
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using r16_rsi)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using r16_rdx)
      (by simpa only [stackSlot_eq s (show 424 ≤ 728 by decide)] using r16_rdi)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using m16_4_40)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using copy16_8)
  have m17_424 : MontgomeryAt t17 (stackSlot s 424) v17 := by
    rw [stackSlot_eq s (show 424 ≤ 728 by decide)]
    exact value17
  have point1 : ProjectiveAt t1 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using input.pointAt
  have point2 : ProjectiveAt t2 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using point1
  have point3 : ProjectiveAt t3 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using point2
  have point4 : ProjectiveAt t4 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work4) point3
  have point5 : ProjectiveAt t5 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using point4
  have point6 : ProjectiveAt t6 (s.regValue .rdi) point :=
    store_point pre ag6 (by decide) point5
  have point7 : ProjectiveAt t7 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using point6
  have point8 : ProjectiveAt t8 (s.regValue .rdi) point :=
    store_point pre ag8 (by decide) point7
  have point9 : ProjectiveAt t9 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using point8
  have point10 : ProjectiveAt t10 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using point9
  have point11 : ProjectiveAt t11 (s.regValue .rdi) point :=
    store_point pre ag11 (by decide) point10
  have point12 : ProjectiveAt t12 (s.regValue .rdi) point :=
    store_point pre ag12 (by decide) point11
  have point13 : ProjectiveAt t13 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using point12
  have point14 : ProjectiveAt t14 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using point13
  have point15 : ProjectiveAt t15 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using point14
  have point16 : ProjectiveAt t16 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using point15
  have point17 : ProjectiveAt t17 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work17) point16
  have r1_rbx : t1.regValue .rbx = s.regValue .rdi :=
    (ag1.read (n := 64) (r := 3) (by simp)).trans r0_rbx
  have r2_rbx : t2.regValue .rbx = s.regValue .rdi :=
    (ag2.read (n := 64) (r := 3) (by simp)).trans r1_rbx
  have r3_rbx : t3.regValue .rbx = s.regValue .rdi :=
    (ag3.read (n := 64) (r := 3) (by simp)).trans r2_rbx
  have r4_rbx : t4.regValue .rbx = s.regValue .rdi :=
    (regs4 .rbx (by decide)).trans r3_rbx
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
    (regs17 .rbx (by decide)).trans r16_rbx
  have r1_r15 : t1.regValue .r15 = stackSlot s 616 :=
    (ag1.read (n := 64) (r := 15) (by simp)).trans r0_r15
  have r2_r15 : t2.regValue .r15 = stackSlot s 616 :=
    (ag2.read (n := 64) (r := 15) (by simp)).trans r1_r15
  have r3_r15 : t3.regValue .r15 = stackSlot s 616 :=
    (ag3.read (n := 64) (r := 15) (by simp)).trans r2_r15
  have r4_r15 : t4.regValue .r15 = stackSlot s 616 :=
    (regs4 .r15 (by decide)).trans r3_r15
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
    (regs17 .r15 (by decide)).trans r16_r15
  have r1_r12 : t1.regValue .r12 = stackSlot s 360 :=
    (ag1.read (n := 64) (r := 12) (by simp)).trans r0_r12
  have r2_r12 : t2.regValue .r12 = stackSlot s 360 :=
    (ag2.read (n := 64) (r := 12) (by simp)).trans r1_r12
  have r3_r12 : t3.regValue .r12 = stackSlot s 360 :=
    (ag3.read (n := 64) (r := 12) (by simp)).trans r2_r12
  have r4_r12 : t4.regValue .r12 = stackSlot s 360 :=
    (regs4 .r12 (by decide)).trans r3_r12
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
    (regs17 .r12 (by decide)).trans r16_r12
  have m1_0_104 : MontgomeryAt t1 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_104
  have m2_0_104 : MontgomeryAt t2 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_104
  have m3_0_104 : MontgomeryAt t3 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_104
  have m4_0_104 : MontgomeryAt t4 (stackSlot s 104) ((values point).xx) :=
    by
    refine ⟨m3_0_104.1, m3_0_104.2.1, fun j hj => ?_⟩
    have h := (bytes4 624 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_104.2.2 j hj
    rw [stackSlot_eq s (show 104 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m5_0_104 : MontgomeryAt t5 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_104
  have m6_0_104 : MontgomeryAt t6 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_0_104
  have m7_0_104 : MontgomeryAt t7 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_0_104
  have m8_0_104 : MontgomeryAt t8 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_104
  have m9_0_104 : MontgomeryAt t9 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_104
  have m10_0_104 : MontgomeryAt t10 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_0_104
  have m11_0_104 : MontgomeryAt t11 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_0_104
  have m12_0_104 : MontgomeryAt t12 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_104
  have m13_0_104 : MontgomeryAt t13 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_104
  have m14_0_104 : MontgomeryAt t14 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_104
  have m15_0_104 : MontgomeryAt t15 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_0_104
  have m16_0_104 : MontgomeryAt t16 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_0_104
  have m17_0_104 : MontgomeryAt t17 (stackSlot s 104) ((values point).xx) :=
    by
    refine ⟨m16_0_104.1, m16_0_104.2.1, fun j hj => ?_⟩
    have h := (bytes17 624 32 (by decide) (by decide) (by decide) j hj)
    have hx := m16_0_104.2.2 j hj
    rw [stackSlot_eq s (show 104 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_136 : MontgomeryAt t1 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_136
  have m2_0_136 : MontgomeryAt t2 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_136
  have m3_0_136 : MontgomeryAt t3 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_136
  have m4_0_136 : MontgomeryAt t4 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m3_0_136.1, m3_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes4 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m5_0_136 : MontgomeryAt t5 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_136
  have m6_0_136 : MontgomeryAt t6 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_0_136
  have m7_0_136 : MontgomeryAt t7 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_0_136
  have m8_0_136 : MontgomeryAt t8 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_136
  have m9_0_136 : MontgomeryAt t9 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_136
  have m10_0_136 : MontgomeryAt t10 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_0_136
  have m11_0_136 : MontgomeryAt t11 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_0_136
  have m12_0_136 : MontgomeryAt t12 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_136
  have m13_0_136 : MontgomeryAt t13 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_136
  have m14_0_136 : MontgomeryAt t14 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_136
  have m15_0_136 : MontgomeryAt t15 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_0_136
  have m16_0_136 : MontgomeryAt t16 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_0_136
  have m17_0_136 : MontgomeryAt t17 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m16_0_136.1, m16_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes17 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m16_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_520 : MontgomeryAt t1 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_520
  have m2_0_520 : MontgomeryAt t2 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_520
  have m3_0_520 : MontgomeryAt t3 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_520
  have m4_0_520 : MontgomeryAt t4 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m3_0_520.1, m3_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes4 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m5_0_520 : MontgomeryAt t5 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_520
  have m6_0_520 : MontgomeryAt t6 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_0_520
  have m7_0_520 : MontgomeryAt t7 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_0_520
  have m8_0_520 : MontgomeryAt t8 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_520
  have m9_0_520 : MontgomeryAt t9 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_520
  have m10_0_520 : MontgomeryAt t10 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_0_520
  have m11_0_520 : MontgomeryAt t11 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_0_520
  have m12_0_520 : MontgomeryAt t12 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_520
  have m13_0_520 : MontgomeryAt t13 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_520
  have m14_0_520 : MontgomeryAt t14 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_520
  have m15_0_520 : MontgomeryAt t15 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_0_520
  have m16_0_520 : MontgomeryAt t16 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_0_520
  have m17_0_520 : MontgomeryAt t17 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m16_0_520.1, m16_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes17 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m16_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_616 : MontgomeryAt t1 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_616
  have m2_0_616 : MontgomeryAt t2 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_616
  have m3_0_616 : MontgomeryAt t3 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_616
  have m4_0_616 : MontgomeryAt t4 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m3_0_616.1, m3_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes4 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m5_0_616 : MontgomeryAt t5 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_616
  have m6_0_616 : MontgomeryAt t6 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_0_616
  have m7_0_616 : MontgomeryAt t7 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_0_616
  have m8_0_616 : MontgomeryAt t8 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_616
  have m9_0_616 : MontgomeryAt t9 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_616
  have m10_0_616 : MontgomeryAt t10 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_0_616
  have m11_0_616 : MontgomeryAt t11 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_0_616
  have m12_0_616 : MontgomeryAt t12 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_616
  have m13_0_616 : MontgomeryAt t13 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_616
  have m14_0_616 : MontgomeryAt t14 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_616
  have m15_0_616 : MontgomeryAt t15 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_0_616
  have m16_0_616 : MontgomeryAt t16 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_0_616
  have m17_0_616 : MontgomeryAt t17 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m16_0_616.1, m16_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes17 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m16_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m1_0_360 : MontgomeryAt t1 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext1] using m0_360
  have m2_0_360 : MontgomeryAt t2 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext2] using m1_0_360
  have m3_0_360 : MontgomeryAt t3 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext3] using m2_0_360
  have m4_0_360 : MontgomeryAt t4 (stackSlot s 360) (tripleZZ point) :=
    by
    refine ⟨m3_0_360.1, m3_0_360.2.1, fun j hj => ?_⟩
    have h := (bytes4 368 32 (by decide) (by decide) (by decide) j hj)
    have hx := m3_0_360.2.2 j hj
    rw [stackSlot_eq s (show 360 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m5_0_360 : MontgomeryAt t5 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext5] using m4_0_360
  have m6_0_360 : MontgomeryAt t6 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag6 (by decide) (by decide) (by decide) m5_0_360
  have m7_0_360 : MontgomeryAt t7 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext7] using m6_0_360
  have m8_0_360 : MontgomeryAt t8 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag8 (by decide) (by decide) (by decide) m7_0_360
  have m9_0_360 : MontgomeryAt t9 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext9] using m8_0_360
  have m10_0_360 : MontgomeryAt t10 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext10] using m9_0_360
  have m11_0_360 : MontgomeryAt t11 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag11 (by decide) (by decide) (by decide) m10_0_360
  have m12_0_360 : MontgomeryAt t12 (stackSlot s 360) (tripleZZ point) :=
    store_montgomery ag12 (by decide) (by decide) (by decide) m11_0_360
  have m13_0_360 : MontgomeryAt t13 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext13] using m12_0_360
  have m14_0_360 : MontgomeryAt t14 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext14] using m13_0_360
  have m15_0_360 : MontgomeryAt t15 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext15] using m14_0_360
  have m16_0_360 : MontgomeryAt t16 (stackSlot s 360) (tripleZZ point) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext16] using m15_0_360
  have m17_0_360 : MontgomeryAt t17 (stackSlot s 360) (tripleZZ point) :=
    by
    refine ⟨m16_0_360.1, m16_0_360.2.1, fun j hj => ?_⟩
    have h := (bytes17 368 32 (by decide) (by decide) (by decide) j hj)
    have hx := m16_0_360.2.2 j hj
    rw [stackSlot_eq s (show 360 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have r15_r14 : t15.regValue .r14 = stackSlot s 424 :=
    (ag15.read (n := 64) (r := 14) (by simp)).trans r14_r14
  have r16_r14 : t16.regValue .r14 = stackSlot s 424 :=
    (ag16.read (n := 64) (r := 14) (by simp)).trans r15_r14
  have r17_r14 : t17.regValue .r14 = stackSlot s 424 :=
    (regs17 .r14 (by decide)).trans r16_r14
  refine ⟨_, t17, ((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17), frame17, rip17, ?_⟩
  exact ⟨⟨point17, r17_rbx, r17_r15, m17_0_104, m17_0_136, m17_0_520, m17_0_616, r17_r12, m17_0_360⟩, r17_r14, m17_424⟩

end P256.Proofs.Projective.Double
