import P256.Proofs.Projective.Double.Combinations.Finish.Prepare

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

set_option maxRecDepth 2048 in
theorem Combinations.finish_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x1062fe)
    (input : YFactorAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x10635a ∧ CombinationsAt s u point := by
  let v22 := (values point).xxMinus
  have frame22 := state
  have rip22 := rip
  have m22_648 := input.factor
  have r22_r13 := input.r13
  have m22_0_424 := input.bxz6
  have r22_r15 := input.r15
  have m22_0_616 := input.yProduct
  have point22 := input.pointAt
  have r22_rbx := input.rbx
  have r22_r14 := input.r14
  have m22_0_136 := input.yy
  have m22_0_520 := input.xProduct
  obtain ⟨t23, run23, frame23, effect23⟩ := step_registers pre frame22
    (offset := 0x62fe) (mov_r64_m64_effect_step 0x1062fe 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 448)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip22, stack_readable (frameOffset := 728) pre frame22 (by decide) (offset := 448) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6306 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag23 : AgreesExcept [.reg 0, .rip] t t23 := effect23.agrees
  have ext23 : t23.external = t.external := ag23.external (by simp [Component.Covers])
  have rip23 : t23.RIP = 0x106306 := effect23.rip
  have write23 : t23.regValue .rax = memLoad t.external (stackPtr t + 448#64) 64 := effect23.writes
  rw [frame22.rsp] at write23
  have r23_rax : t23.regValue .rax = memLoad t.external (stackSlot s 448) 64 := write23.trans (Eq.refl _)
  obtain ⟨t24, run24, frame24, effect24⟩ := step pre frame23 (by decide)
    (offset := 0x6306) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106306 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip23, stack_writable (frameOffset := 728) pre frame23 (by decide) (offset := 32) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame23 (by decide) (offset := 32) (len := 8) (codeOffset := 0x6306) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x630b (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame23 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag24 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t23 t24 := by
    have h : AgreesExcept [.mem (stackPtr t23 + 32#64) 8, .rip] t23 t24 := by
      have h := effect24.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame23.rsp] at h
    exact h
  have rip24 : t24.RIP = 0x10630b := effect24.rip
  have write24 : memLoad t24.external (stackPtr t23 + 32#64) 64 = t23.regValue .rax := effect24.writes
  rw [frame23.rsp] at write24
  have sw24 : memLoad t24.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 := write24.trans r23_rax
  have w23_440_22 : memLoad t23.external (stackSlot s 440) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by rw [ext23]
  have w24_440_22 : memLoad t24.external (stackSlot s 440) 64 = memLoad t.external (stackSlot s 440) 64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans w23_440_22
  obtain ⟨t25, run25, frame25, effect25⟩ := step_registers pre frame24
    (offset := 0x630b) (mov_r64_m64_effect_step 0x10630b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 440)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip24, stack_readable (frameOffset := 728) pre frame24 (by decide) (offset := 440) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6313 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag25 : AgreesExcept [.reg 0, .rip] t24 t25 := effect25.agrees
  have ext25 : t25.external = t24.external := ag25.external (by simp [Component.Covers])
  have rip25 : t25.RIP = 0x106313 := effect25.rip
  have write25 : t25.regValue .rax = memLoad t24.external (stackPtr t24 + 440#64) 64 := effect25.writes
  rw [frame24.rsp] at write25
  have r25_rax : t25.regValue .rax = memLoad t.external (stackSlot s 440) 64 := write25.trans w24_440_22
  obtain ⟨t26, run26, frame26, effect26⟩ := step pre frame25 (by decide)
    (offset := 0x6313) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106313 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip25, stack_writable (frameOffset := 728) pre frame25 (by decide) (offset := 24) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame25 (by decide) (offset := 24) (len := 8) (codeOffset := 0x6313) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6318 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame25 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag26 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t25 t26 := by
    have h : AgreesExcept [.mem (stackPtr t25 + 24#64) 8, .rip] t25 t26 := by
      have h := effect26.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame25.rsp] at h
    exact h
  have rip26 : t26.RIP = 0x106318 := effect26.rip
  have write26 : memLoad t26.external (stackPtr t25 + 24#64) 64 = t25.regValue .rax := effect26.writes
  rw [frame25.rsp] at write26
  have sw26 : memLoad t26.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 := write26.trans r25_rax
  have w23_424_22 : memLoad t23.external (stackSlot s 424) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by rw [ext23]
  have w24_424_22 : memLoad t24.external (stackSlot s 424) 64 = memLoad t.external (stackSlot s 424) 64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans w23_424_22
  have w25_424_22 : memLoad t25.external (stackSlot s 424) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by simpa only [ext25] using w24_424_22
  have w26_424_22 : memLoad t26.external (stackSlot s 424) 64 = memLoad t.external (stackSlot s 424) 64 :=
    (store_read ag26 (by decide) (by decide) (by decide)).trans w25_424_22
  obtain ⟨t27, run27, frame27, effect27⟩ := step_registers pre frame26
    (offset := 0x6318) (mov_r64_m64_effect_step 0x106318 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip26, stack_readable (frameOffset := 728) pre frame26 (by decide) (offset := 424) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6320 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag27 : AgreesExcept [.reg 0, .rip] t26 t27 := effect27.agrees
  have ext27 : t27.external = t26.external := ag27.external (by simp [Component.Covers])
  have rip27 : t27.RIP = 0x106320 := effect27.rip
  have write27 : t27.regValue .rax = memLoad t26.external (stackPtr t26 + 424#64) 64 := effect27.writes
  rw [frame26.rsp] at write27
  have r27_rax : t27.regValue .rax = memLoad t.external (stackSlot s 424) 64 := write27.trans w26_424_22
  have w23_432_22 : memLoad t23.external (stackSlot s 432) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by rw [ext23]
  have w24_432_22 : memLoad t24.external (stackSlot s 432) 64 = memLoad t.external (stackSlot s 432) 64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans w23_432_22
  have w25_432_22 : memLoad t25.external (stackSlot s 432) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext25] using w24_432_22
  have w26_432_22 : memLoad t26.external (stackSlot s 432) 64 = memLoad t.external (stackSlot s 432) 64 :=
    (store_read ag26 (by decide) (by decide) (by decide)).trans w25_432_22
  have w27_432_22 : memLoad t27.external (stackSlot s 432) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext27] using w26_432_22
  obtain ⟨t28, run28, frame28, effect28⟩ := step_registers pre frame27
    (offset := 0x6320) (mov_r64_m64_effect_step 0x106320 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 432)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip27, stack_readable (frameOffset := 728) pre frame27 (by decide) (offset := 432) (len := 8) (by decide)⟩
    (inProgram_of_textOffset 0x6328 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 1, .rip]; decide +kernel)
  have ag28 : AgreesExcept [.reg 1, .rip] t27 t28 := effect28.agrees
  have ext28 : t28.external = t27.external := ag28.external (by simp [Component.Covers])
  have rip28 : t28.RIP = 0x106328 := effect28.rip
  have write28 : t28.regValue .rcx = memLoad t27.external (stackPtr t27 + 432#64) 64 := effect28.writes
  rw [frame27.rsp] at write28
  have r28_rcx : t28.regValue .rcx = memLoad t.external (stackSlot s 432) 64 := write28.trans w27_432_22
  obtain ⟨t29, run29, frame29, effect29⟩ := step pre frame28 (by decide)
    (offset := 0x6328) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106328 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip28, stack_writable (frameOffset := 728) pre frame28 (by decide) (offset := 16) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame28 (by decide) (offset := 16) (len := 8) (codeOffset := 0x6328) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x632d (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame28 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag29 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t28 t29 := by
    have h : AgreesExcept [.mem (stackPtr t28 + 16#64) 8, .rip] t28 t29 := by
      have h := effect29.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame28.rsp] at h
    exact h
  have rip29 : t29.RIP = 0x10632d := effect29.rip
  have write29 : memLoad t29.external (stackPtr t28 + 16#64) 64 = t28.regValue .rcx := effect29.writes
  rw [frame28.rsp] at write29
  have sw29 : memLoad t29.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 := write29.trans r28_rcx
  have r28_rax : t28.regValue .rax = memLoad t.external (stackSlot s 424) 64 :=
    (ag28.read (n := 64) (r := 0) (by simp)).trans r27_rax
  have r29_rax : t29.regValue .rax = memLoad t.external (stackSlot s 424) 64 :=
    (ag29.read (n := 64) (r := 0) (by simp)).trans r28_rax
  obtain ⟨t30, run30, frame30, effect30⟩ := step pre frame29 (by decide)
    (offset := 0x632d) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10632d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip29, stack_writable (frameOffset := 728) pre frame29 (by decide) (offset := 8) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame29 (by decide) (offset := 8) (len := 8) (codeOffset := 0x632d) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6332 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame29 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag30 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t29 t30 := by
    have h : AgreesExcept [.mem (stackPtr t29 + 8#64) 8, .rip] t29 t30 := by
      have h := effect30.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame29.rsp] at h
    exact h
  have rip30 : t30.RIP = 0x106332 := effect30.rip
  have write30 : memLoad t30.external (stackPtr t29 + 8#64) 64 = t29.regValue .rax := effect30.writes
  rw [frame29.rsp] at write30
  have sw30 : memLoad t30.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 424) 64 := write30.trans r29_rax
  obtain ⟨t31, run31, frame31, effect31⟩ := step_registers pre frame30
    (offset := 0x6332) (lea_r64_effect_step 0x106332 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip30
    (inProgram_of_textOffset 0x6337 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 12, .rip]; decide +kernel)
  have ag31 : AgreesExcept [.reg 12, .rip] t30 t31 := effect31.agrees
  have ext31 : t31.external = t30.external := ag31.external (by simp [Component.Covers])
  have rip31 : t31.RIP = 0x106337 := effect31.rip
  have write31 : t31.regValue .r12 = stackPtr t30 + 40#64 := effect31.writes
  rw [frame30.rsp] at write31
  have r31_r12 : t31.regValue .r12 = stackSlot s 40 := write31
  obtain ⟨t32, run32, frame32, effect32⟩ := step_registers pre frame31
    (offset := 0x6337) (lea_r64_effect_step 0x106337 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip31
    (inProgram_of_textOffset 0x633c (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag32 : AgreesExcept [.reg 2, .rip] t31 t32 := effect32.agrees
  have ext32 : t32.external = t31.external := ag32.external (by simp [Component.Covers])
  have rip32 : t32.RIP = 0x10633c := effect32.rip
  have write32 : t32.regValue .rdx = stackPtr t31 + 8#64 := effect32.writes
  rw [frame31.rsp] at write32
  have r32_rdx : t32.regValue .rdx = stackSlot s 8 := write32
  have r32_r12 : t32.regValue .r12 = stackSlot s 40 :=
    (ag32.read (n := 64) (r := 12) (by simp)).trans r31_r12
  obtain ⟨t33, run33, frame33, effect33⟩ := step_registers pre frame32
    (offset := 0x633c) (mov_r64_r64_effect_step 0x10633c 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip32
    (inProgram_of_textOffset 0x633f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag33 : AgreesExcept [.reg 7, .rip] t32 t33 := effect33.agrees
  have ext33 : t33.external = t32.external := ag33.external (by simp [Component.Covers])
  have rip33 : t33.RIP = 0x10633f := effect33.rip
  have write33 : t33.regValue .rdi = t32.regValue .r12 := effect33.writes
  have r33_rdi : t33.regValue .rdi = stackSlot s 40 := write33.trans r32_r12
  have r23_r13 : t23.regValue .r13 = stackSlot s 648 :=
    (ag23.read (n := 64) (r := 13) (by simp)).trans r22_r13
  have r24_r13 : t24.regValue .r13 = stackSlot s 648 :=
    (ag24.read (n := 64) (r := 13) (by simp)).trans r23_r13
  have r25_r13 : t25.regValue .r13 = stackSlot s 648 :=
    (ag25.read (n := 64) (r := 13) (by simp)).trans r24_r13
  have r26_r13 : t26.regValue .r13 = stackSlot s 648 :=
    (ag26.read (n := 64) (r := 13) (by simp)).trans r25_r13
  have r27_r13 : t27.regValue .r13 = stackSlot s 648 :=
    (ag27.read (n := 64) (r := 13) (by simp)).trans r26_r13
  have r28_r13 : t28.regValue .r13 = stackSlot s 648 :=
    (ag28.read (n := 64) (r := 13) (by simp)).trans r27_r13
  have r29_r13 : t29.regValue .r13 = stackSlot s 648 :=
    (ag29.read (n := 64) (r := 13) (by simp)).trans r28_r13
  have r30_r13 : t30.regValue .r13 = stackSlot s 648 :=
    (ag30.read (n := 64) (r := 13) (by simp)).trans r29_r13
  have r31_r13 : t31.regValue .r13 = stackSlot s 648 :=
    (ag31.read (n := 64) (r := 13) (by simp)).trans r30_r13
  have r32_r13 : t32.regValue .r13 = stackSlot s 648 :=
    (ag32.read (n := 64) (r := 13) (by simp)).trans r31_r13
  have r33_r13 : t33.regValue .r13 = stackSlot s 648 :=
    (ag33.read (n := 64) (r := 13) (by simp)).trans r32_r13
  obtain ⟨t34, run34, frame34, effect34⟩ := step_registers pre frame33
    (offset := 0x633f) (mov_r64_r64_effect_step 0x10633f 0x4c 0xee (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip33
    (inProgram_of_textOffset 0x6342 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag34 : AgreesExcept [.reg 6, .rip] t33 t34 := effect34.agrees
  have ext34 : t34.external = t33.external := ag34.external (by simp [Component.Covers])
  have rip34 : t34.RIP = 0x106342 := effect34.rip
  have write34 : t34.regValue .rsi = t33.regValue .r13 := effect34.writes
  have r34_rsi : t34.regValue .rsi = stackSlot s 648 := write34.trans r33_r13
  have r34_rdi : t34.regValue .rdi = stackSlot s 40 :=
    (ag34.read (n := 64) (r := 7) (by simp)).trans r33_rdi
  have m23_22_648 : MontgomeryAt t23 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_648
  have m24_22_648 : MontgomeryAt t24 (stackSlot s 648) (v22) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_22_648
  have m25_22_648 : MontgomeryAt t25 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_22_648
  have m26_22_648 : MontgomeryAt t26 (stackSlot s 648) (v22) :=
    store_montgomery ag26 (by decide) (by decide) (by decide) m25_22_648
  have m27_22_648 : MontgomeryAt t27 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_22_648
  have m28_22_648 : MontgomeryAt t28 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_22_648
  have m29_22_648 : MontgomeryAt t29 (stackSlot s 648) (v22) :=
    store_montgomery ag29 (by decide) (by decide) (by decide) m28_22_648
  have m30_22_648 : MontgomeryAt t30 (stackSlot s 648) (v22) :=
    store_montgomery ag30 (by decide) (by decide) (by decide) m29_22_648
  have m31_22_648 : MontgomeryAt t31 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using m30_22_648
  have m32_22_648 : MontgomeryAt t32 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m31_22_648
  have m33_22_648 : MontgomeryAt t33 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using m32_22_648
  have m34_22_648 : MontgomeryAt t34 (stackSlot s 648) (v22) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using m33_22_648
  have r33_rdx : t33.regValue .rdx = stackSlot s 8 :=
    (ag33.read (n := 64) (r := 2) (by simp)).trans r32_rdx
  have r34_rdx : t34.regValue .rdx = stackSlot s 8 :=
    (ag34.read (n := 64) (r := 2) (by simp)).trans r33_rdx
  have w31_8_22 : memLoad t31.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by simpa only [ext31] using sw30
  have w32_8_22 : memLoad t32.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by simpa only [ext32] using w31_8_22
  have w33_8_22 : memLoad t33.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by simpa only [ext33] using w32_8_22
  have w34_8_22 : memLoad t34.external (stackSlot s 8) 64 = memLoad t.external (stackSlot s 424) 64 :=
    by simpa only [ext34] using w33_8_22
  have w30_16_22 : memLoad t30.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 :=
    (store_read ag30 (by decide) (by decide) (by decide)).trans sw29
  have w31_16_22 : memLoad t31.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext31] using w30_16_22
  have w32_16_22 : memLoad t32.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext32] using w31_16_22
  have w33_16_22 : memLoad t33.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext33] using w32_16_22
  have w34_16_22 : memLoad t34.external (stackSlot s 16) 64 = memLoad t.external (stackSlot s 432) 64 :=
    by simpa only [ext34] using w33_16_22
  have w27_24_22 : memLoad t27.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext27] using sw26
  have w28_24_22 : memLoad t28.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext28] using w27_24_22
  have w29_24_22 : memLoad t29.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    (store_read ag29 (by decide) (by decide) (by decide)).trans w28_24_22
  have w30_24_22 : memLoad t30.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    (store_read ag30 (by decide) (by decide) (by decide)).trans w29_24_22
  have w31_24_22 : memLoad t31.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext31] using w30_24_22
  have w32_24_22 : memLoad t32.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext32] using w31_24_22
  have w33_24_22 : memLoad t33.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext33] using w32_24_22
  have w34_24_22 : memLoad t34.external (stackSlot s 24) 64 = memLoad t.external (stackSlot s 440) 64 :=
    by simpa only [ext34] using w33_24_22
  have w25_32_22 : memLoad t25.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext25] using sw24
  have w26_32_22 : memLoad t26.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    (store_read ag26 (by decide) (by decide) (by decide)).trans w25_32_22
  have w27_32_22 : memLoad t27.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext27] using w26_32_22
  have w28_32_22 : memLoad t28.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext28] using w27_32_22
  have w29_32_22 : memLoad t29.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    (store_read ag29 (by decide) (by decide) (by decide)).trans w28_32_22
  have w30_32_22 : memLoad t30.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    (store_read ag30 (by decide) (by decide) (by decide)).trans w29_32_22
  have w31_32_22 : memLoad t31.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext31] using w30_32_22
  have w32_32_22 : memLoad t32.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext32] using w31_32_22
  have w33_32_22 : memLoad t33.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext33] using w32_32_22
  have w34_32_22 : memLoad t34.external (stackSlot s 32) 64 = memLoad t.external (stackSlot s 448) 64 :=
    by simpa only [ext34] using w33_32_22
  have copy34_8 : MontgomeryAt t34 (stackSlot s 8) ((values point).bxz6) :=
    CrossTerms.copied pre frame34 (by decide) m22_0_424
      w34_8_22 (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w34_16_22) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w34_24_22) (by simpa only [stackSlot, BitVec.add_assoc, BitVec.reduceAdd] using w34_32_22)
  let v35 : Nat := ((v22) * ((values point).bxz6)) % P256.Spec.Operations.domain.p
  let site35 : BinaryCallSite 1016 728 0x113890 280 :=
    { codeOffset := 0x6342, disp := 0xd549, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x13890 (by decide),
      layout := ⟨736, 80, 688, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 720, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n35, t35, run35, frame35, rip35, value35, regs35, bytes35, work35⟩ :=
    binary_call pre frame34 (x := v22) (y := (values point).bxz6)
      (op := fun x y => x*y % P256.Spec.Operations.domain.p) site35
      (fun _ hp hx hy => field_mul_correct hp hx hy)
      rip34
      (by simpa only [stackSlot_eq s (show 648 ≤ 728 by decide)] using r34_rsi)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using r34_rdx)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using r34_rdi)
      (by simpa only [stackSlot_eq s (show 648 ≤ 728 by decide)] using m34_22_648)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using copy34_8)
  have m35_40 : MontgomeryAt t35 (stackSlot s 40) v35 := by
    rw [stackSlot_eq s (show 40 ≤ 728 by decide)]
    exact value35
  obtain ⟨t36, run36, frame36, effect36⟩ := step_registers pre frame35
    (offset := 0x6347) (lea_r64_effect_step 0x106347 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip35
    (inProgram_of_textOffset 0x634f (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag36 : AgreesExcept [.reg 7, .rip] t35 t36 := effect36.agrees
  have ext36 : t36.external = t35.external := ag36.external (by simp [Component.Covers])
  have rip36 : t36.RIP = 0x10634f := effect36.rip
  have write36 : t36.regValue .rdi = stackPtr t35 + 456#64 := effect36.writes
  rw [frame35.rsp] at write36
  have r36_rdi : t36.regValue .rdi = stackSlot s 456 := write36
  have r23_r15 : t23.regValue .r15 = stackSlot s 616 :=
    (ag23.read (n := 64) (r := 15) (by simp)).trans r22_r15
  have r24_r15 : t24.regValue .r15 = stackSlot s 616 :=
    (ag24.read (n := 64) (r := 15) (by simp)).trans r23_r15
  have r25_r15 : t25.regValue .r15 = stackSlot s 616 :=
    (ag25.read (n := 64) (r := 15) (by simp)).trans r24_r15
  have r26_r15 : t26.regValue .r15 = stackSlot s 616 :=
    (ag26.read (n := 64) (r := 15) (by simp)).trans r25_r15
  have r27_r15 : t27.regValue .r15 = stackSlot s 616 :=
    (ag27.read (n := 64) (r := 15) (by simp)).trans r26_r15
  have r28_r15 : t28.regValue .r15 = stackSlot s 616 :=
    (ag28.read (n := 64) (r := 15) (by simp)).trans r27_r15
  have r29_r15 : t29.regValue .r15 = stackSlot s 616 :=
    (ag29.read (n := 64) (r := 15) (by simp)).trans r28_r15
  have r30_r15 : t30.regValue .r15 = stackSlot s 616 :=
    (ag30.read (n := 64) (r := 15) (by simp)).trans r29_r15
  have r31_r15 : t31.regValue .r15 = stackSlot s 616 :=
    (ag31.read (n := 64) (r := 15) (by simp)).trans r30_r15
  have r32_r15 : t32.regValue .r15 = stackSlot s 616 :=
    (ag32.read (n := 64) (r := 15) (by simp)).trans r31_r15
  have r33_r15 : t33.regValue .r15 = stackSlot s 616 :=
    (ag33.read (n := 64) (r := 15) (by simp)).trans r32_r15
  have r34_r15 : t34.regValue .r15 = stackSlot s 616 :=
    (ag34.read (n := 64) (r := 15) (by simp)).trans r33_r15
  have r35_r15 : t35.regValue .r15 = stackSlot s 616 :=
    (regs35 .r15 (by decide)).trans r34_r15
  have r36_r15 : t36.regValue .r15 = stackSlot s 616 :=
    (ag36.read (n := 64) (r := 15) (by simp)).trans r35_r15
  obtain ⟨t37, run37, frame37, effect37⟩ := step_registers pre frame36
    (offset := 0x634f) (mov_r64_r64_effect_step 0x10634f 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip36
    (inProgram_of_textOffset 0x6352 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag37 : AgreesExcept [.reg 6, .rip] t36 t37 := effect37.agrees
  have ext37 : t37.external = t36.external := ag37.external (by simp [Component.Covers])
  have rip37 : t37.RIP = 0x106352 := effect37.rip
  have write37 : t37.regValue .rsi = t36.regValue .r15 := effect37.writes
  have r37_rsi : t37.regValue .rsi = stackSlot s 616 := write37.trans r36_r15
  have r33_r12 : t33.regValue .r12 = stackSlot s 40 :=
    (ag33.read (n := 64) (r := 12) (by simp)).trans r32_r12
  have r34_r12 : t34.regValue .r12 = stackSlot s 40 :=
    (ag34.read (n := 64) (r := 12) (by simp)).trans r33_r12
  have r35_r12 : t35.regValue .r12 = stackSlot s 40 :=
    (regs35 .r12 (by decide)).trans r34_r12
  have r36_r12 : t36.regValue .r12 = stackSlot s 40 :=
    (ag36.read (n := 64) (r := 12) (by simp)).trans r35_r12
  have r37_r12 : t37.regValue .r12 = stackSlot s 40 :=
    (ag37.read (n := 64) (r := 12) (by simp)).trans r36_r12
  obtain ⟨t38, run38, frame38, effect38⟩ := step_registers pre frame37
    (offset := 0x6352) (mov_r64_r64_effect_step 0x106352 0x4c 0xe2 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip37
    (inProgram_of_textOffset 0x6355 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag38 : AgreesExcept [.reg 2, .rip] t37 t38 := effect38.agrees
  have ext38 : t38.external = t37.external := ag38.external (by simp [Component.Covers])
  have rip38 : t38.RIP = 0x106355 := effect38.rip
  have write38 : t38.regValue .rdx = t37.regValue .r12 := effect38.writes
  have r38_rdx : t38.regValue .rdx = stackSlot s 40 := write38.trans r37_r12
  have r37_rdi : t37.regValue .rdi = stackSlot s 456 :=
    (ag37.read (n := 64) (r := 7) (by simp)).trans r36_rdi
  have r38_rdi : t38.regValue .rdi = stackSlot s 456 :=
    (ag38.read (n := 64) (r := 7) (by simp)).trans r37_rdi
  have r38_rsi : t38.regValue .rsi = stackSlot s 616 :=
    (ag38.read (n := 64) (r := 6) (by simp)).trans r37_rsi
  have m23_0_616 : MontgomeryAt t23 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_616
  have m24_0_616 : MontgomeryAt t24 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_616
  have m25_0_616 : MontgomeryAt t25 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_616
  have m26_0_616 : MontgomeryAt t26 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag26 (by decide) (by decide) (by decide) m25_0_616
  have m27_0_616 : MontgomeryAt t27 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_616
  have m28_0_616 : MontgomeryAt t28 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_616
  have m29_0_616 : MontgomeryAt t29 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag29 (by decide) (by decide) (by decide) m28_0_616
  have m30_0_616 : MontgomeryAt t30 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag30 (by decide) (by decide) (by decide) m29_0_616
  have m31_0_616 : MontgomeryAt t31 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using m30_0_616
  have m32_0_616 : MontgomeryAt t32 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m31_0_616
  have m33_0_616 : MontgomeryAt t33 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using m32_0_616
  have m34_0_616 : MontgomeryAt t34 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using m33_0_616
  have m35_0_616 : MontgomeryAt t35 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m34_0_616.1, m34_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes35 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m34_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m36_0_616 : MontgomeryAt t36 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using m35_0_616
  have m37_0_616 : MontgomeryAt t37 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using m36_0_616
  have m38_0_616 : MontgomeryAt t38 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using m37_0_616
  have m36_35_40 : MontgomeryAt t36 (stackSlot s 40) (v35) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using m35_40
  have m37_35_40 : MontgomeryAt t37 (stackSlot s 40) (v35) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using m36_35_40
  have m38_35_40 : MontgomeryAt t38 (stackSlot s 40) (v35) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using m37_35_40
  let v39 : Nat := (((values point).yProduct) + (v35)) % P256.Spec.Operations.domain.p
  let site39 : BinaryCallSite 1016 728 0x1137c0 16 :=
    { codeOffset := 0x6355, disp := 0xd466, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x137c0 (by decide),
      layout := ⟨736, 112, 272, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 688, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n39, t39, run39, frame39, rip39, value39, regs39, bytes39, work39⟩ :=
    binary_call pre frame38 (x := (values point).yProduct) (y := v35)
      (op := fun x y => (x+y) % P256.Spec.Operations.domain.p) site39
      (fun _ hp hx hy => field_add_correct hp hx hy)
      rip38
      (by simpa only [stackSlot_eq s (show 616 ≤ 728 by decide)] using r38_rsi)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using r38_rdx)
      (by simpa only [stackSlot_eq s (show 456 ≤ 728 by decide)] using r38_rdi)
      (by simpa only [stackSlot_eq s (show 616 ≤ 728 by decide)] using m38_0_616)
      (by simpa only [stackSlot_eq s (show 40 ≤ 728 by decide)] using m38_35_40)
  have m39_456 : MontgomeryAt t39 (stackSlot s 456) v39 := by
    rw [stackSlot_eq s (show 456 ≤ 728 by decide)]
    exact value39
  have point23 : ProjectiveAt t23 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using point22
  have point24 : ProjectiveAt t24 (s.regValue .rdi) point :=
    store_point pre ag24 (by decide) point23
  have point25 : ProjectiveAt t25 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using point24
  have point26 : ProjectiveAt t26 (s.regValue .rdi) point :=
    store_point pre ag26 (by decide) point25
  have point27 : ProjectiveAt t27 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using point26
  have point28 : ProjectiveAt t28 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using point27
  have point29 : ProjectiveAt t29 (s.regValue .rdi) point :=
    store_point pre ag29 (by decide) point28
  have point30 : ProjectiveAt t30 (s.regValue .rdi) point :=
    store_point pre ag30 (by decide) point29
  have point31 : ProjectiveAt t31 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using point30
  have point32 : ProjectiveAt t32 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using point31
  have point33 : ProjectiveAt t33 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using point32
  have point34 : ProjectiveAt t34 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using point33
  have point35 : ProjectiveAt t35 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work35) point34
  have point36 : ProjectiveAt t36 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using point35
  have point37 : ProjectiveAt t37 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using point36
  have point38 : ProjectiveAt t38 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using point37
  have point39 : ProjectiveAt t39 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work39) point38
  have r23_rbx : t23.regValue .rbx = s.regValue .rdi :=
    (ag23.read (n := 64) (r := 3) (by simp)).trans r22_rbx
  have r24_rbx : t24.regValue .rbx = s.regValue .rdi :=
    (ag24.read (n := 64) (r := 3) (by simp)).trans r23_rbx
  have r25_rbx : t25.regValue .rbx = s.regValue .rdi :=
    (ag25.read (n := 64) (r := 3) (by simp)).trans r24_rbx
  have r26_rbx : t26.regValue .rbx = s.regValue .rdi :=
    (ag26.read (n := 64) (r := 3) (by simp)).trans r25_rbx
  have r27_rbx : t27.regValue .rbx = s.regValue .rdi :=
    (ag27.read (n := 64) (r := 3) (by simp)).trans r26_rbx
  have r28_rbx : t28.regValue .rbx = s.regValue .rdi :=
    (ag28.read (n := 64) (r := 3) (by simp)).trans r27_rbx
  have r29_rbx : t29.regValue .rbx = s.regValue .rdi :=
    (ag29.read (n := 64) (r := 3) (by simp)).trans r28_rbx
  have r30_rbx : t30.regValue .rbx = s.regValue .rdi :=
    (ag30.read (n := 64) (r := 3) (by simp)).trans r29_rbx
  have r31_rbx : t31.regValue .rbx = s.regValue .rdi :=
    (ag31.read (n := 64) (r := 3) (by simp)).trans r30_rbx
  have r32_rbx : t32.regValue .rbx = s.regValue .rdi :=
    (ag32.read (n := 64) (r := 3) (by simp)).trans r31_rbx
  have r33_rbx : t33.regValue .rbx = s.regValue .rdi :=
    (ag33.read (n := 64) (r := 3) (by simp)).trans r32_rbx
  have r34_rbx : t34.regValue .rbx = s.regValue .rdi :=
    (ag34.read (n := 64) (r := 3) (by simp)).trans r33_rbx
  have r35_rbx : t35.regValue .rbx = s.regValue .rdi :=
    (regs35 .rbx (by decide)).trans r34_rbx
  have r36_rbx : t36.regValue .rbx = s.regValue .rdi :=
    (ag36.read (n := 64) (r := 3) (by simp)).trans r35_rbx
  have r37_rbx : t37.regValue .rbx = s.regValue .rdi :=
    (ag37.read (n := 64) (r := 3) (by simp)).trans r36_rbx
  have r38_rbx : t38.regValue .rbx = s.regValue .rdi :=
    (ag38.read (n := 64) (r := 3) (by simp)).trans r37_rbx
  have r39_rbx : t39.regValue .rbx = s.regValue .rdi :=
    (regs39 .rbx (by decide)).trans r38_rbx
  have r23_r14 : t23.regValue .r14 = stackSlot s 424 :=
    (ag23.read (n := 64) (r := 14) (by simp)).trans r22_r14
  have r24_r14 : t24.regValue .r14 = stackSlot s 424 :=
    (ag24.read (n := 64) (r := 14) (by simp)).trans r23_r14
  have r25_r14 : t25.regValue .r14 = stackSlot s 424 :=
    (ag25.read (n := 64) (r := 14) (by simp)).trans r24_r14
  have r26_r14 : t26.regValue .r14 = stackSlot s 424 :=
    (ag26.read (n := 64) (r := 14) (by simp)).trans r25_r14
  have r27_r14 : t27.regValue .r14 = stackSlot s 424 :=
    (ag27.read (n := 64) (r := 14) (by simp)).trans r26_r14
  have r28_r14 : t28.regValue .r14 = stackSlot s 424 :=
    (ag28.read (n := 64) (r := 14) (by simp)).trans r27_r14
  have r29_r14 : t29.regValue .r14 = stackSlot s 424 :=
    (ag29.read (n := 64) (r := 14) (by simp)).trans r28_r14
  have r30_r14 : t30.regValue .r14 = stackSlot s 424 :=
    (ag30.read (n := 64) (r := 14) (by simp)).trans r29_r14
  have r31_r14 : t31.regValue .r14 = stackSlot s 424 :=
    (ag31.read (n := 64) (r := 14) (by simp)).trans r30_r14
  have r32_r14 : t32.regValue .r14 = stackSlot s 424 :=
    (ag32.read (n := 64) (r := 14) (by simp)).trans r31_r14
  have r33_r14 : t33.regValue .r14 = stackSlot s 424 :=
    (ag33.read (n := 64) (r := 14) (by simp)).trans r32_r14
  have r34_r14 : t34.regValue .r14 = stackSlot s 424 :=
    (ag34.read (n := 64) (r := 14) (by simp)).trans r33_r14
  have r35_r14 : t35.regValue .r14 = stackSlot s 424 :=
    (regs35 .r14 (by decide)).trans r34_r14
  have r36_r14 : t36.regValue .r14 = stackSlot s 424 :=
    (ag36.read (n := 64) (r := 14) (by simp)).trans r35_r14
  have r37_r14 : t37.regValue .r14 = stackSlot s 424 :=
    (ag37.read (n := 64) (r := 14) (by simp)).trans r36_r14
  have r38_r14 : t38.regValue .r14 = stackSlot s 424 :=
    (ag38.read (n := 64) (r := 14) (by simp)).trans r37_r14
  have r39_r14 : t39.regValue .r14 = stackSlot s 424 :=
    (regs39 .r14 (by decide)).trans r38_r14
  have m23_0_136 : MontgomeryAt t23 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_136
  have m24_0_136 : MontgomeryAt t24 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_136
  have m25_0_136 : MontgomeryAt t25 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_136
  have m26_0_136 : MontgomeryAt t26 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag26 (by decide) (by decide) (by decide) m25_0_136
  have m27_0_136 : MontgomeryAt t27 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_136
  have m28_0_136 : MontgomeryAt t28 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_136
  have m29_0_136 : MontgomeryAt t29 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag29 (by decide) (by decide) (by decide) m28_0_136
  have m30_0_136 : MontgomeryAt t30 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag30 (by decide) (by decide) (by decide) m29_0_136
  have m31_0_136 : MontgomeryAt t31 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using m30_0_136
  have m32_0_136 : MontgomeryAt t32 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m31_0_136
  have m33_0_136 : MontgomeryAt t33 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using m32_0_136
  have m34_0_136 : MontgomeryAt t34 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using m33_0_136
  have m35_0_136 : MontgomeryAt t35 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m34_0_136.1, m34_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes35 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m34_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m36_0_136 : MontgomeryAt t36 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using m35_0_136
  have m37_0_136 : MontgomeryAt t37 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using m36_0_136
  have m38_0_136 : MontgomeryAt t38 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using m37_0_136
  have m39_0_136 : MontgomeryAt t39 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m38_0_136.1, m38_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes39 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m38_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m23_0_424 : MontgomeryAt t23 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_424
  have m24_0_424 : MontgomeryAt t24 (stackSlot s 424) ((values point).bxz6) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_424
  have m25_0_424 : MontgomeryAt t25 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_424
  have m26_0_424 : MontgomeryAt t26 (stackSlot s 424) ((values point).bxz6) :=
    store_montgomery ag26 (by decide) (by decide) (by decide) m25_0_424
  have m27_0_424 : MontgomeryAt t27 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_424
  have m28_0_424 : MontgomeryAt t28 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_424
  have m29_0_424 : MontgomeryAt t29 (stackSlot s 424) ((values point).bxz6) :=
    store_montgomery ag29 (by decide) (by decide) (by decide) m28_0_424
  have m30_0_424 : MontgomeryAt t30 (stackSlot s 424) ((values point).bxz6) :=
    store_montgomery ag30 (by decide) (by decide) (by decide) m29_0_424
  have m31_0_424 : MontgomeryAt t31 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using m30_0_424
  have m32_0_424 : MontgomeryAt t32 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m31_0_424
  have m33_0_424 : MontgomeryAt t33 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using m32_0_424
  have m34_0_424 : MontgomeryAt t34 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using m33_0_424
  have m35_0_424 : MontgomeryAt t35 (stackSlot s 424) ((values point).bxz6) :=
    by
    refine ⟨m34_0_424.1, m34_0_424.2.1, fun j hj => ?_⟩
    have h := (bytes35 304 32 (by decide) (by decide) (by decide) j hj)
    have hx := m34_0_424.2.2 j hj
    rw [stackSlot_eq s (show 424 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m36_0_424 : MontgomeryAt t36 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using m35_0_424
  have m37_0_424 : MontgomeryAt t37 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using m36_0_424
  have m38_0_424 : MontgomeryAt t38 (stackSlot s 424) ((values point).bxz6) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using m37_0_424
  have m39_0_424 : MontgomeryAt t39 (stackSlot s 424) ((values point).bxz6) :=
    by
    refine ⟨m38_0_424.1, m38_0_424.2.1, fun j hj => ?_⟩
    have h := (bytes39 304 32 (by decide) (by decide) (by decide) j hj)
    have hx := m38_0_424.2.2 j hj
    rw [stackSlot_eq s (show 424 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m23_0_520 : MontgomeryAt t23 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext23] using m22_0_520
  have m24_0_520 : MontgomeryAt t24 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_520
  have m25_0_520 : MontgomeryAt t25 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_520
  have m26_0_520 : MontgomeryAt t26 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag26 (by decide) (by decide) (by decide) m25_0_520
  have m27_0_520 : MontgomeryAt t27 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_520
  have m28_0_520 : MontgomeryAt t28 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_520
  have m29_0_520 : MontgomeryAt t29 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag29 (by decide) (by decide) (by decide) m28_0_520
  have m30_0_520 : MontgomeryAt t30 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag30 (by decide) (by decide) (by decide) m29_0_520
  have m31_0_520 : MontgomeryAt t31 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext31] using m30_0_520
  have m32_0_520 : MontgomeryAt t32 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext32] using m31_0_520
  have m33_0_520 : MontgomeryAt t33 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext33] using m32_0_520
  have m34_0_520 : MontgomeryAt t34 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext34] using m33_0_520
  have m35_0_520 : MontgomeryAt t35 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m34_0_520.1, m34_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes35 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m34_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m36_0_520 : MontgomeryAt t36 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext36] using m35_0_520
  have m37_0_520 : MontgomeryAt t37 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext37] using m36_0_520
  have m38_0_520 : MontgomeryAt t38 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext38] using m37_0_520
  have m39_0_520 : MontgomeryAt t39 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m38_0_520.1, m38_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes39 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m38_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  refine ⟨_, t39, ((((((((((((((((run23.trans run24).trans run25).trans run26).trans run27).trans run28).trans run29).trans run30).trans run31).trans run32).trans run33).trans run34).trans run35).trans run36).trans run37).trans run38).trans run39), frame39, rip39, point39, r39_rbx, ?_, ?_, ?_, ?_, ?_⟩
  · have ha : stackSlot s 424 = stackPtr s - 304 := stackSlot_eq s (show 424 ≤ 728 by decide)
    exact r39_r14.trans ha
  · have ha : stackSlot s 136 = stackPtr s - 592 := stackSlot_eq s (show 136 ≤ 728 by decide)
    exact ha ▸ m39_0_136
  · have ha : stackSlot s 424 = stackPtr s - 304 := stackSlot_eq s (show 424 ≤ 728 by decide)
    exact ha ▸ m39_0_424
  · have ha : stackSlot s 520 = stackPtr s - 208 := stackSlot_eq s (show 520 ≤ 728 by decide)
    exact ha ▸ m39_0_520
  · have ha : stackSlot s 456 = stackPtr s - 272 := stackSlot_eq s (show 456 ≤ 728 by decide)
    exact ha ▸ m39_456

end P256.Proofs.Projective.Double
