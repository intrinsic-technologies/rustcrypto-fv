import P256.Proofs.Projective.Double.Combinations.BProduct.TripleZZ

import P256.Proofs.Field.Constants

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

set_option maxRecDepth 2048 in
theorem Combinations.b_product_finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x10615f)
    (input : ZZTripledAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x1061ae ∧ BProductAt s u point := by
  let v17 := tripleZZ point
  have frame17 := state
  have rip17 := rip
  have m17_360 := input.zz3
  have r17_rbp := input.rbp
  have m17_0_200 := input.xz2
  have point17 := input.pointAt
  have r17_rbx := input.rbx
  have r17_r15 := input.r15
  have r17_r12 := input.r12
  have m17_0_104 := input.xx
  have m17_0_136 := input.yy
  have m17_0_520 := input.xProduct
  have m17_0_616 := input.yProduct
  obtain ⟨t18, run18, frame18, effect18⟩ := step_registers pre frame17
    (offset := 0x615f) (mov_r64_imm64_effect_step 0x10615f 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xdc30061d04874834)
    (by decide) (by decide +kernel)
    rip17
    (inProgram_of_textOffset 0x6169 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag18 : AgreesExcept [.reg 0, .rip] t t18 := effect18.agrees
  have ext18 : t18.external = t.external := ag18.external (by simp [Component.Covers])
  have rip18 : t18.RIP = 0x106169 := effect18.rip
  have write18 : t18.regValue .rax = 0xdc30061d04874834#64 := effect18.writes
  have r18_rax : t18.regValue .rax = 0xdc30061d04874834#64 := write18
  obtain ⟨t19, run19, frame19, effect19⟩ := step pre frame18 (by decide)
    (offset := 0x6169) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106169 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip18, stack_writable (frameOffset := 728) pre frame18 (by decide) (offset := 32) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame18 (by decide) (offset := 32) (len := 8) (codeOffset := 0x6169) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x616e (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame18 (offset := 32) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag19 : AgreesExcept [.mem (stackSlot s 32) 8, .rip] t18 t19 := by
    have h : AgreesExcept [.mem (stackPtr t18 + 32#64) 8, .rip] t18 t19 := by
      have h := effect19.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame18.rsp] at h
    exact h
  have rip19 : t19.RIP = 0x10616e := effect19.rip
  have write19 : memLoad t19.external (stackPtr t18 + 32#64) 64 = t18.regValue .rax := effect19.writes
  rw [frame18.rsp] at write19
  have sw19 : memLoad t19.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 := write19.trans r18_rax
  obtain ⟨t20, run20, frame20, effect20⟩ := step_registers pre frame19
    (offset := 0x616e) (mov_r64_imm64_effect_step 0x10616e 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xe5a220abf7212ed6)
    (by decide) (by decide +kernel)
    rip19
    (inProgram_of_textOffset 0x6178 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag20 : AgreesExcept [.reg 0, .rip] t19 t20 := effect20.agrees
  have ext20 : t20.external = t19.external := ag20.external (by simp [Component.Covers])
  have rip20 : t20.RIP = 0x106178 := effect20.rip
  have write20 : t20.regValue .rax = 0xe5a220abf7212ed6#64 := effect20.writes
  have r20_rax : t20.regValue .rax = 0xe5a220abf7212ed6#64 := write20
  obtain ⟨t21, run21, frame21, effect21⟩ := step pre frame20 (by decide)
    (offset := 0x6178) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106178 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip20, stack_writable (frameOffset := 728) pre frame20 (by decide) (offset := 24) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame20 (by decide) (offset := 24) (len := 8) (codeOffset := 0x6178) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x617d (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame20 (offset := 24) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag21 : AgreesExcept [.mem (stackSlot s 24) 8, .rip] t20 t21 := by
    have h : AgreesExcept [.mem (stackPtr t20 + 24#64) 8, .rip] t20 t21 := by
      have h := effect21.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame20.rsp] at h
    exact h
  have rip21 : t21.RIP = 0x10617d := effect21.rip
  have write21 : memLoad t21.external (stackPtr t20 + 24#64) 64 = t20.regValue .rax := effect21.writes
  rw [frame20.rsp] at write21
  have sw21 : memLoad t21.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 := write21.trans r20_rax
  obtain ⟨t22, run22, frame22, effect22⟩ := step_registers pre frame21
    (offset := 0x617d) (mov_r64_imm64_effect_step 0x10617d 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xacf005cd78843090)
    (by decide) (by decide +kernel)
    rip21
    (inProgram_of_textOffset 0x6187 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 0, .rip]; decide +kernel)
  have ag22 : AgreesExcept [.reg 0, .rip] t21 t22 := effect22.agrees
  have ext22 : t22.external = t21.external := ag22.external (by simp [Component.Covers])
  have rip22 : t22.RIP = 0x106187 := effect22.rip
  have write22 : t22.regValue .rax = 0xacf005cd78843090#64 := effect22.writes
  have r22_rax : t22.regValue .rax = 0xacf005cd78843090#64 := write22
  obtain ⟨t23, run23, frame23, effect23⟩ := step pre frame22 (by decide)
    (offset := 0x6187) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106187 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip22, stack_writable (frameOffset := 728) pre frame22 (by decide) (offset := 16) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame22 (by decide) (offset := 16) (len := 8) (codeOffset := 0x6187) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x618c (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame22 (offset := 16) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag23 : AgreesExcept [.mem (stackSlot s 16) 8, .rip] t22 t23 := by
    have h : AgreesExcept [.mem (stackPtr t22 + 16#64) 8, .rip] t22 t23 := by
      have h := effect23.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame22.rsp] at h
    exact h
  have rip23 : t23.RIP = 0x10618c := effect23.rip
  have write23 : memLoad t23.external (stackPtr t22 + 16#64) 64 = t22.regValue .rax := effect23.writes
  rw [frame22.rsp] at write23
  have sw23 : memLoad t23.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 := write23.trans r22_rax
  have r18_rbp : t18.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag18.read (n := 64) (r := 5) (by simp)).trans r17_rbp
  have r19_rbp : t19.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag19.read (n := 64) (r := 5) (by simp)).trans r18_rbp
  have r20_rbp : t20.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag20.read (n := 64) (r := 5) (by simp)).trans r19_rbp
  have r21_rbp : t21.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag21.read (n := 64) (r := 5) (by simp)).trans r20_rbp
  have r22_rbp : t22.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag22.read (n := 64) (r := 5) (by simp)).trans r21_rbp
  have r23_rbp : t23.regValue .rbp = 0xd89cdf6229c4bddf#64 :=
    (ag23.read (n := 64) (r := 5) (by simp)).trans r22_rbp
  obtain ⟨t24, run24, frame24, effect24⟩ := step pre frame23 (by decide)
    (offset := 0x618c) (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10618c 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    ⟨rip23, stack_writable (frameOffset := 728) pre frame23 (by decide) (offset := 8) (by decide) (by decide),
      stack_code (frameOffset := 728) pre frame23 (by decide) (offset := 8) (len := 8) (codeOffset := 0x618c) (codeLen := 5) (by decide) (by decide)⟩
    (inProgram_of_textOffset 0x6191 (by decide))
    (by rw [movM64R64Effect_components]; exact store_writes pre frame23 (offset := 8) (by decide))
    (by simp only [movM64R64Effect_components]; simp)
  have ag24 : AgreesExcept [.mem (stackSlot s 8) 8, .rip] t23 t24 := by
    have h : AgreesExcept [.mem (stackPtr t23 + 8#64) 8, .rip] t23 t24 := by
      have h := effect24.agrees
      rw [movM64R64Effect_components] at h
      exact h
    rw [frame23.rsp] at h
    exact h
  have rip24 : t24.RIP = 0x106191 := effect24.rip
  have write24 : memLoad t24.external (stackPtr t23 + 8#64) 64 = t23.regValue .rbp := effect24.writes
  rw [frame23.rsp] at write24
  have sw24 : memLoad t24.external (stackSlot s 8) 64 = 0xd89cdf6229c4bddf#64 := write24.trans r23_rbp
  obtain ⟨t25, run25, frame25, effect25⟩ := step_registers pre frame24
    (offset := 0x6191) (lea_r64_effect_step 0x106191 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip24
    (inProgram_of_textOffset 0x6199 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 14, .rip]; decide +kernel)
  have ag25 : AgreesExcept [.reg 14, .rip] t24 t25 := effect25.agrees
  have ext25 : t25.external = t24.external := ag25.external (by simp [Component.Covers])
  have rip25 : t25.RIP = 0x106199 := effect25.rip
  have write25 : t25.regValue .r14 = stackPtr t24 + 232#64 := effect25.writes
  rw [frame24.rsp] at write25
  have r25_r14 : t25.regValue .r14 = stackSlot s 232 := write25
  obtain ⟨t26, run26, frame26, effect26⟩ := step_registers pre frame25
    (offset := 0x6199) (lea_r64_effect_step 0x106199 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip25
    (inProgram_of_textOffset 0x619e (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 6, .rip]; decide +kernel)
  have ag26 : AgreesExcept [.reg 6, .rip] t25 t26 := effect26.agrees
  have ext26 : t26.external = t25.external := ag26.external (by simp [Component.Covers])
  have rip26 : t26.RIP = 0x10619e := effect26.rip
  have write26 : t26.regValue .rsi = stackPtr t25 + 8#64 := effect26.writes
  rw [frame25.rsp] at write26
  have r26_rsi : t26.regValue .rsi = stackSlot s 8 := write26
  have r26_r14 : t26.regValue .r14 = stackSlot s 232 :=
    (ag26.read (n := 64) (r := 14) (by simp)).trans r25_r14
  obtain ⟨t27, run27, frame27, effect27⟩ := step_registers pre frame26
    (offset := 0x619e) (mov_r64_r64_effect_step 0x10619e 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
    (by decide) (by decide +kernel)
    rip26
    (inProgram_of_textOffset 0x61a1 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 7, .rip]; decide +kernel)
  have ag27 : AgreesExcept [.reg 7, .rip] t26 t27 := effect27.agrees
  have ext27 : t27.external = t26.external := ag27.external (by simp [Component.Covers])
  have rip27 : t27.RIP = 0x1061a1 := effect27.rip
  have write27 : t27.regValue .rdi = t26.regValue .r14 := effect27.writes
  have r27_rdi : t27.regValue .rdi = stackSlot s 232 := write27.trans r26_r14
  obtain ⟨t28, run28, frame28, effect28⟩ := step_registers pre frame27
    (offset := 0x61a1) (lea_r64_effect_step 0x1061a1 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 200)) (by decide) rfl rfl)
    (by decide) (by decide +kernel)
    rip27
    (inProgram_of_textOffset 0x61a9 (by decide))
    (by simp [Component.Covers]) (by change Component.reg 4 ∉ [Component.reg 2, .rip]; decide +kernel)
  have ag28 : AgreesExcept [.reg 2, .rip] t27 t28 := effect28.agrees
  have ext28 : t28.external = t27.external := ag28.external (by simp [Component.Covers])
  have rip28 : t28.RIP = 0x1061a9 := effect28.rip
  have write28 : t28.regValue .rdx = stackPtr t27 + 200#64 := effect28.writes
  rw [frame27.rsp] at write28
  have r28_rdx : t28.regValue .rdx = stackSlot s 200 := write28
  have r28_rdi : t28.regValue .rdi = stackSlot s 232 :=
    (ag28.read (n := 64) (r := 7) (by simp)).trans r27_rdi
  have r27_rsi : t27.regValue .rsi = stackSlot s 8 :=
    (ag27.read (n := 64) (r := 6) (by simp)).trans r26_rsi
  have r28_rsi : t28.regValue .rsi = stackSlot s 8 :=
    (ag28.read (n := 64) (r := 6) (by simp)).trans r27_rsi
  have w25_8_17 : memLoad t25.external (stackSlot s 8) 64 = 0xd89cdf6229c4bddf#64 :=
    by simpa only [ext25] using sw24
  have w26_8_17 : memLoad t26.external (stackSlot s 8) 64 = 0xd89cdf6229c4bddf#64 :=
    by simpa only [ext26] using w25_8_17
  have w27_8_17 : memLoad t27.external (stackSlot s 8) 64 = 0xd89cdf6229c4bddf#64 :=
    by simpa only [ext27] using w26_8_17
  have w28_8_17 : memLoad t28.external (stackSlot s 8) 64 = 0xd89cdf6229c4bddf#64 :=
    by simpa only [ext28] using w27_8_17
  have w24_16_17 : memLoad t24.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans sw23
  have w25_16_17 : memLoad t25.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 :=
    by simpa only [ext25] using w24_16_17
  have w26_16_17 : memLoad t26.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 :=
    by simpa only [ext26] using w25_16_17
  have w27_16_17 : memLoad t27.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 :=
    by simpa only [ext27] using w26_16_17
  have w28_16_17 : memLoad t28.external (stackSlot s 16) 64 = 0xacf005cd78843090#64 :=
    by simpa only [ext28] using w27_16_17
  have w22_24_17 : memLoad t22.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    by simpa only [ext22] using sw21
  have w23_24_17 : memLoad t23.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    (store_read ag23 (by decide) (by decide) (by decide)).trans w22_24_17
  have w24_24_17 : memLoad t24.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans w23_24_17
  have w25_24_17 : memLoad t25.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    by simpa only [ext25] using w24_24_17
  have w26_24_17 : memLoad t26.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    by simpa only [ext26] using w25_24_17
  have w27_24_17 : memLoad t27.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    by simpa only [ext27] using w26_24_17
  have w28_24_17 : memLoad t28.external (stackSlot s 24) 64 = 0xe5a220abf7212ed6#64 :=
    by simpa only [ext28] using w27_24_17
  have w20_32_17 : memLoad t20.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext20] using sw19
  have w21_32_17 : memLoad t21.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    (store_read ag21 (by decide) (by decide) (by decide)).trans w20_32_17
  have w22_32_17 : memLoad t22.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext22] using w21_32_17
  have w23_32_17 : memLoad t23.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    (store_read ag23 (by decide) (by decide) (by decide)).trans w22_32_17
  have w24_32_17 : memLoad t24.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    (store_read ag24 (by decide) (by decide) (by decide)).trans w23_32_17
  have w25_32_17 : memLoad t25.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext25] using w24_32_17
  have w26_32_17 : memLoad t26.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext26] using w25_32_17
  have w27_32_17 : memLoad t27.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext27] using w26_32_17
  have w28_32_17 : memLoad t28.external (stackSlot s 32) 64 = 0xdc30061d04874834#64 :=
    by simpa only [ext28] using w27_32_17
  have constant28 : MontgomeryAt t28 (stackSlot s 8) P256.Spec.Operations.domain.b :=
    by
      apply montgomeryAt_coefficient_b
      · have allocated := stack_readable (frameOffset := 728) pre frame28 (by decide)
          (offset := 8) (len := 32) (by decide)
        rw [frame28.rsp] at allocated
        exact allocated.mem
      · exact w28_8_17
      · change memLoad t28.external (stackSlot s 8 + BitVec.ofNat 64 8) 64 = 0xacf005cd78843090#64
        rw [slot_add]
        exact w28_16_17
      · change memLoad t28.external (stackSlot s 8 + BitVec.ofNat 64 16) 64 = 0xe5a220abf7212ed6#64
        rw [slot_add]
        exact w28_24_17
      · change memLoad t28.external (stackSlot s 8 + BitVec.ofNat 64 24) 64 = 0xdc30061d04874834#64
        rw [slot_add]
        exact w28_32_17
  have m18_0_200 : MontgomeryAt t18 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_200
  have m19_0_200 : MontgomeryAt t19 (stackSlot s 200) ((values point).xz2) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_0_200
  have m20_0_200 : MontgomeryAt t20 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_200
  have m21_0_200 : MontgomeryAt t21 (stackSlot s 200) ((values point).xz2) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_0_200
  have m22_0_200 : MontgomeryAt t22 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_200
  have m23_0_200 : MontgomeryAt t23 (stackSlot s 200) ((values point).xz2) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_0_200
  have m24_0_200 : MontgomeryAt t24 (stackSlot s 200) ((values point).xz2) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_200
  have m25_0_200 : MontgomeryAt t25 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_200
  have m26_0_200 : MontgomeryAt t26 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_0_200
  have m27_0_200 : MontgomeryAt t27 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_200
  have m28_0_200 : MontgomeryAt t28 (stackSlot s 200) ((values point).xz2) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_200
  let v29 : Nat := ((P256.Spec.Operations.domain.b) * ((values point).xz2)) % P256.Spec.Operations.domain.p
  let site29 : BinaryCallSite 1016 728 0x113890 280 :=
    { codeOffset := 0x61a9, disp := 0xd6e2, codeBound := by decide,
      bytes := by decide +kernel, target := by decide +kernel, entryLow := by decide,
      entryProgram := inProgram_of_textOffset 0x13890 (by decide),
      layout := ⟨736, 720, 496, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, stack := rfl, outputSaved := by decide,
      rightOffset := 528, rightAbove := by decide, rightEnd := by decide,
      rightApart := by decide }
  obtain ⟨n29, t29, run29, frame29, rip29, value29, regs29, bytes29, work29⟩ :=
    binary_call pre frame28 (x := P256.Spec.Operations.domain.b) (y := (values point).xz2)
      (op := fun x y => x*y % P256.Spec.Operations.domain.p) site29
      (fun _ hp hx hy => field_mul_correct hp hx hy)
      rip28
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using r28_rsi)
      (by simpa only [stackSlot_eq s (show 200 ≤ 728 by decide)] using r28_rdx)
      (by simpa only [stackSlot_eq s (show 232 ≤ 728 by decide)] using r28_rdi)
      (by simpa only [stackSlot_eq s (show 8 ≤ 728 by decide)] using constant28)
      (by simpa only [stackSlot_eq s (show 200 ≤ 728 by decide)] using m28_0_200)
  have m29_232 : MontgomeryAt t29 (stackSlot s 232) v29 := by
    rw [stackSlot_eq s (show 232 ≤ 728 by decide)]
    exact value29
  have point18 : ProjectiveAt t18 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using point17
  have point19 : ProjectiveAt t19 (s.regValue .rdi) point :=
    store_point pre ag19 (by decide) point18
  have point20 : ProjectiveAt t20 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using point19
  have point21 : ProjectiveAt t21 (s.regValue .rdi) point :=
    store_point pre ag21 (by decide) point20
  have point22 : ProjectiveAt t22 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using point21
  have point23 : ProjectiveAt t23 (s.regValue .rdi) point :=
    store_point pre ag23 (by decide) point22
  have point24 : ProjectiveAt t24 (s.regValue .rdi) point :=
    store_point pre ag24 (by decide) point23
  have point25 : ProjectiveAt t25 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using point24
  have point26 : ProjectiveAt t26 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using point25
  have point27 : ProjectiveAt t27 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using point26
  have point28 : ProjectiveAt t28 (s.regValue .rdi) point :=
    by simpa only [ProjectiveAt, MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using point27
  have point29 : ProjectiveAt t29 (s.regValue .rdi) point :=
    point_of_stack pre (work_stack_frame pre work29) point28
  have r18_rbx : t18.regValue .rbx = s.regValue .rdi :=
    (ag18.read (n := 64) (r := 3) (by simp)).trans r17_rbx
  have r19_rbx : t19.regValue .rbx = s.regValue .rdi :=
    (ag19.read (n := 64) (r := 3) (by simp)).trans r18_rbx
  have r20_rbx : t20.regValue .rbx = s.regValue .rdi :=
    (ag20.read (n := 64) (r := 3) (by simp)).trans r19_rbx
  have r21_rbx : t21.regValue .rbx = s.regValue .rdi :=
    (ag21.read (n := 64) (r := 3) (by simp)).trans r20_rbx
  have r22_rbx : t22.regValue .rbx = s.regValue .rdi :=
    (ag22.read (n := 64) (r := 3) (by simp)).trans r21_rbx
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
    (regs29 .rbx (by decide)).trans r28_rbx
  have r18_r15 : t18.regValue .r15 = stackSlot s 616 :=
    (ag18.read (n := 64) (r := 15) (by simp)).trans r17_r15
  have r19_r15 : t19.regValue .r15 = stackSlot s 616 :=
    (ag19.read (n := 64) (r := 15) (by simp)).trans r18_r15
  have r20_r15 : t20.regValue .r15 = stackSlot s 616 :=
    (ag20.read (n := 64) (r := 15) (by simp)).trans r19_r15
  have r21_r15 : t21.regValue .r15 = stackSlot s 616 :=
    (ag21.read (n := 64) (r := 15) (by simp)).trans r20_r15
  have r22_r15 : t22.regValue .r15 = stackSlot s 616 :=
    (ag22.read (n := 64) (r := 15) (by simp)).trans r21_r15
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
    (regs29 .r15 (by decide)).trans r28_r15
  have r18_r12 : t18.regValue .r12 = stackSlot s 360 :=
    (ag18.read (n := 64) (r := 12) (by simp)).trans r17_r12
  have r19_r12 : t19.regValue .r12 = stackSlot s 360 :=
    (ag19.read (n := 64) (r := 12) (by simp)).trans r18_r12
  have r20_r12 : t20.regValue .r12 = stackSlot s 360 :=
    (ag20.read (n := 64) (r := 12) (by simp)).trans r19_r12
  have r21_r12 : t21.regValue .r12 = stackSlot s 360 :=
    (ag21.read (n := 64) (r := 12) (by simp)).trans r20_r12
  have r22_r12 : t22.regValue .r12 = stackSlot s 360 :=
    (ag22.read (n := 64) (r := 12) (by simp)).trans r21_r12
  have r23_r12 : t23.regValue .r12 = stackSlot s 360 :=
    (ag23.read (n := 64) (r := 12) (by simp)).trans r22_r12
  have r24_r12 : t24.regValue .r12 = stackSlot s 360 :=
    (ag24.read (n := 64) (r := 12) (by simp)).trans r23_r12
  have r25_r12 : t25.regValue .r12 = stackSlot s 360 :=
    (ag25.read (n := 64) (r := 12) (by simp)).trans r24_r12
  have r26_r12 : t26.regValue .r12 = stackSlot s 360 :=
    (ag26.read (n := 64) (r := 12) (by simp)).trans r25_r12
  have r27_r12 : t27.regValue .r12 = stackSlot s 360 :=
    (ag27.read (n := 64) (r := 12) (by simp)).trans r26_r12
  have r28_r12 : t28.regValue .r12 = stackSlot s 360 :=
    (ag28.read (n := 64) (r := 12) (by simp)).trans r27_r12
  have r29_r12 : t29.regValue .r12 = stackSlot s 360 :=
    (regs29 .r12 (by decide)).trans r28_r12
  have m18_0_104 : MontgomeryAt t18 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_104
  have m19_0_104 : MontgomeryAt t19 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_0_104
  have m20_0_104 : MontgomeryAt t20 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_104
  have m21_0_104 : MontgomeryAt t21 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_0_104
  have m22_0_104 : MontgomeryAt t22 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_104
  have m23_0_104 : MontgomeryAt t23 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_0_104
  have m24_0_104 : MontgomeryAt t24 (stackSlot s 104) ((values point).xx) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_104
  have m25_0_104 : MontgomeryAt t25 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_104
  have m26_0_104 : MontgomeryAt t26 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_0_104
  have m27_0_104 : MontgomeryAt t27 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_104
  have m28_0_104 : MontgomeryAt t28 (stackSlot s 104) ((values point).xx) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_104
  have m29_0_104 : MontgomeryAt t29 (stackSlot s 104) ((values point).xx) :=
    by
    refine ⟨m28_0_104.1, m28_0_104.2.1, fun j hj => ?_⟩
    have h := (bytes29 624 32 (by decide) (by decide) (by decide) j hj)
    have hx := m28_0_104.2.2 j hj
    rw [stackSlot_eq s (show 104 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m18_0_136 : MontgomeryAt t18 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_136
  have m19_0_136 : MontgomeryAt t19 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_0_136
  have m20_0_136 : MontgomeryAt t20 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_136
  have m21_0_136 : MontgomeryAt t21 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_0_136
  have m22_0_136 : MontgomeryAt t22 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_136
  have m23_0_136 : MontgomeryAt t23 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_0_136
  have m24_0_136 : MontgomeryAt t24 (stackSlot s 136) ((values point).yy) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_136
  have m25_0_136 : MontgomeryAt t25 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_136
  have m26_0_136 : MontgomeryAt t26 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_0_136
  have m27_0_136 : MontgomeryAt t27 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_136
  have m28_0_136 : MontgomeryAt t28 (stackSlot s 136) ((values point).yy) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_136
  have m29_0_136 : MontgomeryAt t29 (stackSlot s 136) ((values point).yy) :=
    by
    refine ⟨m28_0_136.1, m28_0_136.2.1, fun j hj => ?_⟩
    have h := (bytes29 592 32 (by decide) (by decide) (by decide) j hj)
    have hx := m28_0_136.2.2 j hj
    rw [stackSlot_eq s (show 136 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m18_0_520 : MontgomeryAt t18 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_520
  have m19_0_520 : MontgomeryAt t19 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_0_520
  have m20_0_520 : MontgomeryAt t20 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_520
  have m21_0_520 : MontgomeryAt t21 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_0_520
  have m22_0_520 : MontgomeryAt t22 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_520
  have m23_0_520 : MontgomeryAt t23 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_0_520
  have m24_0_520 : MontgomeryAt t24 (stackSlot s 520) ((values point).xProduct) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_520
  have m25_0_520 : MontgomeryAt t25 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_520
  have m26_0_520 : MontgomeryAt t26 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_0_520
  have m27_0_520 : MontgomeryAt t27 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_520
  have m28_0_520 : MontgomeryAt t28 (stackSlot s 520) ((values point).xProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_520
  have m29_0_520 : MontgomeryAt t29 (stackSlot s 520) ((values point).xProduct) :=
    by
    refine ⟨m28_0_520.1, m28_0_520.2.1, fun j hj => ?_⟩
    have h := (bytes29 208 32 (by decide) (by decide) (by decide) j hj)
    have hx := m28_0_520.2.2 j hj
    rw [stackSlot_eq s (show 520 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m18_0_616 : MontgomeryAt t18 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_0_616
  have m19_0_616 : MontgomeryAt t19 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_0_616
  have m20_0_616 : MontgomeryAt t20 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_0_616
  have m21_0_616 : MontgomeryAt t21 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_0_616
  have m22_0_616 : MontgomeryAt t22 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_0_616
  have m23_0_616 : MontgomeryAt t23 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_0_616
  have m24_0_616 : MontgomeryAt t24 (stackSlot s 616) ((values point).yProduct) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_0_616
  have m25_0_616 : MontgomeryAt t25 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_0_616
  have m26_0_616 : MontgomeryAt t26 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_0_616
  have m27_0_616 : MontgomeryAt t27 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_0_616
  have m28_0_616 : MontgomeryAt t28 (stackSlot s 616) ((values point).yProduct) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_0_616
  have m29_0_616 : MontgomeryAt t29 (stackSlot s 616) ((values point).yProduct) :=
    by
    refine ⟨m28_0_616.1, m28_0_616.2.1, fun j hj => ?_⟩
    have h := (bytes29 112 32 (by decide) (by decide) (by decide) j hj)
    have hx := m28_0_616.2.2 j hj
    rw [stackSlot_eq s (show 616 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have m18_17_360 : MontgomeryAt t18 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext18] using m17_360
  have m19_17_360 : MontgomeryAt t19 (stackSlot s 360) (v17) :=
    store_montgomery ag19 (by decide) (by decide) (by decide) m18_17_360
  have m20_17_360 : MontgomeryAt t20 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext20] using m19_17_360
  have m21_17_360 : MontgomeryAt t21 (stackSlot s 360) (v17) :=
    store_montgomery ag21 (by decide) (by decide) (by decide) m20_17_360
  have m22_17_360 : MontgomeryAt t22 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext22] using m21_17_360
  have m23_17_360 : MontgomeryAt t23 (stackSlot s 360) (v17) :=
    store_montgomery ag23 (by decide) (by decide) (by decide) m22_17_360
  have m24_17_360 : MontgomeryAt t24 (stackSlot s 360) (v17) :=
    store_montgomery ag24 (by decide) (by decide) (by decide) m23_17_360
  have m25_17_360 : MontgomeryAt t25 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext25] using m24_17_360
  have m26_17_360 : MontgomeryAt t26 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext26] using m25_17_360
  have m27_17_360 : MontgomeryAt t27 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext27] using m26_17_360
  have m28_17_360 : MontgomeryAt t28 (stackSlot s 360) (v17) :=
    by simpa only [MontgomeryAt, SecretKeyFromBytes.Scalar.Nat256At, ext28] using m27_17_360
  have m29_17_360 : MontgomeryAt t29 (stackSlot s 360) (v17) :=
    by
    refine ⟨m28_17_360.1, m28_17_360.2.1, fun j hj => ?_⟩
    have h := (bytes29 368 32 (by decide) (by decide) (by decide) j hj)
    have hx := m28_17_360.2.2 j hj
    rw [stackSlot_eq s (show 360 ≤ 728 by decide)] at hx ⊢
    exact h.trans hx
  have r27_r14 : t27.regValue .r14 = stackSlot s 232 :=
    (ag27.read (n := 64) (r := 14) (by simp)).trans r26_r14
  have r28_r14 : t28.regValue .r14 = stackSlot s 232 :=
    (ag28.read (n := 64) (r := 14) (by simp)).trans r27_r14
  have r29_r14 : t29.regValue .r14 = stackSlot s 232 :=
    (regs29 .r14 (by decide)).trans r28_r14
  refine ⟨_, t29, (((((((((((run18.trans run19).trans run20).trans run21).trans run22).trans run23).trans run24).trans run25).trans run26).trans run27).trans run28).trans run29), frame29, rip29, ?_⟩
  exact ⟨⟨point29, r29_rbx, r29_r15, m29_0_104, m29_0_136, m29_0_520,
    m29_0_616, r29_r12, m29_17_360⟩, r29_r14, m29_232⟩

end P256.Proofs.Projective.Double
