import P256.Proofs.Sec1Serialize.Conversion.X.Initial
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Montgomery

set_option autoImplicit false
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step)

namespace P256.Proofs.Sec1Serialize.Conversion
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem x_round2 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110e03) (r14 : t.regValue .r14 = s.regValue .rsi)
    (k13 : t.regValue .r13 = 0xffffffff00000001)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x110e59 ∧
      (u.regValue .r9, u.regValue .r12, u.regValue .r8, u.regValue .r10) =
        Montgomery.compilerRoundBV (t.regValue .r8) (t.regValue .r10) (t.regValue .rsi) (t.regValue .r11)
          ((Operand.mem (s.regValue .rsi + 16) : Operand 64).read t) ∧
      u.regValue .r13 = 0xffffffff00000001 ∧
      u.regValue .rbx = 0xffffffffffffffff ∧
      u.regValue .r15 = 0xffffffff ∧
      AgreesExcept xRegisters t u := by
  let a := t.regValue .r8
  let b := t.regValue .r10
  let c := t.regValue .rsi
  let d := t.regValue .r11
  let z := (Operand.mem (s.regValue .rsi + 16) : Operand 64).read t
  let q := addSpec a z
  let e := (BitVec.ofBool q.2.CF).setWidth 64
  let neg := addSpec (q.1 * 0xffffffffffffffff) q.1
  let ec := adcSpec e (mulHigh64 q.1 0xffffffffffffffff) (BitVec.ofBool neg.2.CF)
  let l := addSpec (q.1 * 0xffffffff) b
  let h := adcSpec (mulHigh64 q.1 0xffffffff) 0 (BitVec.ofBool l.2.CF)
  let k := addSpec (q.1 * 0xffffffff00000001) d
  let j := adcSpec (mulHigh64 q.1 0xffffffff00000001) 0 (BitVec.ofBool k.2.CF)
  let o0 := addSpec l.1 ec.1
  let o1 := adcSpec h.1 c (BitVec.ofBool o0.2.CF)
  let o2 := adcSpec k.1 0 (BitVec.ofBool o1.2.CF)
  let o3 := adcSpec j.1 0 (BitVec.ofBool o2.2.CF)
  have code1 : CodeIn (codeRange 0x110e03 [0x31,0xc9]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10e03 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := xor_r32_r32_effect_step 0x110e03 0xc9 (by decide)
    t stage.ready code1 rip
  change (xorR32R32Effect 0x110e03 2 1 1 t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [xorR32R32Effect_components]) (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x10e05 (by decide))
  have r1_1 : t1.regValue .rcx = 0 := by
    have he : t1.regValue .rcx = (((Operand.reg 1 : Operand 32).read t) ^^^ ((Operand.reg 1 : Operand 32).read t)).setWidth 64 := effect1.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he.trans (by rfl)
  have r8_1 : t1.regValue .r8 = a := (effect1.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans (rfl)
  have r14_1 : t1.regValue .r14 = s.regValue .rsi := (effect1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (r14)
  have addr2 : (AddrMode.base 14 (.d8 16)).addr t1 0x110e09 = s.regValue .rsi + 16 := by
    change t1.regValue .r14 + 16 = _
    rw [r14_1]
  have read2 : MemReadable t1 ((AddrMode.base 14 (.d8 16)).addr t1 0x110e09) 8 := by
    rw [addr2]
    exact input_readable pre stage1.allocated (offset := 16) (by decide)
  have mem2 : t1.external = t.external := (effect1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers]))
  have code2 : CodeIn (codeRange 0x110e05 [0x4d,0x3,0x46,0x10]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10e05 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := add_r64_m64_effect_step 0x110e05 0x4d (by simp [RexWPrefix]) 0 (.base 14 (.d8 16)) (by decide) rfl rfl
    t1 ready1 code2 ⟨effect1.rip, read2⟩
  change (addR64M64Effect 0x110e05 8 (.base 14 (.d8 16)) t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [addR64M64Effect_components]) (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x10e09 (by decide))
  have r8_2 : t2.regValue .r8 = q.1 := by
    have he : t2.regValue .r8 = (addSpec (t1.regValue .r8) ((Operand.mem ((AddrMode.base 14 (.d8 16)).addr t1 0x110e09) : Operand 64).read t1)).1 := effect2.writes
    rw [r8_1, addr2] at he
    change t2.regValue .r8 = (addSpec a (memLoad t1.external (s.regValue .rsi + 16) 64)).1 at he
    rw [mem2] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec (t1.regValue .r8) ((Operand.mem ((AddrMode.base 14 (.d8 16)).addr t1 0x110e09) : Operand 64).read t1)).2.CF := effect2.flags.1
    rw [r8_1, addr2] at he
    change (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec a (memLoad t1.external (s.regValue .rsi + 16) 64)).2.CF at he
    rw [mem2] at he
    exact he
  have r1_2 : t2.regValue .rcx = 0 := (effect2.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans (r1_1)
  have code3 : CodeIn (codeRange 0x110e09 [0xf,0x92,0xc1]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10e09 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := setcc_r8_effect_step 0x110e09 0x92 0xc1 (.inl rfl) (by decide) (by decide)
    t2 ready2 code3 effect2.rip
  change (setccR8Effect 0x110e09 3 1 2 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [setccR8Effect_components]) (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x10e0c (by decide))
  have r1_3 : t3.regValue .rcx = e := by
    have he : t3.regValue .rcx = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) (t2.regValue .rcx) := effect3.writes
    rw [cf2, r1_2, setb_zero] at he
    exact he
  have r8_3 : t3.regValue .r8 = q.1 := (effect3.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans (r8_2)
  have code4 : CodeIn (codeRange 0x110e0c [0x4c,0x89,0xc0]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10e0c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x110e0c 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x110e0c 0 8 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e0f (by decide))
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .r8 := effect4.writes
    rw [r8_3] at he
    exact he
  have code5 : CodeIn (codeRange 0x110e0f [0x48,0xc7,0xc3,0xff,0xff,0xff,0xff]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10e0f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mov_r64_imm32_effect_step 0x110e0f 0x48 0xc3 (by simp [RexWPrefix]) (by decide) (by decide) 0xffffffff
    t4 ready4 code5 effect4.rip
  change (movR64Imm32Effect 0x110e0f 3 0xffffffff t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [movR64Imm32Effect_components]) (by simp [movR64Imm32Effect_components]) (inProgram_of_textOffset 0x10e16 (by decide))
  have r3_5 : t5.regValue .rbx = 0xffffffffffffffff := by
    have he : t5.regValue .rbx = (0xffffffff : BitVec 32).signExtend 64 := effect5.writes
    exact he.trans (by decide +kernel)
  have r0_5 : t5.regValue .rax = q.1 := (effect5.agrees.read (n := 64) (r := 0) (by simp [movR64Imm32Effect_components])).trans (r0_4)
  have code6 : CodeIn (codeRange 0x110e16 [0x48,0xf7,0xe3]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10e16 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := mul_r64_effect_step 0x110e16 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)
    t5 ready5 code6 effect5.rip
  change (mulR64Effect 0x110e16 3 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e19 (by decide))
  have r0_6 : t6.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t6.regValue .rax = t5.regValue .rax * t5.regValue .rbx := effect6.writes.1
    rw [r0_5, r3_5] at he
    exact he
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t6.regValue .rdx = mulHigh64 (t5.regValue .rax) (t5.regValue .rbx) := effect6.writes.2
    rw [r0_5, r3_5] at he
    exact he
  have r8_6 : t6.regValue .r8 = q.1 := (effect6.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 8) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_3)))
  have code7 : CodeIn (codeRange 0x110e19 [0x4c,0x1,0xc0]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10e19 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := add_r64_r64_effect_step 0x110e19 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (addR64R64Effect 0x110e19 0 8 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e1c (by decide))
  have r0_7 : t7.regValue .rax = neg.1 := by
    have he : t7.regValue .rax = (addSpec (t6.regValue .rax) (t6.regValue .r8)).1 := effect7.writes
    rw [r0_6, r8_6] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (addSpec (t6.regValue .rax) (t6.regValue .r8)).2.CF := effect7.flags.1
    rw [r0_6, r8_6] at he
    exact he
  have r1_7 : t7.regValue .rcx = e := (effect7.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_3))))
  have r2_7 : t7.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect7.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_6)
  have cb8 := carry_extract cf7
  have code8 : CodeIn (codeRange 0x110e1c [0x48,0x11,0xd1]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10e1c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := adc_r64_r64_effect_step 0x110e1c 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (adcR64R64Effect 0x110e1c 1 2 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10e1f (by decide))
  have r1_8 : t8.regValue .rcx = ec.1 := by
    have he : t8.regValue .rcx = (adcSpec (t7.regValue .rcx) (t7.regValue .rdx) (t7.RFLAGS.extractLsb' 0 1)).1 := effect8.writes
    rw [cb8, r1_7, r2_7] at he
    exact he
  have cf8 : (StatusFlags.ofRFLAGS t8.RFLAGS).CF = ec.2.CF := by
    have he : (StatusFlags.ofRFLAGS t8.RFLAGS).CF = (adcSpec (t7.regValue .rcx) (t7.regValue .rdx) (t7.RFLAGS.extractLsb' 0 1)).2.CF := effect8.flags.1
    rw [cb8, r1_7, r2_7] at he
    exact he
  have r8_8 : t8.regValue .r8 = q.1 := (effect8.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans (r8_6))
  have code9 : CodeIn (codeRange 0x110e1f [0x4c,0x89,0xc0]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x10e1f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mov_r64_r64_effect_step 0x110e1f 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t8 ready8 code9 effect8.rip
  change (movR64R64Effect 0x110e1f 0 8 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e22 (by decide))
  have r0_9 : t9.regValue .rax = q.1 := by
    have he : t9.regValue .rax = t8.regValue .r8 := effect9.writes
    rw [r8_8] at he
    exact he
  have code10 : CodeIn (codeRange 0x110e22 [0x41,0xbf,0xff,0xff,0xff,0xff]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x10e22 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mov_r32_imm32_rex_effect_step 0x110e22 0x41 0xbf (by simp [RexNoWPrefix]) (by decide) 0xffffffff
    t9 ready9 code10 effect9.rip
  change (movR32Imm32Effect 0x110e22 6 15 0xffffffff t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [movR32Imm32Effect_components]) (by simp [movR32Imm32Effect_components]) (inProgram_of_textOffset 0x10e28 (by decide))
  have r15_10 : t10.regValue .r15 = 0xffffffff := by
    have he : t10.regValue .r15 = (0xffffffff : BitVec 32).setWidth 64 := effect10.writes
    exact he.trans (by decide +kernel)
  have r0_10 : t10.regValue .rax = q.1 := (effect10.agrees.read (n := 64) (r := 0) (by simp [movR32Imm32Effect_components])).trans (r0_9)
  have code11 : CodeIn (codeRange 0x110e28 [0x49,0xf7,0xe7]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x10e28 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mul_r64_effect_step 0x110e28 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide)
    t10 ready10 code11 effect10.rip
  change (mulR64Effect 0x110e28 15 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e2b (by decide))
  have r0_11 : t11.regValue .rax = q.1 * 0xffffffff := by
    have he : t11.regValue .rax = t10.regValue .rax * t10.regValue .r15 := effect11.writes.1
    rw [r0_10, r15_10] at he
    exact he
  have r2_11 : t11.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t11.regValue .rdx = mulHigh64 (t10.regValue .rax) (t10.regValue .r15) := effect11.writes.2
    rw [r0_10, r15_10] at he
    exact he
  have code12 : CodeIn (codeRange 0x110e2b [0x49,0x89,0xd4]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x10e2b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := mov_r64_r64_effect_step 0x110e2b 0x49 0xd4 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (movR64R64Effect 0x110e2b 12 2 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e2e (by decide))
  have r12_12 : t12.regValue .r12 = mulHigh64 q.1 0xffffffff := by
    have he : t12.regValue .r12 = t11.regValue .rdx := effect12.writes
    rw [r2_11] at he
    exact he
  have r0_12 : t12.regValue .rax = q.1 * 0xffffffff := (effect12.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_11)
  have code13 : CodeIn (codeRange 0x110e2e [0x49,0x89,0xc1]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x10e2e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := mov_r64_r64_effect_step 0x110e2e 0x49 0xc1 (by simp [RexWPrefix]) (by decide)
    t12 ready12 code13 effect12.rip
  change (movR64R64Effect 0x110e2e 9 0 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e31 (by decide))
  have r9_13 : t13.regValue .r9 = q.1 * 0xffffffff := by
    have he : t13.regValue .r9 = t12.regValue .rax := effect13.writes
    rw [r0_12] at he
    exact he
  have r10_13 : t13.regValue .r10 = b := (effect13.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 10) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 10) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))))
  have code14 : CodeIn (codeRange 0x110e31 [0x4d,0x1,0xd1]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x10e31 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := add_r64_r64_effect_step 0x110e31 0x4d 0xd1 (by simp [RexWPrefix]) (by decide)
    t13 ready13 code14 effect13.rip
  change (addR64R64Effect 0x110e31 9 10 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e34 (by decide))
  have r9_14 : t14.regValue .r9 = l.1 := by
    have he : t14.regValue .r9 = (addSpec (t13.regValue .r9) (t13.regValue .r10)).1 := effect14.writes
    rw [r9_13, r10_13] at he
    exact he
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (addSpec (t13.regValue .r9) (t13.regValue .r10)).2.CF := effect14.flags.1
    rw [r9_13, r10_13] at he
    exact he
  have r12_14 : t14.regValue .r12 = mulHigh64 q.1 0xffffffff := (effect14.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans (r12_12))
  have cb15 := carry_extract cf14
  have code15 : CodeIn (codeRange 0x110e34 [0x49,0x83,0xd4,0x0]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x10e34 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := adc_r64_imm8_effect_step 0x110e34 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t14 ready14 code15 effect14.rip
  change (adcR64Imm8Effect 0x110e34 12 0 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e38 (by decide))
  have r12_15 : t15.regValue .r12 = h.1 := by
    have he : t15.regValue .r12 = (adcSpec (t14.regValue .r12) 0 (t14.RFLAGS.extractLsb' 0 1)).1 := effect15.writes
    rw [cb15, r12_14] at he
    exact he
  have cf15 : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = h.2.CF := by
    have he : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = (adcSpec (t14.regValue .r12) 0 (t14.RFLAGS.extractLsb' 0 1)).2.CF := effect15.flags.1
    rw [cb15, r12_14] at he
    exact he
  have r8_15 : t15.regValue .r8 = q.1 := (effect15.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 8) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_8)))))))
  have code16 : CodeIn (codeRange 0x110e38 [0x4c,0x89,0xc0]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x10e38 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mov_r64_r64_effect_step 0x110e38 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t15 ready15 code16 effect15.rip
  change (movR64R64Effect 0x110e38 0 8 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e3b (by decide))
  have r0_16 : t16.regValue .rax = q.1 := by
    have he : t16.regValue .rax = t15.regValue .r8 := effect16.writes
    rw [r8_15] at he
    exact he
  have r13_16 : t16.regValue .r13 = 0xffffffff00000001 := (effect16.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 13) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 13) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 13) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 13) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 13) (by simp [xorR32R32Effect_components])).trans (k13))))))))))))))))
  have code17 : CodeIn (codeRange 0x110e3b [0x49,0xf7,0xe5]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x10e3b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mul_r64_effect_step 0x110e3b 0x49 0xe5 (by simp [RexWPrefix]) (by decide) (by decide)
    t16 ready16 code17 effect16.rip
  change (mulR64Effect 0x110e3b 13 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e3e (by decide))
  have r0_17 : t17.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t17.regValue .rax = t16.regValue .rax * t16.regValue .r13 := effect17.writes.1
    rw [r0_16, r13_16] at he
    exact he
  have r2_17 : t17.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t17.regValue .rdx = mulHigh64 (t16.regValue .rax) (t16.regValue .r13) := effect17.writes.2
    rw [r0_16, r13_16] at he
    exact he
  have code18 : CodeIn (codeRange 0x110e3e [0x49,0x89,0xd2]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x10e3e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := mov_r64_r64_effect_step 0x110e3e 0x49 0xd2 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (movR64R64Effect 0x110e3e 10 2 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e41 (by decide))
  have r10_18 : t18.regValue .r10 = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t18.regValue .r10 = t17.regValue .rdx := effect18.writes
    rw [r2_17] at he
    exact he
  have r0_18 : t18.regValue .rax = q.1 * 0xffffffff00000001 := (effect18.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_17)
  have code19 : CodeIn (codeRange 0x110e41 [0x49,0x89,0xc0]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x10e41 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := mov_r64_r64_effect_step 0x110e41 0x49 0xc0 (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (movR64R64Effect 0x110e41 8 0 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e44 (by decide))
  have r8_19 : t19.regValue .r8 = q.1 * 0xffffffff00000001 := by
    have he : t19.regValue .r8 = t18.regValue .rax := effect19.writes
    rw [r0_18] at he
    exact he
  have r11_19 : t19.regValue .r11 = d := (effect19.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 11) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 11) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 11) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))))))))))
  have code20 : CodeIn (codeRange 0x110e44 [0x4d,0x1,0xd8]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x10e44 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := add_r64_r64_effect_step 0x110e44 0x4d 0xd8 (by simp [RexWPrefix]) (by decide)
    t19 ready19 code20 effect19.rip
  change (addR64R64Effect 0x110e44 8 11 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e47 (by decide))
  have r8_20 : t20.regValue .r8 = k.1 := by
    have he : t20.regValue .r8 = (addSpec (t19.regValue .r8) (t19.regValue .r11)).1 := effect20.writes
    rw [r8_19, r11_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (addSpec (t19.regValue .r8) (t19.regValue .r11)).2.CF := effect20.flags.1
    rw [r8_19, r11_19] at he
    exact he
  have r10_20 : t20.regValue .r10 = mulHigh64 q.1 0xffffffff00000001 := (effect20.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_18))
  have cb21 := carry_extract cf20
  have code21 : CodeIn (codeRange 0x110e47 [0x49,0x83,0xd2,0x0]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x10e47 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := adc_r64_imm8_effect_step 0x110e47 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t20 ready20 code21 effect20.rip
  change (adcR64Imm8Effect 0x110e47 10 0 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e4b (by decide))
  have r10_21 : t21.regValue .r10 = j.1 := by
    have he : t21.regValue .r10 = (adcSpec (t20.regValue .r10) 0 (t20.RFLAGS.extractLsb' 0 1)).1 := effect21.writes
    rw [cb21, r10_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = j.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (adcSpec (t20.regValue .r10) 0 (t20.RFLAGS.extractLsb' 0 1)).2.CF := effect21.flags.1
    rw [cb21, r10_20] at he
    exact he
  have r9_21 : t21.regValue .r9 = l.1 := (effect21.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans (r9_14)))))))
  have r1_21 : t21.regValue .rcx = ec.1 := (effect21.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_8)))))))))))))
  have code22 : CodeIn (codeRange 0x110e4b [0x49,0x1,0xc9]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x10e4b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := add_r64_r64_effect_step 0x110e4b 0x49 0xc9 (by simp [RexWPrefix]) (by decide)
    t21 ready21 code22 effect21.rip
  change (addR64R64Effect 0x110e4b 9 1 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e4e (by decide))
  have r9_22 : t22.regValue .r9 = o0.1 := by
    have he : t22.regValue .r9 = (addSpec (t21.regValue .r9) (t21.regValue .rcx)).1 := effect22.writes
    rw [r9_21, r1_21] at he
    exact he
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (addSpec (t21.regValue .r9) (t21.regValue .rcx)).2.CF := effect22.flags.1
    rw [r9_21, r1_21] at he
    exact he
  have r12_22 : t22.regValue .r12 = h.1 := (effect22.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans (r12_15)))))))
  have r6_22 : t22.regValue .rsi = c := (effect22.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 6) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 6) (by simp [movR64Imm32Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 6) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 6) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components])).trans (rfl))))))))))))))))))))))
  have cb23 := carry_extract cf22
  have code23 : CodeIn (codeRange 0x110e4e [0x49,0x11,0xf4]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x10e4e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_r64_effect_step 0x110e4e 0x49 0xf4 (by simp [RexWPrefix]) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64R64Effect 0x110e4e 12 6 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10e51 (by decide))
  have r12_23 : t23.regValue .r12 = o1.1 := by
    have he : t23.regValue .r12 = (adcSpec (t22.regValue .r12) (t22.regValue .rsi) (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [cb23, r12_22, r6_22] at he
    exact he
  have cf23 : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = (adcSpec (t22.regValue .r12) (t22.regValue .rsi) (t22.RFLAGS.extractLsb' 0 1)).2.CF := effect23.flags.1
    rw [cb23, r12_22, r6_22] at he
    exact he
  have r8_23 : t23.regValue .r8 = k.1 := (effect23.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_20)))
  have cb24 := carry_extract cf23
  have code24 : CodeIn (codeRange 0x110e51 [0x49,0x83,0xd0,0x0]) t23 :=
    programText_slice (programLoaded_codeIn stage23.loaded) 0x10e51 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t24, step24, ready24, effect24⟩ := adc_r64_imm8_effect_step 0x110e51 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t23 ready23 code24 effect23.rip
  change (adcR64Imm8Effect 0x110e51 8 0 t23).Holds t23 t24 at effect24
  have stage24 := stage23.step_registers pre step24 ready24 effect24
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e55 (by decide))
  have r8_24 : t24.regValue .r8 = o2.1 := by
    have he : t24.regValue .r8 = (adcSpec (t23.regValue .r8) 0 (t23.RFLAGS.extractLsb' 0 1)).1 := effect24.writes
    rw [cb24, r8_23] at he
    exact he
  have cf24 : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = (adcSpec (t23.regValue .r8) 0 (t23.RFLAGS.extractLsb' 0 1)).2.CF := effect24.flags.1
    rw [cb24, r8_23] at he
    exact he
  have r10_24 : t24.regValue .r10 = j.1 := (effect24.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans (r10_21)))
  have cb25 := carry_extract cf24
  have code25 : CodeIn (codeRange 0x110e55 [0x49,0x83,0xd2,0x0]) t24 :=
    programText_slice (programLoaded_codeIn stage24.loaded) 0x10e55 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t25, step25, ready25, effect25⟩ := adc_r64_imm8_effect_step 0x110e55 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t24 ready24 code25 effect24.rip
  change (adcR64Imm8Effect 0x110e55 10 0 t24).Holds t24 t25 at effect25
  have stage25 := stage24.step_registers pre step25 ready25 effect25
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e59 (by decide))
  have r10_25 : t25.regValue .r10 = o3.1 := by
    have he : t25.regValue .r10 = (adcSpec (t24.regValue .r10) 0 (t24.RFLAGS.extractLsb' 0 1)).1 := effect25.writes
    rw [cb25, r10_24] at he
    exact he
  have cf25 : (StatusFlags.ofRFLAGS t25.RFLAGS).CF = o3.2.CF := by
    have he : (StatusFlags.ofRFLAGS t25.RFLAGS).CF = (adcSpec (t24.regValue .r10) 0 (t24.RFLAGS.extractLsb' 0 1)).2.CF := effect25.flags.1
    rw [cb25, r10_24] at he
    exact he
  have r9_25 : t25.regValue .r9 = o0.1 := (effect25.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans (r9_22)))
  have r12_25 : t25.regValue .r12 = o1.1 := (effect25.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans (r12_23))
  have r8_25 : t25.regValue .r8 = o2.1 := (effect25.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_24)
  have r13_25 : t25.regValue .r13 = 0xffffffff00000001 := (effect25.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans (r13_16)))))))))
  have r3_25 : t25.regValue .rbx = 0xffffffffffffffff := (effect25.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 3) (by simp [movR32Imm32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans (r3_5))))))))))))))))))))
  have r15_25 : t25.regValue .r15 = 0xffffffff := (effect25.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans (r15_10)))))))))))))))
  have agree {a b c : RamState} (ha : AgreesExcept xRegisters a b) (hb : AgreesExcept xRegisters b c) : AgreesExcept xRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag1 : AgreesExcept xRegisters t t1 := effect1.agrees.mono (by simp [xorR32R32Effect_components, xRegisters])
  have ag2 : AgreesExcept xRegisters t1 t2 := effect2.agrees.mono (by simp [addR64M64Effect_components, xRegisters])
  have ag3 : AgreesExcept xRegisters t2 t3 := effect3.agrees.mono (by simp [setccR8Effect_components, xRegisters])
  have ag4 : AgreesExcept xRegisters t3 t4 := effect4.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag5 : AgreesExcept xRegisters t4 t5 := effect5.agrees.mono (by simp [movR64Imm32Effect_components, xRegisters])
  have ag6 : AgreesExcept xRegisters t5 t6 := effect6.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag7 : AgreesExcept xRegisters t6 t7 := effect7.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag8 : AgreesExcept xRegisters t7 t8 := effect8.agrees.mono (by simp [adcR64R64Effect_components, xRegisters])
  have ag9 : AgreesExcept xRegisters t8 t9 := effect9.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag10 : AgreesExcept xRegisters t9 t10 := effect10.agrees.mono (by simp [movR32Imm32Effect_components, xRegisters])
  have ag11 : AgreesExcept xRegisters t10 t11 := effect11.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag12 : AgreesExcept xRegisters t11 t12 := effect12.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag13 : AgreesExcept xRegisters t12 t13 := effect13.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag14 : AgreesExcept xRegisters t13 t14 := effect14.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag15 : AgreesExcept xRegisters t14 t15 := effect15.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag16 : AgreesExcept xRegisters t15 t16 := effect16.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag17 : AgreesExcept xRegisters t16 t17 := effect17.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag18 : AgreesExcept xRegisters t17 t18 := effect18.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag19 : AgreesExcept xRegisters t18 t19 := effect19.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag20 : AgreesExcept xRegisters t19 t20 := effect20.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag21 : AgreesExcept xRegisters t20 t21 := effect21.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag22 : AgreesExcept xRegisters t21 t22 := effect22.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag23 : AgreesExcept xRegisters t22 t23 := effect23.agrees.mono (by simp [adcR64R64Effect_components, xRegisters])
  have ag24 : AgreesExcept xRegisters t23 t24 := effect24.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag25 : AgreesExcept xRegisters t24 t25 := effect25.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  refine ⟨t25, stage25, effect25.rip, ?_, r13_25, r3_25, r15_25, (agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 (agree ag8 (agree ag9 (agree ag10 (agree ag11 (agree ag12 (agree ag13 (agree ag14 (agree ag15 (agree ag16 (agree ag17 (agree ag18 (agree ag19 (agree ag20 (agree ag21 (agree ag22 (agree ag23 (agree ag24 ag25))))))))))))))))))))))))⟩
  change (t25.regValue .r9, t25.regValue .r12, t25.regValue .r8, t25.regValue .r10) = (o0.1, o1.1, o2.1, o3.1)
  rw [r9_25, r12_25, r8_25, r10_25]

end P256.Proofs.Sec1Serialize.Conversion
