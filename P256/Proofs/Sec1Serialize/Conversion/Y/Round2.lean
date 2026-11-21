import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Montgomery
import P256.Proofs.Sec1Serialize.Conversion.Stage

set_option autoImplicit false
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step)


namespace P256.Proofs.Sec1Serialize.Conversion
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open Program Program.ScalarFrame
open P256.Proofs.Common.Encoding.Serialize
open X86 X86.Machine X86.UserProcess X86Proofs

theorem y_round_two [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110f21) (r14 : t.regValue .r14 = s.regValue .rsi)
    (a b c d z : BitVec 64)
    (ha : t.regValue .r8 = a) (hb : t.regValue .r10 = b)
    (hc : t.regValue .rsi = c) (hd : t.regValue .r11 = d) (hz : t.regValue .rcx = 0)
    (load : (Operand.mem (s.regValue .rsi + 48) : Operand 64).read t = z) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110f80 ∧
      (let result := Montgomery.compilerRoundBV a b c d z
       u.regValue .r9 = result.1 ∧ u.regValue .rbp = result.2.1 ∧
       u.regValue .r8 = result.2.2.1 ∧ u.regValue .r10 = result.2.2.2) ∧
      u.regValue .rcx = 0 ∧ AgreesExcept
        [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t u := by
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
  have addr1 : (AddrMode.base 14 (.d8 48)).addr t 0x110f25 = s.regValue .rsi + 48 := by
    change t.regValue .r14 + 48 = _
    rw [r14]
  have read1 : MemReadable t ((AddrMode.base 14 (.d8 48)).addr t 0x110f25) 8 := by
    rw [addr1]
    exact input_readable pre stage.allocated (offset := 48) (by decide)
  have code1 : CodeIn (codeRange 0x110f21 [0x4d,0x3,0x46,0x30]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10f21 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := add_r64_m64_effect_step 0x110f21 0x4d (by simp [RexWPrefix]) 0 (.base 14 (.d8 48)) (by decide) rfl rfl
    t stage.ready code1 ⟨rip, read1⟩
  change (addR64M64Effect 0x110f21 8 (.base 14 (.d8 48)) t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [addR64M64Effect_components]) (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x10f25 (by decide))
  have w8_1 : t1.regValue .r8 = q.1 := by
    have value : t1.regValue .r8 = t.regValue .r8 + (Operand.mem ((AddrMode.base 14 (.d8 48)).addr t 0x110f25) : Operand 64).read t := effect1.writes
    rw [ha, addr1, load] at value
    exact value
  have cf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = q.2.CF := by
    have value : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec (t.regValue .r8) ((Operand.mem ((AddrMode.base 14 (.d8 48)).addr t 0x110f25) : Operand 64).read t)).2.CF := effect1.flags.1
    rw [ha, addr1, load] at value
    exact value
  have r1_1 : t1.regValue .rcx = 0 :=
    (effect1.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans (hz)
  have code2 : CodeIn (codeRange 0x110f25 [0xf,0x92,0xc1]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10f25 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := setcc_r8_effect_step 0x110f25 0x92 0xc1 (.inl rfl) (by decide) (by decide)
    t1 ready1 code2 effect1.rip
  change (setccR8Effect 0x110f25 3 1 2 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [setccR8Effect_components]) (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x10f28 (by decide))
  have w1_2 : t2.regValue .rcx = e := by
    have value : t2.regValue .rcx = mergeGPR 8 (if (StatusFlags.ofRFLAGS t1.RFLAGS).CF then 1 else 0) (t1.regValue .rcx) := effect2.writes
    rw [cf1, r1_1, setb_zero] at value
    exact value
  have r8_2 : t2.regValue .r8 = q.1 :=
    (effect2.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans (w8_1)
  have code3 : CodeIn (codeRange 0x110f28 [0x4c,0x89,0xc0]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10f28 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := mov_r64_r64_effect_step 0x110f28 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t2 ready2 code3 effect2.rip
  change (movR64R64Effect 0x110f28 0 8 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f2b (by decide))
  have w0_3 : t3.regValue .rax = q.1 := by
    have value : t3.regValue .rax = t2.regValue .r8 := effect3.writes
    rw [r8_2] at value
    exact value
  have code4 : CodeIn (codeRange 0x110f2b [0x48,0xc7,0xc2,0xff,0xff,0xff,0xff]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10f2b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_imm32_effect_step 0x110f2b 0x48 0xc2 (by simp [RexWPrefix]) (by decide) (by decide) 0xffffffff
    t3 ready3 code4 effect3.rip
  change (movR64Imm32Effect 0x110f2b 2 0xffffffff t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64Imm32Effect_components]) (by simp [movR64Imm32Effect_components]) (inProgram_of_textOffset 0x10f32 (by decide))
  have w2_4 : t4.regValue .rdx = 0xffffffffffffffff := by
    have value : t4.regValue .rdx = 0xffffffffffffffff := effect4.writes
    exact value
  have r0_4 : t4.regValue .rax = q.1 :=
    (effect4.agrees.read (n := 64) (r := 0) (by simp [movR64Imm32Effect_components])).trans (w0_3)
  have code5 : CodeIn (codeRange 0x110f32 [0x48,0xf7,0xe2]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10f32 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x110f32 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x110f32 2 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10f35 (by decide))
  have w0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have value : t5.regValue .rax = t4.regValue .rax * t4.regValue .rdx := effect5.writes.1
    rw [r0_4, w2_4] at value
    exact value
  have w2_5 : t5.regValue .rdx = mulHigh64 (q.1) (0xffffffffffffffff) := by
    have value : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .rdx) := effect5.writes.2
    rw [r0_4, w2_4] at value
    exact value
  have r8_5 : t5.regValue .r8 = q.1 :=
    (effect5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 8) (by simp [movR64Imm32Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_2)))
  have code6 : CodeIn (codeRange 0x110f35 [0x4c,0x1,0xc0]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10f35 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x110f35 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x110f35 0 8 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10f38 (by decide))
  have w0_6 : t6.regValue .rax = neg.1 := by
    have value : t6.regValue .rax = t5.regValue .rax + t5.regValue .r8 := effect6.writes
    rw [w0_5, r8_5] at value
    exact value
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have value : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .r8)).2.CF := effect6.flags.1
    rw [w0_5, r8_5] at value
    exact value
  have r1_6 : t6.regValue .rcx = e :=
    (effect6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64Imm32Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (w1_2))))
  have r2_6 : t6.regValue .rdx = mulHigh64 (q.1) (0xffffffffffffffff) :=
    (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (w2_5)
  have code7 : CodeIn (codeRange 0x110f38 [0x48,0x11,0xd1]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10f38 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x110f38 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x110f38 1 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10f3b (by decide))
  have w1_7 : t7.regValue .rcx = ec.1 := by
    have value : t7.regValue .rcx = (adcSpec (t6.regValue .rcx) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [r1_6, r2_6, carry_extract cf6] at value
    exact value
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = ec.2.CF := by
    have value : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec (t6.regValue .rcx) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).2.CF := effect7.flags.1
    rw [r1_6, r2_6, carry_extract cf6] at value
    exact value
  have r8_7 : t7.regValue .r8 = q.1 :=
    (effect7.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans (r8_5))
  have code8 : CodeIn (codeRange 0x110f3b [0x4c,0x89,0xc0]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10f3b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r64_r64_effect_step 0x110f3b 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x110f3b 0 8 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f3e (by decide))
  have w0_8 : t8.regValue .rax = q.1 := by
    have value : t8.regValue .rax = t7.regValue .r8 := effect8.writes
    rw [r8_7] at value
    exact value
  have code9 : CodeIn (codeRange 0x110f3e [0xba,0xff,0xff,0xff,0xff]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x10f3e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mov_r32_imm32_effect_step 0x110f3e 0xba (by decide) 0xffffffff
    t8 ready8 code9 effect8.rip
  change (movR32Imm32Effect 0x110f3e 5 2 0xffffffff t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [movR32Imm32Effect_components]) (by simp [movR32Imm32Effect_components]) (inProgram_of_textOffset 0x10f43 (by decide))
  have w2_9 : t9.regValue .rdx = 0xffffffff := by
    have value : t9.regValue .rdx = 0xffffffff := effect9.writes
    exact value
  have r0_9 : t9.regValue .rax = q.1 :=
    (effect9.agrees.read (n := 64) (r := 0) (by simp [movR32Imm32Effect_components])).trans (w0_8)
  have code10 : CodeIn (codeRange 0x110f43 [0x48,0xf7,0xe2]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x10f43 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mul_r64_effect_step 0x110f43 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)
    t9 ready9 code10 effect9.rip
  change (mulR64Effect 0x110f43 2 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10f46 (by decide))
  have w0_10 : t10.regValue .rax = q.1 * 0xffffffff := by
    have value : t10.regValue .rax = t9.regValue .rax * t9.regValue .rdx := effect10.writes.1
    rw [r0_9, w2_9] at value
    exact value
  have w2_10 : t10.regValue .rdx = mulHigh64 (q.1) (0xffffffff) := by
    have value : t10.regValue .rdx = mulHigh64 (t9.regValue .rax) (t9.regValue .rdx) := effect10.writes.2
    rw [r0_9, w2_9] at value
    exact value
  have code11 : CodeIn (codeRange 0x110f46 [0x48,0x89,0xd5]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x10f46 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x110f46 0x48 0xd5 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x110f46 5 2 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f49 (by decide))
  have w5_11 : t11.regValue .rbp = mulHigh64 (q.1) (0xffffffff) := by
    have value : t11.regValue .rbp = t10.regValue .rdx := effect11.writes
    rw [w2_10] at value
    exact value
  have r0_11 : t11.regValue .rax = q.1 * 0xffffffff :=
    (effect11.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (w0_10)
  have code12 : CodeIn (codeRange 0x110f49 [0x49,0x89,0xc1]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x10f49 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := mov_r64_r64_effect_step 0x110f49 0x49 0xc1 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (movR64R64Effect 0x110f49 9 0 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f4c (by decide))
  have w9_12 : t12.regValue .r9 = q.1 * 0xffffffff := by
    have value : t12.regValue .r9 = t11.regValue .rax := effect12.writes
    rw [r0_11] at value
    exact value
  have r10_12 : t12.regValue .r10 = b :=
    (effect12.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 10) (by simp [movR32Imm32Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 10) (by simp [movR64Imm32Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans (hb))))))))))))
  have code13 : CodeIn (codeRange 0x110f4c [0x4d,0x1,0xd1]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x10f4c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := add_r64_r64_effect_step 0x110f4c 0x4d 0xd1 (by simp [RexWPrefix]) (by decide)
    t12 ready12 code13 effect12.rip
  change (addR64R64Effect 0x110f4c 9 10 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10f4f (by decide))
  have w9_13 : t13.regValue .r9 = l.1 := by
    have value : t13.regValue .r9 = t12.regValue .r9 + t12.regValue .r10 := effect13.writes
    rw [w9_12, r10_12] at value
    exact value
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = l.2.CF := by
    have value : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (addSpec (t12.regValue .r9) (t12.regValue .r10)).2.CF := effect13.flags.1
    rw [w9_12, r10_12] at value
    exact value
  have r5_13 : t13.regValue .rbp = mulHigh64 (q.1) (0xffffffff) :=
    (effect13.agrees.read (n := 64) (r := 5) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 5) (by simp [movR64R64Effect_components])).trans (w5_11))
  have code14 : CodeIn (codeRange 0x110f4f [0x48,0x83,0xd5,0x0]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x10f4f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := adc_r64_imm8_effect_step 0x110f4f 0x48 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t13 ready13 code14 effect13.rip
  change (adcR64Imm8Effect 0x110f4f 5 0 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10f53 (by decide))
  have w5_14 : t14.regValue .rbp = h.1 := by
    have value : t14.regValue .rbp = (adcSpec (t13.regValue .rbp) (0) (t13.RFLAGS.extractLsb' 0 1)).1 := effect14.writes
    rw [r5_13, carry_extract cf13] at value
    exact value
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = h.2.CF := by
    have value : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (adcSpec (t13.regValue .rbp) (0) (t13.RFLAGS.extractLsb' 0 1)).2.CF := effect14.flags.1
    rw [r5_13, carry_extract cf13] at value
    exact value
  have r8_14 : t14.regValue .r8 = q.1 :=
    (effect14.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 8) (by simp [movR32Imm32Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_7)))))))
  have code15 : CodeIn (codeRange 0x110f53 [0x4c,0x89,0xc0]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x10f53 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mov_r64_r64_effect_step 0x110f53 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t14 ready14 code15 effect14.rip
  change (movR64R64Effect 0x110f53 0 8 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f56 (by decide))
  have w0_15 : t15.regValue .rax = q.1 := by
    have value : t15.regValue .rax = t14.regValue .r8 := effect15.writes
    rw [r8_14] at value
    exact value
  have code16 : CodeIn (codeRange 0x110f56 [0x48,0xba,0x1,0x0,0x0,0x0,0xff,0xff,0xff,0xff]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x10f56 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mov_r64_imm64_effect_step 0x110f56 0x48 0xba (by simp [RexWPrefix]) (by decide) 0xffffffff00000001
    t15 ready15 code16 effect15.rip
  change (movR64Imm64Effect 0x110f56 2 0xffffffff00000001 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [movR64Imm64Effect_components]) (by simp [movR64Imm64Effect_components]) (inProgram_of_textOffset 0x10f60 (by decide))
  have w2_16 : t16.regValue .rdx = 0xffffffff00000001 := by
    have value : t16.regValue .rdx = 0xffffffff00000001 := effect16.writes
    exact value
  have r0_16 : t16.regValue .rax = q.1 :=
    (effect16.agrees.read (n := 64) (r := 0) (by simp [movR64Imm64Effect_components])).trans (w0_15)
  have code17 : CodeIn (codeRange 0x110f60 [0x48,0xf7,0xe2]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x10f60 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mul_r64_effect_step 0x110f60 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)
    t16 ready16 code17 effect16.rip
  change (mulR64Effect 0x110f60 2 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10f63 (by decide))
  have w0_17 : t17.regValue .rax = q.1 * 0xffffffff00000001 := by
    have value : t17.regValue .rax = t16.regValue .rax * t16.regValue .rdx := effect17.writes.1
    rw [r0_16, w2_16] at value
    exact value
  have w2_17 : t17.regValue .rdx = mulHigh64 (q.1) (0xffffffff00000001) := by
    have value : t17.regValue .rdx = mulHigh64 (t16.regValue .rax) (t16.regValue .rdx) := effect17.writes.2
    rw [r0_16, w2_16] at value
    exact value
  have code18 : CodeIn (codeRange 0x110f63 [0x49,0x89,0xd2]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x10f63 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := mov_r64_r64_effect_step 0x110f63 0x49 0xd2 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (movR64R64Effect 0x110f63 10 2 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f66 (by decide))
  have w10_18 : t18.regValue .r10 = mulHigh64 (q.1) (0xffffffff00000001) := by
    have value : t18.regValue .r10 = t17.regValue .rdx := effect18.writes
    rw [w2_17] at value
    exact value
  have r0_18 : t18.regValue .rax = q.1 * 0xffffffff00000001 :=
    (effect18.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (w0_17)
  have code19 : CodeIn (codeRange 0x110f66 [0x49,0x89,0xc0]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x10f66 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := mov_r64_r64_effect_step 0x110f66 0x49 0xc0 (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (movR64R64Effect 0x110f66 8 0 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10f69 (by decide))
  have w8_19 : t19.regValue .r8 = q.1 * 0xffffffff00000001 := by
    have value : t19.regValue .r8 = t18.regValue .rax := effect19.writes
    rw [r0_18] at value
    exact value
  have r11_19 : t19.regValue .r11 = d :=
    (effect19.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 11) (by simp [movR64Imm64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 11) (by simp [movR32Imm32Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [movR64Imm32Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 11) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans (hd)))))))))))))))))))
  have code20 : CodeIn (codeRange 0x110f69 [0x4d,0x1,0xd8]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x10f69 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := add_r64_r64_effect_step 0x110f69 0x4d 0xd8 (by simp [RexWPrefix]) (by decide)
    t19 ready19 code20 effect19.rip
  change (addR64R64Effect 0x110f69 8 11 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10f6c (by decide))
  have w8_20 : t20.regValue .r8 = k.1 := by
    have value : t20.regValue .r8 = t19.regValue .r8 + t19.regValue .r11 := effect20.writes
    rw [w8_19, r11_19] at value
    exact value
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = k.2.CF := by
    have value : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (addSpec (t19.regValue .r8) (t19.regValue .r11)).2.CF := effect20.flags.1
    rw [w8_19, r11_19] at value
    exact value
  have r10_20 : t20.regValue .r10 = mulHigh64 (q.1) (0xffffffff00000001) :=
    (effect20.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (w10_18))
  have code21 : CodeIn (codeRange 0x110f6c [0x49,0x83,0xd2,0x0]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x10f6c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := adc_r64_imm8_effect_step 0x110f6c 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t20 ready20 code21 effect20.rip
  change (adcR64Imm8Effect 0x110f6c 10 0 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10f70 (by decide))
  have w10_21 : t21.regValue .r10 = j.1 := by
    have value : t21.regValue .r10 = (adcSpec (t20.regValue .r10) (0) (t20.RFLAGS.extractLsb' 0 1)).1 := effect21.writes
    rw [r10_20, carry_extract cf20] at value
    exact value
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = j.2.CF := by
    have value : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (adcSpec (t20.regValue .r10) (0) (t20.RFLAGS.extractLsb' 0 1)).2.CF := effect21.flags.1
    rw [r10_20, carry_extract cf20] at value
    exact value
  have r9_21 : t21.regValue .r9 = l.1 :=
    (effect21.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [movR64Imm64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans (w9_13))))))))
  have r1_21 : t21.regValue .rcx = ec.1 :=
    (effect21.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 1) (by simp [movR64Imm64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [movR32Imm32Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (w1_7))))))))))))))
  have code22 : CodeIn (codeRange 0x110f70 [0x49,0x1,0xc9]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x10f70 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := add_r64_r64_effect_step 0x110f70 0x49 0xc9 (by simp [RexWPrefix]) (by decide)
    t21 ready21 code22 effect21.rip
  change (addR64R64Effect 0x110f70 9 1 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10f73 (by decide))
  have w9_22 : t22.regValue .r9 = o0.1 := by
    have value : t22.regValue .r9 = t21.regValue .r9 + t21.regValue .rcx := effect22.writes
    rw [r9_21, r1_21] at value
    exact value
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o0.2.CF := by
    have value : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (addSpec (t21.regValue .r9) (t21.regValue .rcx)).2.CF := effect22.flags.1
    rw [r9_21, r1_21] at value
    exact value
  have r5_22 : t22.regValue .rbp = h.1 :=
    (effect22.agrees.read (n := 64) (r := 5) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 5) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 5) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 5) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 5) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 5) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 5) (by simp [movR64Imm64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 5) (by simp [movR64R64Effect_components])).trans (w5_14))))))))
  have r6_22 : t22.regValue .rsi = c :=
    (effect22.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 6) (by simp [movR64Imm64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 6) (by simp [movR32Imm32Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 6) (by simp [movR64Imm32Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 6) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 6) (by simp [addR64M64Effect_components])).trans (hc))))))))))))))))))))))
  have code23 : CodeIn (codeRange 0x110f73 [0x48,0x11,0xf5]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x10f73 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_r64_effect_step 0x110f73 0x48 0xf5 (by simp [RexWPrefix]) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64R64Effect 0x110f73 5 6 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10f76 (by decide))
  have w5_23 : t23.regValue .rbp = o1.1 := by
    have value : t23.regValue .rbp = (adcSpec (t22.regValue .rbp) (t22.regValue .rsi) (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [r5_22, r6_22, carry_extract cf22] at value
    exact value
  have cf23 : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = o1.2.CF := by
    have value : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = (adcSpec (t22.regValue .rbp) (t22.regValue .rsi) (t22.RFLAGS.extractLsb' 0 1)).2.CF := effect23.flags.1
    rw [r5_22, r6_22, carry_extract cf22] at value
    exact value
  have r8_23 : t23.regValue .r8 = k.1 :=
    (effect23.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (w8_20)))
  have code24 : CodeIn (codeRange 0x110f76 [0x49,0x83,0xd0,0x0]) t23 :=
    programText_slice (programLoaded_codeIn stage23.loaded) 0x10f76 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t24, step24, ready24, effect24⟩ := adc_r64_imm8_effect_step 0x110f76 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t23 ready23 code24 effect23.rip
  change (adcR64Imm8Effect 0x110f76 8 0 t23).Holds t23 t24 at effect24
  have stage24 := stage23.step_registers pre step24 ready24 effect24
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10f7a (by decide))
  have w8_24 : t24.regValue .r8 = o2.1 := by
    have value : t24.regValue .r8 = (adcSpec (t23.regValue .r8) (0) (t23.RFLAGS.extractLsb' 0 1)).1 := effect24.writes
    rw [r8_23, carry_extract cf23] at value
    exact value
  have cf24 : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = o2.2.CF := by
    have value : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = (adcSpec (t23.regValue .r8) (0) (t23.RFLAGS.extractLsb' 0 1)).2.CF := effect24.flags.1
    rw [r8_23, carry_extract cf23] at value
    exact value
  have r10_24 : t24.regValue .r10 = j.1 :=
    (effect24.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans (w10_21)))
  have code25 : CodeIn (codeRange 0x110f7a [0x49,0x83,0xd2,0x0]) t24 :=
    programText_slice (programLoaded_codeIn stage24.loaded) 0x10f7a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t25, step25, ready25, effect25⟩ := adc_r64_imm8_effect_step 0x110f7a 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t24 ready24 code25 effect24.rip
  change (adcR64Imm8Effect 0x110f7a 10 0 t24).Holds t24 t25 at effect25
  have stage25 := stage24.step_registers pre step25 ready25 effect25
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10f7e (by decide))
  have w10_25 : t25.regValue .r10 = o3.1 := by
    have value : t25.regValue .r10 = (adcSpec (t24.regValue .r10) (0) (t24.RFLAGS.extractLsb' 0 1)).1 := effect25.writes
    rw [r10_24, carry_extract cf24] at value
    exact value
  have cf25 : (StatusFlags.ofRFLAGS t25.RFLAGS).CF = o3.2.CF := by
    have value : (StatusFlags.ofRFLAGS t25.RFLAGS).CF = (adcSpec (t24.regValue .r10) (0) (t24.RFLAGS.extractLsb' 0 1)).2.CF := effect25.flags.1
    rw [r10_24, carry_extract cf24] at value
    exact value
  have code26 : CodeIn (codeRange 0x110f7e [0x31,0xc9]) t25 :=
    programText_slice (programLoaded_codeIn stage25.loaded) 0x10f7e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t26, step26, ready26, effect26⟩ := xor_r32_r32_effect_step 0x110f7e 0xc9 (by decide)
    t25 ready25 code26 effect25.rip
  change (xorR32R32Effect 0x110f7e 2 1 1 t25).Holds t25 t26 at effect26
  have stage26 := stage25.step_registers pre step26 ready26 effect26
    (by simp [xorR32R32Effect_components]) (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x10f80 (by decide))
  have w1_26 : t26.regValue .rcx = 0 := by
    have value : t26.regValue .rcx = (((Operand.reg 1 : Operand 32).read t25) ^^^ ((Operand.reg 1 : Operand 32).read t25)).setWidth 64 := effect26.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at value
    exact value.trans (by rfl)
  have r9_26 : t26.regValue .r9 = o0.1 :=
    (effect26.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans ((effect25.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans (w9_22))))
  have r5_26 : t26.regValue .rbp = o1.1 :=
    (effect26.agrees.read (n := 64) (r := 5) (by simp [xorR32R32Effect_components])).trans ((effect25.agrees.read (n := 64) (r := 5) (by simp [adcR64Imm8Effect_components])).trans ((effect24.agrees.read (n := 64) (r := 5) (by simp [adcR64Imm8Effect_components])).trans (w5_23)))
  have r8_26 : t26.regValue .r8 = o2.1 :=
    (effect26.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans ((effect25.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (w8_24))
  have r10_26 : t26.regValue .r10 = o3.1 :=
    (effect26.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (w10_25)
  have agree {a b c : RamState} (ha : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] a b) (hb : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] b c) : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag1 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t t1 := effect1.agrees.mono (by simp [addR64M64Effect_components])
  have ag2 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t1 t2 := effect2.agrees.mono (by simp [setccR8Effect_components])
  have ag3 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t2 t3 := effect3.agrees.mono (by simp [movR64R64Effect_components])
  have ag4 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t3 t4 := effect4.agrees.mono (by simp [movR64Imm32Effect_components])
  have ag5 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t4 t5 := effect5.agrees.mono (by simp [mulR64Effect_components])
  have ag6 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t5 t6 := effect6.agrees.mono (by simp [addR64R64Effect_components])
  have ag7 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t6 t7 := effect7.agrees.mono (by simp [adcR64R64Effect_components])
  have ag8 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t7 t8 := effect8.agrees.mono (by simp [movR64R64Effect_components])
  have ag9 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t8 t9 := effect9.agrees.mono (by simp [movR32Imm32Effect_components])
  have ag10 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t9 t10 := effect10.agrees.mono (by simp [mulR64Effect_components])
  have ag11 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t10 t11 := effect11.agrees.mono (by simp [movR64R64Effect_components])
  have ag12 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t11 t12 := effect12.agrees.mono (by simp [movR64R64Effect_components])
  have ag13 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t12 t13 := effect13.agrees.mono (by simp [addR64R64Effect_components])
  have ag14 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t13 t14 := effect14.agrees.mono (by simp [adcR64Imm8Effect_components])
  have ag15 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t14 t15 := effect15.agrees.mono (by simp [movR64R64Effect_components])
  have ag16 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t15 t16 := effect16.agrees.mono (by simp [movR64Imm64Effect_components])
  have ag17 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t16 t17 := effect17.agrees.mono (by simp [mulR64Effect_components])
  have ag18 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t17 t18 := effect18.agrees.mono (by simp [movR64R64Effect_components])
  have ag19 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t18 t19 := effect19.agrees.mono (by simp [movR64R64Effect_components])
  have ag20 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t19 t20 := effect20.agrees.mono (by simp [addR64R64Effect_components])
  have ag21 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t20 t21 := effect21.agrees.mono (by simp [adcR64Imm8Effect_components])
  have ag22 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t21 t22 := effect22.agrees.mono (by simp [addR64R64Effect_components])
  have ag23 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t22 t23 := effect23.agrees.mono (by simp [adcR64R64Effect_components])
  have ag24 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t23 t24 := effect24.agrees.mono (by simp [adcR64Imm8Effect_components])
  have ag25 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t24 t25 := effect25.agrees.mono (by simp [adcR64Imm8Effect_components])
  have ag26 : AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8,.reg 9,.reg 10,.reg 11,.flags,.rip] t25 t26 := effect26.agrees.mono (by simp [xorR32R32Effect_components])
  exact ⟨t26, stage26, effect26.rip, ⟨r9_26, r5_26, r8_26, r10_26⟩, w1_26, agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 (agree ag8 (agree ag9 (agree ag10 (agree ag11 (agree ag12 (agree ag13 (agree ag14 (agree ag15 (agree ag16 (agree ag17 (agree ag18 (agree ag19 (agree ag20 (agree ag21 (agree ag22 (agree ag23 (agree ag24 (agree ag25 (ag26)))))))))))))))))))))))))⟩
end P256.Proofs.Sec1Serialize.Conversion
