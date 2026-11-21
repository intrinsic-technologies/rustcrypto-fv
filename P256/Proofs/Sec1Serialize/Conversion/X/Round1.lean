import P256.Proofs.Sec1Serialize.Conversion.X.Initial
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Montgomery

set_option autoImplicit false
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)

namespace P256.Proofs.Sec1Serialize.Conversion
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem x_round1 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110daf) (r14 : t.regValue .r14 = s.regValue .rsi)
    (k13 : t.regValue .r13 = 0xffffffff00000001)
    (k15 : t.regValue .r15 = 0)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x110e03 ∧
      (u.regValue .r8, u.regValue .r10, u.regValue .rsi, u.regValue .r11) =
        Montgomery.compilerRoundBV (t.regValue .rsi) (t.regValue .rcx) (t.regValue .r9) (t.regValue .rbx)
          ((Operand.mem (s.regValue .rsi + 8) : Operand 64).read t) ∧
      u.regValue .r13 = 0xffffffff00000001 ∧
      AgreesExcept xRegisters t u := by
  let a := t.regValue .rsi
  let b := t.regValue .rcx
  let c := t.regValue .r9
  let d := t.regValue .rbx
  let z := (Operand.mem (s.regValue .rsi + 8) : Operand 64).read t
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
  have r6_0 : t.regValue .rsi = a := rfl
  have addr1 : (AddrMode.base 14 (.d8 8)).addr t 0x110db3 = s.regValue .rsi + 8 := by
    change t.regValue .r14 + 8 = _
    rw [r14]
  have read1 : MemReadable t ((AddrMode.base 14 (.d8 8)).addr t 0x110db3) 8 := by
    rw [addr1]
    exact input_readable pre stage.allocated (offset := 8) (by decide)
  have mem1 : t.external = t.external := rfl
  have code1 : CodeIn (codeRange 0x110daf [0x49,0x3,0x76,0x8]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10daf _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := add_r64_m64_effect_step 0x110daf 0x49 (by simp [RexWPrefix]) 6 (.base 14 (.d8 8)) (by decide) rfl rfl
    t stage.ready code1 ⟨rip, read1⟩
  change (addR64M64Effect 0x110daf 6 (.base 14 (.d8 8)) t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [addR64M64Effect_components]) (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x10db3 (by decide))
  have r6_1 : t1.regValue .rsi = q.1 := by
    have he : t1.regValue .rsi = (addSpec (t.regValue .rsi) ((Operand.mem ((AddrMode.base 14 (.d8 8)).addr t 0x110db3) : Operand 64).read t)).1 := effect1.writes
    rw [r6_0, addr1] at he
    change t1.regValue .rsi = (addSpec a (memLoad t.external (s.regValue .rsi + 8) 64)).1 at he
    rw [mem1] at he
    exact he
  have cf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec (t.regValue .rsi) ((Operand.mem ((AddrMode.base 14 (.d8 8)).addr t 0x110db3) : Operand 64).read t)).2.CF := effect1.flags.1
    rw [r6_0, addr1] at he
    change (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec a (memLoad t.external (s.regValue .rsi + 8) 64)).2.CF at he
    rw [mem1] at he
    exact he
  have r15_1 : t1.regValue .r15 = 0 := (effect1.agrees.read (n := 64) (r := 15) (by simp [addR64M64Effect_components])).trans (k15)
  have code2 : CodeIn (codeRange 0x110db3 [0x41,0xf,0x92,0xc7]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10db3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := setcc_r8_rex_effect_step 0x110db3 0x41 0x92 0xc7 (by simp [RexPrefix]) (.inl rfl) (by decide)
    t1 ready1 code2 effect1.rip
  change (setccR8Effect 0x110db3 4 15 2 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [setccR8Effect_components]) (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x10db7 (by decide))
  have r15_2 : t2.regValue .r15 = e := by
    have he : t2.regValue .r15 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t1.RFLAGS).CF then 1 else 0) (t1.regValue .r15) := effect2.writes
    rw [cf1, r15_1, setb_zero] at he
    exact he
  have code3 : CodeIn (codeRange 0x110db7 [0x48,0xc7,0xc2,0xff,0xff,0xff,0xff]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10db7 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := mov_r64_imm32_effect_step 0x110db7 0x48 0xc2 (by simp [RexWPrefix]) (by decide) (by decide) 0xffffffff
    t2 ready2 code3 effect2.rip
  change (movR64Imm32Effect 0x110db7 2 0xffffffff t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [movR64Imm32Effect_components]) (by simp [movR64Imm32Effect_components]) (inProgram_of_textOffset 0x10dbe (by decide))
  have r2_3 : t3.regValue .rdx = 0xffffffffffffffff := by
    have he : t3.regValue .rdx = (0xffffffff : BitVec 32).signExtend 64 := effect3.writes
    exact he.trans (by decide +kernel)
  have r6_3 : t3.regValue .rsi = q.1 := (effect3.agrees.read (n := 64) (r := 6) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 6) (by simp [setccR8Effect_components])).trans (r6_1))
  have code4 : CodeIn (codeRange 0x110dbe [0x48,0x89,0xf0]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10dbe _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x110dbe 0x48 0xf0 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x110dbe 0 6 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10dc1 (by decide))
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .rsi := effect4.writes
    rw [r6_3] at he
    exact he
  have r2_4 : t4.regValue .rdx = 0xffffffffffffffff := (effect4.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans (r2_3)
  have code5 : CodeIn (codeRange 0x110dc1 [0x48,0xf7,0xe2]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10dc1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x110dc1 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x110dc1 2 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10dc4 (by decide))
  have r0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t5.regValue .rax = t4.regValue .rax * t4.regValue .rdx := effect5.writes.1
    rw [r0_4, r2_4] at he
    exact he
  have r2_5 : t5.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .rdx) := effect5.writes.2
    rw [r0_4, r2_4] at he
    exact he
  have r6_5 : t5.regValue .rsi = q.1 := (effect5.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r6_3))
  have code6 : CodeIn (codeRange 0x110dc4 [0x48,0x1,0xf0]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10dc4 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x110dc4 0x48 0xf0 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x110dc4 0 6 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10dc7 (by decide))
  have r0_6 : t6.regValue .rax = neg.1 := by
    have he : t6.regValue .rax = (addSpec (t5.regValue .rax) (t5.regValue .rsi)).1 := effect6.writes
    rw [r0_5, r6_5] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .rsi)).2.CF := effect6.flags.1
    rw [r0_5, r6_5] at he
    exact he
  have r15_6 : t6.regValue .r15 = e := (effect6.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 15) (by simp [movR64Imm32Effect_components])).trans (r15_2))))
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_5)
  have cb7 := carry_extract cf6
  have code7 : CodeIn (codeRange 0x110dc7 [0x49,0x11,0xd7]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10dc7 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x110dc7 0x49 0xd7 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x110dc7 15 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10dca (by decide))
  have r15_7 : t7.regValue .r15 = ec.1 := by
    have he : t7.regValue .r15 = (adcSpec (t6.regValue .r15) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [cb7, r15_6, r2_6] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = ec.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec (t6.regValue .r15) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).2.CF := effect7.flags.1
    rw [cb7, r15_6, r2_6] at he
    exact he
  have code8 : CodeIn (codeRange 0x110dca [0xba,0xff,0xff,0xff,0xff]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10dca _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r32_imm32_effect_step 0x110dca 0xba (by decide) 0xffffffff
    t7 ready7 code8 effect7.rip
  change (movR32Imm32Effect 0x110dca 5 2 0xffffffff t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR32Imm32Effect_components]) (by simp [movR32Imm32Effect_components]) (inProgram_of_textOffset 0x10dcf (by decide))
  have r2_8 : t8.regValue .rdx = 0xffffffff := by
    have he : t8.regValue .rdx = (0xffffffff : BitVec 32).setWidth 64 := effect8.writes
    exact he.trans (by decide +kernel)
  have r6_8 : t8.regValue .rsi = q.1 := (effect8.agrees.read (n := 64) (r := 6) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans (r6_5)))
  have code9 : CodeIn (codeRange 0x110dcf [0x48,0x89,0xf0]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x10dcf _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mov_r64_r64_effect_step 0x110dcf 0x48 0xf0 (by simp [RexWPrefix]) (by decide)
    t8 ready8 code9 effect8.rip
  change (movR64R64Effect 0x110dcf 0 6 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10dd2 (by decide))
  have r0_9 : t9.regValue .rax = q.1 := by
    have he : t9.regValue .rax = t8.regValue .rsi := effect9.writes
    rw [r6_8] at he
    exact he
  have r2_9 : t9.regValue .rdx = 0xffffffff := (effect9.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans (r2_8)
  have code10 : CodeIn (codeRange 0x110dd2 [0x48,0xf7,0xe2]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x10dd2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mul_r64_effect_step 0x110dd2 0x48 0xe2 (by simp [RexWPrefix]) (by decide) (by decide)
    t9 ready9 code10 effect9.rip
  change (mulR64Effect 0x110dd2 2 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10dd5 (by decide))
  have r0_10 : t10.regValue .rax = q.1 * 0xffffffff := by
    have he : t10.regValue .rax = t9.regValue .rax * t9.regValue .rdx := effect10.writes.1
    rw [r0_9, r2_9] at he
    exact he
  have r2_10 : t10.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t10.regValue .rdx = mulHigh64 (t9.regValue .rax) (t9.regValue .rdx) := effect10.writes.2
    rw [r0_9, r2_9] at he
    exact he
  have code11 : CodeIn (codeRange 0x110dd5 [0x49,0x89,0xd2]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x10dd5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x110dd5 0x49 0xd2 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x110dd5 10 2 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10dd8 (by decide))
  have r10_11 : t11.regValue .r10 = mulHigh64 q.1 0xffffffff := by
    have he : t11.regValue .r10 = t10.regValue .rdx := effect11.writes
    rw [r2_10] at he
    exact he
  have r0_11 : t11.regValue .rax = q.1 * 0xffffffff := (effect11.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_10)
  have code12 : CodeIn (codeRange 0x110dd8 [0x49,0x89,0xc0]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x10dd8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := mov_r64_r64_effect_step 0x110dd8 0x49 0xc0 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (movR64R64Effect 0x110dd8 8 0 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10ddb (by decide))
  have r8_12 : t12.regValue .r8 = q.1 * 0xffffffff := by
    have he : t12.regValue .r8 = t11.regValue .rax := effect12.writes
    rw [r0_11] at he
    exact he
  have r1_12 : t12.regValue .rcx = b := (effect12.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 1) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 1) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 1) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 1) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans (rfl))))))))))))
  have code13 : CodeIn (codeRange 0x110ddb [0x49,0x1,0xc8]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x10ddb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := add_r64_r64_effect_step 0x110ddb 0x49 0xc8 (by simp [RexWPrefix]) (by decide)
    t12 ready12 code13 effect12.rip
  change (addR64R64Effect 0x110ddb 8 1 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10dde (by decide))
  have r8_13 : t13.regValue .r8 = l.1 := by
    have he : t13.regValue .r8 = (addSpec (t12.regValue .r8) (t12.regValue .rcx)).1 := effect13.writes
    rw [r8_12, r1_12] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (addSpec (t12.regValue .r8) (t12.regValue .rcx)).2.CF := effect13.flags.1
    rw [r8_12, r1_12] at he
    exact he
  have r10_13 : t13.regValue .r10 = mulHigh64 q.1 0xffffffff := (effect13.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_11))
  have cb14 := carry_extract cf13
  have code14 : CodeIn (codeRange 0x110dde [0x49,0x83,0xd2,0x0]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x10dde _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := adc_r64_imm8_effect_step 0x110dde 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t13 ready13 code14 effect13.rip
  change (adcR64Imm8Effect 0x110dde 10 0 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10de2 (by decide))
  have r10_14 : t14.regValue .r10 = h.1 := by
    have he : t14.regValue .r10 = (adcSpec (t13.regValue .r10) 0 (t13.RFLAGS.extractLsb' 0 1)).1 := effect14.writes
    rw [cb14, r10_13] at he
    exact he
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = h.2.CF := by
    have he : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (adcSpec (t13.regValue .r10) 0 (t13.RFLAGS.extractLsb' 0 1)).2.CF := effect14.flags.1
    rw [cb14, r10_13] at he
    exact he
  have r6_14 : t14.regValue .rsi = q.1 := (effect14.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r6_8))))))
  have code15 : CodeIn (codeRange 0x110de2 [0x48,0x89,0xf0]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x10de2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mov_r64_r64_effect_step 0x110de2 0x48 0xf0 (by simp [RexWPrefix]) (by decide)
    t14 ready14 code15 effect14.rip
  change (movR64R64Effect 0x110de2 0 6 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10de5 (by decide))
  have r0_15 : t15.regValue .rax = q.1 := by
    have he : t15.regValue .rax = t14.regValue .rsi := effect15.writes
    rw [r6_14] at he
    exact he
  have r13_15 : t15.regValue .r13 = 0xffffffff00000001 := (effect15.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 13) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 13) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 13) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 13) (by simp [addR64M64Effect_components])).trans (k13)))))))))))))))
  have code16 : CodeIn (codeRange 0x110de5 [0x49,0xf7,0xe5]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x10de5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mul_r64_effect_step 0x110de5 0x49 0xe5 (by simp [RexWPrefix]) (by decide) (by decide)
    t15 ready15 code16 effect15.rip
  change (mulR64Effect 0x110de5 13 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10de8 (by decide))
  have r0_16 : t16.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t16.regValue .rax = t15.regValue .rax * t15.regValue .r13 := effect16.writes.1
    rw [r0_15, r13_15] at he
    exact he
  have r2_16 : t16.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t16.regValue .rdx = mulHigh64 (t15.regValue .rax) (t15.regValue .r13) := effect16.writes.2
    rw [r0_15, r13_15] at he
    exact he
  have code17 : CodeIn (codeRange 0x110de8 [0x49,0x89,0xd3]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x10de8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mov_r64_r64_effect_step 0x110de8 0x49 0xd3 (by simp [RexWPrefix]) (by decide)
    t16 ready16 code17 effect16.rip
  change (movR64R64Effect 0x110de8 11 2 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10deb (by decide))
  have r11_17 : t17.regValue .r11 = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t17.regValue .r11 = t16.regValue .rdx := effect17.writes
    rw [r2_16] at he
    exact he
  have r0_17 : t17.regValue .rax = q.1 * 0xffffffff00000001 := (effect17.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_16)
  have code18 : CodeIn (codeRange 0x110deb [0x48,0x89,0xc6]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x10deb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := mov_r64_r64_effect_step 0x110deb 0x48 0xc6 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (movR64R64Effect 0x110deb 6 0 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10dee (by decide))
  have r6_18 : t18.regValue .rsi = q.1 * 0xffffffff00000001 := by
    have he : t18.regValue .rsi = t17.regValue .rax := effect18.writes
    rw [r0_17] at he
    exact he
  have r3_18 : t18.regValue .rbx = d := (effect18.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 3) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 3) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 3) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 3) (by simp [addR64M64Effect_components])).trans (rfl))))))))))))))))))
  have code19 : CodeIn (codeRange 0x110dee [0x48,0x1,0xde]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x10dee _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := add_r64_r64_effect_step 0x110dee 0x48 0xde (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (addR64R64Effect 0x110dee 6 3 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10df1 (by decide))
  have r6_19 : t19.regValue .rsi = k.1 := by
    have he : t19.regValue .rsi = (addSpec (t18.regValue .rsi) (t18.regValue .rbx)).1 := effect19.writes
    rw [r6_18, r3_18] at he
    exact he
  have cf19 : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = (addSpec (t18.regValue .rsi) (t18.regValue .rbx)).2.CF := effect19.flags.1
    rw [r6_18, r3_18] at he
    exact he
  have r11_19 : t19.regValue .r11 = mulHigh64 q.1 0xffffffff00000001 := (effect19.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans (r11_17))
  have cb20 := carry_extract cf19
  have code20 : CodeIn (codeRange 0x110df1 [0x49,0x83,0xd3,0x0]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x10df1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := adc_r64_imm8_effect_step 0x110df1 0x49 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t19 ready19 code20 effect19.rip
  change (adcR64Imm8Effect 0x110df1 11 0 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10df5 (by decide))
  have r11_20 : t20.regValue .r11 = j.1 := by
    have he : t20.regValue .r11 = (adcSpec (t19.regValue .r11) 0 (t19.RFLAGS.extractLsb' 0 1)).1 := effect20.writes
    rw [cb20, r11_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = j.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (adcSpec (t19.regValue .r11) 0 (t19.RFLAGS.extractLsb' 0 1)).2.CF := effect20.flags.1
    rw [cb20, r11_19] at he
    exact he
  have r8_20 : t20.regValue .r8 = l.1 := (effect20.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_13)))))))
  have r15_20 : t20.regValue .r15 = ec.1 := (effect20.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 15) (by simp [movR32Imm32Effect_components])).trans (r15_7)))))))))))))
  have code21 : CodeIn (codeRange 0x110df5 [0x4d,0x1,0xf8]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x10df5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := add_r64_r64_effect_step 0x110df5 0x4d 0xf8 (by simp [RexWPrefix]) (by decide)
    t20 ready20 code21 effect20.rip
  change (addR64R64Effect 0x110df5 8 15 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10df8 (by decide))
  have r8_21 : t21.regValue .r8 = o0.1 := by
    have he : t21.regValue .r8 = (addSpec (t20.regValue .r8) (t20.regValue .r15)).1 := effect21.writes
    rw [r8_20, r15_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (addSpec (t20.regValue .r8) (t20.regValue .r15)).2.CF := effect21.flags.1
    rw [r8_20, r15_20] at he
    exact he
  have r10_21 : t21.regValue .r10 = h.1 := (effect21.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_14)))))))
  have r9_21 : t21.regValue .r9 = c := (effect21.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 9) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 9) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 9) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 9) (by simp [addR64M64Effect_components])).trans (rfl)))))))))))))))))))))
  have cb22 := carry_extract cf21
  have code22 : CodeIn (codeRange 0x110df8 [0x4d,0x11,0xca]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x10df8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := adc_r64_r64_effect_step 0x110df8 0x4d 0xca (by simp [RexWPrefix]) (by decide)
    t21 ready21 code22 effect21.rip
  change (adcR64R64Effect 0x110df8 10 9 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10dfb (by decide))
  have r10_22 : t22.regValue .r10 = o1.1 := by
    have he : t22.regValue .r10 = (adcSpec (t21.regValue .r10) (t21.regValue .r9) (t21.RFLAGS.extractLsb' 0 1)).1 := effect22.writes
    rw [cb22, r10_21, r9_21] at he
    exact he
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (adcSpec (t21.regValue .r10) (t21.regValue .r9) (t21.RFLAGS.extractLsb' 0 1)).2.CF := effect22.flags.1
    rw [cb22, r10_21, r9_21] at he
    exact he
  have r6_22 : t22.regValue .rsi = k.1 := (effect22.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans (r6_19)))
  have cb23 := carry_extract cf22
  have code23 : CodeIn (codeRange 0x110dfb [0x48,0x83,0xd6,0x0]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x10dfb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_imm8_effect_step 0x110dfb 0x48 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64Imm8Effect 0x110dfb 6 0 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10dff (by decide))
  have r6_23 : t23.regValue .rsi = o2.1 := by
    have he : t23.regValue .rsi = (adcSpec (t22.regValue .rsi) 0 (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [cb23, r6_22] at he
    exact he
  have cf23 : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = (adcSpec (t22.regValue .rsi) 0 (t22.RFLAGS.extractLsb' 0 1)).2.CF := effect23.flags.1
    rw [cb23, r6_22] at he
    exact he
  have r11_23 : t23.regValue .r11 = j.1 := (effect23.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans (r11_20)))
  have cb24 := carry_extract cf23
  have code24 : CodeIn (codeRange 0x110dff [0x49,0x83,0xd3,0x0]) t23 :=
    programText_slice (programLoaded_codeIn stage23.loaded) 0x10dff _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t24, step24, ready24, effect24⟩ := adc_r64_imm8_effect_step 0x110dff 0x49 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t23 ready23 code24 effect23.rip
  change (adcR64Imm8Effect 0x110dff 11 0 t23).Holds t23 t24 at effect24
  have stage24 := stage23.step_registers pre step24 ready24 effect24
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e03 (by decide))
  have r11_24 : t24.regValue .r11 = o3.1 := by
    have he : t24.regValue .r11 = (adcSpec (t23.regValue .r11) 0 (t23.RFLAGS.extractLsb' 0 1)).1 := effect24.writes
    rw [cb24, r11_23] at he
    exact he
  have cf24 : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = o3.2.CF := by
    have he : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = (adcSpec (t23.regValue .r11) 0 (t23.RFLAGS.extractLsb' 0 1)).2.CF := effect24.flags.1
    rw [cb24, r11_23] at he
    exact he
  have r8_24 : t24.regValue .r8 = o0.1 := (effect24.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans (r8_21)))
  have r10_24 : t24.regValue .r10 = o1.1 := (effect24.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans (r10_22))
  have r6_24 : t24.regValue .rsi = o2.1 := (effect24.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans (r6_23)
  have r13_24 : t24.regValue .r13 = 0xffffffff00000001 := (effect24.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans (r13_15)))))))))
  have agree {a b c : RamState} (ha : AgreesExcept xRegisters a b) (hb : AgreesExcept xRegisters b c) : AgreesExcept xRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag1 : AgreesExcept xRegisters t t1 := effect1.agrees.mono (by simp [addR64M64Effect_components, xRegisters])
  have ag2 : AgreesExcept xRegisters t1 t2 := effect2.agrees.mono (by simp [setccR8Effect_components, xRegisters])
  have ag3 : AgreesExcept xRegisters t2 t3 := effect3.agrees.mono (by simp [movR64Imm32Effect_components, xRegisters])
  have ag4 : AgreesExcept xRegisters t3 t4 := effect4.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag5 : AgreesExcept xRegisters t4 t5 := effect5.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag6 : AgreesExcept xRegisters t5 t6 := effect6.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag7 : AgreesExcept xRegisters t6 t7 := effect7.agrees.mono (by simp [adcR64R64Effect_components, xRegisters])
  have ag8 : AgreesExcept xRegisters t7 t8 := effect8.agrees.mono (by simp [movR32Imm32Effect_components, xRegisters])
  have ag9 : AgreesExcept xRegisters t8 t9 := effect9.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag10 : AgreesExcept xRegisters t9 t10 := effect10.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag11 : AgreesExcept xRegisters t10 t11 := effect11.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag12 : AgreesExcept xRegisters t11 t12 := effect12.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag13 : AgreesExcept xRegisters t12 t13 := effect13.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag14 : AgreesExcept xRegisters t13 t14 := effect14.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag15 : AgreesExcept xRegisters t14 t15 := effect15.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag16 : AgreesExcept xRegisters t15 t16 := effect16.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag17 : AgreesExcept xRegisters t16 t17 := effect17.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag18 : AgreesExcept xRegisters t17 t18 := effect18.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag19 : AgreesExcept xRegisters t18 t19 := effect19.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag20 : AgreesExcept xRegisters t19 t20 := effect20.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag21 : AgreesExcept xRegisters t20 t21 := effect21.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag22 : AgreesExcept xRegisters t21 t22 := effect22.agrees.mono (by simp [adcR64R64Effect_components, xRegisters])
  have ag23 : AgreesExcept xRegisters t22 t23 := effect23.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag24 : AgreesExcept xRegisters t23 t24 := effect24.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  refine ⟨t24, stage24, effect24.rip, ?_, r13_24, (agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 (agree ag8 (agree ag9 (agree ag10 (agree ag11 (agree ag12 (agree ag13 (agree ag14 (agree ag15 (agree ag16 (agree ag17 (agree ag18 (agree ag19 (agree ag20 (agree ag21 (agree ag22 (agree ag23 ag24)))))))))))))))))))))))⟩
  change (t24.regValue .r8, t24.regValue .r10, t24.regValue .rsi, t24.regValue .r11) = (o0.1, o1.1, o2.1, o3.1)
  rw [r8_24, r10_24, r6_24, r11_24]

end P256.Proofs.Sec1Serialize.Conversion
