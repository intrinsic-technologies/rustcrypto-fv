import P256.Proofs.Ecdh.Normalize.Conversion.State


set_option autoImplicit false
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)
open P256.Proofs.Program (CalleePre inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Ecdh.Normalize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1Serialize.Conversion
open P256.Proofs.Program

theorem round1 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : ¬ InProgram boundary.rip) (stage : Stage s start t boundary)
    (source : t.regValue .rsi = s.regValue .rsi)
    (rip : t.RIP = 0x107d30) (constant : t.regValue .r14 = 0xffffffff00000001)
    (zero : t.regValue .r13 = 0)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x107d85 ∧
      (u.regValue .r8, u.regValue .r10, u.regValue .rcx, u.regValue .r11) =
        Montgomery.compilerRoundBV (t.regValue .rcx) (t.regValue .r11) (t.regValue .r9) (t.regValue .rbx)
          ((Operand.mem (s.regValue .rsi + 8) : Operand 64).read t) ∧
      u.regValue .r14 = 0xffffffff00000001 ∧
      u.regValue .r15 = 0xffffffffffffffff ∧
      u.regValue .r12 = 0xffffffff ∧
      AgreesExcept inputRegisters t u := by
  let a := t.regValue .rcx
  let b := t.regValue .r11
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
  have r1_0 : t.regValue .rcx = a := rfl
  have addr1 : (AddrMode.base 6 (.d8 8)).addr t 0x107d34 = s.regValue .rsi + 8 := by
    change t.regValue .rsi + 8 = _
    rw [source]
  have read1 : MemReadable t ((AddrMode.base 6 (.d8 8)).addr t 0x107d34) 8 := by
    rw [addr1]
    exact stage.readable_offset 8 (by decide)
  have mem1 : t.external = t.external := rfl
  have code1 : CodeIn (codeRange 0x107d30 [72, 3, 78, 8]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x7d30 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := add_r64_m64_effect_step 0x107d30 0x48 (by simp [RexWPrefix]) 1 (.base 6 (.d8 8)) (by decide) rfl rfl
    t stage.ready code1 ⟨rip, read1⟩
  change (addR64M64Effect 0x107d30 1 (.base 6 (.d8 8)) t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x7d34 (by decide))
  have r1_1 : t1.regValue .rcx = q.1 := by
    have he : t1.regValue .rcx = (addSpec (t.regValue .rcx) ((Operand.mem ((AddrMode.base 6 (.d8 8)).addr t 0x107d34) : Operand 64).read t)).1 := effect1.writes
    rw [r1_0, addr1] at he
    change t1.regValue .rcx = (addSpec a (memLoad t.external (s.regValue .rsi + 8) 64)).1 at he
    rw [mem1] at he
    exact he
  have cf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec (t.regValue .rcx) ((Operand.mem ((AddrMode.base 6 (.d8 8)).addr t 0x107d34) : Operand 64).read t)).2.CF := effect1.flags.1
    rw [r1_0, addr1] at he
    change (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec a (memLoad t.external (s.regValue .rsi + 8) 64)).2.CF at he
    rw [mem1] at he
    exact he
  have r13_1 : t1.regValue .r13 = 0 := (effect1.agrees.read (n := 64) (r := 13) (by simp [addR64M64Effect_components])).trans (zero)
  have code2 : CodeIn (codeRange 0x107d34 [65, 15, 146, 197]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x7d34 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := setcc_r8_rex_effect_step 0x107d34 0x41 0x92 0xc5 (by simp [RexPrefix]) (.inl rfl) (by decide)
    t1 ready1 code2 effect1.rip
  change (setccR8Effect 0x107d34 4 13 2 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x7d38 (by decide))
  have r13_2 : t2.regValue .r13 = e := by
    have he : t2.regValue .r13 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t1.RFLAGS).CF then 1 else 0) (t1.regValue .r13) := effect2.writes
    rw [cf1, r13_1, setb_zero] at he
    exact he
  have code3 : CodeIn (codeRange 0x107d38 [73, 199, 199, 255, 255, 255, 255]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x7d38 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := mov_r64_imm32_effect_step 0x107d38 0x49 0xc7 (by simp [RexWPrefix]) (by decide) (by decide) 0xffffffff
    t2 ready2 code3 effect2.rip
  change (movR64Imm32Effect 0x107d38 15 0xffffffff t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [movR64Imm32Effect_components]) (inProgram_of_textOffset 0x7d3f (by decide))
  have r15_3 : t3.regValue .r15 = 0xffffffffffffffff := by
    have he : t3.regValue .r15 = (0xffffffff : BitVec 32).signExtend 64 := effect3.writes
    exact he.trans (by decide +kernel)
  have r1_3 : t3.regValue .rcx = q.1 := (effect3.agrees.read (n := 64) (r := 1) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 1) (by simp [setccR8Effect_components])).trans (r1_1))
  have code4 : CodeIn (codeRange 0x107d3f [72, 137, 200]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x7d3f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x107d3f 0x48 0xc8 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x107d3f 0 1 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d42 (by decide))
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .rcx := effect4.writes
    rw [r1_3] at he
    exact he
  have r15_4 : t4.regValue .r15 = 0xffffffffffffffff := (effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans (r15_3)
  have code5 : CodeIn (codeRange 0x107d42 [73, 247, 231]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x7d42 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x107d42 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x107d42 15 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x7d45 (by decide))
  have r0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t5.regValue .rax = t4.regValue .rax * t4.regValue .r15 := effect5.writes.1
    rw [r0_4, r15_4] at he
    exact he
  have r2_5 : t5.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .r15) := effect5.writes.2
    rw [r0_4, r15_4] at he
    exact he
  have r1_5 : t5.regValue .rcx = q.1 := (effect5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_3))
  have code6 : CodeIn (codeRange 0x107d45 [72, 1, 200]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x7d45 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x107d45 0x48 0xc8 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x107d45 0 1 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x7d48 (by decide))
  have r0_6 : t6.regValue .rax = neg.1 := by
    have he : t6.regValue .rax = (addSpec (t5.regValue .rax) (t5.regValue .rcx)).1 := effect6.writes
    rw [r0_5, r1_5] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .rcx)).2.CF := effect6.flags.1
    rw [r0_5, r1_5] at he
    exact he
  have r13_6 : t6.regValue .r13 = e := (effect6.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 13) (by simp [movR64Imm32Effect_components])).trans (r13_2))))
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_5)
  have cb7 := carry_extract cf6
  have code7 : CodeIn (codeRange 0x107d48 [73, 17, 213]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x7d48 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x107d48 0x49 0xd5 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x107d48 13 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x7d4b (by decide))
  have r13_7 : t7.regValue .r13 = ec.1 := by
    have he : t7.regValue .r13 = (adcSpec (t6.regValue .r13) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [cb7, r13_6, r2_6] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = ec.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec (t6.regValue .r13) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).2.CF := effect7.flags.1
    rw [cb7, r13_6, r2_6] at he
    exact he
  have code8 : CodeIn (codeRange 0x107d4b [65, 188, 255, 255, 255, 255]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x7d4b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r32_imm32_rex_effect_step 0x107d4b 0x41 0xbc (by simp [RexNoWPrefix]) (by decide) 0xffffffff
    t7 ready7 code8 effect7.rip
  change (movR32Imm32Effect 0x107d4b 6 12 0xffffffff t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR32Imm32Effect_components]) (inProgram_of_textOffset 0x7d51 (by decide))
  have r12_8 : t8.regValue .r12 = 0xffffffff := by
    have he : t8.regValue .r12 = (0xffffffff : BitVec 32).setWidth 64 := effect8.writes
    exact he.trans (by decide +kernel)
  have r1_8 : t8.regValue .rcx = q.1 := (effect8.agrees.read (n := 64) (r := 1) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 1) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans (r1_5)))
  have code9 : CodeIn (codeRange 0x107d51 [72, 137, 200]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x7d51 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mov_r64_r64_effect_step 0x107d51 0x48 0xc8 (by simp [RexWPrefix]) (by decide)
    t8 ready8 code9 effect8.rip
  change (movR64R64Effect 0x107d51 0 1 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d54 (by decide))
  have r0_9 : t9.regValue .rax = q.1 := by
    have he : t9.regValue .rax = t8.regValue .rcx := effect9.writes
    rw [r1_8] at he
    exact he
  have r12_9 : t9.regValue .r12 = 0xffffffff := (effect9.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans (r12_8)
  have code10 : CodeIn (codeRange 0x107d54 [73, 247, 228]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x7d54 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mul_r64_effect_step 0x107d54 0x49 0xe4 (by simp [RexWPrefix]) (by decide) (by decide)
    t9 ready9 code10 effect9.rip
  change (mulR64Effect 0x107d54 12 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x7d57 (by decide))
  have r0_10 : t10.regValue .rax = q.1 * 0xffffffff := by
    have he : t10.regValue .rax = t9.regValue .rax * t9.regValue .r12 := effect10.writes.1
    rw [r0_9, r12_9] at he
    exact he
  have r2_10 : t10.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t10.regValue .rdx = mulHigh64 (t9.regValue .rax) (t9.regValue .r12) := effect10.writes.2
    rw [r0_9, r12_9] at he
    exact he
  have code11 : CodeIn (codeRange 0x107d57 [73, 137, 210]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x7d57 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x107d57 0x49 0xd2 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x107d57 10 2 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d5a (by decide))
  have r10_11 : t11.regValue .r10 = mulHigh64 q.1 0xffffffff := by
    have he : t11.regValue .r10 = t10.regValue .rdx := effect11.writes
    rw [r2_10] at he
    exact he
  have r0_11 : t11.regValue .rax = q.1 * 0xffffffff := (effect11.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_10)
  have code12 : CodeIn (codeRange 0x107d5a [73, 137, 192]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x7d5a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := mov_r64_r64_effect_step 0x107d5a 0x49 0xc0 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (movR64R64Effect 0x107d5a 8 0 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d5d (by decide))
  have r8_12 : t12.regValue .r8 = q.1 * 0xffffffff := by
    have he : t12.regValue .r8 = t11.regValue .rax := effect12.writes
    rw [r0_11] at he
    exact he
  have r11_12 : t12.regValue .r11 = b := (effect12.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 11) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 11) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 11) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans (rfl))))))))))))
  have code13 : CodeIn (codeRange 0x107d5d [77, 1, 216]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x7d5d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := add_r64_r64_effect_step 0x107d5d 0x4d 0xd8 (by simp [RexWPrefix]) (by decide)
    t12 ready12 code13 effect12.rip
  change (addR64R64Effect 0x107d5d 8 11 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x7d60 (by decide))
  have r8_13 : t13.regValue .r8 = l.1 := by
    have he : t13.regValue .r8 = (addSpec (t12.regValue .r8) (t12.regValue .r11)).1 := effect13.writes
    rw [r8_12, r11_12] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (addSpec (t12.regValue .r8) (t12.regValue .r11)).2.CF := effect13.flags.1
    rw [r8_12, r11_12] at he
    exact he
  have r10_13 : t13.regValue .r10 = mulHigh64 q.1 0xffffffff := (effect13.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_11))
  have cb14 := carry_extract cf13
  have code14 : CodeIn (codeRange 0x107d60 [73, 131, 210, 0]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x7d60 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := adc_r64_imm8_effect_step 0x107d60 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t13 ready13 code14 effect13.rip
  change (adcR64Imm8Effect 0x107d60 10 0 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x7d64 (by decide))
  have r10_14 : t14.regValue .r10 = h.1 := by
    have he : t14.regValue .r10 = (adcSpec (t13.regValue .r10) 0 (t13.RFLAGS.extractLsb' 0 1)).1 := effect14.writes
    rw [cb14, r10_13] at he
    exact he
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = h.2.CF := by
    have he : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (adcSpec (t13.regValue .r10) 0 (t13.RFLAGS.extractLsb' 0 1)).2.CF := effect14.flags.1
    rw [cb14, r10_13] at he
    exact he
  have r1_14 : t14.regValue .rcx = q.1 := (effect14.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_8))))))
  have code15 : CodeIn (codeRange 0x107d64 [72, 137, 200]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x7d64 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mov_r64_r64_effect_step 0x107d64 0x48 0xc8 (by simp [RexWPrefix]) (by decide)
    t14 ready14 code15 effect14.rip
  change (movR64R64Effect 0x107d64 0 1 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d67 (by decide))
  have r0_15 : t15.regValue .rax = q.1 := by
    have he : t15.regValue .rax = t14.regValue .rcx := effect15.writes
    rw [r1_14] at he
    exact he
  have r14_15 : t15.regValue .r14 = 0xffffffff00000001 := (effect15.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 14) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 14) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 14) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 14) (by simp [addR64M64Effect_components])).trans (constant)))))))))))))))
  have code16 : CodeIn (codeRange 0x107d67 [73, 247, 230]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x7d67 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mul_r64_effect_step 0x107d67 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)
    t15 ready15 code16 effect15.rip
  change (mulR64Effect 0x107d67 14 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x7d6a (by decide))
  have r0_16 : t16.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t16.regValue .rax = t15.regValue .rax * t15.regValue .r14 := effect16.writes.1
    rw [r0_15, r14_15] at he
    exact he
  have r2_16 : t16.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t16.regValue .rdx = mulHigh64 (t15.regValue .rax) (t15.regValue .r14) := effect16.writes.2
    rw [r0_15, r14_15] at he
    exact he
  have code17 : CodeIn (codeRange 0x107d6a [73, 137, 211]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x7d6a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mov_r64_r64_effect_step 0x107d6a 0x49 0xd3 (by simp [RexWPrefix]) (by decide)
    t16 ready16 code17 effect16.rip
  change (movR64R64Effect 0x107d6a 11 2 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d6d (by decide))
  have r11_17 : t17.regValue .r11 = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t17.regValue .r11 = t16.regValue .rdx := effect17.writes
    rw [r2_16] at he
    exact he
  have r0_17 : t17.regValue .rax = q.1 * 0xffffffff00000001 := (effect17.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_16)
  have code18 : CodeIn (codeRange 0x107d6d [72, 137, 193]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x7d6d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := mov_r64_r64_effect_step 0x107d6d 0x48 0xc1 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (movR64R64Effect 0x107d6d 1 0 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x7d70 (by decide))
  have r1_18 : t18.regValue .rcx = q.1 * 0xffffffff00000001 := by
    have he : t18.regValue .rcx = t17.regValue .rax := effect18.writes
    rw [r0_17] at he
    exact he
  have r3_18 : t18.regValue .rbx = d := (effect18.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 3) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 3) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 3) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 3) (by simp [addR64M64Effect_components])).trans (rfl))))))))))))))))))
  have code19 : CodeIn (codeRange 0x107d70 [72, 1, 217]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x7d70 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := add_r64_r64_effect_step 0x107d70 0x48 0xd9 (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (addR64R64Effect 0x107d70 1 3 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x7d73 (by decide))
  have r1_19 : t19.regValue .rcx = k.1 := by
    have he : t19.regValue .rcx = (addSpec (t18.regValue .rcx) (t18.regValue .rbx)).1 := effect19.writes
    rw [r1_18, r3_18] at he
    exact he
  have cf19 : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = (addSpec (t18.regValue .rcx) (t18.regValue .rbx)).2.CF := effect19.flags.1
    rw [r1_18, r3_18] at he
    exact he
  have r11_19 : t19.regValue .r11 = mulHigh64 q.1 0xffffffff00000001 := (effect19.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans (r11_17))
  have cb20 := carry_extract cf19
  have code20 : CodeIn (codeRange 0x107d73 [73, 131, 211, 0]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x7d73 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := adc_r64_imm8_effect_step 0x107d73 0x49 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t19 ready19 code20 effect19.rip
  change (adcR64Imm8Effect 0x107d73 11 0 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x7d77 (by decide))
  have r11_20 : t20.regValue .r11 = j.1 := by
    have he : t20.regValue .r11 = (adcSpec (t19.regValue .r11) 0 (t19.RFLAGS.extractLsb' 0 1)).1 := effect20.writes
    rw [cb20, r11_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = j.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (adcSpec (t19.regValue .r11) 0 (t19.RFLAGS.extractLsb' 0 1)).2.CF := effect20.flags.1
    rw [cb20, r11_19] at he
    exact he
  have r8_20 : t20.regValue .r8 = l.1 := (effect20.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_13)))))))
  have r13_20 : t20.regValue .r13 = ec.1 := (effect20.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 13) (by simp [movR32Imm32Effect_components])).trans (r13_7)))))))))))))
  have code21 : CodeIn (codeRange 0x107d77 [77, 1, 232]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x7d77 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := add_r64_r64_effect_step 0x107d77 0x4d 0xe8 (by simp [RexWPrefix]) (by decide)
    t20 ready20 code21 effect20.rip
  change (addR64R64Effect 0x107d77 8 13 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x7d7a (by decide))
  have r8_21 : t21.regValue .r8 = o0.1 := by
    have he : t21.regValue .r8 = (addSpec (t20.regValue .r8) (t20.regValue .r13)).1 := effect21.writes
    rw [r8_20, r13_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (addSpec (t20.regValue .r8) (t20.regValue .r13)).2.CF := effect21.flags.1
    rw [r8_20, r13_20] at he
    exact he
  have r10_21 : t21.regValue .r10 = h.1 := (effect21.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_14)))))))
  have r9_21 : t21.regValue .r9 = c := (effect21.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 9) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 9) (by simp [movR64Imm32Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 9) (by simp [setccR8Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 9) (by simp [addR64M64Effect_components])).trans (rfl)))))))))))))))))))))
  have cb22 := carry_extract cf21
  have code22 : CodeIn (codeRange 0x107d7a [77, 17, 202]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x7d7a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := adc_r64_r64_effect_step 0x107d7a 0x4d 0xca (by simp [RexWPrefix]) (by decide)
    t21 ready21 code22 effect21.rip
  change (adcR64R64Effect 0x107d7a 10 9 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x7d7d (by decide))
  have r10_22 : t22.regValue .r10 = o1.1 := by
    have he : t22.regValue .r10 = (adcSpec (t21.regValue .r10) (t21.regValue .r9) (t21.RFLAGS.extractLsb' 0 1)).1 := effect22.writes
    rw [cb22, r10_21, r9_21] at he
    exact he
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (adcSpec (t21.regValue .r10) (t21.regValue .r9) (t21.RFLAGS.extractLsb' 0 1)).2.CF := effect22.flags.1
    rw [cb22, r10_21, r9_21] at he
    exact he
  have r1_22 : t22.regValue .rcx = k.1 := (effect22.agrees.read (n := 64) (r := 1) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans (r1_19)))
  have cb23 := carry_extract cf22
  have code23 : CodeIn (codeRange 0x107d7d [72, 131, 209, 0]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x7d7d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_imm8_effect_step 0x107d7d 0x48 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64Imm8Effect 0x107d7d 1 0 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x7d81 (by decide))
  have r1_23 : t23.regValue .rcx = o2.1 := by
    have he : t23.regValue .rcx = (adcSpec (t22.regValue .rcx) 0 (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [cb23, r1_22] at he
    exact he
  have cf23 : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = (adcSpec (t22.regValue .rcx) 0 (t22.RFLAGS.extractLsb' 0 1)).2.CF := effect23.flags.1
    rw [cb23, r1_22] at he
    exact he
  have r11_23 : t23.regValue .r11 = j.1 := (effect23.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans (r11_20)))
  have cb24 := carry_extract cf23
  have code24 : CodeIn (codeRange 0x107d81 [73, 131, 211, 0]) t23 :=
    programText_slice (programLoaded_codeIn stage23.loaded) 0x7d81 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t24, step24, ready24, effect24⟩ := adc_r64_imm8_effect_step 0x107d81 0x49 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t23 ready23 code24 effect23.rip
  change (adcR64Imm8Effect 0x107d81 11 0 t23).Holds t23 t24 at effect24
  have stage24 := stage23.step_registers pre step24 ready24 effect24
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x7d85 (by decide))
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
  have r1_24 : t24.regValue .rcx = o2.1 := (effect24.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans (r1_23)
  have r14_24 : t24.regValue .r14 = 0xffffffff00000001 := (effect24.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r14_15)))))))))
  have r15_24 : t24.regValue .r15 = 0xffffffffffffffff := (effect24.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 15) (by simp [movR32Imm32Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans (r15_3)))))))))))))))))))))
  have r12_24 : t24.regValue .r12 = 0xffffffff := (effect24.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans (r12_8))))))))))))))))
  have ag1 : AgreesExcept inputRegisters t t1 := effect1.agrees.mono (by simp [addR64M64Effect_components, inputRegisters])
  have ag2 : AgreesExcept inputRegisters t1 t2 := effect2.agrees.mono (by simp [setccR8Effect_components, inputRegisters])
  have ag3 : AgreesExcept inputRegisters t2 t3 := effect3.agrees.mono (by simp [movR64Imm32Effect_components, inputRegisters])
  have ag4 : AgreesExcept inputRegisters t3 t4 := effect4.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag5 : AgreesExcept inputRegisters t4 t5 := effect5.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have ag6 : AgreesExcept inputRegisters t5 t6 := effect6.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have ag7 : AgreesExcept inputRegisters t6 t7 := effect7.agrees.mono (by simp [adcR64R64Effect_components, inputRegisters])
  have ag8 : AgreesExcept inputRegisters t7 t8 := effect8.agrees.mono (by simp [movR32Imm32Effect_components, inputRegisters])
  have ag9 : AgreesExcept inputRegisters t8 t9 := effect9.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag10 : AgreesExcept inputRegisters t9 t10 := effect10.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have ag11 : AgreesExcept inputRegisters t10 t11 := effect11.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag12 : AgreesExcept inputRegisters t11 t12 := effect12.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag13 : AgreesExcept inputRegisters t12 t13 := effect13.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have ag14 : AgreesExcept inputRegisters t13 t14 := effect14.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have ag15 : AgreesExcept inputRegisters t14 t15 := effect15.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag16 : AgreesExcept inputRegisters t15 t16 := effect16.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have ag17 : AgreesExcept inputRegisters t16 t17 := effect17.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag18 : AgreesExcept inputRegisters t17 t18 := effect18.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have ag19 : AgreesExcept inputRegisters t18 t19 := effect19.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have ag20 : AgreesExcept inputRegisters t19 t20 := effect20.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have ag21 : AgreesExcept inputRegisters t20 t21 := effect21.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have ag22 : AgreesExcept inputRegisters t21 t22 := effect22.agrees.mono (by simp [adcR64R64Effect_components, inputRegisters])
  have ag23 : AgreesExcept inputRegisters t22 t23 := effect23.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have ag24 : AgreesExcept inputRegisters t23 t24 := effect24.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  refine ⟨t24, stage24, effect24.rip, ?_, r14_24, r15_24, r12_24, (agrees_trans ag1 (agrees_trans ag2 (agrees_trans ag3 (agrees_trans ag4 (agrees_trans ag5 (agrees_trans ag6 (agrees_trans ag7 (agrees_trans ag8 (agrees_trans ag9 (agrees_trans ag10 (agrees_trans ag11 (agrees_trans ag12 (agrees_trans ag13 (agrees_trans ag14 (agrees_trans ag15 (agrees_trans ag16 (agrees_trans ag17 (agrees_trans ag18 (agrees_trans ag19 (agrees_trans ag20 (agrees_trans ag21 (agrees_trans ag22 (agrees_trans ag23 ag24)))))))))))))))))))))))⟩
  change (t24.regValue .r8, t24.regValue .r10, t24.regValue .rcx, t24.regValue .r11) = (o0.1, o1.1, o2.1, o3.1)
  rw [r8_24, r10_24, r1_24, r11_24]

end P256.Proofs.Ecdh.Normalize.Conversion
