import P256.Proofs.Ecdh.Normalize.Conversion.State

set_option autoImplicit false

open P256.Proofs.Common.Instructions
  (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step
   mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry
  (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect
   adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb
  (setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)
open P256.Proofs.Program
  (inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Decode

open P256.Proofs.Ecdh.Normalize.Conversion (Stage registers inputRegisters agrees_trans read_mem_of_agrees)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1Serialize.Conversion hiding Stage
open P256.Proofs.Program

theorem round3 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : ¬ InProgram boundary.rip) (stage : Stage s start t boundary)
    (source : t.regValue .rsi = s.regValue .rsi)
    (rip : t.RIP = 0x114310) (constant : t.regValue .r14 = 0xffffffff00000001)
    (mask : t.regValue .r15 = 0xffffffffffffffff)
    (half : t.regValue .r12 = 0xffffffff)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x114355 ∧
      (u.regValue .rsi, u.regValue .rcx, u.regValue .rax, u.regValue .rdx) =
        Montgomery.compilerRoundBV (t.regValue .r9) (t.regValue .rbx) (t.regValue .r8) (t.regValue .r10)
          ((Operand.mem (s.regValue .rsi + 24) : Operand 64).read t) ∧
      u.regValue .r14 = 0xffffffff00000001 ∧
      u.regValue .r15 = 0xffffffffffffffff ∧
      u.regValue .r12 = 0xffffffff ∧
      AgreesExcept registers t u := by
  let a := t.regValue .r9
  let b := t.regValue .rbx
  let c := t.regValue .r8
  let d := t.regValue .r10
  let z := (Operand.mem (s.regValue .rsi + 24) : Operand 64).read t
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
  have r9_0 : t.regValue .r9 = a := rfl
  have r3_0 : t.regValue .rbx = b := rfl
  have r8_0 : t.regValue .r8 = c := rfl
  have r10_0 : t.regValue .r10 = d := rfl
  have code1 : CodeIn (codeRange 0x114310 [69, 49, 219]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x14310 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := xor_r32_r32_rex_effect_step 0x114310 0x45 0xdb (by simp [RexNoWPrefix]) (by decide)
    t stage.ready code1 rip
  change (xorR32R32Effect 0x114310 3 11 11 t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x14313 (by decide))
  have r11_1 : t1.regValue .r11 = 0 := by
    have he : t1.regValue .r11 = (((Operand.reg 11 : Operand 32).read t) ^^^
      ((Operand.reg 11 : Operand 32).read t)).setWidth 64 := effect1.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he.trans (by rfl)
  have r9_1 : t1.regValue .r9 = a := (effect1.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans (r9_0)
  have addr2 : (AddrMode.base 6 (.d8 24)).addr t1 0x114317 = s.regValue .rsi + 24 := by
    change t1.regValue .rsi + 24 = _
    rw [show t1.regValue .rsi = t.regValue .rsi from effect1.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components]), source]
  have read2 : MemReadable t1 ((AddrMode.base 6 (.d8 24)).addr t1 0x114317) 8 := by
    rw [addr2]
    exact stage1.readable_offset 24 (by decide)
  have mem2 : t1.external = t.external :=
    effect1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])
  have code2 : CodeIn (codeRange 0x114313 [76, 3, 78, 24]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x14313 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := add_r64_m64_effect_step 0x114313 0x4c (by simp [RexWPrefix]) 1 (.base 6 (.d8 24)) (by decide) rfl rfl
    t1 ready1 code2 ⟨effect1.rip, read2⟩
  change (addR64M64Effect 0x114313 9 (.base 6 (.d8 24)) t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x14317 (by decide))
  have r9_2 : t2.regValue .r9 = q.1 := by
    have he : t2.regValue .r9 = (addSpec (t1.regValue .r9) ((Operand.mem ((AddrMode.base 6 (.d8 24)).addr t1 0x114317) : Operand 64).read t1)).1 := effect2.writes
    rw [r9_1, addr2] at he
    change t2.regValue .r9 = (addSpec a (memLoad t1.external (s.regValue .rsi + 24) 64)).1 at he
    rw [mem2] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec (t1.regValue .r9) ((Operand.mem ((AddrMode.base 6 (.d8 24)).addr t1 0x114317) : Operand 64).read t1)).2.CF := effect2.flags.1
    rw [r9_1, addr2] at he
    change (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec a (memLoad t1.external (s.regValue .rsi + 24) 64)).2.CF at he
    rw [mem2] at he
    exact he
  have code3 : CodeIn (codeRange 0x114317 [65, 15, 146, 195]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x14317 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := setcc_r8_rex_effect_step 0x114317 0x41 0x92 0xc3 (by simp [RexPrefix]) (.inl rfl) (by decide)
    t2 ready2 code3 effect2.rip
  change (setccR8Effect 0x114317 4 11 2 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x1431b (by decide))
  have r11_2 : t2.regValue .r11 = 0 := (effect2.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans (r11_1)
  have r11_3 : t3.regValue .r11 = e := by
    have he : t3.regValue .r11 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) (t2.regValue .r11) := effect3.writes
    rw [cf2, r11_2, setb_zero] at he
    exact he
  have code4 : CodeIn (codeRange 0x11431b [76, 137, 200]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x1431b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x11431b 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x11431b 0 9 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x1431e (by decide))
  have r9_3 : t3.regValue .r9 = q.1 := (effect3.agrees.read (n := 64) (r := 9) (by simp [setccR8Effect_components])).trans (r9_2)
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .r9 := effect4.writes
    rw [r9_3] at he
    exact he
  have code5 : CodeIn (codeRange 0x11431e [73, 247, 231]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x1431e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x11431e 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x11431e 15 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x14321 (by decide))
  have r15_4 : t4.regValue .r15 = 0xffffffffffffffff := (effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 15) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 15) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 15) (by simp [xorR32R32Effect_components])).trans (mask))))
  have r0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t5.regValue .rax = t4.regValue .rax * t4.regValue .r15 := effect5.writes.1
    rw [r0_4, r15_4] at he
    exact he
  have r2_5 : t5.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .r15) := effect5.writes.2
    rw [r0_4, r15_4] at he
    exact he
  have code6 : CodeIn (codeRange 0x114321 [76, 1, 200]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x14321 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x114321 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x114321 0 9 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x14324 (by decide))
  have r9_5 : t5.regValue .r9 = q.1 := (effect5.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r9_3))
  have r0_6 : t6.regValue .rax = neg.1 := by
    have he : t6.regValue .rax = (addSpec (t5.regValue .rax) (t5.regValue .r9)).1 := effect6.writes
    rw [r0_5, r9_5] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .r9)).2.CF := effect6.flags.1
    rw [r0_5, r9_5] at he
    exact he
  have code7 : CodeIn (codeRange 0x114324 [73, 17, 211]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x14324 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x114324 0x49 0xd3 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x114324 11 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x14327 (by decide))
  have r11_6 : t6.regValue .r11 = e := (effect6.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans (r11_3)))
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_5)
  have cb7 := carry_extract cf6
  have r11_7 : t7.regValue .r11 = ec.1 := by
    have he : t7.regValue .r11 = (adcSpec (t6.regValue .r11) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [cb7, r11_6, r2_6] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = ec.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec (t6.regValue .r11) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).2.CF := effect7.flags.1
    rw [cb7, r11_6, r2_6] at he
    exact he
  have code8 : CodeIn (codeRange 0x114327 [76, 137, 200]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x14327 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r64_r64_effect_step 0x114327 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x114327 0 9 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x1432a (by decide))
  have r9_7 : t7.regValue .r9 = q.1 := (effect7.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans (r9_5))
  have r0_8 : t8.regValue .rax = q.1 := by
    have he : t8.regValue .rax = t7.regValue .r9 := effect8.writes
    rw [r9_7] at he
    exact he
  have code9 : CodeIn (codeRange 0x11432a [73, 247, 228]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x1432a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mul_r64_effect_step 0x11432a 0x49 0xe4 (by simp [RexWPrefix]) (by decide) (by decide)
    t8 ready8 code9 effect8.rip
  change (mulR64Effect 0x11432a 12 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x1432d (by decide))
  have r12_8 : t8.regValue .r12 = 0xffffffff := (effect8.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 12) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 12) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 12) (by simp [xorR32R32Effect_components])).trans (half))))))))
  have r0_9 : t9.regValue .rax = q.1 * 0xffffffff := by
    have he : t9.regValue .rax = t8.regValue .rax * t8.regValue .r12 := effect9.writes.1
    rw [r0_8, r12_8] at he
    exact he
  have r2_9 : t9.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t9.regValue .rdx = mulHigh64 (t8.regValue .rax) (t8.regValue .r12) := effect9.writes.2
    rw [r0_8, r12_8] at he
    exact he
  have code10 : CodeIn (codeRange 0x11432d [72, 137, 209]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x1432d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mov_r64_r64_effect_step 0x11432d 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
    t9 ready9 code10 effect9.rip
  change (movR64R64Effect 0x11432d 1 2 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x14330 (by decide))
  have r1_10 : t10.regValue .rcx = mulHigh64 q.1 0xffffffff := by
    have he : t10.regValue .rcx = t9.regValue .rdx := effect10.writes
    rw [r2_9] at he
    exact he
  have code11 : CodeIn (codeRange 0x114330 [72, 137, 198]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x14330 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x114330 0x48 0xc6 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x114330 6 0 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x14333 (by decide))
  have r0_10 : t10.regValue .rax = q.1 * 0xffffffff := (effect10.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_9)
  have r6_11 : t11.regValue .rsi = q.1 * 0xffffffff := by
    have he : t11.regValue .rsi = t10.regValue .rax := effect11.writes
    rw [r0_10] at he
    exact he
  have code12 : CodeIn (codeRange 0x114333 [72, 1, 222]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x14333 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := add_r64_r64_effect_step 0x114333 0x48 0xde (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (addR64R64Effect 0x114333 6 3 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x14336 (by decide))
  have r3_11 : t11.regValue .rbx = b := (effect11.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 3) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 3) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 3) (by simp [xorR32R32Effect_components])).trans (r3_0)))))))))))
  have r6_12 : t12.regValue .rsi = l.1 := by
    have he : t12.regValue .rsi = (addSpec (t11.regValue .rsi) (t11.regValue .rbx)).1 := effect12.writes
    rw [r6_11, r3_11] at he
    exact he
  have cf12 : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = (addSpec (t11.regValue .rsi) (t11.regValue .rbx)).2.CF := effect12.flags.1
    rw [r6_11, r3_11] at he
    exact he
  have code13 : CodeIn (codeRange 0x114336 [72, 131, 209, 0]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x14336 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := adc_r64_imm8_effect_step 0x114336 0x48 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t12 ready12 code13 effect12.rip
  change (adcR64Imm8Effect 0x114336 1 0 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x1433a (by decide))
  have r1_12 : t12.regValue .rcx = mulHigh64 q.1 0xffffffff := (effect12.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_10))
  have cb13 := carry_extract cf12
  have r1_13 : t13.regValue .rcx = h.1 := by
    have he : t13.regValue .rcx = (adcSpec (t12.regValue .rcx) (0) (t12.RFLAGS.extractLsb' 0 1)).1 := effect13.writes
    rw [cb13, r1_12] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = h.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (adcSpec (t12.regValue .rcx) (0) (t12.RFLAGS.extractLsb' 0 1)).2.CF := effect13.flags.1
    rw [cb13, r1_12] at he
    exact he
  have code14 : CodeIn (codeRange 0x11433a [76, 137, 200]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x1433a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := mov_r64_r64_effect_step 0x11433a 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t13 ready13 code14 effect13.rip
  change (movR64R64Effect 0x11433a 0 9 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x1433d (by decide))
  have r9_13 : t13.regValue .r9 = q.1 := (effect13.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r9_7))))))
  have r0_14 : t14.regValue .rax = q.1 := by
    have he : t14.regValue .rax = t13.regValue .r9 := effect14.writes
    rw [r9_13] at he
    exact he
  have code15 : CodeIn (codeRange 0x11433d [73, 247, 230]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x1433d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mul_r64_effect_step 0x11433d 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)
    t14 ready14 code15 effect14.rip
  change (mulR64Effect 0x11433d 14 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x14340 (by decide))
  have r14_14 : t14.regValue .r14 = 0xffffffff00000001 := (effect14.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 14) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 14) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (constant))))))))))))))
  have r0_15 : t15.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t15.regValue .rax = t14.regValue .rax * t14.regValue .r14 := effect15.writes.1
    rw [r0_14, r14_14] at he
    exact he
  have r2_15 : t15.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t15.regValue .rdx = mulHigh64 (t14.regValue .rax) (t14.regValue .r14) := effect15.writes.2
    rw [r0_14, r14_14] at he
    exact he
  have code16 : CodeIn (codeRange 0x114340 [76, 1, 208]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x14340 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := add_r64_r64_effect_step 0x114340 0x4c 0xd0 (by simp [RexWPrefix]) (by decide)
    t15 ready15 code16 effect15.rip
  change (addR64R64Effect 0x114340 0 10 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x14343 (by decide))
  have r10_15 : t15.regValue .r10 = d := (effect15.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (r10_0)))))))))))))))
  have r0_16 : t16.regValue .rax = k.1 := by
    have he : t16.regValue .rax = (addSpec (t15.regValue .rax) (t15.regValue .r10)).1 := effect16.writes
    rw [r0_15, r10_15] at he
    exact he
  have cf16 : (StatusFlags.ofRFLAGS t16.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t16.RFLAGS).CF = (addSpec (t15.regValue .rax) (t15.regValue .r10)).2.CF := effect16.flags.1
    rw [r0_15, r10_15] at he
    exact he
  have code17 : CodeIn (codeRange 0x114343 [72, 131, 210, 0]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x14343 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := adc_r64_imm8_effect_step 0x114343 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t16 ready16 code17 effect16.rip
  change (adcR64Imm8Effect 0x114343 2 0 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x14347 (by decide))
  have r2_16 : t16.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := (effect16.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_15)
  have cb17 := carry_extract cf16
  have r2_17 : t17.regValue .rdx = j.1 := by
    have he : t17.regValue .rdx = (adcSpec (t16.regValue .rdx) (0) (t16.RFLAGS.extractLsb' 0 1)).1 := effect17.writes
    rw [cb17, r2_16] at he
    exact he
  have cf17 : (StatusFlags.ofRFLAGS t17.RFLAGS).CF = j.2.CF := by
    have he : (StatusFlags.ofRFLAGS t17.RFLAGS).CF = (adcSpec (t16.regValue .rdx) (0) (t16.RFLAGS.extractLsb' 0 1)).2.CF := effect17.flags.1
    rw [cb17, r2_16] at he
    exact he
  have code18 : CodeIn (codeRange 0x114347 [76, 1, 222]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x14347 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := add_r64_r64_effect_step 0x114347 0x4c 0xde (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (addR64R64Effect 0x114347 6 11 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x1434a (by decide))
  have r6_17 : t17.regValue .rsi = l.1 := (effect17.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans (r6_12)))))
  have r11_17 : t17.regValue .r11 = ec.1 := (effect17.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans (r11_7))))))))))
  have r6_18 : t18.regValue .rsi = o0.1 := by
    have he : t18.regValue .rsi = (addSpec (t17.regValue .rsi) (t17.regValue .r11)).1 := effect18.writes
    rw [r6_17, r11_17] at he
    exact he
  have cf18 : (StatusFlags.ofRFLAGS t18.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t18.RFLAGS).CF = (addSpec (t17.regValue .rsi) (t17.regValue .r11)).2.CF := effect18.flags.1
    rw [r6_17, r11_17] at he
    exact he
  have code19 : CodeIn (codeRange 0x11434a [76, 17, 193]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x1434a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := adc_r64_r64_effect_step 0x11434a 0x4c 0xc1 (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (adcR64R64Effect 0x11434a 1 8 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x1434d (by decide))
  have r1_18 : t18.regValue .rcx = h.1 := (effect18.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_13)))))
  have r8_18 : t18.regValue .r8 = c := (effect18.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 8) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans (r8_0))))))))))))))))))
  have cb19 := carry_extract cf18
  have r1_19 : t19.regValue .rcx = o1.1 := by
    have he : t19.regValue .rcx = (adcSpec (t18.regValue .rcx) (t18.regValue .r8) (t18.RFLAGS.extractLsb' 0 1)).1 := effect19.writes
    rw [cb19, r1_18, r8_18] at he
    exact he
  have cf19 : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = (adcSpec (t18.regValue .rcx) (t18.regValue .r8) (t18.RFLAGS.extractLsb' 0 1)).2.CF := effect19.flags.1
    rw [cb19, r1_18, r8_18] at he
    exact he
  have code20 : CodeIn (codeRange 0x11434d [72, 131, 208, 0]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x1434d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := adc_r64_imm8_effect_step 0x11434d 0x48 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t19 ready19 code20 effect19.rip
  change (adcR64Imm8Effect 0x11434d 0 0 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x14351 (by decide))
  have r0_19 : t19.regValue .rax = k.1 := (effect19.agrees.read (n := 64) (r := 0) (by simp [adcR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 0) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 0) (by simp [adcR64Imm8Effect_components])).trans (r0_16)))
  have cb20 := carry_extract cf19
  have r0_20 : t20.regValue .rax = o2.1 := by
    have he : t20.regValue .rax = (adcSpec (t19.regValue .rax) (0) (t19.RFLAGS.extractLsb' 0 1)).1 := effect20.writes
    rw [cb20, r0_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (adcSpec (t19.regValue .rax) (0) (t19.RFLAGS.extractLsb' 0 1)).2.CF := effect20.flags.1
    rw [cb20, r0_19] at he
    exact he
  have code21 : CodeIn (codeRange 0x114351 [72, 131, 210, 0]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x14351 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := adc_r64_imm8_effect_step 0x114351 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t20 ready20 code21 effect20.rip
  change (adcR64Imm8Effect 0x114351 2 0 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x14355 (by decide))
  have r2_20 : t20.regValue .rdx = j.1 := (effect20.agrees.read (n := 64) (r := 2) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 2) (by simp [adcR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_17)))
  have cb21 := carry_extract cf20
  have r2_21 : t21.regValue .rdx = o3.1 := by
    have he : t21.regValue .rdx = (adcSpec (t20.regValue .rdx) (0) (t20.RFLAGS.extractLsb' 0 1)).1 := effect21.writes
    rw [cb21, r2_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = o3.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (adcSpec (t20.regValue .rdx) (0) (t20.RFLAGS.extractLsb' 0 1)).2.CF := effect21.flags.1
    rw [cb21, r2_20] at he
    exact he
  have r6_21 : t21.regValue .rsi = o0.1 := (effect21.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans (r6_18)))
  have r1_21 : t21.regValue .rcx = o1.1 := (effect21.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans (r1_19))
  have r0_21 : t21.regValue .rax = o2.1 := (effect21.agrees.read (n := 64) (r := 0) (by simp [adcR64Imm8Effect_components])).trans (r0_20)
  have r14_21 : t21.regValue .r14 = 0xffffffff00000001 := (effect21.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r14_14)))))))
  have r15_21 : t21.regValue .r15 = 0xffffffffffffffff := (effect21.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans (r15_4)))))))))))))))))
  have r12_21 : t21.regValue .r12 = 0xffffffff := (effect21.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans (r12_8)))))))))))))
  have ag1 : AgreesExcept registers t t1 :=
    effect1.agrees.mono (by simp [xorR32R32Effect_components, registers])
  have ag2 : AgreesExcept registers t1 t2 :=
    effect2.agrees.mono (by simp [addR64M64Effect_components, registers])
  have ag3 : AgreesExcept registers t2 t3 :=
    effect3.agrees.mono (by simp [setccR8Effect_components, registers])
  have ag4 : AgreesExcept registers t3 t4 :=
    effect4.agrees.mono (by simp [movR64R64Effect_components, registers])
  have ag5 : AgreesExcept registers t4 t5 :=
    effect5.agrees.mono (by simp [mulR64Effect_components, registers])
  have ag6 : AgreesExcept registers t5 t6 :=
    effect6.agrees.mono (by simp [addR64R64Effect_components, registers])
  have ag7 : AgreesExcept registers t6 t7 :=
    effect7.agrees.mono (by simp [adcR64R64Effect_components, registers])
  have ag8 : AgreesExcept registers t7 t8 :=
    effect8.agrees.mono (by simp [movR64R64Effect_components, registers])
  have ag9 : AgreesExcept registers t8 t9 :=
    effect9.agrees.mono (by simp [mulR64Effect_components, registers])
  have ag10 : AgreesExcept registers t9 t10 :=
    effect10.agrees.mono (by simp [movR64R64Effect_components, registers])
  have ag11 : AgreesExcept registers t10 t11 :=
    effect11.agrees.mono (by simp [movR64R64Effect_components, registers])
  have ag12 : AgreesExcept registers t11 t12 :=
    effect12.agrees.mono (by simp [addR64R64Effect_components, registers])
  have ag13 : AgreesExcept registers t12 t13 :=
    effect13.agrees.mono (by simp [adcR64Imm8Effect_components, registers])
  have ag14 : AgreesExcept registers t13 t14 :=
    effect14.agrees.mono (by simp [movR64R64Effect_components, registers])
  have ag15 : AgreesExcept registers t14 t15 :=
    effect15.agrees.mono (by simp [mulR64Effect_components, registers])
  have ag16 : AgreesExcept registers t15 t16 :=
    effect16.agrees.mono (by simp [addR64R64Effect_components, registers])
  have ag17 : AgreesExcept registers t16 t17 :=
    effect17.agrees.mono (by simp [adcR64Imm8Effect_components, registers])
  have ag18 : AgreesExcept registers t17 t18 :=
    effect18.agrees.mono (by simp [addR64R64Effect_components, registers])
  have ag19 : AgreesExcept registers t18 t19 :=
    effect19.agrees.mono (by simp [adcR64R64Effect_components, registers])
  have ag20 : AgreesExcept registers t19 t20 :=
    effect20.agrees.mono (by simp [adcR64Imm8Effect_components, registers])
  have ag21 : AgreesExcept registers t20 t21 :=
    effect21.agrees.mono (by simp [adcR64Imm8Effect_components, registers])
  refine ⟨t21, stage21, effect21.rip, ?_, r14_21, r15_21, r12_21, agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (ag1) ag2) ag3) ag4) ag5) ag6) ag7) ag8) ag9) ag10) ag11) ag12) ag13) ag14) ag15) ag16) ag17) ag18) ag19) ag20) ag21⟩
  change (t21.regValue .rsi, t21.regValue .rcx, t21.regValue .rax, t21.regValue .rdx) = (o0.1, o1.1, o2.1, o3.1)
  rw [r6_21, r1_21, r0_21, r2_21]

end P256.Proofs.Field.Decode
