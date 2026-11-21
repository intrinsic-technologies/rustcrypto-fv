import P256.Proofs.Ecdh.Normalize.Conversion.State

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_rex_effect_step)
open P256.Proofs.Program (inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Decode

open P256.Proofs.Ecdh.Normalize.Conversion (Stage registers inputRegisters agrees_trans read_mem_of_agrees)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Sec1Serialize.Conversion hiding Stage
open P256.Proofs.Program

theorem round2 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : ¬ InProgram boundary.rip) (stage : Stage s start t boundary)
    (source : t.regValue .rsi = s.regValue .rsi)
    (rip : t.RIP = 0x1142c5) (constant : t.regValue .r14 = 0xffffffff00000001)
    (mask : t.regValue .r15 = 0xffffffffffffffff)
    (half : t.regValue .r12 = 0xffffffff)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x114310 ∧
      (u.regValue .r9, u.regValue .rbx, u.regValue .r8, u.regValue .r10) =
        Montgomery.compilerRoundBV (t.regValue .r8) (t.regValue .r10) (t.regValue .rcx) (t.regValue .r11)
          ((Operand.mem (s.regValue .rsi + 16) : Operand 64).read t) ∧
      u.regValue .r14 = 0xffffffff00000001 ∧
      u.regValue .r15 = 0xffffffffffffffff ∧
      u.regValue .r12 = 0xffffffff ∧
      AgreesExcept inputRegisters t u := by
  let a := t.regValue .r8
  let b := t.regValue .r10
  let c := t.regValue .rcx
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
  have code1 : CodeIn (codeRange 0x1142c5 [69, 49, 237]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x142c5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := xor_r32_r32_rex_effect_step 0x1142c5 0x45 0xed (by simp [RexNoWPrefix]) (by decide)
    t stage.ready code1 rip
  change (xorR32R32Effect 0x1142c5 3 13 13 t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x142c8 (by decide))
  have r13_1 : t1.regValue .r13 = 0 := by
    have he : t1.regValue .r13 = (((Operand.reg 13 : Operand 32).read t) ^^^ ((Operand.reg 13 : Operand 32).read t)).setWidth 64 := effect1.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he.trans (by rfl)
  have ag1 : AgreesExcept inputRegisters t t1 :=
    effect1.agrees.mono (by simp [xorR32R32Effect_components, inputRegisters])
  have r8_1 : t1.regValue .r8 = a := (effect1.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans (rfl)
  have addr2 : (AddrMode.base 6 (.d8 16)).addr t1 0x1142cc = s.regValue .rsi + 16 := by
    change t1.regValue .rsi + 16 = _
    rw [show t1.regValue .rsi = t.regValue .rsi from effect1.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components]), source]
  have read2 : MemReadable t1 ((AddrMode.base 6 (.d8 16)).addr t1 0x1142cc) 8 := by
    rw [addr2]
    exact stage1.readable_offset 16 (by decide)
  have mem2 : t1.external = t.external :=
    effect1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])
  have code2 : CodeIn (codeRange 0x1142c8 [76, 3, 70, 16]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x142c8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := add_r64_m64_effect_step 0x1142c8 0x4c (by simp [RexWPrefix]) 0 (.base 6 (.d8 16)) (by decide) rfl rfl
    t1 ready1 code2 ⟨effect1.rip, read2⟩
  change (addR64M64Effect 0x1142c8 8 (.base 6 (.d8 16)) t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x142cc (by decide))
  have r8_2 : t2.regValue .r8 = q.1 := by
    have he : t2.regValue .r8 = (addSpec (t1.regValue .r8) ((Operand.mem ((AddrMode.base 6 (.d8 16)).addr t1 0x1142cc) : Operand 64).read t1)).1 := effect2.writes
    rw [r8_1, addr2] at he
    change t2.regValue .r8 = (addSpec a (memLoad t1.external (s.regValue .rsi + 16) 64)).1 at he
    rw [mem2] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec (t1.regValue .r8) ((Operand.mem ((AddrMode.base 6 (.d8 16)).addr t1 0x1142cc) : Operand 64).read t1)).2.CF := effect2.flags.1
    rw [r8_1, addr2] at he
    change (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec a (memLoad t1.external (s.regValue .rsi + 16) 64)).2.CF at he
    rw [mem2] at he
    exact he
  have ag2 : AgreesExcept inputRegisters t1 t2 :=
    effect2.agrees.mono (by simp [addR64M64Effect_components, inputRegisters])
  have code3 : CodeIn (codeRange 0x1142cc [65, 15, 146, 197]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x142cc _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := setcc_r8_rex_effect_step 0x1142cc 0x41 0x92 0xc5 (by simp [RexPrefix]) (.inl rfl) (by decide)
    t2 ready2 code3 effect2.rip
  change (setccR8Effect 0x1142cc 4 13 2 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x142d0 (by decide))
  have r13_2 : t2.regValue .r13 = 0 := (effect2.agrees.read (n := 64) (r := 13) (by simp [addR64M64Effect_components])).trans (r13_1)
  have r13_3 : t3.regValue .r13 = e := by
    have he : t3.regValue .r13 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) (t2.regValue .r13) := effect3.writes
    rw [cf2, r13_2, setb_zero] at he
    exact he
  have ag3 : AgreesExcept inputRegisters t2 t3 :=
    effect3.agrees.mono (by simp [setccR8Effect_components, inputRegisters])
  have r8_3 : t3.regValue .r8 = q.1 := (effect3.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans (r8_2)
  have code4 : CodeIn (codeRange 0x1142d0 [76, 137, 192]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x142d0 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x1142d0 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x1142d0 0 8 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142d3 (by decide))
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .r8 := effect4.writes
    rw [r8_3] at he
    exact he
  have ag4 : AgreesExcept inputRegisters t3 t4 :=
    effect4.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r15_4 : t4.regValue .r15 = 0xffffffffffffffff := (effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 15) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 15) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 15) (by simp [xorR32R32Effect_components])).trans (mask))))
  have code5 : CodeIn (codeRange 0x1142d3 [73, 247, 231]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x142d3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x1142d3 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x1142d3 15 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x142d6 (by decide))
  have r0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t5.regValue .rax = t4.regValue .rax * t4.regValue .r15 := effect5.writes.1
    rw [r0_4, r15_4] at he
    exact he
  have r2_5 : t5.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .r15) := effect5.writes.2
    rw [r0_4, r15_4] at he
    exact he
  have ag5 : AgreesExcept inputRegisters t4 t5 :=
    effect5.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have r8_5 : t5.regValue .r8 = q.1 := (effect5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_3))
  have code6 : CodeIn (codeRange 0x1142d6 [76, 1, 192]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x142d6 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x1142d6 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x1142d6 0 8 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x142d9 (by decide))
  have r0_6 : t6.regValue .rax = neg.1 := by
    have he : t6.regValue .rax = (addSpec (t5.regValue .rax) (t5.regValue .r8)).1 := effect6.writes
    rw [r0_5, r8_5] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .r8)).2.CF := effect6.flags.1
    rw [r0_5, r8_5] at he
    exact he
  have ag6 : AgreesExcept inputRegisters t5 t6 :=
    effect6.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have r13_6 : t6.regValue .r13 = e := (effect6.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans (r13_3)))
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_5)
  have cb7 := carry_extract cf6
  have code7 : CodeIn (codeRange 0x1142d9 [73, 17, 213]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x142d9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x1142d9 0x49 0xd5 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x1142d9 13 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x142dc (by decide))
  have r13_7 : t7.regValue .r13 = ec.1 := by
    have he : t7.regValue .r13 = (adcSpec (t6.regValue .r13) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [cb7, r13_6, r2_6] at he
    exact he
  have ag7 : AgreesExcept inputRegisters t6 t7 :=
    effect7.agrees.mono (by simp [adcR64R64Effect_components, inputRegisters])
  have r8_7 : t7.regValue .r8 = q.1 := (effect7.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans (r8_5))
  have code8 : CodeIn (codeRange 0x1142dc [76, 137, 192]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x142dc _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r64_r64_effect_step 0x1142dc 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x1142dc 0 8 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142df (by decide))
  have r0_8 : t8.regValue .rax = q.1 := by
    have he : t8.regValue .rax = t7.regValue .r8 := effect8.writes
    rw [r8_7] at he
    exact he
  have ag8 : AgreesExcept inputRegisters t7 t8 :=
    effect8.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r12_8 : t8.regValue .r12 = 0xffffffff := (effect8.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 12) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 12) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 12) (by simp [xorR32R32Effect_components])).trans (half))))))))
  have code9 : CodeIn (codeRange 0x1142df [73, 247, 228]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x142df _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mul_r64_effect_step 0x1142df 0x49 0xe4 (by simp [RexWPrefix]) (by decide) (by decide)
    t8 ready8 code9 effect8.rip
  change (mulR64Effect 0x1142df 12 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x142e2 (by decide))
  have r0_9 : t9.regValue .rax = q.1 * 0xffffffff := by
    have he : t9.regValue .rax = t8.regValue .rax * t8.regValue .r12 := effect9.writes.1
    rw [r0_8, r12_8] at he
    exact he
  have r2_9 : t9.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t9.regValue .rdx = mulHigh64 (t8.regValue .rax) (t8.regValue .r12) := effect9.writes.2
    rw [r0_8, r12_8] at he
    exact he
  have ag9 : AgreesExcept inputRegisters t8 t9 :=
    effect9.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have code10 : CodeIn (codeRange 0x1142e2 [72, 137, 211]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x142e2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mov_r64_r64_effect_step 0x1142e2 0x48 0xd3 (by simp [RexWPrefix]) (by decide)
    t9 ready9 code10 effect9.rip
  change (movR64R64Effect 0x1142e2 3 2 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142e5 (by decide))
  have r3_10 : t10.regValue .rbx = mulHigh64 q.1 0xffffffff := by
    have he : t10.regValue .rbx = t9.regValue .rdx := effect10.writes
    rw [r2_9] at he
    exact he
  have ag10 : AgreesExcept inputRegisters t9 t10 :=
    effect10.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r0_10 : t10.regValue .rax = q.1 * 0xffffffff := (effect10.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_9)
  have code11 : CodeIn (codeRange 0x1142e5 [73, 137, 193]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x142e5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x1142e5 0x49 0xc1 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x1142e5 9 0 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142e8 (by decide))
  have r9_11 : t11.regValue .r9 = q.1 * 0xffffffff := by
    have he : t11.regValue .r9 = t10.regValue .rax := effect11.writes
    rw [r0_10] at he
    exact he
  have ag11 : AgreesExcept inputRegisters t10 t11 :=
    effect11.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r10_11 : t11.regValue .r10 = b := (effect11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))
  have code12 : CodeIn (codeRange 0x1142e8 [77, 1, 209]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x142e8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := add_r64_r64_effect_step 0x1142e8 0x4d 0xd1 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (addR64R64Effect 0x1142e8 9 10 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x142eb (by decide))
  have r9_12 : t12.regValue .r9 = l.1 := by
    have he : t12.regValue .r9 = (addSpec (t11.regValue .r9) (t11.regValue .r10)).1 := effect12.writes
    rw [r9_11, r10_11] at he
    exact he
  have cf12 : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = (addSpec (t11.regValue .r9) (t11.regValue .r10)).2.CF := effect12.flags.1
    rw [r9_11, r10_11] at he
    exact he
  have ag12 : AgreesExcept inputRegisters t11 t12 :=
    effect12.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have r3_12 : t12.regValue .rbx = mulHigh64 q.1 0xffffffff := (effect12.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans (r3_10))
  have cb13 := carry_extract cf12
  have code13 : CodeIn (codeRange 0x1142eb [72, 131, 211, 0]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x142eb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := adc_r64_imm8_effect_step 0x1142eb 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t12 ready12 code13 effect12.rip
  change (adcR64Imm8Effect 0x1142eb 3 0 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x142ef (by decide))
  have r3_13 : t13.regValue .rbx = h.1 := by
    have he : t13.regValue .rbx = (adcSpec (t12.regValue .rbx) 0 (t12.RFLAGS.extractLsb' 0 1)).1 := effect13.writes
    rw [cb13, r3_12] at he
    exact he
  have ag13 : AgreesExcept inputRegisters t12 t13 :=
    effect13.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have r8_13 : t13.regValue .r8 = q.1 := (effect13.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r8_7))))))
  have code14 : CodeIn (codeRange 0x1142ef [76, 137, 192]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x142ef _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := mov_r64_r64_effect_step 0x1142ef 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)
    t13 ready13 code14 effect13.rip
  change (movR64R64Effect 0x1142ef 0 8 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142f2 (by decide))
  have r0_14 : t14.regValue .rax = q.1 := by
    have he : t14.regValue .rax = t13.regValue .r8 := effect14.writes
    rw [r8_13] at he
    exact he
  have ag14 : AgreesExcept inputRegisters t13 t14 :=
    effect14.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r14_14 : t14.regValue .r14 = 0xffffffff00000001 := (effect14.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 14) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 14) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (constant))))))))))))))
  have code15 : CodeIn (codeRange 0x1142f2 [73, 247, 230]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x142f2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mul_r64_effect_step 0x1142f2 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)
    t14 ready14 code15 effect14.rip
  change (mulR64Effect 0x1142f2 14 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x142f5 (by decide))
  have r0_15 : t15.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t15.regValue .rax = t14.regValue .rax * t14.regValue .r14 := effect15.writes.1
    rw [r0_14, r14_14] at he
    exact he
  have r2_15 : t15.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t15.regValue .rdx = mulHigh64 (t14.regValue .rax) (t14.regValue .r14) := effect15.writes.2
    rw [r0_14, r14_14] at he
    exact he
  have ag15 : AgreesExcept inputRegisters t14 t15 :=
    effect15.agrees.mono (by simp [mulR64Effect_components, inputRegisters])
  have code16 : CodeIn (codeRange 0x1142f5 [73, 137, 210]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x142f5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mov_r64_r64_effect_step 0x1142f5 0x49 0xd2 (by simp [RexWPrefix]) (by decide)
    t15 ready15 code16 effect15.rip
  change (movR64R64Effect 0x1142f5 10 2 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142f8 (by decide))
  have r10_16 : t16.regValue .r10 = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t16.regValue .r10 = t15.regValue .rdx := effect16.writes
    rw [r2_15] at he
    exact he
  have ag16 : AgreesExcept inputRegisters t15 t16 :=
    effect16.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r0_16 : t16.regValue .rax = q.1 * 0xffffffff00000001 := (effect16.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_15)
  have code17 : CodeIn (codeRange 0x1142f8 [73, 137, 192]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x142f8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mov_r64_r64_effect_step 0x1142f8 0x49 0xc0 (by simp [RexWPrefix]) (by decide)
    t16 ready16 code17 effect16.rip
  change (movR64R64Effect 0x1142f8 8 0 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x142fb (by decide))
  have r8_17 : t17.regValue .r8 = q.1 * 0xffffffff00000001 := by
    have he : t17.regValue .r8 = t16.regValue .rax := effect17.writes
    rw [r0_16] at he
    exact he
  have ag17 : AgreesExcept inputRegisters t16 t17 :=
    effect17.agrees.mono (by simp [movR64R64Effect_components, inputRegisters])
  have r11_17 : t17.regValue .r11 = d := (effect17.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 11) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 11) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 11) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))))))))
  have code18 : CodeIn (codeRange 0x1142fb [77, 1, 216]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x142fb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := add_r64_r64_effect_step 0x1142fb 0x4d 0xd8 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (addR64R64Effect 0x1142fb 8 11 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x142fe (by decide))
  have r8_18 : t18.regValue .r8 = k.1 := by
    have he : t18.regValue .r8 = (addSpec (t17.regValue .r8) (t17.regValue .r11)).1 := effect18.writes
    rw [r8_17, r11_17] at he
    exact he
  have cf18 : (StatusFlags.ofRFLAGS t18.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t18.RFLAGS).CF = (addSpec (t17.regValue .r8) (t17.regValue .r11)).2.CF := effect18.flags.1
    rw [r8_17, r11_17] at he
    exact he
  have ag18 : AgreesExcept inputRegisters t17 t18 :=
    effect18.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have r10_18 : t18.regValue .r10 = mulHigh64 q.1 0xffffffff00000001 := (effect18.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r10_16))
  have cb19 := carry_extract cf18
  have code19 : CodeIn (codeRange 0x1142fe [73, 131, 210, 0]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x142fe _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := adc_r64_imm8_effect_step 0x1142fe 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t18 ready18 code19 effect18.rip
  change (adcR64Imm8Effect 0x1142fe 10 0 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x14302 (by decide))
  have r10_19 : t19.regValue .r10 = j.1 := by
    have he : t19.regValue .r10 = (adcSpec (t18.regValue .r10) 0 (t18.RFLAGS.extractLsb' 0 1)).1 := effect19.writes
    rw [cb19, r10_18] at he
    exact he
  have ag19 : AgreesExcept inputRegisters t18 t19 :=
    effect19.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have r9_19 : t19.regValue .r9 = l.1 := (effect19.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans (r9_12)))))))
  have r13_19 : t19.regValue .r13 = ec.1 := (effect19.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans (r13_7))))))))))))
  have code20 : CodeIn (codeRange 0x114302 [77, 1, 233]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x14302 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := add_r64_r64_effect_step 0x114302 0x4d 0xe9 (by simp [RexWPrefix]) (by decide)
    t19 ready19 code20 effect19.rip
  change (addR64R64Effect 0x114302 9 13 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x14305 (by decide))
  have r9_20 : t20.regValue .r9 = o0.1 := by
    have he : t20.regValue .r9 = (addSpec (t19.regValue .r9) (t19.regValue .r13)).1 := effect20.writes
    rw [r9_19, r13_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (addSpec (t19.regValue .r9) (t19.regValue .r13)).2.CF := effect20.flags.1
    rw [r9_19, r13_19] at he
    exact he
  have ag20 : AgreesExcept inputRegisters t19 t20 :=
    effect20.agrees.mono (by simp [addR64R64Effect_components, inputRegisters])
  have r3_20 : t20.regValue .rbx = h.1 := (effect20.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans (r3_13)))))))
  have r1_20 : t20.regValue .rcx = c := (effect20.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 1) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 1) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 1) (by simp [xorR32R32Effect_components])).trans (rfl))))))))))))))))))))
  have cb21 := carry_extract cf20
  have code21 : CodeIn (codeRange 0x114305 [72, 17, 203]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x14305 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := adc_r64_r64_effect_step 0x114305 0x48 0xcb (by simp [RexWPrefix]) (by decide)
    t20 ready20 code21 effect20.rip
  change (adcR64R64Effect 0x114305 3 1 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x14308 (by decide))
  have r3_21 : t21.regValue .rbx = o1.1 := by
    have he : t21.regValue .rbx = (adcSpec (t20.regValue .rbx) (t20.regValue .rcx) (t20.RFLAGS.extractLsb' 0 1)).1 := effect21.writes
    rw [cb21, r3_20, r1_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (adcSpec (t20.regValue .rbx) (t20.regValue .rcx) (t20.RFLAGS.extractLsb' 0 1)).2.CF := effect21.flags.1
    rw [cb21, r3_20, r1_20] at he
    exact he
  have ag21 : AgreesExcept inputRegisters t20 t21 :=
    effect21.agrees.mono (by simp [adcR64R64Effect_components, inputRegisters])
  have r8_21 : t21.regValue .r8 = k.1 := (effect21.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_18)))
  have cb22 := carry_extract cf21
  have code22 : CodeIn (codeRange 0x114308 [73, 131, 208, 0]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x14308 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := adc_r64_imm8_effect_step 0x114308 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t21 ready21 code22 effect21.rip
  change (adcR64Imm8Effect 0x114308 8 0 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x1430c (by decide))
  have r8_22 : t22.regValue .r8 = o2.1 := by
    have he : t22.regValue .r8 = (adcSpec (t21.regValue .r8) 0 (t21.RFLAGS.extractLsb' 0 1)).1 := effect22.writes
    rw [cb22, r8_21] at he
    exact he
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (adcSpec (t21.regValue .r8) 0 (t21.RFLAGS.extractLsb' 0 1)).2.CF := effect22.flags.1
    rw [cb22, r8_21] at he
    exact he
  have ag22 : AgreesExcept inputRegisters t21 t22 :=
    effect22.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have r10_22 : t22.regValue .r10 = j.1 := (effect22.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans (r10_19)))
  have cb23 := carry_extract cf22
  have code23 : CodeIn (codeRange 0x11430c [73, 131, 210, 0]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x1430c _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_imm8_effect_step 0x11430c 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64Imm8Effect 0x11430c 10 0 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x14310 (by decide))
  have r10_23 : t23.regValue .r10 = o3.1 := by
    have he : t23.regValue .r10 = (adcSpec (t22.regValue .r10) 0 (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [cb23, r10_22] at he
    exact he
  have ag23 : AgreesExcept inputRegisters t22 t23 :=
    effect23.agrees.mono (by simp [adcR64Imm8Effect_components, inputRegisters])
  have r9_23 : t23.regValue .r9 = o0.1 := (effect23.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans (r9_20)))
  have r3_23 : t23.regValue .rbx = o1.1 := (effect23.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans (r3_21))
  have r8_23 : t23.regValue .r8 = o2.1 := (effect23.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans (r8_22)
  have r14_23 : t23.regValue .r14 = 0xffffffff00000001 := (effect23.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r14_14)))))))))
  have r15_23 : t23.regValue .r15 = 0xffffffffffffffff := (effect23.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans (r15_4)))))))))))))))))))
  have r12_23 : t23.regValue .r12 = 0xffffffff := (effect23.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans (r12_8)))))))))))))))
  refine ⟨t23, stage23, effect23.rip, ?_, r14_23, r15_23, r12_23, agrees_trans ag1 (agrees_trans ag2 (agrees_trans ag3 (agrees_trans ag4 (agrees_trans ag5 (agrees_trans ag6 (agrees_trans ag7 (agrees_trans ag8 (agrees_trans ag9 (agrees_trans ag10 (agrees_trans ag11 (agrees_trans ag12 (agrees_trans ag13 (agrees_trans ag14 (agrees_trans ag15 (agrees_trans ag16 (agrees_trans ag17 (agrees_trans ag18 (agrees_trans ag19 (agrees_trans ag20 (agrees_trans ag21 (agrees_trans ag22 (ag23))))))))))))))))))))))⟩
  change (t23.regValue .r9, t23.regValue .rbx, t23.regValue .r8, t23.regValue .r10) = (o0.1, o1.1, o2.1, o3.1)
  rw [r9_23, r3_23, r8_23, r10_23]

end P256.Proofs.Field.Decode
