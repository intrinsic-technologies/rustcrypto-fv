import P256.Proofs.Sec1Serialize.Conversion.X.Initial
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic.Montgomery

set_option autoImplicit false
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step)

namespace P256.Proofs.Sec1Serialize.Conversion
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem x_round3 [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110e59) (r14 : t.regValue .r14 = s.regValue .rsi)
    (k13 : t.regValue .r13 = 0xffffffff00000001)
    (k3 : t.regValue .rbx = 0xffffffffffffffff)
    (k15 : t.regValue .r15 = 0xffffffff)
    : ∃ u, Stage s start u boundary ∧ u.RIP = 0x110ea5 ∧
      (u.regValue .rbx, u.regValue .r15, u.regValue .r12, u.regValue .r13) =
        Montgomery.compilerRoundBV (t.regValue .r9) (t.regValue .r12) (t.regValue .r8) (t.regValue .r10)
          ((Operand.mem (s.regValue .rsi + 24) : Operand 64).read t) ∧
      u.regValue .r9 = 0xffffffff00000001 ∧
      AgreesExcept xRegisters t u := by
  let a := t.regValue .r9
  let b := t.regValue .r12
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
  have code1 : CodeIn (codeRange 0x110e59 [0x31,0xc9]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10e59 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := xor_r32_r32_effect_step 0x110e59 0xc9 (by decide)
    t stage.ready code1 rip
  change (xorR32R32Effect 0x110e59 2 1 1 t).Holds t t1 at effect1
  have stage1 := stage.step_registers pre step1 ready1 effect1
    (by simp [xorR32R32Effect_components]) (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x10e5b (by decide))
  have r1_1 : t1.regValue .rcx = 0 := by
    have he : t1.regValue .rcx = (((Operand.reg 1 : Operand 32).read t) ^^^ ((Operand.reg 1 : Operand 32).read t)).setWidth 64 := effect1.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he.trans (by rfl)
  have r9_1 : t1.regValue .r9 = a := (effect1.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans (rfl)
  have r14_1 : t1.regValue .r14 = s.regValue .rsi := (effect1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (r14)
  have addr2 : (AddrMode.base 14 (.d8 24)).addr t1 0x110e5f = s.regValue .rsi + 24 := by
    change t1.regValue .r14 + 24 = _
    rw [r14_1]
  have read2 : MemReadable t1 ((AddrMode.base 14 (.d8 24)).addr t1 0x110e5f) 8 := by
    rw [addr2]
    exact input_readable pre stage1.allocated (offset := 24) (by decide)
  have mem2 : t1.external = t.external := (effect1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers]))
  have code2 : CodeIn (codeRange 0x110e5b [0x4d,0x3,0x4e,0x18]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10e5b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := add_r64_m64_effect_step 0x110e5b 0x4d (by simp [RexWPrefix]) 1 (.base 14 (.d8 24)) (by decide) rfl rfl
    t1 ready1 code2 ⟨effect1.rip, read2⟩
  change (addR64M64Effect 0x110e5b 9 (.base 14 (.d8 24)) t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [addR64M64Effect_components]) (by simp [addR64M64Effect_components]) (inProgram_of_textOffset 0x10e5f (by decide))
  have r9_2 : t2.regValue .r9 = q.1 := by
    have he : t2.regValue .r9 = (addSpec (t1.regValue .r9) ((Operand.mem ((AddrMode.base 14 (.d8 24)).addr t1 0x110e5f) : Operand 64).read t1)).1 := effect2.writes
    rw [r9_1, addr2] at he
    change t2.regValue .r9 = (addSpec a (memLoad t1.external (s.regValue .rsi + 24) 64)).1 at he
    rw [mem2] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = q.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec (t1.regValue .r9) ((Operand.mem ((AddrMode.base 14 (.d8 24)).addr t1 0x110e5f) : Operand 64).read t1)).2.CF := effect2.flags.1
    rw [r9_1, addr2] at he
    change (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec a (memLoad t1.external (s.regValue .rsi + 24) 64)).2.CF at he
    rw [mem2] at he
    exact he
  have r1_2 : t2.regValue .rcx = 0 := (effect2.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans (r1_1)
  have code3 : CodeIn (codeRange 0x110e5f [0xf,0x92,0xc1]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10e5f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := setcc_r8_effect_step 0x110e5f 0x92 0xc1 (.inl rfl) (by decide) (by decide)
    t2 ready2 code3 effect2.rip
  change (setccR8Effect 0x110e5f 3 1 2 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [setccR8Effect_components]) (by simp [setccR8Effect_components]) (inProgram_of_textOffset 0x10e62 (by decide))
  have r1_3 : t3.regValue .rcx = e := by
    have he : t3.regValue .rcx = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) (t2.regValue .rcx) := effect3.writes
    rw [cf2, r1_2, setb_zero] at he
    exact he
  have r9_3 : t3.regValue .r9 = q.1 := (effect3.agrees.read (n := 64) (r := 9) (by simp [setccR8Effect_components])).trans (r9_2)
  have code4 : CodeIn (codeRange 0x110e62 [0x4c,0x89,0xc8]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10e62 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mov_r64_r64_effect_step 0x110e62 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t3 ready3 code4 effect3.rip
  change (movR64R64Effect 0x110e62 0 9 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e65 (by decide))
  have r0_4 : t4.regValue .rax = q.1 := by
    have he : t4.regValue .rax = t3.regValue .r9 := effect4.writes
    rw [r9_3] at he
    exact he
  have r3_4 : t4.regValue .rbx = 0xffffffffffffffff := (effect4.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 3) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 3) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 3) (by simp [xorR32R32Effect_components])).trans (k3))))
  have code5 : CodeIn (codeRange 0x110e65 [0x48,0xf7,0xe3]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10e65 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mul_r64_effect_step 0x110e65 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)
    t4 ready4 code5 effect4.rip
  change (mulR64Effect 0x110e65 3 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e68 (by decide))
  have r0_5 : t5.regValue .rax = q.1 * 0xffffffffffffffff := by
    have he : t5.regValue .rax = t4.regValue .rax * t4.regValue .rbx := effect5.writes.1
    rw [r0_4, r3_4] at he
    exact he
  have r2_5 : t5.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := by
    have he : t5.regValue .rdx = mulHigh64 (t4.regValue .rax) (t4.regValue .rbx) := effect5.writes.2
    rw [r0_4, r3_4] at he
    exact he
  have r9_5 : t5.regValue .r9 = q.1 := (effect5.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r9_3))
  have code6 : CodeIn (codeRange 0x110e68 [0x4c,0x1,0xc8]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10e68 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := add_r64_r64_effect_step 0x110e68 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (addR64R64Effect 0x110e68 0 9 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e6b (by decide))
  have r0_6 : t6.regValue .rax = neg.1 := by
    have he : t6.regValue .rax = (addSpec (t5.regValue .rax) (t5.regValue .r9)).1 := effect6.writes
    rw [r0_5, r9_5] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = neg.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec (t5.regValue .rax) (t5.regValue .r9)).2.CF := effect6.flags.1
    rw [r0_5, r9_5] at he
    exact he
  have r1_6 : t6.regValue .rcx = e := (effect6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_3)))
  have r2_6 : t6.regValue .rdx = mulHigh64 q.1 0xffffffffffffffff := (effect6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r2_5)
  have cb7 := carry_extract cf6
  have code7 : CodeIn (codeRange 0x110e6b [0x48,0x11,0xd1]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10e6b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := adc_r64_r64_effect_step 0x110e6b 0x48 0xd1 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (adcR64R64Effect 0x110e6b 1 2 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10e6e (by decide))
  have r1_7 : t7.regValue .rcx = ec.1 := by
    have he : t7.regValue .rcx = (adcSpec (t6.regValue .rcx) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).1 := effect7.writes
    rw [cb7, r1_6, r2_6] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = ec.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec (t6.regValue .rcx) (t6.regValue .rdx) (t6.RFLAGS.extractLsb' 0 1)).2.CF := effect7.flags.1
    rw [cb7, r1_6, r2_6] at he
    exact he
  have r9_7 : t7.regValue .r9 = q.1 := (effect7.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans (r9_5))
  have code8 : CodeIn (codeRange 0x110e6e [0x4c,0x89,0xc8]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10e6e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r64_r64_effect_step 0x110e6e 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x110e6e 0 9 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e71 (by decide))
  have r0_8 : t8.regValue .rax = q.1 := by
    have he : t8.regValue .rax = t7.regValue .r9 := effect8.writes
    rw [r9_7] at he
    exact he
  have r15_8 : t8.regValue .r15 = 0xffffffff := (effect8.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 15) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 15) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 15) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 15) (by simp [xorR32R32Effect_components])).trans (k15))))))))
  have code9 : CodeIn (codeRange 0x110e71 [0x49,0xf7,0xe7]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x10e71 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := mul_r64_effect_step 0x110e71 0x49 0xe7 (by simp [RexWPrefix]) (by decide) (by decide)
    t8 ready8 code9 effect8.rip
  change (mulR64Effect 0x110e71 15 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e74 (by decide))
  have r0_9 : t9.regValue .rax = q.1 * 0xffffffff := by
    have he : t9.regValue .rax = t8.regValue .rax * t8.regValue .r15 := effect9.writes.1
    rw [r0_8, r15_8] at he
    exact he
  have r2_9 : t9.regValue .rdx = mulHigh64 q.1 0xffffffff := by
    have he : t9.regValue .rdx = mulHigh64 (t8.regValue .rax) (t8.regValue .r15) := effect9.writes.2
    rw [r0_8, r15_8] at he
    exact he
  have code10 : CodeIn (codeRange 0x110e74 [0x49,0x89,0xd7]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x10e74 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, step10, ready10, effect10⟩ := mov_r64_r64_effect_step 0x110e74 0x49 0xd7 (by simp [RexWPrefix]) (by decide)
    t9 ready9 code10 effect9.rip
  change (movR64R64Effect 0x110e74 15 2 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers pre step10 ready10 effect10
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e77 (by decide))
  have r15_10 : t10.regValue .r15 = mulHigh64 q.1 0xffffffff := by
    have he : t10.regValue .r15 = t9.regValue .rdx := effect10.writes
    rw [r2_9] at he
    exact he
  have r0_10 : t10.regValue .rax = q.1 * 0xffffffff := (effect10.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_9)
  have code11 : CodeIn (codeRange 0x110e77 [0x48,0x89,0xc3]) t10 :=
    programText_slice (programLoaded_codeIn stage10.loaded) 0x10e77 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, step11, ready11, effect11⟩ := mov_r64_r64_effect_step 0x110e77 0x48 0xc3 (by simp [RexWPrefix]) (by decide)
    t10 ready10 code11 effect10.rip
  change (movR64R64Effect 0x110e77 3 0 t10).Holds t10 t11 at effect11
  have stage11 := stage10.step_registers pre step11 ready11 effect11
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e7a (by decide))
  have r3_11 : t11.regValue .rbx = q.1 * 0xffffffff := by
    have he : t11.regValue .rbx = t10.regValue .rax := effect11.writes
    rw [r0_10] at he
    exact he
  have r12_11 : t11.regValue .r12 = b := (effect11.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 12) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 12) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 12) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 12) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 12) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))
  have code12 : CodeIn (codeRange 0x110e7a [0x4c,0x1,0xe3]) t11 :=
    programText_slice (programLoaded_codeIn stage11.loaded) 0x10e7a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, step12, ready12, effect12⟩ := add_r64_r64_effect_step 0x110e7a 0x4c 0xe3 (by simp [RexWPrefix]) (by decide)
    t11 ready11 code12 effect11.rip
  change (addR64R64Effect 0x110e7a 3 12 t11).Holds t11 t12 at effect12
  have stage12 := stage11.step_registers pre step12 ready12 effect12
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e7d (by decide))
  have r3_12 : t12.regValue .rbx = l.1 := by
    have he : t12.regValue .rbx = (addSpec (t11.regValue .rbx) (t11.regValue .r12)).1 := effect12.writes
    rw [r3_11, r12_11] at he
    exact he
  have cf12 : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = l.2.CF := by
    have he : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = (addSpec (t11.regValue .rbx) (t11.regValue .r12)).2.CF := effect12.flags.1
    rw [r3_11, r12_11] at he
    exact he
  have r15_12 : t12.regValue .r15 = mulHigh64 q.1 0xffffffff := (effect12.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans (r15_10))
  have cb13 := carry_extract cf12
  have code13 : CodeIn (codeRange 0x110e7d [0x49,0x83,0xd7,0x0]) t12 :=
    programText_slice (programLoaded_codeIn stage12.loaded) 0x10e7d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, step13, ready13, effect13⟩ := adc_r64_imm8_effect_step 0x110e7d 0x49 0xd7 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t12 ready12 code13 effect12.rip
  change (adcR64Imm8Effect 0x110e7d 15 0 t12).Holds t12 t13 at effect13
  have stage13 := stage12.step_registers pre step13 ready13 effect13
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e81 (by decide))
  have r15_13 : t13.regValue .r15 = h.1 := by
    have he : t13.regValue .r15 = (adcSpec (t12.regValue .r15) 0 (t12.RFLAGS.extractLsb' 0 1)).1 := effect13.writes
    rw [cb13, r15_12] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = h.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (adcSpec (t12.regValue .r15) 0 (t12.RFLAGS.extractLsb' 0 1)).2.CF := effect13.flags.1
    rw [cb13, r15_12] at he
    exact he
  have r9_13 : t13.regValue .r9 = q.1 := (effect13.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r9_7))))))
  have code14 : CodeIn (codeRange 0x110e81 [0x4c,0x89,0xc8]) t13 :=
    programText_slice (programLoaded_codeIn stage13.loaded) 0x10e81 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, step14, ready14, effect14⟩ := mov_r64_r64_effect_step 0x110e81 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)
    t13 ready13 code14 effect13.rip
  change (movR64R64Effect 0x110e81 0 9 t13).Holds t13 t14 at effect14
  have stage14 := stage13.step_registers pre step14 ready14 effect14
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e84 (by decide))
  have r0_14 : t14.regValue .rax = q.1 := by
    have he : t14.regValue .rax = t13.regValue .r9 := effect14.writes
    rw [r9_13] at he
    exact he
  have r13_14 : t14.regValue .r13 = 0xffffffff00000001 := (effect14.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 13) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 13) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 13) (by simp [xorR32R32Effect_components])).trans (k13))))))))))))))
  have code15 : CodeIn (codeRange 0x110e84 [0x4d,0x89,0xe9]) t14 :=
    programText_slice (programLoaded_codeIn stage14.loaded) 0x10e84 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, step15, ready15, effect15⟩ := mov_r64_r64_effect_step 0x110e84 0x4d 0xe9 (by simp [RexWPrefix]) (by decide)
    t14 ready14 code15 effect14.rip
  change (movR64R64Effect 0x110e84 9 13 t14).Holds t14 t15 at effect15
  have stage15 := stage14.step_registers pre step15 ready15 effect15
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e87 (by decide))
  have r9_15 : t15.regValue .r9 = 0xffffffff00000001 := by
    have he : t15.regValue .r9 = t14.regValue .r13 := effect15.writes
    rw [r13_14] at he
    exact he
  have r0_15 : t15.regValue .rax = q.1 := (effect15.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_14)
  have r13_15 : t15.regValue .r13 = 0xffffffff00000001 := (effect15.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans (r13_14)
  have code16 : CodeIn (codeRange 0x110e87 [0x49,0xf7,0xe5]) t15 :=
    programText_slice (programLoaded_codeIn stage15.loaded) 0x10e87 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, step16, ready16, effect16⟩ := mul_r64_effect_step 0x110e87 0x49 0xe5 (by simp [RexWPrefix]) (by decide) (by decide)
    t15 ready15 code16 effect15.rip
  change (mulR64Effect 0x110e87 13 t15).Holds t15 t16 at effect16
  have stage16 := stage15.step_registers pre step16 ready16 effect16
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10e8a (by decide))
  have r0_16 : t16.regValue .rax = q.1 * 0xffffffff00000001 := by
    have he : t16.regValue .rax = t15.regValue .rax * t15.regValue .r13 := effect16.writes.1
    rw [r0_15, r13_15] at he
    exact he
  have r2_16 : t16.regValue .rdx = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t16.regValue .rdx = mulHigh64 (t15.regValue .rax) (t15.regValue .r13) := effect16.writes.2
    rw [r0_15, r13_15] at he
    exact he
  have code17 : CodeIn (codeRange 0x110e8a [0x49,0x89,0xd5]) t16 :=
    programText_slice (programLoaded_codeIn stage16.loaded) 0x10e8a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, step17, ready17, effect17⟩ := mov_r64_r64_effect_step 0x110e8a 0x49 0xd5 (by simp [RexWPrefix]) (by decide)
    t16 ready16 code17 effect16.rip
  change (movR64R64Effect 0x110e8a 13 2 t16).Holds t16 t17 at effect17
  have stage17 := stage16.step_registers pre step17 ready17 effect17
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e8d (by decide))
  have r13_17 : t17.regValue .r13 = mulHigh64 q.1 0xffffffff00000001 := by
    have he : t17.regValue .r13 = t16.regValue .rdx := effect17.writes
    rw [r2_16] at he
    exact he
  have r0_17 : t17.regValue .rax = q.1 * 0xffffffff00000001 := (effect17.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_16)
  have code18 : CodeIn (codeRange 0x110e8d [0x49,0x89,0xc4]) t17 :=
    programText_slice (programLoaded_codeIn stage17.loaded) 0x10e8d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t18, step18, ready18, effect18⟩ := mov_r64_r64_effect_step 0x110e8d 0x49 0xc4 (by simp [RexWPrefix]) (by decide)
    t17 ready17 code18 effect17.rip
  change (movR64R64Effect 0x110e8d 12 0 t17).Holds t17 t18 at effect18
  have stage18 := stage17.step_registers pre step18 ready18 effect18
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10e90 (by decide))
  have r12_18 : t18.regValue .r12 = q.1 * 0xffffffff00000001 := by
    have he : t18.regValue .r12 = t17.regValue .rax := effect18.writes
    rw [r0_17] at he
    exact he
  have r10_18 : t18.regValue .r10 = d := (effect18.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (rfl))))))))))))))))))
  have code19 : CodeIn (codeRange 0x110e90 [0x4d,0x1,0xd4]) t18 :=
    programText_slice (programLoaded_codeIn stage18.loaded) 0x10e90 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t19, step19, ready19, effect19⟩ := add_r64_r64_effect_step 0x110e90 0x4d 0xd4 (by simp [RexWPrefix]) (by decide)
    t18 ready18 code19 effect18.rip
  change (addR64R64Effect 0x110e90 12 10 t18).Holds t18 t19 at effect19
  have stage19 := stage18.step_registers pre step19 ready19 effect19
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e93 (by decide))
  have r12_19 : t19.regValue .r12 = k.1 := by
    have he : t19.regValue .r12 = (addSpec (t18.regValue .r12) (t18.regValue .r10)).1 := effect19.writes
    rw [r12_18, r10_18] at he
    exact he
  have cf19 : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = k.2.CF := by
    have he : (StatusFlags.ofRFLAGS t19.RFLAGS).CF = (addSpec (t18.regValue .r12) (t18.regValue .r10)).2.CF := effect19.flags.1
    rw [r12_18, r10_18] at he
    exact he
  have r13_19 : t19.regValue .r13 = mulHigh64 q.1 0xffffffff00000001 := (effect19.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans (r13_17))
  have cb20 := carry_extract cf19
  have code20 : CodeIn (codeRange 0x110e93 [0x49,0x83,0xd5,0x0]) t19 :=
    programText_slice (programLoaded_codeIn stage19.loaded) 0x10e93 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t20, step20, ready20, effect20⟩ := adc_r64_imm8_effect_step 0x110e93 0x49 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t19 ready19 code20 effect19.rip
  change (adcR64Imm8Effect 0x110e93 13 0 t19).Holds t19 t20 at effect20
  have stage20 := stage19.step_registers pre step20 ready20 effect20
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10e97 (by decide))
  have r13_20 : t20.regValue .r13 = j.1 := by
    have he : t20.regValue .r13 = (adcSpec (t19.regValue .r13) 0 (t19.RFLAGS.extractLsb' 0 1)).1 := effect20.writes
    rw [cb20, r13_19] at he
    exact he
  have cf20 : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = j.2.CF := by
    have he : (StatusFlags.ofRFLAGS t20.RFLAGS).CF = (adcSpec (t19.regValue .r13) 0 (t19.RFLAGS.extractLsb' 0 1)).2.CF := effect20.flags.1
    rw [cb20, r13_19] at he
    exact he
  have r3_20 : t20.regValue .rbx = l.1 := (effect20.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans (r3_12))))))))
  have r1_20 : t20.regValue .rcx = ec.1 := (effect20.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r1_7)))))))))))))
  have code21 : CodeIn (codeRange 0x110e97 [0x48,0x1,0xcb]) t20 :=
    programText_slice (programLoaded_codeIn stage20.loaded) 0x10e97 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t21, step21, ready21, effect21⟩ := add_r64_r64_effect_step 0x110e97 0x48 0xcb (by simp [RexWPrefix]) (by decide)
    t20 ready20 code21 effect20.rip
  change (addR64R64Effect 0x110e97 3 1 t20).Holds t20 t21 at effect21
  have stage21 := stage20.step_registers pre step21 ready21 effect21
    (by simp [addR64R64Effect_components]) (by simp [addR64R64Effect_components]) (inProgram_of_textOffset 0x10e9a (by decide))
  have r3_21 : t21.regValue .rbx = o0.1 := by
    have he : t21.regValue .rbx = (addSpec (t20.regValue .rbx) (t20.regValue .rcx)).1 := effect21.writes
    rw [r3_20, r1_20] at he
    exact he
  have cf21 : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = o0.2.CF := by
    have he : (StatusFlags.ofRFLAGS t21.RFLAGS).CF = (addSpec (t20.regValue .rbx) (t20.regValue .rcx)).2.CF := effect21.flags.1
    rw [r3_20, r1_20] at he
    exact he
  have r15_21 : t21.regValue .r15 = h.1 := (effect21.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 15) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 15) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 15) (by simp [movR64R64Effect_components])).trans (r15_13))))))))
  have r8_21 : t21.regValue .r8 = c := (effect21.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect15.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect14.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect13.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((effect12.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect11.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect10.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 8) (by simp [addR64M64Effect_components])).trans ((effect1.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans (rfl)))))))))))))))))))))
  have cb22 := carry_extract cf21
  have code22 : CodeIn (codeRange 0x110e9a [0x4d,0x11,0xc7]) t21 :=
    programText_slice (programLoaded_codeIn stage21.loaded) 0x10e9a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t22, step22, ready22, effect22⟩ := adc_r64_r64_effect_step 0x110e9a 0x4d 0xc7 (by simp [RexWPrefix]) (by decide)
    t21 ready21 code22 effect21.rip
  change (adcR64R64Effect 0x110e9a 15 8 t21).Holds t21 t22 at effect22
  have stage22 := stage21.step_registers pre step22 ready22 effect22
    (by simp [adcR64R64Effect_components]) (by simp [adcR64R64Effect_components]) (inProgram_of_textOffset 0x10e9d (by decide))
  have r15_22 : t22.regValue .r15 = o1.1 := by
    have he : t22.regValue .r15 = (adcSpec (t21.regValue .r15) (t21.regValue .r8) (t21.RFLAGS.extractLsb' 0 1)).1 := effect22.writes
    rw [cb22, r15_21, r8_21] at he
    exact he
  have cf22 : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = o1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t22.RFLAGS).CF = (adcSpec (t21.regValue .r15) (t21.regValue .r8) (t21.RFLAGS.extractLsb' 0 1)).2.CF := effect22.flags.1
    rw [cb22, r15_21, r8_21] at he
    exact he
  have r12_22 : t22.regValue .r12 = k.1 := (effect22.agrees.read (n := 64) (r := 12) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 12) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans (r12_19)))
  have cb23 := carry_extract cf22
  have code23 : CodeIn (codeRange 0x110e9d [0x49,0x83,0xd4,0x0]) t22 :=
    programText_slice (programLoaded_codeIn stage22.loaded) 0x10e9d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t23, step23, ready23, effect23⟩ := adc_r64_imm8_effect_step 0x110e9d 0x49 0xd4 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t22 ready22 code23 effect22.rip
  change (adcR64Imm8Effect 0x110e9d 12 0 t22).Holds t22 t23 at effect23
  have stage23 := stage22.step_registers pre step23 ready23 effect23
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10ea1 (by decide))
  have r12_23 : t23.regValue .r12 = o2.1 := by
    have he : t23.regValue .r12 = (adcSpec (t22.regValue .r12) 0 (t22.RFLAGS.extractLsb' 0 1)).1 := effect23.writes
    rw [cb23, r12_22] at he
    exact he
  have cf23 : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = o2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t23.RFLAGS).CF = (adcSpec (t22.regValue .r12) 0 (t22.RFLAGS.extractLsb' 0 1)).2.CF := effect23.flags.1
    rw [cb23, r12_22] at he
    exact he
  have r13_23 : t23.regValue .r13 = j.1 := (effect23.agrees.read (n := 64) (r := 13) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 13) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 13) (by simp [addR64R64Effect_components])).trans (r13_20)))
  have cb24 := carry_extract cf23
  have code24 : CodeIn (codeRange 0x110ea1 [0x49,0x83,0xd5,0x0]) t23 :=
    programText_slice (programLoaded_codeIn stage23.loaded) 0x10ea1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t24, step24, ready24, effect24⟩ := adc_r64_imm8_effect_step 0x110ea1 0x49 0xd5 0 (by simp [RexWPrefix]) (by decide) (by decide)
    t23 ready23 code24 effect23.rip
  change (adcR64Imm8Effect 0x110ea1 13 0 t23).Holds t23 t24 at effect24
  have stage24 := stage23.step_registers pre step24 ready24 effect24
    (by simp [adcR64Imm8Effect_components]) (by simp [adcR64Imm8Effect_components]) (inProgram_of_textOffset 0x10ea5 (by decide))
  have r13_24 : t24.regValue .r13 = o3.1 := by
    have he : t24.regValue .r13 = (adcSpec (t23.regValue .r13) 0 (t23.RFLAGS.extractLsb' 0 1)).1 := effect24.writes
    rw [cb24, r13_23] at he
    exact he
  have cf24 : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = o3.2.CF := by
    have he : (StatusFlags.ofRFLAGS t24.RFLAGS).CF = (adcSpec (t23.regValue .r13) 0 (t23.RFLAGS.extractLsb' 0 1)).2.CF := effect24.flags.1
    rw [cb24, r13_23] at he
    exact he
  have r3_24 : t24.regValue .rbx = o0.1 := (effect24.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans (r3_21)))
  have r15_24 : t24.regValue .r15 = o1.1 := (effect24.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 15) (by simp [adcR64Imm8Effect_components])).trans (r15_22))
  have r12_24 : t24.regValue .r12 = o2.1 := (effect24.agrees.read (n := 64) (r := 12) (by simp [adcR64Imm8Effect_components])).trans (r12_23)
  have r9_24 : t24.regValue .r9 = 0xffffffff00000001 := (effect24.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect23.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect22.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((effect21.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect20.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans ((effect19.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans ((effect18.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect17.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans ((effect16.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans (r9_15)))))))))
  have agree {a b c : RamState} (ha : AgreesExcept xRegisters a b) (hb : AgreesExcept xRegisters b c) : AgreesExcept xRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag1 : AgreesExcept xRegisters t t1 := effect1.agrees.mono (by simp [xorR32R32Effect_components, xRegisters])
  have ag2 : AgreesExcept xRegisters t1 t2 := effect2.agrees.mono (by simp [addR64M64Effect_components, xRegisters])
  have ag3 : AgreesExcept xRegisters t2 t3 := effect3.agrees.mono (by simp [setccR8Effect_components, xRegisters])
  have ag4 : AgreesExcept xRegisters t3 t4 := effect4.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag5 : AgreesExcept xRegisters t4 t5 := effect5.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag6 : AgreesExcept xRegisters t5 t6 := effect6.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag7 : AgreesExcept xRegisters t6 t7 := effect7.agrees.mono (by simp [adcR64R64Effect_components, xRegisters])
  have ag8 : AgreesExcept xRegisters t7 t8 := effect8.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag9 : AgreesExcept xRegisters t8 t9 := effect9.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag10 : AgreesExcept xRegisters t9 t10 := effect10.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag11 : AgreesExcept xRegisters t10 t11 := effect11.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag12 : AgreesExcept xRegisters t11 t12 := effect12.agrees.mono (by simp [addR64R64Effect_components, xRegisters])
  have ag13 : AgreesExcept xRegisters t12 t13 := effect13.agrees.mono (by simp [adcR64Imm8Effect_components, xRegisters])
  have ag14 : AgreesExcept xRegisters t13 t14 := effect14.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
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
  refine ⟨t24, stage24, effect24.rip, ?_, r9_24, (agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 (agree ag8 (agree ag9 (agree ag10 (agree ag11 (agree ag12 (agree ag13 (agree ag14 (agree ag15 (agree ag16 (agree ag17 (agree ag18 (agree ag19 (agree ag20 (agree ag21 (agree ag22 (agree ag23 ag24)))))))))))))))))))))))⟩
  change (t24.regValue .rbx, t24.regValue .r15, t24.regValue .r12, t24.regValue .r13) = (o0.1, o1.1, o2.1, o3.1)
  rw [r3_24, r15_24, r12_24, r13_24]

end P256.Proofs.Sec1Serialize.Conversion
