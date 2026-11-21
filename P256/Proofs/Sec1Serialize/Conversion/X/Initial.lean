import P256.Proofs.Sec1Serialize.Conversion.Stage


set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)

namespace P256.Proofs.Sec1Serialize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def xRegisters : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 12, .reg 13, .reg 15, .flags, .rip]

theorem x_initial [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110d88) (rsi : t.regValue .rsi = s.regValue .rsi) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110daf ∧
      (let a := (Operand.mem (s.regValue .rsi) : Operand 64).read t
       u.regValue .rsi = a <<< 32 ∧ u.regValue .rcx = a >>> 32 ∧
       u.regValue .r9 = a * 0xffffffff00000001 ∧
       u.regValue .rbx = mulHigh64 a 0xffffffff00000001) ∧
      u.regValue .r13 = 0xffffffff00000001 ∧ u.regValue .r15 = 0 ∧
      AgreesExcept xRegisters t u := by
  let a := (Operand.mem (s.regValue .rsi) : Operand 64).read t
  have code0 : CodeIn (codeRange 0x110d88 [0x48,0x8b,0x06]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10d88 _
      (by decide +kernel) (by decide +kernel)
  have addr0 : (AddrMode.base 6 .none).addr t 0x110d8b = s.regValue .rsi := by
    change t.regValue .rsi + 0 = _
    rw [rsi]
    exact BitVec.add_zero _
  have read0 : MemReadable t ((AddrMode.base 6 .none).addr t 0x110d8b) 8 := by
    rw [addr0]
    simpa using
      (input_readable pre stage.allocated (offset := 0) (by decide))
  obtain ⟨t0, step0, ready0, effect0⟩ := mov_r64_m64_effect_step 0x110d88 0x48
    (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide) rfl rfl
    t stage.ready code0 ⟨rip, read0⟩
  change (movR64M64Effect 0x110d88 0 (.base 6 .none) t).Holds t t0 at effect0
  have stage0 := stage.step_registers pre step0 ready0 effect0 (by simp) (by simp)
    (inProgram_of_textOffset 0x10d8b (by decide))
  have a0 : t0.regValue .rax = a := by
    have e := effect0.writes
    change t0.regValue .rax = (Operand.mem ((AddrMode.base 6 .none).addr t 0x110d8b) : Operand 64).read t at e
    rw [addr0] at e
    exact e
  have code1 : CodeIn (codeRange 0x110d8b [0x48,0x89,0xc1]) t0 :=
    programText_slice (programLoaded_codeIn stage0.loaded) 0x10d8b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := mov_r64_r64_effect_step 0x110d8b 0x48 0xc1 (by simp [RexWPrefix]) (by decide)
    t0 ready0 code1 effect0.rip
  change (movR64R64Effect 0x110d8b 1 0 t0).Holds t0 t1 at effect1
  have stage1 := stage0.step_registers pre step1 ready1 effect1
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10d8e (by decide))
  have r0_1 : t1.regValue .rax = a :=
    (effect1.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans a0
  have r1_1 : t1.regValue .rcx = a := by
    have e : t1.regValue .rcx = t0.regValue .rax := effect1.writes
    rw [a0] at e
    exact e
  have code2 : CodeIn (codeRange 0x110d8e [0x48,0x89,0xc6]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10d8e _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := mov_r64_r64_effect_step 0x110d8e 0x48 0xc6 (by simp [RexWPrefix]) (by decide)
    t1 ready1 code2 effect1.rip
  change (movR64R64Effect 0x110d8e 6 0 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10d91 (by decide))
  have r0_2 : t2.regValue .rax = a :=
    (effect2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_1
  have r1_2 : t2.regValue .rcx = a :=
    (effect2.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans r1_1
  have r6_2 : t2.regValue .rsi = a := by
    have e : t2.regValue .rsi = t1.regValue .rax := effect2.writes
    rw [r0_1] at e
    exact e
  have code3 : CodeIn (codeRange 0x110d91 [0x48,0xc1,0xe6,0x20]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10d91 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := shl_r64_imm8_effect_step 0x110d91 0x48 0xe6 0x20 (by simp [RexWPrefix]) (by decide) (by decide)
    t2 ready2 code3 effect2.rip
  change (shlR64Effect 0x110d91 4 6 32 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [shlR64Effect_components]) (by simp [shlR64Effect_components]) (inProgram_of_textOffset 0x10d95 (by decide))
  have r0_3 : t3.regValue .rax = a :=
    (effect3.agrees.read (n := 64) (r := 0) (by simp [shlR64Effect_components])).trans r0_2
  have r1_3 : t3.regValue .rcx = a :=
    (effect3.agrees.read (n := 64) (r := 1) (by simp [shlR64Effect_components])).trans r1_2
  have r6_3 : t3.regValue .rsi = a <<< 32 := by
    have e : t3.regValue .rsi = t2.regValue .rsi <<< 32 := effect3.writes
    rw [r6_2] at e
    exact e
  have code4 : CodeIn (codeRange 0x110d95 [0x48,0xc1,0xe9,0x20]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10d95 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := shr_r64_imm8_effect_step 0x110d95 0x48 0xe9 0x20 (by simp [RexWPrefix]) (by decide) (by decide)
    t3 ready3 code4 effect3.rip
  change (shrR64Effect 0x110d95 4 1 32 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [shrR64Effect_components]) (by simp [shrR64Effect_components]) (inProgram_of_textOffset 0x10d99 (by decide))
  have r0_4 : t4.regValue .rax = a :=
    (effect4.agrees.read (n := 64) (r := 0) (by simp [shrR64Effect_components])).trans r0_3
  have r6_4 : t4.regValue .rsi = a <<< 32 :=
    (effect4.agrees.read (n := 64) (r := 6) (by simp [shrR64Effect_components])).trans r6_3
  have r1_4 : t4.regValue .rcx = a >>> 32 := by
    have e : t4.regValue .rcx = t3.regValue .rcx >>> 32 := effect4.writes
    rw [r1_3] at e
    exact e
  have code5 : CodeIn (codeRange 0x110d99 [0x49,0xbd,0x1,0x0,0x0,0x0,0xff,0xff,0xff,0xff]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10d99 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mov_r64_imm64_effect_step 0x110d99 0x49 0xbd (by simp [RexWPrefix]) (by decide) 0xffffffff00000001
    t4 ready4 code5 effect4.rip
  change (movR64Imm64Effect 0x110d99 13 0xffffffff00000001 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [movR64Imm64Effect_components]) (by simp [movR64Imm64Effect_components]) (inProgram_of_textOffset 0x10da3 (by decide))
  have r0_5 : t5.regValue .rax = a :=
    (effect5.agrees.read (n := 64) (r := 0) (by simp [movR64Imm64Effect_components])).trans r0_4
  have r6_5 : t5.regValue .rsi = a <<< 32 :=
    (effect5.agrees.read (n := 64) (r := 6) (by simp [movR64Imm64Effect_components])).trans r6_4
  have r1_5 : t5.regValue .rcx = a >>> 32 :=
    (effect5.agrees.read (n := 64) (r := 1) (by simp [movR64Imm64Effect_components])).trans r1_4
  have r13_5 : t5.regValue .r13 = 0xffffffff00000001 := by
    have e : t5.regValue .r13 = 0xffffffff00000001 := effect5.writes
    exact e
  have code6 : CodeIn (codeRange 0x110da3 [0x49,0xf7,0xe5]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10da3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := mul_r64_effect_step 0x110da3 0x49 0xe5 (by simp [RexWPrefix]) (by decide) (by decide)
    t5 ready5 code6 effect5.rip
  change (mulR64Effect 0x110da3 13 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10da6 (by decide))
  have r6_6 : t6.regValue .rsi = a <<< 32 :=
    (effect6.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans r6_5
  have r1_6 : t6.regValue .rcx = a >>> 32 :=
    (effect6.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans r1_5
  have r13_6 : t6.regValue .r13 = 0xffffffff00000001 :=
    (effect6.agrees.read (n := 64) (r := 13) (by simp [mulR64Effect_components])).trans r13_5
  have r0_6 : t6.regValue .rax = a * 0xffffffff00000001 := by
    have e : t6.regValue .rax = t5.regValue .rax * t5.regValue .r13 := effect6.writes.1
    rw [r0_5, r13_5] at e
    exact e
  have r2_6 : t6.regValue .rdx = mulHigh64 a 0xffffffff00000001 := by
    have e : t6.regValue .rdx = mulHigh64 (t5.regValue .rax) (t5.regValue .r13) := effect6.writes.2
    rw [r0_5, r13_5] at e
    exact e
  have code7 : CodeIn (codeRange 0x110da6 [0x49,0x89,0xc1]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10da6 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := mov_r64_r64_effect_step 0x110da6 0x49 0xc1 (by simp [RexWPrefix]) (by decide)
    t6 ready6 code7 effect6.rip
  change (movR64R64Effect 0x110da6 9 0 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10da9 (by decide))
  have r6_7 : t7.regValue .rsi = a <<< 32 :=
    (effect7.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans r6_6
  have r1_7 : t7.regValue .rcx = a >>> 32 :=
    (effect7.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans r1_6
  have r13_7 : t7.regValue .r13 = 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans r13_6
  have r0_7 : t7.regValue .rax = a * 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_6
  have r2_7 : t7.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans r2_6
  have r9_7 : t7.regValue .r9 = a * 0xffffffff00000001 := by
    have e : t7.regValue .r9 = t6.regValue .rax := effect7.writes
    rw [r0_6] at e
    exact e
  have code8 : CodeIn (codeRange 0x110da9 [0x48,0x89,0xd3]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10da9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := mov_r64_r64_effect_step 0x110da9 0x48 0xd3 (by simp [RexWPrefix]) (by decide)
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x110da9 3 2 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10dac (by decide))
  have r6_8 : t8.regValue .rsi = a <<< 32 :=
    (effect8.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans r6_7
  have r1_8 : t8.regValue .rcx = a >>> 32 :=
    (effect8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans r1_7
  have r13_8 : t8.regValue .r13 = 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 13) (by simp [movR64R64Effect_components])).trans r13_7
  have r0_8 : t8.regValue .rax = a * 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_7
  have r2_8 : t8.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans r2_7
  have r9_8 : t8.regValue .r9 = a * 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans r9_7
  have r3_8 : t8.regValue .rbx = mulHigh64 a 0xffffffff00000001 := by
    have e : t8.regValue .rbx = t7.regValue .rdx := effect8.writes
    rw [r2_7] at e
    exact e
  have code9 : CodeIn (codeRange 0x110dac [0x45,0x31,0xff]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x10dac _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, step9, ready9, effect9⟩ := xor_r32_r32_rex_effect_step 0x110dac 0x45 0xff (by simp [RexNoWPrefix]) (by decide)
    t8 ready8 code9 effect8.rip
  change (xorR32R32Effect 0x110dac 3 15 15 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers pre step9 ready9 effect9
    (by simp [xorR32R32Effect_components]) (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x10daf (by decide))
  have r6_9 : t9.regValue .rsi = a <<< 32 :=
    (effect9.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components])).trans r6_8
  have r1_9 : t9.regValue .rcx = a >>> 32 :=
    (effect9.agrees.read (n := 64) (r := 1) (by simp [xorR32R32Effect_components])).trans r1_8
  have r13_9 : t9.regValue .r13 = 0xffffffff00000001 :=
    (effect9.agrees.read (n := 64) (r := 13) (by simp [xorR32R32Effect_components])).trans r13_8
  have r0_9 : t9.regValue .rax = a * 0xffffffff00000001 :=
    (effect9.agrees.read (n := 64) (r := 0) (by simp [xorR32R32Effect_components])).trans r0_8
  have r2_9 : t9.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect9.agrees.read (n := 64) (r := 2) (by simp [xorR32R32Effect_components])).trans r2_8
  have r9_9 : t9.regValue .r9 = a * 0xffffffff00000001 :=
    (effect9.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans r9_8
  have r3_9 : t9.regValue .rbx = mulHigh64 a 0xffffffff00000001 :=
    (effect9.agrees.read (n := 64) (r := 3) (by simp [xorR32R32Effect_components])).trans r3_8
  have r15_9 : t9.regValue .r15 = 0 := by
    have e : t9.regValue .r15 = (((Operand.reg 15 : Operand 32).read t8) ^^^ ((Operand.reg 15 : Operand 32).read t8)).setWidth 64 := effect9.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at e
    exact e.trans (by rfl)
  have agree {a b c : RamState} (ha : AgreesExcept xRegisters a b) (hb : AgreesExcept xRegisters b c) : AgreesExcept xRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag0 : AgreesExcept xRegisters t t0 := effect0.agrees.mono (by simp [movR64M64Effect_components, xRegisters])
  have ag1 : AgreesExcept xRegisters t0 t1 := effect1.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag2 : AgreesExcept xRegisters t1 t2 := effect2.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag3 : AgreesExcept xRegisters t2 t3 := effect3.agrees.mono (by simp [shlR64Effect_components, xRegisters])
  have ag4 : AgreesExcept xRegisters t3 t4 := effect4.agrees.mono (by simp [shrR64Effect_components, xRegisters])
  have ag5 : AgreesExcept xRegisters t4 t5 := effect5.agrees.mono (by simp [movR64Imm64Effect_components, xRegisters])
  have ag6 : AgreesExcept xRegisters t5 t6 := effect6.agrees.mono (by simp [mulR64Effect_components, xRegisters])
  have ag7 : AgreesExcept xRegisters t6 t7 := effect7.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag8 : AgreesExcept xRegisters t7 t8 := effect8.agrees.mono (by simp [movR64R64Effect_components, xRegisters])
  have ag9 : AgreesExcept xRegisters t8 t9 := effect9.agrees.mono (by simp [xorR32R32Effect_components, xRegisters])
  exact ⟨t9, stage9, effect9.rip, ⟨r6_9, r1_9, r9_9, r3_9⟩, r13_9, r15_9, (agree ag0 (agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 (agree ag8 ag9)))))))))⟩

end P256.Proofs.Sec1Serialize.Conversion
