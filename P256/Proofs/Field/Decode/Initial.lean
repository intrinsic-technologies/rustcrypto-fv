import P256.Proofs.Ecdh.Normalize.Conversion.State

set_option autoImplicit false
open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)

namespace P256.Proofs.Field.Decode

open P256.Proofs.Ecdh.Normalize.Conversion (Stage registers inputRegisters agrees_trans read_mem_of_agrees)
open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem initial [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip) (stage : Stage s start t boundary)
    (source : t.regValue .rsi = s.regValue .rsi) (rip : t.RIP = 0x114249) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x114270 ∧
      (let a := memLoad t.external (s.regValue .rsi) 64
       u.regValue .rcx = a <<< 32 ∧ u.regValue .r11 = a >>> 32 ∧
       u.regValue .r9 = a * 0xffffffff00000001 ∧
       u.regValue .rbx = mulHigh64 a 0xffffffff00000001) ∧
      u.regValue .r14 = 0xffffffff00000001 ∧ u.regValue .r13 = 0 ∧
      AgreesExcept inputRegisters t u := by
  let a := memLoad t.external (s.regValue .rsi) 64
  have code1 : CodeIn (codeRange 0x114249 [72, 139, 6]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x14249 _ (by decide) (by decide +kernel)
  have readable : MemReadable t ((AddrMode.base 6 .none).addr t 0x11424c) 8 := by
    change MemReadable t (t.regValue .rsi + 0) 8
    rw [source]
    exact stage.readable_offset 0 (by decide)
  obtain ⟨t1,step1,ready1,effect1⟩ := mov_r64_m64_effect_step 0x114249 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide) rfl rfl
    t stage.ready code1 ⟨rip,readable⟩
  change (movR64M64Effect 0x114249 0 (.base 6 .none) t).Holds t t1 at effect1
  have stage1 := stage.step_registers outside step1 ready1 effect1
    (by simp [movR64M64Effect_components]) (inProgram_of_textOffset 0x1424c (by decide))
  have r0_1 : t1.regValue .rax = a := by
    have h : t1.regValue .rax = memLoad t.external (t.regValue .rsi + 0) 64 := effect1.writes
    simpa [source, a] using h
  have ag1 : AgreesExcept inputRegisters t t1 := effect1.agrees.mono (by simp [movR64M64Effect_components,inputRegisters])
  have code2 : CodeIn (codeRange 0x11424c [73, 137, 195]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x1424c _ (by decide) (by decide +kernel)
  obtain ⟨t2,step2,ready2,effect2⟩ := mov_r64_r64_effect_step 0x11424c 0x49 0xc3 (by simp [RexWPrefix]) rfl
    t1 ready1 code2 effect1.rip
  change (movR64R64Effect 0x11424c 11 0 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers outside step2 ready2 effect2
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x1424f (by decide))
  have r11_2 : t2.regValue .r11 = a := by
    have h : t2.regValue .r11 = t1.regValue .rax := effect2.writes
    have p0 : t1.regValue .rax = a := r0_1
    rw [p0] at h
    exact h
  have ag2 : AgreesExcept inputRegisters t1 t2 := effect2.agrees.mono (by simp [movR64R64Effect_components,inputRegisters])
  have code3 : CodeIn (codeRange 0x11424f [72, 137, 193]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x1424f _ (by decide) (by decide +kernel)
  obtain ⟨t3,step3,ready3,effect3⟩ := mov_r64_r64_effect_step 0x11424f 0x48 0xc1 (by simp [RexWPrefix]) rfl
    t2 ready2 code3 effect2.rip
  change (movR64R64Effect 0x11424f 1 0 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers outside step3 ready3 effect3
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x14252 (by decide))
  have r1_3 : t3.regValue .rcx = a := by
    have h : t3.regValue .rcx = t2.regValue .rax := effect3.writes
    have p0 : t2.regValue .rax = a := (effect2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_1)
    rw [p0] at h
    exact h
  have ag3 : AgreesExcept inputRegisters t2 t3 := effect3.agrees.mono (by simp [movR64R64Effect_components,inputRegisters])
  have code4 : CodeIn (codeRange 0x114252 [72, 193, 225, 32]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x14252 _ (by decide) (by decide +kernel)
  obtain ⟨t4,step4,ready4,effect4⟩ := shl_r64_imm8_effect_step 0x114252 0x48 0xe1 32 (by simp [RexWPrefix]) (by decide) (by decide)
    t3 ready3 code4 effect3.rip
  change (shlR64Effect 0x114252 4 1 32 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers outside step4 ready4 effect4
    (by simp [shlR64Effect_components]) (inProgram_of_textOffset 0x14256 (by decide))
  have r1_4 : t4.regValue .rcx = a <<< 32 := by
    have h : t4.regValue .rcx = t3.regValue .rcx <<< 32 := effect4.writes
    have p1 : t3.regValue .rcx = a := r1_3
    rw [p1] at h
    exact h
  have ag4 : AgreesExcept inputRegisters t3 t4 := effect4.agrees.mono (by simp [shlR64Effect_components,inputRegisters])
  have code5 : CodeIn (codeRange 0x114256 [73, 190, 1, 0, 0, 0, 255, 255, 255, 255]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x14256 _ (by decide) (by decide +kernel)
  obtain ⟨t5,step5,ready5,effect5⟩ := mov_r64_imm64_effect_step 0x114256 0x49 0xbe (by simp [RexWPrefix]) (by decide) 0xffffffff00000001
    t4 ready4 code5 effect4.rip
  change (movR64Imm64Effect 0x114256 14 0xffffffff00000001 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers outside step5 ready5 effect5
    (by simp [movR64Imm64Effect_components]) (inProgram_of_textOffset 0x14260 (by decide))
  have r14_5 : t5.regValue .r14 = 0xffffffff00000001 := by
    exact effect5.writes
  have ag5 : AgreesExcept inputRegisters t4 t5 := effect5.agrees.mono (by simp [movR64Imm64Effect_components,inputRegisters])
  have code6 : CodeIn (codeRange 0x114260 [73, 247, 230]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x14260 _ (by decide) (by decide +kernel)
  obtain ⟨t6,step6,ready6,effect6⟩ := mul_r64_effect_step 0x114260 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)
    t5 ready5 code6 effect5.rip
  change (mulR64Effect 0x114260 14 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers outside step6 ready6 effect6
    (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x14263 (by decide))
  have r0_6 : t6.regValue .rax = a * 0xffffffff00000001 := by
    have h : t6.regValue .rax = t5.regValue .rax * t5.regValue .r14 := effect6.writes.1
    have p0 : t5.regValue .rax = a := (effect5.agrees.read (n := 64) (r := 0) (by simp [movR64Imm64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 0) (by simp [shlR64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_1))))
    have p14 : t5.regValue .r14 = 0xffffffff00000001 := r14_5
    rw [p0,p14] at h
    exact h
  have r2_6 : t6.regValue .rdx = mulHigh64 a 0xffffffff00000001 := by
    have h : t6.regValue .rdx = mulHigh64 (t5.regValue .rax) (t5.regValue .r14) := effect6.writes.2
    have p0 : t5.regValue .rax = a := (effect5.agrees.read (n := 64) (r := 0) (by simp [movR64Imm64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 0) (by simp [shlR64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans ((effect2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r0_1))))
    have p14 : t5.regValue .r14 = 0xffffffff00000001 := r14_5
    rw [p0,p14] at h
    exact h
  have ag6 : AgreesExcept inputRegisters t5 t6 := effect6.agrees.mono (by simp [mulR64Effect_components,inputRegisters])
  have code7 : CodeIn (codeRange 0x114263 [73, 137, 193]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x14263 _ (by decide) (by decide +kernel)
  obtain ⟨t7,step7,ready7,effect7⟩ := mov_r64_r64_effect_step 0x114263 0x49 0xc1 (by simp [RexWPrefix]) rfl
    t6 ready6 code7 effect6.rip
  change (movR64R64Effect 0x114263 9 0 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers outside step7 ready7 effect7
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x14266 (by decide))
  have r9_7 : t7.regValue .r9 = a * 0xffffffff00000001 := by
    have h : t7.regValue .r9 = t6.regValue .rax := effect7.writes
    have p0 : t6.regValue .rax = a * 0xffffffff00000001 := r0_6
    rw [p0] at h
    exact h
  have ag7 : AgreesExcept inputRegisters t6 t7 := effect7.agrees.mono (by simp [movR64R64Effect_components,inputRegisters])
  have code8 : CodeIn (codeRange 0x114266 [72, 137, 211]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x14266 _ (by decide) (by decide +kernel)
  obtain ⟨t8,step8,ready8,effect8⟩ := mov_r64_r64_effect_step 0x114266 0x48 0xd3 (by simp [RexWPrefix]) rfl
    t7 ready7 code8 effect7.rip
  change (movR64R64Effect 0x114266 3 2 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers outside step8 ready8 effect8
    (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x14269 (by decide))
  have r3_8 : t8.regValue .rbx = mulHigh64 a 0xffffffff00000001 := by
    have h : t8.regValue .rbx = t7.regValue .rdx := effect8.writes
    have p2 : t7.regValue .rdx = mulHigh64 a 0xffffffff00000001 := (effect7.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans (r2_6)
    rw [p2] at h
    exact h
  have ag8 : AgreesExcept inputRegisters t7 t8 := effect8.agrees.mono (by simp [movR64R64Effect_components,inputRegisters])
  have code9 : CodeIn (codeRange 0x114269 [73, 193, 235, 32]) t8 :=
    programText_slice (programLoaded_codeIn stage8.loaded) 0x14269 _ (by decide) (by decide +kernel)
  obtain ⟨t9,step9,ready9,effect9⟩ := shr_r64_imm8_effect_step 0x114269 0x49 0xeb 32 (by simp [RexWPrefix]) (by decide) (by decide)
    t8 ready8 code9 effect8.rip
  change (shrR64Effect 0x114269 4 11 32 t8).Holds t8 t9 at effect9
  have stage9 := stage8.step_registers outside step9 ready9 effect9
    (by simp [shrR64Effect_components]) (inProgram_of_textOffset 0x1426d (by decide))
  have r11_9 : t9.regValue .r11 = a >>> 32 := by
    have h : t9.regValue .r11 = t8.regValue .r11 >>> 32 := effect9.writes
    have p11 : t8.regValue .r11 = a := (effect8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 11) (by simp [movR64Imm64Effect_components])).trans ((effect4.agrees.read (n := 64) (r := 11) (by simp [shlR64Effect_components])).trans ((effect3.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans (r11_2))))))
    rw [p11] at h
    exact h
  have ag9 : AgreesExcept inputRegisters t8 t9 := effect9.agrees.mono (by simp [shrR64Effect_components,inputRegisters])
  have code10 : CodeIn (codeRange 0x11426d [69, 49, 237]) t9 :=
    programText_slice (programLoaded_codeIn stage9.loaded) 0x1426d _ (by decide) (by decide +kernel)
  obtain ⟨t10,step10,ready10,effect10⟩ := xor_r32_r32_rex_effect_step 0x11426d 0x45 0xed (by simp [RexNoWPrefix]) (by decide)
    t9 ready9 code10 effect9.rip
  change (xorR32R32Effect 0x11426d 3 13 13 t9).Holds t9 t10 at effect10
  have stage10 := stage9.step_registers outside step10 ready10 effect10
    (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x14270 (by decide))
  have r13_10 : t10.regValue .r13 = 0 := by
    have h := effect10.writes
    simp only [xorR32R32Effect, Write.AllHold, BitVec.xor_self, BitVec.setWidth_zero] at h
    exact h
  have ag10 : AgreesExcept inputRegisters t9 t10 := effect10.agrees.mono (by simp [xorR32R32Effect_components,inputRegisters])
  have final1 : t10.regValue .rcx = a <<< 32 := (effect10.agrees.read (n := 64) (r := 1) (by simp [xorR32R32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 1) (by simp [shrR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((effect5.agrees.read (n := 64) (r := 1) (by simp [movR64Imm64Effect_components])).trans (r1_4))))))
  have final11 : t10.regValue .r11 = a >>> 32 := (effect10.agrees.read (n := 64) (r := 11) (by simp [xorR32R32Effect_components])).trans (r11_9)
  have final9 : t10.regValue .r9 = a * 0xffffffff00000001 := (effect10.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 9) (by simp [shrR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r9_7)))
  have final3 : t10.regValue .rbx = mulHigh64 a 0xffffffff00000001 := (effect10.agrees.read (n := 64) (r := 3) (by simp [xorR32R32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 3) (by simp [shrR64Effect_components])).trans (r3_8))
  have final14 : t10.regValue .r14 = 0xffffffff00000001 := (effect10.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans ((effect9.agrees.read (n := 64) (r := 14) (by simp [shrR64Effect_components])).trans ((effect8.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect7.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((effect6.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r14_5)))))
  have final13 : t10.regValue .r13 = 0 := r13_10
  exact ⟨t10,stage10,effect10.rip,⟨final1,final11,final9,final3⟩,final14,final13,agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (agrees_trans (ag1) ag2) ag3) ag4) ag5) ag6) ag7) ag8) ag9) ag10⟩

end P256.Proofs.Field.Decode
