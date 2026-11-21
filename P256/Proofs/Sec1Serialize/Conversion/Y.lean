import P256.Proofs.Sec1Serialize.Conversion.Y.Round1
import P256.Proofs.Sec1Serialize.Conversion.Y.Round2
import P256.Proofs.Sec1Serialize.Conversion.Y.Round3
import P256.Proofs.Sec1Serialize.Conversion.Arithmetic
import P256.Proofs.Sec1Serialize.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Sec1Serialize.Conversion.SavePointer

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)


namespace P256.Proofs.Sec1Serialize.Conversion

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open Program Program.ScalarFrame
open P256.Proofs.Common.Encoding.Serialize
open X86 X86.Machine X86.UserProcess X86Proofs

private def yRegisters : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6, .reg 8, .reg 9, .reg 10, .reg 11, .flags, .rip]

theorem y_initial [Bindings] {s start t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x110d70 72 65 328) (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110ea5) (r14 : t.regValue .r14 = s.regValue .rsi)
    (r9 : t.regValue .r9 = 0xffffffff00000001) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110ec2 ∧
      (let a := (Operand.mem (s.regValue .rsi + 32) : Operand 64).read t
       u.regValue .rsi = a <<< 32 ∧ u.regValue .r11 = a >>> 32 ∧
       u.regValue .r9 = a * 0xffffffff00000001 ∧
       u.regValue .rbp = mulHigh64 a 0xffffffff00000001) ∧
      u.regValue .rcx = 0 ∧ AgreesExcept yRegisters t u := by
  let a := (Operand.mem (s.regValue .rsi + 32) : Operand 64).read t
  have code0 : CodeIn (codeRange 0x110ea5 [0x49,0x8b,0x46,0x20]) t :=
    programText_slice (programLoaded_codeIn stage.loaded) 0x10ea5 _
      (by decide +kernel) (by decide +kernel)
  have addr0 : (AddrMode.base 14 (.d8 32)).addr t 0x110ea9 = s.regValue .rsi + 32 := by
    change t.regValue .r14 + 32 = _
    rw [r14]
  have read0 : MemReadable t ((AddrMode.base 14 (.d8 32)).addr t 0x110ea9) 8 := by
    rw [addr0]
    exact input_readable pre stage.allocated (offset := 32) (by decide)
  obtain ⟨t0, step0, ready0, effect0⟩ := mov_r64_m64_effect_step 0x110ea5 0x49
    (by simp [RexWPrefix]) 0 (.base 14 (.d8 32)) (by decide) rfl rfl
    t stage.ready code0 ⟨rip, read0⟩
  change (movR64M64Effect 0x110ea5 0 (.base 14 (.d8 32)) t).Holds t t0 at effect0
  have stage0 := stage.step_registers pre step0 ready0 effect0 (by simp) (by simp)
    (inProgram_of_textOffset 0x10ea9 (by decide))
  have a0 : t0.regValue .rax = a := by
    have e := effect0.writes
    change t0.regValue .rax = (Operand.mem ((AddrMode.base 14 (.d8 32)).addr t 0x110ea9) : Operand 64).read t at e
    rw [addr0] at e
    exact e
  have k0 : t0.regValue .r9 = 0xffffffff00000001 := (effect0.agrees.read (n := 64) (r := 9) (by simp)).trans r9
  have code1 : CodeIn (codeRange 0x110ea9 [0x49,0x89,0xc3]) t0 :=
    programText_slice (programLoaded_codeIn stage0.loaded) 0x10ea9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, step1, ready1, effect1⟩ := mov_r64_r64_effect_step 0x110ea9 0x49 0xc3 (by simp [RexWPrefix]) (by decide)
    t0 ready0 code1 effect0.rip
  change (movR64R64Effect 0x110ea9 11 0 t0).Holds t0 t1 at effect1
  have stage1 := stage0.step_registers pre step1 ready1 effect1
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10eac (by decide))
  have r0_1 : t1.regValue .rax = a :=
    (effect1.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans a0
  have r9_1 : t1.regValue .r9 = 0xffffffff00000001 :=
    (effect1.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans k0
  have r11_1 : t1.regValue .r11 = a := by
    have e : t1.regValue .r11 = t0.regValue .rax := effect1.writes
    rw [a0] at e
    exact e
  have code2 : CodeIn (codeRange 0x110eac [0x48,0x89,0xc6]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x10eac _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, step2, ready2, effect2⟩ := mov_r64_r64_effect_step 0x110eac 0x48 0xc6 (by simp [RexWPrefix]) (by decide)
    t1 ready1 code2 effect1.rip
  change (movR64R64Effect 0x110eac 6 0 t1).Holds t1 t2 at effect2
  have stage2 := stage1.step_registers pre step2 ready2 effect2
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10eaf (by decide))
  have r0_2 : t2.regValue .rax = a :=
    (effect2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_1
  have r9_2 : t2.regValue .r9 = 0xffffffff00000001 :=
    (effect2.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans r9_1
  have r11_2 : t2.regValue .r11 = a :=
    (effect2.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans r11_1
  have r6_2 : t2.regValue .rsi = a := by
    have e : t2.regValue .rsi = t1.regValue .rax := effect2.writes
    rw [r0_1] at e
    exact e
  have code3 : CodeIn (codeRange 0x110eaf [0x48,0xc1,0xe6,0x20]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x10eaf _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, step3, ready3, effect3⟩ := shl_r64_imm8_effect_step 0x110eaf 0x48 0xe6 0x20 (by simp [RexWPrefix]) (by decide) (by decide)
    t2 ready2 code3 effect2.rip
  change (shlR64Effect 0x110eaf 4 6 32 t2).Holds t2 t3 at effect3
  have stage3 := stage2.step_registers pre step3 ready3 effect3
    (by simp [shlR64Effect_components]) (by simp [shlR64Effect_components]) (inProgram_of_textOffset 0x10eb3 (by decide))
  have r0_3 : t3.regValue .rax = a :=
    (effect3.agrees.read (n := 64) (r := 0) (by simp [shlR64Effect_components])).trans r0_2
  have r9_3 : t3.regValue .r9 = 0xffffffff00000001 :=
    (effect3.agrees.read (n := 64) (r := 9) (by simp [shlR64Effect_components])).trans r9_2
  have r11_3 : t3.regValue .r11 = a :=
    (effect3.agrees.read (n := 64) (r := 11) (by simp [shlR64Effect_components])).trans r11_2
  have r6_3 : t3.regValue .rsi = a <<< 32 := by
    have e : t3.regValue .rsi = t2.regValue .rsi <<< 32 := effect3.writes
    rw [r6_2] at e
    exact e
  have code4 : CodeIn (codeRange 0x110eb3 [0x49,0xf7,0xe1]) t3 :=
    programText_slice (programLoaded_codeIn stage3.loaded) 0x10eb3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, step4, ready4, effect4⟩ := mul_r64_effect_step 0x110eb3 0x49 0xe1 (by simp [RexWPrefix]) (by decide) (by decide)
    t3 ready3 code4 effect3.rip
  change (mulR64Effect 0x110eb3 9 t3).Holds t3 t4 at effect4
  have stage4 := stage3.step_registers pre step4 ready4 effect4
    (by simp [mulR64Effect_components]) (by simp [mulR64Effect_components]) (inProgram_of_textOffset 0x10eb6 (by decide))
  have r9_4 : t4.regValue .r9 = 0xffffffff00000001 :=
    (effect4.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans r9_3
  have r11_4 : t4.regValue .r11 = a :=
    (effect4.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans r11_3
  have r6_4 : t4.regValue .rsi = a <<< 32 :=
    (effect4.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans r6_3
  have r0_4 : t4.regValue .rax = a * 0xffffffff00000001 := by
    have e : t4.regValue .rax = t3.regValue .rax * t3.regValue .r9 := effect4.writes.1
    rw [r0_3, r9_3] at e
    exact e
  have r2_4 : t4.regValue .rdx = mulHigh64 a 0xffffffff00000001 := by
    have e : t4.regValue .rdx = mulHigh64 (t3.regValue .rax) (t3.regValue .r9) := effect4.writes.2
    rw [r0_3, r9_3] at e
    exact e
  have code5 : CodeIn (codeRange 0x110eb6 [0x49,0x89,0xc1]) t4 :=
    programText_slice (programLoaded_codeIn stage4.loaded) 0x10eb6 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, step5, ready5, effect5⟩ := mov_r64_r64_effect_step 0x110eb6 0x49 0xc1 (by simp [RexWPrefix]) (by decide)
    t4 ready4 code5 effect4.rip
  change (movR64R64Effect 0x110eb6 9 0 t4).Holds t4 t5 at effect5
  have stage5 := stage4.step_registers pre step5 ready5 effect5
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10eb9 (by decide))
  have r11_5 : t5.regValue .r11 = a :=
    (effect5.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans r11_4
  have r6_5 : t5.regValue .rsi = a <<< 32 :=
    (effect5.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans r6_4
  have r0_5 : t5.regValue .rax = a * 0xffffffff00000001 :=
    (effect5.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_4
  have r2_5 : t5.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect5.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans r2_4
  have r9_5 : t5.regValue .r9 = a * 0xffffffff00000001 := by
    have e : t5.regValue .r9 = t4.regValue .rax := effect5.writes
    rw [r0_4] at e
    exact e
  have code6 : CodeIn (codeRange 0x110eb9 [0x48,0x89,0xd5]) t5 :=
    programText_slice (programLoaded_codeIn stage5.loaded) 0x10eb9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, step6, ready6, effect6⟩ := mov_r64_r64_effect_step 0x110eb9 0x48 0xd5 (by simp [RexWPrefix]) (by decide)
    t5 ready5 code6 effect5.rip
  change (movR64R64Effect 0x110eb9 5 2 t5).Holds t5 t6 at effect6
  have stage6 := stage5.step_registers pre step6 ready6 effect6
    (by simp [movR64R64Effect_components]) (by simp [movR64R64Effect_components]) (inProgram_of_textOffset 0x10ebc (by decide))
  have r11_6 : t6.regValue .r11 = a :=
    (effect6.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans r11_5
  have r6_6 : t6.regValue .rsi = a <<< 32 :=
    (effect6.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans r6_5
  have r0_6 : t6.regValue .rax = a * 0xffffffff00000001 :=
    (effect6.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans r0_5
  have r2_6 : t6.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect6.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans r2_5
  have r9_6 : t6.regValue .r9 = a * 0xffffffff00000001 :=
    (effect6.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans r9_5
  have r5_6 : t6.regValue .rbp = mulHigh64 a 0xffffffff00000001 := by
    have e : t6.regValue .rbp = t5.regValue .rdx := effect6.writes
    rw [r2_5] at e
    exact e
  have code7 : CodeIn (codeRange 0x110ebc [0x49,0xc1,0xeb,0x20]) t6 :=
    programText_slice (programLoaded_codeIn stage6.loaded) 0x10ebc _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, step7, ready7, effect7⟩ := shr_r64_imm8_effect_step 0x110ebc 0x49 0xeb 0x20 (by simp [RexWPrefix]) (by decide) (by decide)
    t6 ready6 code7 effect6.rip
  change (shrR64Effect 0x110ebc 4 11 32 t6).Holds t6 t7 at effect7
  have stage7 := stage6.step_registers pre step7 ready7 effect7
    (by simp [shrR64Effect_components]) (by simp [shrR64Effect_components]) (inProgram_of_textOffset 0x10ec0 (by decide))
  have r6_7 : t7.regValue .rsi = a <<< 32 :=
    (effect7.agrees.read (n := 64) (r := 6) (by simp [shrR64Effect_components])).trans r6_6
  have r0_7 : t7.regValue .rax = a * 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 0) (by simp [shrR64Effect_components])).trans r0_6
  have r2_7 : t7.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 2) (by simp [shrR64Effect_components])).trans r2_6
  have r9_7 : t7.regValue .r9 = a * 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 9) (by simp [shrR64Effect_components])).trans r9_6
  have r5_7 : t7.regValue .rbp = mulHigh64 a 0xffffffff00000001 :=
    (effect7.agrees.read (n := 64) (r := 5) (by simp [shrR64Effect_components])).trans r5_6
  have r11_7 : t7.regValue .r11 = a >>> 32 := by
    have e : t7.regValue .r11 = t6.regValue .r11 >>> 32 := effect7.writes
    rw [r11_6] at e
    exact e
  have code8 : CodeIn (codeRange 0x110ec0 [0x31,0xc9]) t7 :=
    programText_slice (programLoaded_codeIn stage7.loaded) 0x10ec0 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, step8, ready8, effect8⟩ := xor_r32_r32_effect_step 0x110ec0 0xc9 (by decide)
    t7 ready7 code8 effect7.rip
  change (xorR32R32Effect 0x110ec0 2 1 1 t7).Holds t7 t8 at effect8
  have stage8 := stage7.step_registers pre step8 ready8 effect8
    (by simp [xorR32R32Effect_components]) (by simp [xorR32R32Effect_components]) (inProgram_of_textOffset 0x10ec2 (by decide))
  have r6_8 : t8.regValue .rsi = a <<< 32 :=
    (effect8.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components])).trans r6_7
  have r0_8 : t8.regValue .rax = a * 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 0) (by simp [xorR32R32Effect_components])).trans r0_7
  have r2_8 : t8.regValue .rdx = mulHigh64 a 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 2) (by simp [xorR32R32Effect_components])).trans r2_7
  have r9_8 : t8.regValue .r9 = a * 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans r9_7
  have r5_8 : t8.regValue .rbp = mulHigh64 a 0xffffffff00000001 :=
    (effect8.agrees.read (n := 64) (r := 5) (by simp [xorR32R32Effect_components])).trans r5_7
  have r11_8 : t8.regValue .r11 = a >>> 32 :=
    (effect8.agrees.read (n := 64) (r := 11) (by simp [xorR32R32Effect_components])).trans r11_7
  have r1_8 : t8.regValue .rcx = 0 := by
    have e : t8.regValue .rcx = (((Operand.reg 1 : Operand 32).read t7) ^^^ ((Operand.reg 1 : Operand 32).read t7)).setWidth 64 := effect8.writes
    simp only [BitVec.xor_self, BitVec.setWidth_zero] at e
    exact e.trans (by rfl)
  have agree {a b c : RamState} (ha : AgreesExcept yRegisters a b) (hb : AgreesExcept yRegisters b c) : AgreesExcept yRegisters a c :=
    (ha.trans hb).mono fun _ hc => (List.mem_append.mp hc).elim id id
  have ag0 : AgreesExcept yRegisters t t0 := effect0.agrees.mono (by simp [movR64M64Effect_components, yRegisters])
  have ag1 : AgreesExcept yRegisters t0 t1 := effect1.agrees.mono (by simp [movR64R64Effect_components, yRegisters])
  have ag2 : AgreesExcept yRegisters t1 t2 := effect2.agrees.mono (by simp [movR64R64Effect_components, yRegisters])
  have ag3 : AgreesExcept yRegisters t2 t3 := effect3.agrees.mono (by simp [shlR64Effect_components, yRegisters])
  have ag4 : AgreesExcept yRegisters t3 t4 := effect4.agrees.mono (by simp [mulR64Effect_components, yRegisters])
  have ag5 : AgreesExcept yRegisters t4 t5 := effect5.agrees.mono (by simp [movR64R64Effect_components, yRegisters])
  have ag6 : AgreesExcept yRegisters t5 t6 := effect6.agrees.mono (by simp [movR64R64Effect_components, yRegisters])
  have ag7 : AgreesExcept yRegisters t6 t7 := effect7.agrees.mono (by simp [shrR64Effect_components, yRegisters])
  have ag8 : AgreesExcept yRegisters t7 t8 := effect8.agrees.mono (by simp [xorR32R32Effect_components, yRegisters])
  exact ⟨t8, stage8, effect8.rip, ⟨r6_8, r11_8, r9_8, r5_8⟩, r1_8,
    agree ag0 (agree ag1 (agree ag2 (agree ag3 (agree ag4 (agree ag5 (agree ag6 (agree ag7 ag8)))))))⟩

theorem convert_y_mode [bindings : Bindings] {s start t : RamState}
    {boundary : ReturnBoundary} {x y : Nat} {mode : BitVec 32}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110ea5)
    (input : Field.MontgomeryAt t (s.regValue .rsi + 32) y)
    (x0 : t.regValue .rbx = canonicalLimb x 0)
    (x1 : t.regValue .r15 = canonicalLimb x 1)
    (x2 : t.regValue .r12 = canonicalLimb x 2)
    (x3 : t.regValue .r13 = canonicalLimb x 3)
    (r9 : t.regValue .r9 = 0xffffffff00000001)
    (r14 : t.regValue .r14 = s.regValue .rsi)
    (rdi : t.regValue .rdi = s.regValue .rdi)
    (compress : (Operand.mem (stackPtr s - 300) : Operand 32).read t = mode) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110fdc ∧ Converted u x y ∧
      u.regValue .rdi = s.regValue .rdi ∧ (Operand.mem (stackPtr s - 300) : Operand 32).read u = mode ∧
      (Operand.mem (s.regValue .rsp - 192) : Operand 64).read u = s.regValue .rsi := by
  let a0 := (Operand.mem (s.regValue .rsi + 32) : Operand 64).read t
  let a1 := (Operand.mem (s.regValue .rsi + 40) : Operand 64).read t
  let a2 := (Operand.mem (s.regValue .rsi + 48) : Operand 64).read t
  let a3 := (Operand.mem (s.regValue .rsi + 56) : Operand 64).read t
  let v1 := Montgomery.compilerRoundBV (a0 <<< 32) (a0 >>> 32)
    (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001) a1
  let v2 := Montgomery.compilerRoundBV v1.1 v1.2.1 v1.2.2.1 v1.2.2.2 a2
  obtain ⟨t0, stage0, rip0, vals0, zero0, agree0⟩ := y_initial pre stage rip r14 r9
  have mem0 : t0.external = t.external := agree0.external (by simp [yRegisters, Component.Covers])
  have pointer0 : t0.regValue .r14 = s.regValue .rsi :=
    (agree0.read (n := 64) (r := 14) (by simp [yRegisters])).trans r14
  have load1 : (Operand.mem (s.regValue .rsi + 40) : Operand 64).read t0 = a1 := by
    change memLoad t0.external _ _ = _
    rw [mem0]
    rfl
  obtain ⟨t1, stage1, rip1, vals1, zero1, agree1⟩ := y_round_one pre stage0 rip0 pointer0
    (a0 <<< 32) (a0 >>> 32) (a0 * 0xffffffff00000001) (mulHigh64 a0 0xffffffff00000001)
    a1 vals0.1 vals0.2.1 vals0.2.2.1 vals0.2.2.2 zero0 load1
  change AgreesExcept yRegisters t0 t1 at agree1
  change t1.regValue .r8 = v1.1 ∧ t1.regValue .r10 = v1.2.1 ∧
    t1.regValue .rsi = v1.2.2.1 ∧ t1.regValue .r11 = v1.2.2.2 at vals1
  have mem1 : t1.external = t.external :=
    (agree1.external (by simp [yRegisters, Component.Covers])).trans mem0
  have pointer1 : t1.regValue .r14 = s.regValue .rsi :=
    (agree1.read (n := 64) (r := 14) (by simp [yRegisters])).trans pointer0
  have load2 : (Operand.mem (s.regValue .rsi + 48) : Operand 64).read t1 = a2 := by
    change memLoad t1.external _ _ = _
    rw [mem1]
    rfl
  obtain ⟨t2, stage2, rip2, vals2, zero2, agree2⟩ := y_round_two pre stage1 rip1 pointer1
    v1.1 v1.2.1 v1.2.2.1 v1.2.2.2 a2 vals1.1 vals1.2.1 vals1.2.2.1 vals1.2.2.2 zero1 load2
  change AgreesExcept yRegisters t1 t2 at agree2
  change t2.regValue .r9 = v2.1 ∧ t2.regValue .rbp = v2.2.1 ∧
    t2.regValue .r8 = v2.2.2.1 ∧ t2.regValue .r10 = v2.2.2.2 at vals2
  have mem2 : t2.external = t.external :=
    (agree2.external (by simp [yRegisters, Component.Covers])).trans mem1
  have pointer2 : t2.regValue .r14 = s.regValue .rsi :=
    (agree2.read (n := 64) (r := 14) (by simp [yRegisters])).trans pointer1
  have compress2 : (Operand.mem (stackPtr s - 300) : Operand 32).read t2 = mode := by
    change memLoad t2.external _ _ = mode
    rw [mem2]
    exact compress
  obtain ⟨t3, stage3, rip3, agree3, saved3, compress3⟩ :=
    save_input_pointer_mode pre stage2 rip2 compress2
  have load3 : (Operand.mem (s.regValue .rsi + 56) : Operand 64).read t3 = a3 := by
    apply memLoad_congr
    intro i hi
    have he := (input_byte pre stage3.toFrameState (i := 56+i) (by omega)).trans
      (input_byte pre stage.toFrameState (i := 56+i) (by omega)).symm
    simpa only [memByte, PhysicalMemory.read, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat]
      using congrArg (fun x => x.getD 0) he
  have pointer3 : t3.regValue .r14 = s.regValue .rsi :=
    (agree3.read (n := 64) (r := 14) (by simp)).trans pointer2
  obtain ⟨u, stage4, rip4, vals4, agree4⟩ := y_round_three pre stage3 rip3 pointer3
    v2.1 v2.2.1 v2.2.2.1 v2.2.2.2 a3
    ((agree3.read (n := 64) (r := 9) (by simp)).trans vals2.1)
    ((agree3.read (n := 64) (r := 5) (by simp)).trans vals2.2.1)
    ((agree3.read (n := 64) (r := 8) (by simp)).trans vals2.2.2.1)
    ((agree3.read (n := 64) (r := 10) (by simp)).trans vals2.2.2.2)
    ((agree3.read (n := 64) (r := 1) (by simp)).trans zero2) load3
  change AgreesExcept yRegisters t3 u at agree4
  have mem4 : u.external = t3.external := agree4.external (by simp [yRegisters, Component.Covers])
  have total : AgreesExcept (yRegisters ++ [.mem (s.regValue .rsp - 192) 8]) t u := by
    apply (agree0.trans (agree1.trans (agree2.trans (agree3.trans agree4)))).mono
    intro c hc
    simp only [List.mem_append] at hc ⊢
    rcases hc with hc | hc | hc | hc | hc
    · exact .inl hc
    · exact .inl hc
    · exact .inl hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact .inr (List.mem_cons_self ..)
      · simp [yRegisters]
    · exact .inl hc
  have math : compilerConversionBV a0 a1 a2 a3 =
      (canonicalLimb y 0, canonicalLimb y 1, canonicalLimb y 2, canonicalLimb y 3) := by
    have hm := compilerConversionBV_of_montgomeryAt input
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    exact hm
  change u.regValue .rsi = (compilerConversionBV a0 a1 a2 a3).1 ∧
    u.regValue .r11 = (compilerConversionBV a0 a1 a2 a3).2.1 ∧
    u.regValue .rax = (compilerConversionBV a0 a1 a2 a3).2.2.1 ∧
    u.regValue .rdx = (compilerConversionBV a0 a1 a2 a3).2.2.2 at vals4
  rw [math] at vals4
  refine ⟨u, stage4, rip4, ?_, ?_, ?_, ?_⟩
  · exact ⟨(total.read (n := 64) (r := 3) (by simp [yRegisters])).trans x0,
      (total.read (n := 64) (r := 15) (by simp [yRegisters])).trans x1,
      (total.read (n := 64) (r := 12) (by simp [yRegisters])).trans x2,
      (total.read (n := 64) (r := 13) (by simp [yRegisters])).trans x3,
      vals4.1, vals4.2.1, vals4.2.2.1, vals4.2.2.2⟩
  · exact (total.read (n := 64) (r := 7) (by simp [yRegisters])).trans rdi
  · change memLoad u.external _ _ = mode
    rw [mem4]
    exact compress3
  · change memLoad u.external _ _ = _
    rw [mem4]
    exact saved3.trans pointer2

theorem convert_y_correct [bindings : Bindings] {s start t : RamState}
    {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s start t boundary)
    (rip : t.RIP = 0x110ea5)
    (input : Field.MontgomeryAt t (s.regValue .rsi + 32) y)
    (x0 : t.regValue .rbx = canonicalLimb x 0)
    (x1 : t.regValue .r15 = canonicalLimb x 1)
    (x2 : t.regValue .r12 = canonicalLimb x 2)
    (x3 : t.regValue .r13 = canonicalLimb x 3)
    (r9 : t.regValue .r9 = 0xffffffff00000001)
    (r14 : t.regValue .r14 = s.regValue .rsi)
    (rdi : t.regValue .rdi = s.regValue .rdi)
    (compress : compressionFlag s t) :
    ∃ u, Stage s start u boundary ∧ u.RIP = 0x110fdc ∧ Converted u x y ∧
      u.regValue .rdi = s.regValue .rdi ∧ compressionFlag s u ∧
      (Operand.mem (s.regValue .rsp - 192) : Operand 64).read u = s.regValue .rsi :=
  convert_y_mode pre stage rip input x0 x1 x2 x3 r9 r14 rdi compress

end P256.Proofs.Sec1Serialize.Conversion
