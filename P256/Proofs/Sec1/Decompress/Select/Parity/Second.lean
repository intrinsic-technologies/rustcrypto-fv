import P256.Proofs.Sec1.Decompress.Select.Parity.First

set_option autoImplicit false

open P256.Proofs.Sec1Serialize (canonicalLimb)
open P256.Proofs.Sec1Serialize.Conversion (compilerConversionBV compilerConversionBV_of_montgomeryAt)
open P256.Proofs.Sec1Serialize.Conversion.Montgomery (compilerRoundBV)
open P256.Proofs.Common.Instructions (addR64M64Effect addR64M64Effect_components add_r64_m64_effect_step mulHigh64 mulR64Effect mulR64Effect_components mul_r64_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8Imm8Effect and_sil_one_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR32Imm8Effect adcR32Imm8Effect_components adcR32R32Effect adcR32R32Effect_components adcR64Imm8Effect adcR64Imm8Effect_components adcR64R64Effect adcR64R64Effect_components adcSpec adcSpec_result adc_r32_imm8_effect_step adc_r32_r32_effect_step adc_r32_r32_rex_effect_step adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.MovzxByte (movzxR32R8Effect movzx_r32_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.Setb (setccR8Effect setccR8Effect_components setcc_r8_effect_step setcc_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft (shlR64Effect shlR64Effect_components shl_r64_imm8_effect_step)
open P256.Proofs.Program (CalleePre boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice readyToStep)
open P256.Proofs.Field (MontgomeryAt)

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace P256.Proofs.Sec1.Decompress.Select.Parity

set_option maxHeartbeats 2000000 in
theorem second_block [Bindings] {u : RamState} {boundary : ReturnBoundary} (a b : BitVec 64) (c : BitVec 32)
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x10ffd7)
    (input : (Operand.reg 9 : Operand 64).read u = a ∧
      (Operand.reg 7 : Operand 64).read u = b ∧
      (Operand.reg 6 : Operand 64).read u = c.setWidth 64 ∧
      (Operand.reg 14 : Operand 64).read u = 0xffffffffffffffff ∧
      (Operand.reg 3 : Operand 64).read u = 0xffffffff)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ t.RIP = 0x110009 ∧
      AgreesExcept registers u t ∧ (Operand.reg 8 : Operand 64).read t = (second a b c (memLoad u.external (stackPtr u+168) 64)).1 ∧
      (Operand.reg 1 : Operand 64).read t = (second a b c (memLoad u.external (stackPtr u+168) 64)).2.setWidth 64 ∧
      (Operand.reg 14 : Operand 64).read t = 0xffffffffffffffff := by
  let a0 := memLoad u.external (stackPtr u+152) 64
  let a1 := memLoad u.external (stackPtr u+160) 64
  let a2 := memLoad u.external (stackPtr u+168) 64
  let a3 := memLoad u.external (stackPtr u+176) 64
  rcases input with ⟨input9, input7, input6, input14, input3⟩
  have mem0 : u.external = u.external := rfl
  have agg0 : AgreesExcept registers u u := AgreesExcept.refl _ _
  have code1 : CodeIn (codeRange 0x10ffd7 [0x45, 0x31, 0xd2]) u :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem0) 0xffd7 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, run1, ready1, he1⟩ :=
    (xor_r32_r32_rex_effect_step 0x10ffd7 0x45 0xd2 (by simp [RexNoWPrefix]) (by decide)).advances ready code1 rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffda (by decide)))
  change (xorR32R32Effect 0x10ffd7 3 10 10 u).Holds u t1 at he1
  have mem1 : t1.external = u.external :=
    (he1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans mem0
  have agg1 : AgreesExcept registers u t1 :=
    (agg0.trans he1.agrees).mono (by simp [xorR32R32Effect_components, registers])
  have r1_10 : (Operand.reg 10 : Operand 64).read t1 = 0 := by
    have he : (Operand.reg 10 : Operand 64).read t1 = (((Operand.reg 10 : Operand 32).read u) ^^^ ((Operand.reg 10 : Operand 32).read u)).setWidth 64 := he1.writes
    simp only [read32, BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he
  have r1_9 : (Operand.reg 9 : Operand 64).read t1 = a := (he1.agrees.read (n := 64) (r := 9) (by simp [xorR32R32Effect_components])).trans (input9)
  have r1_4 : (Operand.reg 4 : Operand 64).read t1 = ((Operand.reg 4 : Operand 64).read u) := (he1.agrees.read (n := 64) (r := 4) (by simp [xorR32R32Effect_components])).trans ((by rfl))
  have addr2 : (AddrMode.sib 4 none 0 (.d32 168)).addr t1 0x10ffe2 = stackPtr u+168 := by
    change (Operand.reg 4 : Operand 64).read t1 + 168 = _
    rw [r1_4]
    rfl
  have read2 : MemReadable t1 ((AddrMode.sib 4 none 0 (.d32 168)).addr t1 0x10ffe2) 8 := by
    rw [addr2]
    exact (readable 2 (by decide)).of_external_eq mem1
  let v2 := addSpec (a) (a2)
  have code2 : CodeIn (codeRange 0x10ffda [0x4c, 0x3, 0x8c, 0x24, 0xa8, 0x0, 0x0, 0x0]) t1 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem1) 0xffda _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, run2, ready2, he2⟩ :=
    (add_r64_m64_effect_step 0x10ffda 0x4c (by simp [RexWPrefix]) 1 (AddrMode.sib 4 none 0 (.d32 168)) (by decide) rfl rfl).advances ready1 code2 ⟨he1.rip, read2⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0xffe2 (by decide)))
  change (addR64M64Effect 0x10ffda 9 (AddrMode.sib 4 none 0 (.d32 168)) t1).Holds t1 t2 at he2
  have mem2 : t2.external = u.external :=
    (he2.agrees.external (by simp [addR64M64Effect_components, Component.Covers])).trans mem1
  have agg2 : AgreesExcept registers u t2 :=
    (agg1.trans he2.agrees).mono (by simp [addR64M64Effect_components, registers])
  have r2_9 : (Operand.reg 9 : Operand 64).read t2 = v2.1 := by
    have he : (Operand.reg 9 : Operand 64).read t2 = (addSpec ((Operand.reg 9 : Operand 64).read t1) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 168)).addr t1 0x10ffe2) : Operand 64).read t1)).1 := he2.writes
    simp only [r1_9, addr2, mem1, readMem] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = v2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read t1) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 168)).addr t1 0x10ffe2) : Operand 64).read t1)).2.CF := he2.flags.1
    simp only [r1_9, addr2, mem1, readMem] at he
    exact he
  have r2_10 : (Operand.reg 10 : Operand 64).read t2 = 0 := (he2.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans (r1_10)
  have code3 : CodeIn (codeRange 0x10ffe2 [0x41, 0xf, 0x92, 0xc2]) t2 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem2) 0xffe2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, run3, ready3, he3⟩ :=
    (setcc_r8_rex_effect_step 0x10ffe2 0x41 0x92 0xc2 (by simp [RexPrefix]) (.inl rfl) (by decide)).advances ready2 code3 he2.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffe6 (by decide)))
  change (setccR8Effect 0x10ffe2 4 10 2 t2).Holds t2 t3 at he3
  have mem3 : t3.external = u.external :=
    (he3.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem2
  have agg3 : AgreesExcept registers u t3 :=
    (agg2.trans he3.agrees).mono (by simp [setccR8Effect_components, registers])
  have r3_10 : (Operand.reg 10 : Operand 64).read t3 = (BitVec.ofBool v2.2.CF).setWidth 64 := by
    have he : (Operand.reg 10 : Operand 64).read t3 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) ((Operand.reg 10 : Operand 64).read t2) := he3.writes
    simp only [r2_10, cf2, P256.Proofs.Sec1Serialize.Conversion.setb_zero] at he
    exact he
  have r3_9 : (Operand.reg 9 : Operand 64).read t3 = v2.1 := (he3.agrees.read (n := 64) (r := 9) (by simp [setccR8Effect_components])).trans (r2_9)
  have code4 : CodeIn (codeRange 0x10ffe6 [0x4c, 0x89, 0xc8]) t3 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem3) 0xffe6 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, run4, ready4, he4⟩ :=
    (mov_r64_r64_effect_step 0x10ffe6 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances ready3 code4 he3.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffe9 (by decide)))
  change (movR64R64Effect 0x10ffe6 0 9 t3).Holds t3 t4 at he4
  have mem4 : t4.external = u.external :=
    (he4.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem3
  have agg4 : AgreesExcept registers u t4 :=
    (agg3.trans he4.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r4_0 : (Operand.reg 0 : Operand 64).read t4 = v2.1 := by
    have he : (Operand.reg 0 : Operand 64).read t4 = ((Operand.reg 9 : Operand 64).read t3) := he4.writes
    simp only [r3_9] at he
    exact he
  have r4_14 : (Operand.reg 14 : Operand 64).read t4 = 0xffffffffffffffff := (he4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 14) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 14) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (input14))))
  let v5 := ((v2.1)*(0xffffffffffffffff), mulHigh64 (v2.1) (0xffffffffffffffff))
  have code5 : CodeIn (codeRange 0x10ffe9 [0x49, 0xf7, 0xe6]) t4 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem4) 0xffe9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, run5, ready5, he5⟩ :=
    (mul_r64_effect_step 0x10ffe9 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 code5 he4.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffec (by decide)))
  change (mulR64Effect 0x10ffe9 14 t4).Holds t4 t5 at he5
  have mem5 : t5.external = u.external :=
    (he5.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem4
  have agg5 : AgreesExcept registers u t5 :=
    (agg4.trans he5.agrees).mono (by simp [mulR64Effect_components, registers])
  have r5_0 : (Operand.reg 0 : Operand 64).read t5 = v5.1 := by
    have he : (Operand.reg 0 : Operand 64).read t5 = ((Operand.reg 0 : Operand 64).read t4) * ((Operand.reg 14 : Operand 64).read t4) := he5.writes.1
    simp only [r4_0, r4_14] at he
    exact he
  have r5_2 : (Operand.reg 2 : Operand 64).read t5 = v5.2 := by
    have he : (Operand.reg 2 : Operand 64).read t5 = mulHigh64 ((Operand.reg 0 : Operand 64).read t4) ((Operand.reg 14 : Operand 64).read t4) := he5.writes.2
    simp only [r4_0, r4_14] at he
    exact he
  have r5_9 : (Operand.reg 9 : Operand 64).read t5 = v2.1 := (he5.agrees.read (n := 64) (r := 9) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 9) (by simp [movR64R64Effect_components])).trans (r3_9))
  let v6 := addSpec (v5.1) (v2.1)
  have code6 : CodeIn (codeRange 0x10ffec [0x4c, 0x1, 0xc8]) t5 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem5) 0xffec _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, run6, ready6, he6⟩ :=
    (add_r64_r64_effect_step 0x10ffec 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances ready5 code6 he5.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffef (by decide)))
  change (addR64R64Effect 0x10ffec 0 9 t5).Holds t5 t6 at he6
  have mem6 : t6.external = u.external :=
    (he6.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem5
  have agg6 : AgreesExcept registers u t6 :=
    (agg5.trans he6.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r6_0 : (Operand.reg 0 : Operand 64).read t6 = v6.1 := by
    have he : (Operand.reg 0 : Operand 64).read t6 = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 9 : Operand 64).read t5))).1 := he6.writes
    simp only [r5_0, r5_9] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = v6.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 9 : Operand 64).read t5))).2.CF := he6.flags.1
    simp only [r5_0, r5_9] at he
    exact he
  have r6_10 : (Operand.reg 10 : Operand 64).read t6 = (BitVec.ofBool v2.2.CF).setWidth 64 := (he6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r3_10)))
  have r6_2 : (Operand.reg 2 : Operand 64).read t6 = v5.2 := (he6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r5_2)
  have carry7 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf6
  let v7 := adcSpec ((BitVec.ofBool v2.2.CF).setWidth 64) (v5.2) (BitVec.ofBool v6.2.CF)
  have code7 : CodeIn (codeRange 0x10ffef [0x49, 0x11, 0xd2]) t6 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem6) 0xffef _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, run7, ready7, he7⟩ :=
    (adc_r64_r64_effect_step 0x10ffef 0x49 0xd2 (by simp [RexWPrefix]) (by decide)).advances ready6 code7 he6.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xfff2 (by decide)))
  change (adcR64R64Effect 0x10ffef 10 2 t6).Holds t6 t7 at he7
  have mem7 : t7.external = u.external :=
    (he7.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem6
  have agg7 : AgreesExcept registers u t7 :=
    (agg6.trans he7.agrees).mono (by simp [adcR64R64Effect_components, registers])
  have r7_10 : (Operand.reg 10 : Operand 64).read t7 = v7.1 := by
    have he : (Operand.reg 10 : Operand 64).read t7 = (adcSpec ((Operand.reg 10 : Operand 64).read t6) (((Operand.reg 2 : Operand 64).read t6)) (t6.RFLAGS.extractLsb' 0 1)).1 := he7.writes
    simp only [r6_10, r6_2, carry7] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = v7.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec ((Operand.reg 10 : Operand 64).read t6) (((Operand.reg 2 : Operand 64).read t6)) (t6.RFLAGS.extractLsb' 0 1)).2.CF := he7.flags.1
    simp only [r6_10, r6_2, carry7] at he
    exact he
  have r7_9 : (Operand.reg 9 : Operand 64).read t7 = v2.1 := (he7.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 9) (by simp [addR64R64Effect_components])).trans (r5_9))
  have code8 : CodeIn (codeRange 0x10fff2 [0x4c, 0x89, 0xc8]) t7 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem7) 0xfff2 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, run8, ready8, he8⟩ :=
    (mov_r64_r64_effect_step 0x10fff2 0x4c 0xc8 (by simp [RexWPrefix]) (by decide)).advances ready7 code8 he7.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xfff5 (by decide)))
  change (movR64R64Effect 0x10fff2 0 9 t7).Holds t7 t8 at he8
  have mem8 : t8.external = u.external :=
    (he8.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem7
  have agg8 : AgreesExcept registers u t8 :=
    (agg7.trans he8.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r8_0 : (Operand.reg 0 : Operand 64).read t8 = v2.1 := by
    have he : (Operand.reg 0 : Operand 64).read t8 = ((Operand.reg 9 : Operand 64).read t7) := he8.writes
    simp only [r7_9] at he
    exact he
  have r8_3 : (Operand.reg 3 : Operand 64).read t8 = 0xffffffff := (he8.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 3) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 3) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 3) (by simp [xorR32R32Effect_components])).trans (input3))))))))
  let v9 := ((v2.1)*(0xffffffff), mulHigh64 (v2.1) (0xffffffff))
  have code9 : CodeIn (codeRange 0x10fff5 [0x48, 0xf7, 0xe3]) t8 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem8) 0xfff5 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, run9, ready9, he9⟩ :=
    (mul_r64_effect_step 0x10fff5 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready8 code9 he8.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xfff8 (by decide)))
  change (mulR64Effect 0x10fff5 3 t8).Holds t8 t9 at he9
  have mem9 : t9.external = u.external :=
    (he9.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem8
  have agg9 : AgreesExcept registers u t9 :=
    (agg8.trans he9.agrees).mono (by simp [mulR64Effect_components, registers])
  have r9_0 : (Operand.reg 0 : Operand 64).read t9 = v9.1 := by
    have he : (Operand.reg 0 : Operand 64).read t9 = ((Operand.reg 0 : Operand 64).read t8) * ((Operand.reg 3 : Operand 64).read t8) := he9.writes.1
    simp only [r8_0, r8_3] at he
    exact he
  have r9_2 : (Operand.reg 2 : Operand 64).read t9 = v9.2 := by
    have he : (Operand.reg 2 : Operand 64).read t9 = mulHigh64 ((Operand.reg 0 : Operand 64).read t8) ((Operand.reg 3 : Operand 64).read t8) := he9.writes.2
    simp only [r8_0, r8_3] at he
    exact he
  have code10 : CodeIn (codeRange 0x10fff8 [0x48, 0x89, 0xd1]) t9 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem9) 0xfff8 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, run10, ready10, he10⟩ :=
    (mov_r64_r64_effect_step 0x10fff8 0x48 0xd1 (by simp [RexWPrefix]) (by decide)).advances ready9 code10 he9.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xfffb (by decide)))
  change (movR64R64Effect 0x10fff8 1 2 t9).Holds t9 t10 at he10
  have mem10 : t10.external = u.external :=
    (he10.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem9
  have agg10 : AgreesExcept registers u t10 :=
    (agg9.trans he10.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r10_1 : (Operand.reg 1 : Operand 64).read t10 = v9.2 := by
    have he : (Operand.reg 1 : Operand 64).read t10 = ((Operand.reg 2 : Operand 64).read t9) := he10.writes
    simp only [r9_2] at he
    exact he
  have r10_0 : (Operand.reg 0 : Operand 64).read t10 = v9.1 := (he10.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r9_0)
  have code11 : CodeIn (codeRange 0x10fffb [0x49, 0x89, 0xc0]) t10 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem10) 0xfffb _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, run11, ready11, he11⟩ :=
    (mov_r64_r64_effect_step 0x10fffb 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready10 code11 he10.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xfffe (by decide)))
  change (movR64R64Effect 0x10fffb 8 0 t10).Holds t10 t11 at he11
  have mem11 : t11.external = u.external :=
    (he11.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem10
  have agg11 : AgreesExcept registers u t11 :=
    (agg10.trans he11.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r11_8 : (Operand.reg 8 : Operand 64).read t11 = v9.1 := by
    have he : (Operand.reg 8 : Operand 64).read t11 = ((Operand.reg 0 : Operand 64).read t10) := he11.writes
    simp only [r10_0] at he
    exact he
  have r11_7 : (Operand.reg 7 : Operand 64).read t11 = b := (he11.agrees.read (n := 64) (r := 7) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 7) (by simp [movR64R64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 7) (by simp [mulR64Effect_components])).trans ((he8.agrees.read (n := 64) (r := 7) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 7) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 7) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 7) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 7) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 7) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 7) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 7) (by simp [xorR32R32Effect_components])).trans (input7)))))))))))
  let v12 := addSpec (v9.1) (b)
  have code12 : CodeIn (codeRange 0x10fffe [0x49, 0x1, 0xf8]) t11 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem11) 0xfffe _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, run12, ready12, he12⟩ :=
    (add_r64_r64_effect_step 0x10fffe 0x49 0xf8 (by simp [RexWPrefix]) (by decide)).advances ready11 code12 he11.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10001 (by decide)))
  change (addR64R64Effect 0x10fffe 8 7 t11).Holds t11 t12 at he12
  have mem12 : t12.external = u.external :=
    (he12.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem11
  have agg12 : AgreesExcept registers u t12 :=
    (agg11.trans he12.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r12_8 : (Operand.reg 8 : Operand 64).read t12 = v12.1 := by
    have he : (Operand.reg 8 : Operand 64).read t12 = (addSpec ((Operand.reg 8 : Operand 64).read t11) (((Operand.reg 7 : Operand 64).read t11))).1 := he12.writes
    simp only [r11_8, r11_7] at he
    exact he
  have cf12 : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = v12.2.CF := by
    have he : (StatusFlags.ofRFLAGS t12.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read t11) (((Operand.reg 7 : Operand 64).read t11))).2.CF := he12.flags.1
    simp only [r11_8, r11_7] at he
    exact he
  have r12_1 : (Operand.reg 1 : Operand 64).read t12 = v9.2 := (he12.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r10_1))
  have carry13 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf12
  let v13 := adcSpec ((v9.2).setWidth 32) (0) (BitVec.ofBool v12.2.CF)
  have code13 : CodeIn (codeRange 0x110001 [0x83, 0xd1, 0x0]) t12 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem12) 0x10001 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, run13, ready13, he13⟩ :=
    (adc_r32_imm8_effect_step 0x110001 0xd1 0 (by decide) (by decide)).advances ready12 code13 he12.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10004 (by decide)))
  change (adcR32Imm8Effect 0x110001 3 1 0 t12).Holds t12 t13 at he13
  have mem13 : t13.external = u.external :=
    (he13.agrees.external (by simp [adcR32Imm8Effect_components, Component.Covers])).trans mem12
  have agg13 : AgreesExcept registers u t13 :=
    (agg12.trans he13.agrees).mono (by simp [adcR32Imm8Effect_components, registers])
  have r13_1 : (Operand.reg 1 : Operand 64).read t13 = v13.1.setWidth 64 := by
    have he : (Operand.reg 1 : Operand 64).read t13 = (adcSpec ((Operand.reg 1 : Operand 32).read t12) ((0 : BitVec 8).signExtend 32) (t12.RFLAGS.extractLsb' 0 1)).1.setWidth 64 := he13.writes
    simp only [read32, r12_1, carry13] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = v13.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (adcSpec ((Operand.reg 1 : Operand 32).read t12) ((0 : BitVec 8).signExtend 32) (t12.RFLAGS.extractLsb' 0 1)).2.CF := he13.flags.1
    simp only [read32, r12_1, carry13] at he
    exact he
  have r13_8 : (Operand.reg 8 : Operand 64).read t13 = v12.1 := (he13.agrees.read (n := 64) (r := 8) (by simp [adcR32Imm8Effect_components])).trans (r12_8)
  have r13_10 : (Operand.reg 10 : Operand 64).read t13 = v7.1 := (he13.agrees.read (n := 64) (r := 10) (by simp [adcR32Imm8Effect_components])).trans ((he12.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((he8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans (r7_10))))))
  let v14 := addSpec (v12.1) (v7.1)
  have code14 : CodeIn (codeRange 0x110004 [0x4d, 0x1, 0xd0]) t13 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem13) 0x10004 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, run14, ready14, he14⟩ :=
    (add_r64_r64_effect_step 0x110004 0x4d 0xd0 (by simp [RexWPrefix]) (by decide)).advances ready13 code14 he13.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10007 (by decide)))
  change (addR64R64Effect 0x110004 8 10 t13).Holds t13 t14 at he14
  have mem14 : t14.external = u.external :=
    (he14.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem13
  have agg14 : AgreesExcept registers u t14 :=
    (agg13.trans he14.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r14_8 : (Operand.reg 8 : Operand 64).read t14 = v14.1 := by
    have he : (Operand.reg 8 : Operand 64).read t14 = (addSpec ((Operand.reg 8 : Operand 64).read t13) (((Operand.reg 10 : Operand 64).read t13))).1 := he14.writes
    simp only [r13_8, r13_10] at he
    exact he
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = v14.2.CF := by
    have he : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read t13) (((Operand.reg 10 : Operand 64).read t13))).2.CF := he14.flags.1
    simp only [r13_8, r13_10] at he
    exact he
  have r14_1 : (Operand.reg 1 : Operand 64).read t14 = v13.1.setWidth 64 := (he14.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans (r13_1)
  have r14_6 : (Operand.reg 6 : Operand 64).read t14 = c.setWidth 64 := (he14.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he13.agrees.read (n := 64) (r := 6) (by simp [adcR32Imm8Effect_components])).trans ((he12.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((he8.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 6) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 6) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components])).trans (input6))))))))))))))
  have carry15 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf14
  let v15 := adcSpec ((v13.1.setWidth 64).setWidth 32) ((c.setWidth 64).setWidth 32) (BitVec.ofBool v14.2.CF)
  have code15 : CodeIn (codeRange 0x110007 [0x11, 0xf1]) t14 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem14) 0x10007 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, run15, ready15, he15⟩ :=
    (adc_r32_r32_effect_step 0x110007 0xf1 (by decide)).advances ready14 code15 he14.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10009 (by decide)))
  change (adcR32R32Effect 0x110007 2 1 6 t14).Holds t14 t15 at he15
  have mem15 : t15.external = u.external :=
    (he15.agrees.external (by simp [adcR32R32Effect_components, Component.Covers])).trans mem14
  have agg15 : AgreesExcept registers u t15 :=
    (agg14.trans he15.agrees).mono (by simp [adcR32R32Effect_components, registers])
  have r15_1 : (Operand.reg 1 : Operand 64).read t15 = v15.1.setWidth 64 := by
    have he : (Operand.reg 1 : Operand 64).read t15 = (adcSpec ((Operand.reg 1 : Operand 32).read t14) (((Operand.reg 6 : Operand 32).read t14)) (t14.RFLAGS.extractLsb' 0 1)).1.setWidth 64 := he15.writes
    simp only [read32, r14_1, r14_6, carry15] at he
    exact he
  have cf15 : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = v15.2.CF := by
    have he : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = (adcSpec ((Operand.reg 1 : Operand 32).read t14) (((Operand.reg 6 : Operand 32).read t14)) (t14.RFLAGS.extractLsb' 0 1)).2.CF := he15.flags.1
    simp only [read32, r14_1, r14_6, carry15] at he
    exact he
  have r15_8 : (Operand.reg 8 : Operand 64).read t15 = v14.1 := (he15.agrees.read (n := 64) (r := 8) (by simp [adcR32R32Effect_components])).trans (r14_8)
  have r15_14 : (Operand.reg 14 : Operand 64).read t15 = 0xffffffffffffffff := (he15.agrees.read (n := 64) (r := 14) (by simp [adcR32R32Effect_components])).trans ((he14.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he13.agrees.read (n := 64) (r := 14) (by simp [adcR32Imm8Effect_components])).trans ((he12.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((he8.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r4_14)))))))))))
  refine ⟨15, t15, ((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15), ready15, he15.rip, agg15, ?_ , ?_ , ?_ ⟩
  · have h := r15_8
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v2, v5, v6, v7, v9, v12, v13, v14, v15] using h
  · have h := r15_1
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v2, v5, v6, v7, v9, v12, v13, v14, v15] using h
  · have h := r15_14
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v2, v5, v6, v7, v9, v12, v13, v14, v15] using h


end P256.Proofs.Sec1.Decompress.Select.Parity
