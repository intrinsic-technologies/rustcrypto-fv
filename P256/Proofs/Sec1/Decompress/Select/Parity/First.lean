import P256.Proofs.Sec1.Decompress.Select.Parity.Initial

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
theorem first_block [Bindings] {u : RamState} {boundary : ReturnBoundary} (a0 : BitVec 64)
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x10ff98)
    (input : (Operand.reg 6 : Operand 64).read u = a0 <<< 32 ∧
      (Operand.reg 11 : Operand 64).read u = a0 >>> 32 ∧
      (Operand.reg 8 : Operand 64).read u = a0*0xffffffff00000001 ∧
      (Operand.reg 10 : Operand 64).read u = mulHigh64 a0 0xffffffff00000001 ∧
      (Operand.reg 1 : Operand 64).read u = 0)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ t.RIP = 0x10ffd7 ∧
      AgreesExcept registers u t ∧ (Operand.reg 9 : Operand 64).read t = (first a0 (memLoad u.external (stackPtr u+160) 64)).1 ∧
      (Operand.reg 7 : Operand 64).read t = (first a0 (memLoad u.external (stackPtr u+160) 64)).2.1 ∧
      (Operand.reg 6 : Operand 64).read t = (first a0 (memLoad u.external (stackPtr u+160) 64)).2.2.setWidth 64 ∧
      (Operand.reg 14 : Operand 64).read t = 0xffffffffffffffff ∧
      (Operand.reg 3 : Operand 64).read t = 0xffffffff := by
  let a1 := memLoad u.external (stackPtr u+160) 64
  let a2 := memLoad u.external (stackPtr u+168) 64
  let a3 := memLoad u.external (stackPtr u+176) 64
  rcases input with ⟨input6, input11, input8, input10, input1⟩
  have mem0 : u.external = u.external := rfl
  have agg0 : AgreesExcept registers u u := AgreesExcept.refl _ _
  have addr1 : (AddrMode.sib 4 none 0 (.d32 160)).addr u 0x10ffa0 = stackPtr u+160 := by
    change (Operand.reg 4 : Operand 64).read u + 160 = _
    rfl
  have read1 : MemReadable u ((AddrMode.sib 4 none 0 (.d32 160)).addr u 0x10ffa0) 8 := by
    rw [addr1]
    exact (readable 1 (by decide)).of_external_eq mem0
  let v1 := addSpec (a0 <<< 32) (a1)
  have code1 : CodeIn (codeRange 0x10ff98 [0x48, 0x3, 0xb4, 0x24, 0xa0, 0x0, 0x0, 0x0]) u :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem0) 0xff98 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, run1, ready1, he1⟩ :=
    (add_r64_m64_effect_step 0x10ff98 0x48 (by simp [RexWPrefix]) 6 (AddrMode.sib 4 none 0 (.d32 160)) (by decide) rfl rfl).advances ready code1 ⟨rip, read1⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0xffa0 (by decide)))
  change (addR64M64Effect 0x10ff98 6 (AddrMode.sib 4 none 0 (.d32 160)) u).Holds u t1 at he1
  have mem1 : t1.external = u.external :=
    (he1.agrees.external (by simp [addR64M64Effect_components, Component.Covers])).trans mem0
  have agg1 : AgreesExcept registers u t1 :=
    (agg0.trans he1.agrees).mono (by simp [addR64M64Effect_components, registers])
  have r1_6 : (Operand.reg 6 : Operand 64).read t1 = v1.1 := by
    have he : (Operand.reg 6 : Operand 64).read t1 = (addSpec ((Operand.reg 6 : Operand 64).read u) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 160)).addr u 0x10ffa0) : Operand 64).read u)).1 := he1.writes
    simp only [input6, addr1, readMem] at he
    exact he
  have cf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = v1.2.CF := by
    have he : (StatusFlags.ofRFLAGS t1.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 64).read u) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 160)).addr u 0x10ffa0) : Operand 64).read u)).2.CF := he1.flags.1
    simp only [input6, addr1, readMem] at he
    exact he
  have r1_1 : (Operand.reg 1 : Operand 64).read t1 = 0 := (he1.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans (input1)
  have code2 : CodeIn (codeRange 0x10ffa0 [0xf, 0x92, 0xc1]) t1 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem1) 0xffa0 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, run2, ready2, he2⟩ :=
    (setcc_r8_effect_step 0x10ffa0 0x92 0xc1 (.inl rfl) (by decide) (by decide)).advances ready1 code2 he1.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffa3 (by decide)))
  change (setccR8Effect 0x10ffa0 3 1 2 t1).Holds t1 t2 at he2
  have mem2 : t2.external = u.external :=
    (he2.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem1
  have agg2 : AgreesExcept registers u t2 :=
    (agg1.trans he2.agrees).mono (by simp [setccR8Effect_components, registers])
  have r2_1 : (Operand.reg 1 : Operand 64).read t2 = (BitVec.ofBool v1.2.CF).setWidth 64 := by
    have he : (Operand.reg 1 : Operand 64).read t2 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t1.RFLAGS).CF then 1 else 0) ((Operand.reg 1 : Operand 64).read t1) := he2.writes
    simp only [r1_1, cf1, P256.Proofs.Sec1Serialize.Conversion.setb_zero] at he
    exact he
  have code3 : CodeIn (codeRange 0x10ffa3 [0x49, 0xc7, 0xc6, 0xff, 0xff, 0xff, 0xff]) t2 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem2) 0xffa3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, run3, ready3, he3⟩ :=
    (mov_r64_imm32_effect_step 0x10ffa3 0x49 0xc6 (by simp [RexWPrefix]) (by decide) (by decide) 0xffffffff).advances ready2 code3 he2.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffaa (by decide)))
  change (movR64Imm32Effect 0x10ffa3 14 0xffffffff t2).Holds t2 t3 at he3
  have mem3 : t3.external = u.external :=
    (he3.agrees.external (by simp [movR64Imm32Effect_components, Component.Covers])).trans mem2
  have agg3 : AgreesExcept registers u t3 :=
    (agg2.trans he3.agrees).mono (by simp [movR64Imm32Effect_components, registers])
  have r3_14 : (Operand.reg 14 : Operand 64).read t3 = 0xffffffffffffffff := by
    have he : (Operand.reg 14 : Operand 64).read t3 = (0xffffffff : BitVec 32).signExtend 64 := he3.writes
    exact he
  have r3_6 : (Operand.reg 6 : Operand 64).read t3 = v1.1 := (he3.agrees.read (n := 64) (r := 6) (by simp [movR64Imm32Effect_components])).trans ((he2.agrees.read (n := 64) (r := 6) (by simp [setccR8Effect_components])).trans (r1_6))
  have code4 : CodeIn (codeRange 0x10ffaa [0x48, 0x89, 0xf0]) t3 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem3) 0xffaa _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, run4, ready4, he4⟩ :=
    (mov_r64_r64_effect_step 0x10ffaa 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances ready3 code4 he3.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffad (by decide)))
  change (movR64R64Effect 0x10ffaa 0 6 t3).Holds t3 t4 at he4
  have mem4 : t4.external = u.external :=
    (he4.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem3
  have agg4 : AgreesExcept registers u t4 :=
    (agg3.trans he4.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r4_0 : (Operand.reg 0 : Operand 64).read t4 = v1.1 := by
    have he : (Operand.reg 0 : Operand 64).read t4 = ((Operand.reg 6 : Operand 64).read t3) := he4.writes
    simp only [r3_6] at he
    exact he
  have r4_14 : (Operand.reg 14 : Operand 64).read t4 = 0xffffffffffffffff := (he4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans (r3_14)
  let v5 := ((v1.1)*(0xffffffffffffffff), mulHigh64 (v1.1) (0xffffffffffffffff))
  have code5 : CodeIn (codeRange 0x10ffad [0x49, 0xf7, 0xe6]) t4 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem4) 0xffad _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, run5, ready5, he5⟩ :=
    (mul_r64_effect_step 0x10ffad 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 code5 he4.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffb0 (by decide)))
  change (mulR64Effect 0x10ffad 14 t4).Holds t4 t5 at he5
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
  have r5_6 : (Operand.reg 6 : Operand 64).read t5 = v1.1 := (he5.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r3_6))
  let v6 := addSpec (v5.1) (v1.1)
  have code6 : CodeIn (codeRange 0x10ffb0 [0x48, 0x1, 0xf0]) t5 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem5) 0xffb0 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, run6, ready6, he6⟩ :=
    (add_r64_r64_effect_step 0x10ffb0 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances ready5 code6 he5.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffb3 (by decide)))
  change (addR64R64Effect 0x10ffb0 0 6 t5).Holds t5 t6 at he6
  have mem6 : t6.external = u.external :=
    (he6.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem5
  have agg6 : AgreesExcept registers u t6 :=
    (agg5.trans he6.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r6_0 : (Operand.reg 0 : Operand 64).read t6 = v6.1 := by
    have he : (Operand.reg 0 : Operand 64).read t6 = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 6 : Operand 64).read t5))).1 := he6.writes
    simp only [r5_0, r5_6] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = v6.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 6 : Operand 64).read t5))).2.CF := he6.flags.1
    simp only [r5_0, r5_6] at he
    exact he
  have r6_1 : (Operand.reg 1 : Operand 64).read t6 = (BitVec.ofBool v1.2.CF).setWidth 64 := (he6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 1) (by simp [movR64Imm32Effect_components])).trans (r2_1))))
  have r6_2 : (Operand.reg 2 : Operand 64).read t6 = v5.2 := (he6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r5_2)
  have carry7 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf6
  let v7 := adcSpec ((BitVec.ofBool v1.2.CF).setWidth 64) (v5.2) (BitVec.ofBool v6.2.CF)
  have code7 : CodeIn (codeRange 0x10ffb3 [0x48, 0x11, 0xd1]) t6 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem6) 0xffb3 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, run7, ready7, he7⟩ :=
    (adc_r64_r64_effect_step 0x10ffb3 0x48 0xd1 (by simp [RexWPrefix]) (by decide)).advances ready6 code7 he6.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffb6 (by decide)))
  change (adcR64R64Effect 0x10ffb3 1 2 t6).Holds t6 t7 at he7
  have mem7 : t7.external = u.external :=
    (he7.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem6
  have agg7 : AgreesExcept registers u t7 :=
    (agg6.trans he7.agrees).mono (by simp [adcR64R64Effect_components, registers])
  have r7_1 : (Operand.reg 1 : Operand 64).read t7 = v7.1 := by
    have he : (Operand.reg 1 : Operand 64).read t7 = (adcSpec ((Operand.reg 1 : Operand 64).read t6) (((Operand.reg 2 : Operand 64).read t6)) (t6.RFLAGS.extractLsb' 0 1)).1 := he7.writes
    simp only [r6_1, r6_2, carry7] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = v7.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec ((Operand.reg 1 : Operand 64).read t6) (((Operand.reg 2 : Operand 64).read t6)) (t6.RFLAGS.extractLsb' 0 1)).2.CF := he7.flags.1
    simp only [r6_1, r6_2, carry7] at he
    exact he
  have r7_6 : (Operand.reg 6 : Operand 64).read t7 = v1.1 := (he7.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans (r5_6))
  have code8 : CodeIn (codeRange 0x10ffb6 [0x48, 0x89, 0xf0]) t7 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem7) 0xffb6 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, run8, ready8, he8⟩ :=
    (mov_r64_r64_effect_step 0x10ffb6 0x48 0xf0 (by simp [RexWPrefix]) (by decide)).advances ready7 code8 he7.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffb9 (by decide)))
  change (movR64R64Effect 0x10ffb6 0 6 t7).Holds t7 t8 at he8
  have mem8 : t8.external = u.external :=
    (he8.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem7
  have agg8 : AgreesExcept registers u t8 :=
    (agg7.trans he8.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r8_0 : (Operand.reg 0 : Operand 64).read t8 = v1.1 := by
    have he : (Operand.reg 0 : Operand 64).read t8 = ((Operand.reg 6 : Operand 64).read t7) := he8.writes
    simp only [r7_6] at he
    exact he
  have code9 : CodeIn (codeRange 0x10ffb9 [0xbb, 0xff, 0xff, 0xff, 0xff]) t8 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem8) 0xffb9 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, run9, ready9, he9⟩ :=
    (mov_r32_imm32_effect_step 0x10ffb9 0xbb (by decide) 0xffffffff).advances ready8 code9 he8.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffbe (by decide)))
  change (movR32Imm32Effect 0x10ffb9 5 3 0xffffffff t8).Holds t8 t9 at he9
  have mem9 : t9.external = u.external :=
    (he9.agrees.external (by simp [movR32Imm32Effect_components, Component.Covers])).trans mem8
  have agg9 : AgreesExcept registers u t9 :=
    (agg8.trans he9.agrees).mono (by simp [movR32Imm32Effect_components, registers])
  have r9_3 : (Operand.reg 3 : Operand 64).read t9 = 0xffffffff := by
    have he : (Operand.reg 3 : Operand 64).read t9 = (0xffffffff : BitVec 32).setWidth 64 := he9.writes
    exact he
  have r9_0 : (Operand.reg 0 : Operand 64).read t9 = v1.1 := (he9.agrees.read (n := 64) (r := 0) (by simp [movR32Imm32Effect_components])).trans (r8_0)
  let v10 := ((v1.1)*(0xffffffff), mulHigh64 (v1.1) (0xffffffff))
  have code10 : CodeIn (codeRange 0x10ffbe [0x48, 0xf7, 0xe3]) t9 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem9) 0xffbe _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, run10, ready10, he10⟩ :=
    (mul_r64_effect_step 0x10ffbe 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready9 code10 he9.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffc1 (by decide)))
  change (mulR64Effect 0x10ffbe 3 t9).Holds t9 t10 at he10
  have mem10 : t10.external = u.external :=
    (he10.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem9
  have agg10 : AgreesExcept registers u t10 :=
    (agg9.trans he10.agrees).mono (by simp [mulR64Effect_components, registers])
  have r10_0 : (Operand.reg 0 : Operand 64).read t10 = v10.1 := by
    have he : (Operand.reg 0 : Operand 64).read t10 = ((Operand.reg 0 : Operand 64).read t9) * ((Operand.reg 3 : Operand 64).read t9) := he10.writes.1
    simp only [r9_0, r9_3] at he
    exact he
  have r10_2 : (Operand.reg 2 : Operand 64).read t10 = v10.2 := by
    have he : (Operand.reg 2 : Operand 64).read t10 = mulHigh64 ((Operand.reg 0 : Operand 64).read t9) ((Operand.reg 3 : Operand 64).read t9) := he10.writes.2
    simp only [r9_0, r9_3] at he
    exact he
  have code11 : CodeIn (codeRange 0x10ffc1 [0x48, 0x89, 0xd7]) t10 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem10) 0xffc1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, run11, ready11, he11⟩ :=
    (mov_r64_r64_effect_step 0x10ffc1 0x48 0xd7 (by simp [RexWPrefix]) (by decide)).advances ready10 code11 he10.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffc4 (by decide)))
  change (movR64R64Effect 0x10ffc1 7 2 t10).Holds t10 t11 at he11
  have mem11 : t11.external = u.external :=
    (he11.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem10
  have agg11 : AgreesExcept registers u t11 :=
    (agg10.trans he11.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r11_7 : (Operand.reg 7 : Operand 64).read t11 = v10.2 := by
    have he : (Operand.reg 7 : Operand 64).read t11 = ((Operand.reg 2 : Operand 64).read t10) := he11.writes
    simp only [r10_2] at he
    exact he
  have r11_0 : (Operand.reg 0 : Operand 64).read t11 = v10.1 := (he11.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r10_0)
  have code12 : CodeIn (codeRange 0x10ffc4 [0x49, 0x89, 0xc1]) t11 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem11) 0xffc4 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t12, run12, ready12, he12⟩ :=
    (mov_r64_r64_effect_step 0x10ffc4 0x49 0xc1 (by simp [RexWPrefix]) (by decide)).advances ready11 code12 he11.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffc7 (by decide)))
  change (movR64R64Effect 0x10ffc4 9 0 t11).Holds t11 t12 at he12
  have mem12 : t12.external = u.external :=
    (he12.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem11
  have agg12 : AgreesExcept registers u t12 :=
    (agg11.trans he12.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r12_9 : (Operand.reg 9 : Operand 64).read t12 = v10.1 := by
    have he : (Operand.reg 9 : Operand 64).read t12 = ((Operand.reg 0 : Operand 64).read t11) := he12.writes
    simp only [r11_0] at he
    exact he
  have r12_11 : (Operand.reg 11 : Operand 64).read t12 = a0 >>> 32 := (he12.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 11) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 11) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 11) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 11) (by simp [movR64Imm32Effect_components])).trans ((he2.agrees.read (n := 64) (r := 11) (by simp [setccR8Effect_components])).trans ((he1.agrees.read (n := 64) (r := 11) (by simp [addR64M64Effect_components])).trans (input11))))))))))))
  let v13 := addSpec (v10.1) (a0 >>> 32)
  have code13 : CodeIn (codeRange 0x10ffc7 [0x4d, 0x1, 0xd9]) t12 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem12) 0xffc7 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t13, run13, ready13, he13⟩ :=
    (add_r64_r64_effect_step 0x10ffc7 0x4d 0xd9 (by simp [RexWPrefix]) (by decide)).advances ready12 code13 he12.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffca (by decide)))
  change (addR64R64Effect 0x10ffc7 9 11 t12).Holds t12 t13 at he13
  have mem13 : t13.external = u.external :=
    (he13.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem12
  have agg13 : AgreesExcept registers u t13 :=
    (agg12.trans he13.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r13_9 : (Operand.reg 9 : Operand 64).read t13 = v13.1 := by
    have he : (Operand.reg 9 : Operand 64).read t13 = (addSpec ((Operand.reg 9 : Operand 64).read t12) (((Operand.reg 11 : Operand 64).read t12))).1 := he13.writes
    simp only [r12_9, r12_11] at he
    exact he
  have cf13 : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = v13.2.CF := by
    have he : (StatusFlags.ofRFLAGS t13.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read t12) (((Operand.reg 11 : Operand 64).read t12))).2.CF := he13.flags.1
    simp only [r12_9, r12_11] at he
    exact he
  have r13_7 : (Operand.reg 7 : Operand 64).read t13 = v10.2 := (he13.agrees.read (n := 64) (r := 7) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 7) (by simp [movR64R64Effect_components])).trans (r11_7))
  have carry14 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf13
  let v14 := adcSpec (v10.2) (0) (BitVec.ofBool v13.2.CF)
  have code14 : CodeIn (codeRange 0x10ffca [0x48, 0x83, 0xd7, 0x0]) t13 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem13) 0xffca _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t14, run14, ready14, he14⟩ :=
    (adc_r64_imm8_effect_step 0x10ffca 0x48 0xd7 0 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready13 code14 he13.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffce (by decide)))
  change (adcR64Imm8Effect 0x10ffca 7 0 t13).Holds t13 t14 at he14
  have mem14 : t14.external = u.external :=
    (he14.agrees.external (by simp [adcR64Imm8Effect_components, Component.Covers])).trans mem13
  have agg14 : AgreesExcept registers u t14 :=
    (agg13.trans he14.agrees).mono (by simp [adcR64Imm8Effect_components, registers])
  have r14_7 : (Operand.reg 7 : Operand 64).read t14 = v14.1 := by
    have he : (Operand.reg 7 : Operand 64).read t14 = (adcSpec ((Operand.reg 7 : Operand 64).read t13) ((0 : BitVec 8).signExtend 64) (t13.RFLAGS.extractLsb' 0 1)).1 := he14.writes
    simp only [r13_7, carry14] at he
    exact he
  have cf14 : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = v14.2.CF := by
    have he : (StatusFlags.ofRFLAGS t14.RFLAGS).CF = (adcSpec ((Operand.reg 7 : Operand 64).read t13) ((0 : BitVec 8).signExtend 64) (t13.RFLAGS.extractLsb' 0 1)).2.CF := he14.flags.1
    simp only [r13_7, carry14] at he
    exact he
  have r14_9 : (Operand.reg 9 : Operand 64).read t14 = v13.1 := (he14.agrees.read (n := 64) (r := 9) (by simp [adcR64Imm8Effect_components])).trans (r13_9)
  have r14_1 : (Operand.reg 1 : Operand 64).read t14 = v7.1 := (he14.agrees.read (n := 64) (r := 1) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 1) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans (r7_1)))))))
  let v15 := addSpec (v13.1) (v7.1)
  have code15 : CodeIn (codeRange 0x10ffce [0x49, 0x1, 0xc9]) t14 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem14) 0xffce _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t15, run15, ready15, he15⟩ :=
    (add_r64_r64_effect_step 0x10ffce 0x49 0xc9 (by simp [RexWPrefix]) (by decide)).advances ready14 code15 he14.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffd1 (by decide)))
  change (addR64R64Effect 0x10ffce 9 1 t14).Holds t14 t15 at he15
  have mem15 : t15.external = u.external :=
    (he15.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem14
  have agg15 : AgreesExcept registers u t15 :=
    (agg14.trans he15.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r15_9 : (Operand.reg 9 : Operand 64).read t15 = v15.1 := by
    have he : (Operand.reg 9 : Operand 64).read t15 = (addSpec ((Operand.reg 9 : Operand 64).read t14) (((Operand.reg 1 : Operand 64).read t14))).1 := he15.writes
    simp only [r14_9, r14_1] at he
    exact he
  have cf15 : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = v15.2.CF := by
    have he : (StatusFlags.ofRFLAGS t15.RFLAGS).CF = (addSpec ((Operand.reg 9 : Operand 64).read t14) (((Operand.reg 1 : Operand 64).read t14))).2.CF := he15.flags.1
    simp only [r14_9, r14_1] at he
    exact he
  have r15_7 : (Operand.reg 7 : Operand 64).read t15 = v14.1 := (he15.agrees.read (n := 64) (r := 7) (by simp [addR64R64Effect_components])).trans (r14_7)
  have r15_8 : (Operand.reg 8 : Operand 64).read t15 = a0*0xffffffff00000001 := (he15.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((he14.agrees.read (n := 64) (r := 8) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 8) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 8) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 8) (by simp [movR64Imm32Effect_components])).trans ((he2.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans ((he1.agrees.read (n := 64) (r := 8) (by simp [addR64M64Effect_components])).trans (input8)))))))))))))))
  have carry16 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf15
  let v16 := adcSpec (v14.1) (a0*0xffffffff00000001) (BitVec.ofBool v15.2.CF)
  have code16 : CodeIn (codeRange 0x10ffd1 [0x4c, 0x11, 0xc7]) t15 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem15) 0xffd1 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t16, run16, ready16, he16⟩ :=
    (adc_r64_r64_effect_step 0x10ffd1 0x4c 0xc7 (by simp [RexWPrefix]) (by decide)).advances ready15 code16 he15.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffd4 (by decide)))
  change (adcR64R64Effect 0x10ffd1 7 8 t15).Holds t15 t16 at he16
  have mem16 : t16.external = u.external :=
    (he16.agrees.external (by simp [adcR64R64Effect_components, Component.Covers])).trans mem15
  have agg16 : AgreesExcept registers u t16 :=
    (agg15.trans he16.agrees).mono (by simp [adcR64R64Effect_components, registers])
  have r16_7 : (Operand.reg 7 : Operand 64).read t16 = v16.1 := by
    have he : (Operand.reg 7 : Operand 64).read t16 = (adcSpec ((Operand.reg 7 : Operand 64).read t15) (((Operand.reg 8 : Operand 64).read t15)) (t15.RFLAGS.extractLsb' 0 1)).1 := he16.writes
    simp only [r15_7, r15_8, carry16] at he
    exact he
  have cf16 : (StatusFlags.ofRFLAGS t16.RFLAGS).CF = v16.2.CF := by
    have he : (StatusFlags.ofRFLAGS t16.RFLAGS).CF = (adcSpec ((Operand.reg 7 : Operand 64).read t15) (((Operand.reg 8 : Operand 64).read t15)) (t15.RFLAGS.extractLsb' 0 1)).2.CF := he16.flags.1
    simp only [r15_7, r15_8, carry16] at he
    exact he
  have r16_6 : (Operand.reg 6 : Operand 64).read t16 = v1.1 := (he16.agrees.read (n := 64) (r := 6) (by simp [adcR64R64Effect_components])).trans ((he15.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he14.agrees.read (n := 64) (r := 6) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 6) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r7_6)))))))))
  have r16_10 : (Operand.reg 10 : Operand 64).read t16 = mulHigh64 a0 0xffffffff00000001 := (he16.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((he15.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((he14.agrees.read (n := 64) (r := 10) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 10) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 10) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 10) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 10) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 10) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 10) (by simp [movR64Imm32Effect_components])).trans ((he2.agrees.read (n := 64) (r := 10) (by simp [setccR8Effect_components])).trans ((he1.agrees.read (n := 64) (r := 10) (by simp [addR64M64Effect_components])).trans (input10))))))))))))))))
  have carry17 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf16
  let v17 := adcSpec ((v1.1).setWidth 32) ((mulHigh64 a0 0xffffffff00000001).setWidth 32) (BitVec.ofBool v16.2.CF)
  have code17 : CodeIn (codeRange 0x10ffd4 [0x44, 0x11, 0xd6]) t16 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem16) 0xffd4 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t17, run17, ready17, he17⟩ :=
    (adc_r32_r32_rex_effect_step 0x10ffd4 0x44 0xd6 (by simp [RexNoWPrefix]) (by decide)).advances ready16 code17 he16.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xffd7 (by decide)))
  change (adcR32R32Effect 0x10ffd4 3 6 10 t16).Holds t16 t17 at he17
  have mem17 : t17.external = u.external :=
    (he17.agrees.external (by simp [adcR32R32Effect_components, Component.Covers])).trans mem16
  have agg17 : AgreesExcept registers u t17 :=
    (agg16.trans he17.agrees).mono (by simp [adcR32R32Effect_components, registers])
  have r17_6 : (Operand.reg 6 : Operand 64).read t17 = v17.1.setWidth 64 := by
    have he : (Operand.reg 6 : Operand 64).read t17 = (adcSpec ((Operand.reg 6 : Operand 32).read t16) (((Operand.reg 10 : Operand 32).read t16)) (t16.RFLAGS.extractLsb' 0 1)).1.setWidth 64 := he17.writes
    simp only [read32, r16_6, r16_10, carry17] at he
    exact he
  have cf17 : (StatusFlags.ofRFLAGS t17.RFLAGS).CF = v17.2.CF := by
    have he : (StatusFlags.ofRFLAGS t17.RFLAGS).CF = (adcSpec ((Operand.reg 6 : Operand 32).read t16) (((Operand.reg 10 : Operand 32).read t16)) (t16.RFLAGS.extractLsb' 0 1)).2.CF := he17.flags.1
    simp only [read32, r16_6, r16_10, carry17] at he
    exact he
  have r17_9 : (Operand.reg 9 : Operand 64).read t17 = v15.1 := (he17.agrees.read (n := 64) (r := 9) (by simp [adcR32R32Effect_components])).trans ((he16.agrees.read (n := 64) (r := 9) (by simp [adcR64R64Effect_components])).trans (r15_9))
  have r17_7 : (Operand.reg 7 : Operand 64).read t17 = v16.1 := (he17.agrees.read (n := 64) (r := 7) (by simp [adcR32R32Effect_components])).trans (r16_7)
  have r17_14 : (Operand.reg 14 : Operand 64).read t17 = 0xffffffffffffffff := (he17.agrees.read (n := 64) (r := 14) (by simp [adcR32R32Effect_components])).trans ((he16.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((he15.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he14.agrees.read (n := 64) (r := 14) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans ((he9.agrees.read (n := 64) (r := 14) (by simp [movR32Imm32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 14) (by simp [adcR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 14) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 14) (by simp [mulR64Effect_components])).trans (r4_14)))))))))))))
  have r17_3 : (Operand.reg 3 : Operand 64).read t17 = 0xffffffff := (he17.agrees.read (n := 64) (r := 3) (by simp [adcR32R32Effect_components])).trans ((he16.agrees.read (n := 64) (r := 3) (by simp [adcR64R64Effect_components])).trans ((he15.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((he14.agrees.read (n := 64) (r := 3) (by simp [adcR64Imm8Effect_components])).trans ((he13.agrees.read (n := 64) (r := 3) (by simp [addR64R64Effect_components])).trans ((he12.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((he11.agrees.read (n := 64) (r := 3) (by simp [movR64R64Effect_components])).trans ((he10.agrees.read (n := 64) (r := 3) (by simp [mulR64Effect_components])).trans (r9_3))))))))
  refine ⟨17, t17, ((((((((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16).trans run17), ready17, he17.rip, agg17, ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · have h := r17_9
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v1, v5, v6, v7, v10, v13, v14, v15, v16, v17] using h
  · have h := r17_7
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v1, v5, v6, v7, v10, v13, v14, v15, v16, v17] using h
  · have h := r17_6
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v1, v5, v6, v7, v10, v13, v14, v15, v16, v17] using h
  · have h := r17_14
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v1, v5, v6, v7, v10, v13, v14, v15, v16, v17] using h
  · have h := r17_3
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v1, v5, v6, v7, v10, v13, v14, v15, v16, v17] using h


end P256.Proofs.Sec1.Decompress.Select.Parity
