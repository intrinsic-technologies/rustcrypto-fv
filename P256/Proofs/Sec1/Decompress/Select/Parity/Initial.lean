import P256.Proofs.Sec1.Decompress.Select.Parity.Model

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
theorem initial [Bindings] {u : RamState} {boundary : ReturnBoundary}
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x10ff77)
    (input : (Operand.reg 14 : Operand 64).read u = 0xffffffff00000001)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ t.RIP = 0x10ff98 ∧
      AgreesExcept registers u t ∧ (Operand.reg 6 : Operand 64).read t = (memLoad u.external (stackPtr u+152) 64) <<< 32 ∧
      (Operand.reg 11 : Operand 64).read t = (memLoad u.external (stackPtr u+152) 64) >>> 32 ∧
      (Operand.reg 8 : Operand 64).read t = (memLoad u.external (stackPtr u+152) 64)*0xffffffff00000001 ∧
      (Operand.reg 10 : Operand 64).read t = mulHigh64 (memLoad u.external (stackPtr u+152) 64) 0xffffffff00000001 ∧
      (Operand.reg 1 : Operand 64).read t = 0 := by
  let a0 := memLoad u.external (stackPtr u+152) 64
  let a1 := memLoad u.external (stackPtr u+160) 64
  let a2 := memLoad u.external (stackPtr u+168) 64
  let a3 := memLoad u.external (stackPtr u+176) 64
  have input14 := input
  have mem0 : u.external = u.external := rfl
  have agg0 : AgreesExcept registers u u := AgreesExcept.refl _ _
  have addr1 : (AddrMode.sib 4 none 0 (.d32 152)).addr u 0x10ff7f = stackPtr u+152 := by
    change (Operand.reg 4 : Operand 64).read u + 152 = _
    rfl
  have read1 : MemReadable u ((AddrMode.sib 4 none 0 (.d32 152)).addr u 0x10ff7f) 8 := by
    rw [addr1]
    exact (readable 0 (by decide)).of_external_eq mem0
  have code1 : CodeIn (codeRange 0x10ff77 [0x48, 0x8b, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0]) u :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem0) 0xff77 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, run1, ready1, he1⟩ :=
    (mov_r64_m64_effect_step 0x10ff77 0x48 (by simp [RexWPrefix]) 0 (AddrMode.sib 4 none 0 (.d32 152)) (by decide) rfl rfl).advances ready code1 ⟨rip, read1⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0xff7f (by decide)))
  change (movR64M64Effect 0x10ff77 0 (AddrMode.sib 4 none 0 (.d32 152)) u).Holds u t1 at he1
  have mem1 : t1.external = u.external :=
    (he1.agrees.external (by simp [movR64M64Effect_components, Component.Covers])).trans mem0
  have agg1 : AgreesExcept registers u t1 :=
    (agg0.trans he1.agrees).mono (by simp [movR64M64Effect_components, registers])
  have r1_0 : (Operand.reg 0 : Operand 64).read t1 = a0 := by
    have he : (Operand.reg 0 : Operand 64).read t1 = (Operand.mem ((AddrMode.sib 4 none 0 (.d32 152)).addr u 0x10ff7f) : Operand 64).read u := he1.writes
    simp only [addr1, readMem] at he
    exact he
  have code2 : CodeIn (codeRange 0x10ff7f [0x48, 0x89, 0xc6]) t1 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem1) 0xff7f _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, run2, ready2, he2⟩ :=
    (mov_r64_r64_effect_step 0x10ff7f 0x48 0xc6 (by simp [RexWPrefix]) (by decide)).advances ready1 code2 he1.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff82 (by decide)))
  change (movR64R64Effect 0x10ff7f 6 0 t1).Holds t1 t2 at he2
  have mem2 : t2.external = u.external :=
    (he2.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem1
  have agg2 : AgreesExcept registers u t2 :=
    (agg1.trans he2.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r2_6 : (Operand.reg 6 : Operand 64).read t2 = a0 := by
    have he : (Operand.reg 6 : Operand 64).read t2 = ((Operand.reg 0 : Operand 64).read t1) := he2.writes
    simp only [r1_0] at he
    exact he
  have r2_0 : (Operand.reg 0 : Operand 64).read t2 = a0 := (he2.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r1_0)
  have code3 : CodeIn (codeRange 0x10ff82 [0x49, 0x89, 0xc3]) t2 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem2) 0xff82 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, run3, ready3, he3⟩ :=
    (mov_r64_r64_effect_step 0x10ff82 0x49 0xc3 (by simp [RexWPrefix]) (by decide)).advances ready2 code3 he2.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff85 (by decide)))
  change (movR64R64Effect 0x10ff82 11 0 t2).Holds t2 t3 at he3
  have mem3 : t3.external = u.external :=
    (he3.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem2
  have agg3 : AgreesExcept registers u t3 :=
    (agg2.trans he3.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r3_11 : (Operand.reg 11 : Operand 64).read t3 = a0 := by
    have he : (Operand.reg 11 : Operand 64).read t3 = ((Operand.reg 0 : Operand 64).read t2) := he3.writes
    simp only [r2_0] at he
    exact he
  have code4 : CodeIn (codeRange 0x10ff85 [0x49, 0xc1, 0xeb, 0x20]) t3 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem3) 0xff85 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, run4, ready4, he4⟩ :=
    (shr_r64_imm8_effect_step 0x10ff85 0x49 0xeb 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready3 code4 he3.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff89 (by decide)))
  change (shrR64Effect 0x10ff85 4 11 32 t3).Holds t3 t4 at he4
  have mem4 : t4.external = u.external :=
    (he4.agrees.external (by simp [shrR64Effect_components, Component.Covers])).trans mem3
  have agg4 : AgreesExcept registers u t4 :=
    (agg3.trans he4.agrees).mono (by simp [shrR64Effect_components, registers])
  have r4_11 : (Operand.reg 11 : Operand 64).read t4 = (a0 >>> 32) := by
    have he : (Operand.reg 11 : Operand 64).read t4 = ((Operand.reg 11 : Operand 64).read t3) >>> 32 := he4.writes
    simp only [r3_11] at he
    exact he
  have r4_6 : (Operand.reg 6 : Operand 64).read t4 = a0 := (he4.agrees.read (n := 64) (r := 6) (by simp [shrR64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r2_6))
  have code5 : CodeIn (codeRange 0x10ff89 [0x48, 0xc1, 0xe6, 0x20]) t4 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem4) 0xff89 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, run5, ready5, he5⟩ :=
    (shl_r64_imm8_effect_step 0x10ff89 0x48 0xe6 32 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 code5 he4.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff8d (by decide)))
  change (shlR64Effect 0x10ff89 4 6 32 t4).Holds t4 t5 at he5
  have mem5 : t5.external = u.external :=
    (he5.agrees.external (by simp [shlR64Effect_components, Component.Covers])).trans mem4
  have agg5 : AgreesExcept registers u t5 :=
    (agg4.trans he5.agrees).mono (by simp [shlR64Effect_components, registers])
  have r5_6 : (Operand.reg 6 : Operand 64).read t5 = (a0 <<< 32) := by
    have he : (Operand.reg 6 : Operand 64).read t5 = ((Operand.reg 6 : Operand 64).read t4) <<< 32 := he5.writes
    simp only [r4_6] at he
    exact he
  have r5_0 : (Operand.reg 0 : Operand 64).read t5 = a0 := (he5.agrees.read (n := 64) (r := 0) (by simp [shlR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 0) (by simp [shrR64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 0) (by simp [movR64R64Effect_components])).trans (r2_0)))
  have r5_14 : (Operand.reg 14 : Operand 64).read t5 = 0xffffffff00000001 := (he5.agrees.read (n := 64) (r := 14) (by simp [shlR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 14) (by simp [shrR64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he2.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 14) (by simp [movR64M64Effect_components])).trans (input14)))))
  let v6 := ((a0)*(0xffffffff00000001), mulHigh64 (a0) (0xffffffff00000001))
  have code6 : CodeIn (codeRange 0x10ff8d [0x49, 0xf7, 0xe6]) t5 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem5) 0xff8d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, run6, ready6, he6⟩ :=
    (mul_r64_effect_step 0x10ff8d 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready5 code6 he5.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff90 (by decide)))
  change (mulR64Effect 0x10ff8d 14 t5).Holds t5 t6 at he6
  have mem6 : t6.external = u.external :=
    (he6.agrees.external (by simp [mulR64Effect_components, Component.Covers])).trans mem5
  have agg6 : AgreesExcept registers u t6 :=
    (agg5.trans he6.agrees).mono (by simp [mulR64Effect_components, registers])
  have r6_0 : (Operand.reg 0 : Operand 64).read t6 = v6.1 := by
    have he : (Operand.reg 0 : Operand 64).read t6 = ((Operand.reg 0 : Operand 64).read t5) * ((Operand.reg 14 : Operand 64).read t5) := he6.writes.1
    simp only [r5_0, r5_14] at he
    exact he
  have r6_2 : (Operand.reg 2 : Operand 64).read t6 = v6.2 := by
    have he : (Operand.reg 2 : Operand 64).read t6 = mulHigh64 ((Operand.reg 0 : Operand 64).read t5) ((Operand.reg 14 : Operand 64).read t5) := he6.writes.2
    simp only [r5_0, r5_14] at he
    exact he
  have code7 : CodeIn (codeRange 0x10ff90 [0x49, 0x89, 0xc0]) t6 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem6) 0xff90 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, run7, ready7, he7⟩ :=
    (mov_r64_r64_effect_step 0x10ff90 0x49 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready6 code7 he6.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff93 (by decide)))
  change (movR64R64Effect 0x10ff90 8 0 t6).Holds t6 t7 at he7
  have mem7 : t7.external = u.external :=
    (he7.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem6
  have agg7 : AgreesExcept registers u t7 :=
    (agg6.trans he7.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r7_8 : (Operand.reg 8 : Operand 64).read t7 = v6.1 := by
    have he : (Operand.reg 8 : Operand 64).read t7 = ((Operand.reg 0 : Operand 64).read t6) := he7.writes
    simp only [r6_0] at he
    exact he
  have r7_2 : (Operand.reg 2 : Operand 64).read t7 = v6.2 := (he7.agrees.read (n := 64) (r := 2) (by simp [movR64R64Effect_components])).trans (r6_2)
  have code8 : CodeIn (codeRange 0x10ff93 [0x49, 0x89, 0xd2]) t7 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem7) 0xff93 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, run8, ready8, he8⟩ :=
    (mov_r64_r64_effect_step 0x10ff93 0x49 0xd2 (by simp [RexWPrefix]) (by decide)).advances ready7 code8 he7.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff96 (by decide)))
  change (movR64R64Effect 0x10ff93 10 2 t7).Holds t7 t8 at he8
  have mem8 : t8.external = u.external :=
    (he8.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem7
  have agg8 : AgreesExcept registers u t8 :=
    (agg7.trans he8.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r8_10 : (Operand.reg 10 : Operand 64).read t8 = v6.2 := by
    have he : (Operand.reg 10 : Operand 64).read t8 = ((Operand.reg 2 : Operand 64).read t7) := he8.writes
    simp only [r7_2] at he
    exact he
  have r8_1 : (Operand.reg 1 : Operand 64).read t8 = ((Operand.reg 1 : Operand 64).read u) := (he8.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 1) (by simp [shlR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 1) (by simp [shrR64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he2.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 1) (by simp [movR64M64Effect_components])).trans ((by rfl)))))))))
  have code9 : CodeIn (codeRange 0x10ff96 [0x31, 0xc9]) t8 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem8) 0xff96 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, run9, ready9, he9⟩ :=
    (xor_r32_r32_effect_step 0x10ff96 0xc9 (by decide)).advances ready8 code9 he8.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0xff98 (by decide)))
  change (xorR32R32Effect 0x10ff96 2 1 1 t8).Holds t8 t9 at he9
  have mem9 : t9.external = u.external :=
    (he9.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans mem8
  have agg9 : AgreesExcept registers u t9 :=
    (agg8.trans he9.agrees).mono (by simp [xorR32R32Effect_components, registers])
  have r9_1 : (Operand.reg 1 : Operand 64).read t9 = 0 := by
    have he : (Operand.reg 1 : Operand 64).read t9 = (((Operand.reg 1 : Operand 32).read t8) ^^^ ((Operand.reg 1 : Operand 32).read t8)).setWidth 64 := he9.writes
    simp only [read32, r8_1, BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he
  have r9_6 : (Operand.reg 6 : Operand 64).read t9 = (a0 <<< 32) := (he9.agrees.read (n := 64) (r := 6) (by simp [xorR32R32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans (r5_6))))
  have r9_11 : (Operand.reg 11 : Operand 64).read t9 = (a0 >>> 32) := (he9.agrees.read (n := 64) (r := 11) (by simp [xorR32R32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he7.agrees.read (n := 64) (r := 11) (by simp [movR64R64Effect_components])).trans ((he6.agrees.read (n := 64) (r := 11) (by simp [mulR64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 11) (by simp [shlR64Effect_components])).trans (r4_11)))))
  have r9_8 : (Operand.reg 8 : Operand 64).read t9 = v6.1 := (he9.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans ((he8.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r7_8))
  have r9_10 : (Operand.reg 10 : Operand 64).read t9 = v6.2 := (he9.agrees.read (n := 64) (r := 10) (by simp [xorR32R32Effect_components])).trans (r8_10)
  refine ⟨9, t9, ((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9), ready9, he9.rip, agg9, ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · have h := r9_6
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v6] using h
  · have h := r9_11
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v6] using h
  · have h := r9_8
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v6] using h
  · have h := r9_10
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v6] using h
  · have h := r9_1
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v6] using h


end P256.Proofs.Sec1.Decompress.Select.Parity
