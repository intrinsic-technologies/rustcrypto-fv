import P256.Proofs.Sec1.Decompress.Select.Parity.Second

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
theorem last_block [Bindings] {u : RamState} {boundary : ReturnBoundary} (a : BitVec 64) (b : BitVec 32)
    (hout : ¬ InProgram boundary.rip) (ready : ReadyToStep u) (loaded : ProgramLoaded u)
    (rip : u.RIP = 0x110009)
    (input : (Operand.reg 8 : Operand 64).read u = a ∧
      (Operand.reg 1 : Operand 64).read u = b.setWidth 64 ∧
      (Operand.reg 14 : Operand 64).read u = 0xffffffffffffffff)
    (readable : ∀ i < 4, MemReadable u (stackPtr u + BitVec.ofNat 64 (152+8*i)) 8) :
    ∃ fuel t, Advances boundary fuel u t ∧ ReadyToStep t ∧ t.RIP = 0x11002f ∧
      AgreesExcept registers u t ∧ (Operand.reg 7 : Operand 64).read t = ((last a b (memLoad u.external (stackPtr u+176) 64)).setWidth 8 &&& 1).setWidth 64 := by
  let a0 := memLoad u.external (stackPtr u+152) 64
  let a1 := memLoad u.external (stackPtr u+160) 64
  let a2 := memLoad u.external (stackPtr u+168) 64
  let a3 := memLoad u.external (stackPtr u+176) 64
  rcases input with ⟨input8, input1, input14⟩
  have mem0 : u.external = u.external := rfl
  have agg0 : AgreesExcept registers u u := AgreesExcept.refl _ _
  have code1 : CodeIn (codeRange 0x110009 [0x31, 0xf6]) u :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem0) 0x10009 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, run1, ready1, he1⟩ :=
    (xor_r32_r32_effect_step 0x110009 0xf6 (by decide)).advances ready code1 rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x1000b (by decide)))
  change (xorR32R32Effect 0x110009 2 6 6 u).Holds u t1 at he1
  have mem1 : t1.external = u.external :=
    (he1.agrees.external (by simp [xorR32R32Effect_components, Component.Covers])).trans mem0
  have agg1 : AgreesExcept registers u t1 :=
    (agg0.trans he1.agrees).mono (by simp [xorR32R32Effect_components, registers])
  have r1_6 : (Operand.reg 6 : Operand 64).read t1 = 0 := by
    have he : (Operand.reg 6 : Operand 64).read t1 = (((Operand.reg 6 : Operand 32).read u) ^^^ ((Operand.reg 6 : Operand 32).read u)).setWidth 64 := he1.writes
    simp only [read32, BitVec.xor_self, BitVec.setWidth_zero] at he
    exact he
  have r1_8 : (Operand.reg 8 : Operand 64).read t1 = a := (he1.agrees.read (n := 64) (r := 8) (by simp [xorR32R32Effect_components])).trans (input8)
  have r1_4 : (Operand.reg 4 : Operand 64).read t1 = ((Operand.reg 4 : Operand 64).read u) := (he1.agrees.read (n := 64) (r := 4) (by simp [xorR32R32Effect_components])).trans ((by rfl))
  have addr2 : (AddrMode.sib 4 none 0 (.d32 176)).addr t1 0x110013 = stackPtr u+176 := by
    change (Operand.reg 4 : Operand 64).read t1 + 176 = _
    rw [r1_4]
    rfl
  have read2 : MemReadable t1 ((AddrMode.sib 4 none 0 (.d32 176)).addr t1 0x110013) 8 := by
    rw [addr2]
    exact (readable 3 (by decide)).of_external_eq mem1
  let v2 := addSpec (a) (a3)
  have code2 : CodeIn (codeRange 0x11000b [0x4c, 0x3, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0]) t1 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem1) 0x1000b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, run2, ready2, he2⟩ :=
    (add_r64_m64_effect_step 0x11000b 0x4c (by simp [RexWPrefix]) 0 (AddrMode.sib 4 none 0 (.d32 176)) (by decide) rfl rfl).advances ready1 code2 ⟨he1.rip, read2⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x10013 (by decide)))
  change (addR64M64Effect 0x11000b 8 (AddrMode.sib 4 none 0 (.d32 176)) t1).Holds t1 t2 at he2
  have mem2 : t2.external = u.external :=
    (he2.agrees.external (by simp [addR64M64Effect_components, Component.Covers])).trans mem1
  have agg2 : AgreesExcept registers u t2 :=
    (agg1.trans he2.agrees).mono (by simp [addR64M64Effect_components, registers])
  have r2_8 : (Operand.reg 8 : Operand 64).read t2 = v2.1 := by
    have he : (Operand.reg 8 : Operand 64).read t2 = (addSpec ((Operand.reg 8 : Operand 64).read t1) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 176)).addr t1 0x110013) : Operand 64).read t1)).1 := he2.writes
    simp only [r1_8, addr2, mem1, readMem] at he
    exact he
  have cf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = v2.2.CF := by
    have he : (StatusFlags.ofRFLAGS t2.RFLAGS).CF = (addSpec ((Operand.reg 8 : Operand 64).read t1) ((Operand.mem ((AddrMode.sib 4 none 0 (.d32 176)).addr t1 0x110013) : Operand 64).read t1)).2.CF := he2.flags.1
    simp only [r1_8, addr2, mem1, readMem] at he
    exact he
  have r2_6 : (Operand.reg 6 : Operand 64).read t2 = 0 := (he2.agrees.read (n := 64) (r := 6) (by simp [addR64M64Effect_components])).trans (r1_6)
  have code3 : CodeIn (codeRange 0x110013 [0x40, 0xf, 0x92, 0xc6]) t2 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem2) 0x10013 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t3, run3, ready3, he3⟩ :=
    (setcc_r8_rex_effect_step 0x110013 0x40 0x92 0xc6 (by simp [RexPrefix]) (.inl rfl) (by decide)).advances ready2 code3 he2.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10017 (by decide)))
  change (setccR8Effect 0x110013 4 6 2 t2).Holds t2 t3 at he3
  have mem3 : t3.external = u.external :=
    (he3.agrees.external (by simp [setccR8Effect_components, Component.Covers])).trans mem2
  have agg3 : AgreesExcept registers u t3 :=
    (agg2.trans he3.agrees).mono (by simp [setccR8Effect_components, registers])
  have r3_6 : (Operand.reg 6 : Operand 64).read t3 = (BitVec.ofBool v2.2.CF).setWidth 64 := by
    have he : (Operand.reg 6 : Operand 64).read t3 = mergeGPR 8 (if (StatusFlags.ofRFLAGS t2.RFLAGS).CF then 1 else 0) ((Operand.reg 6 : Operand 64).read t2) := he3.writes
    simp only [r2_6, cf2, P256.Proofs.Sec1Serialize.Conversion.setb_zero] at he
    exact he
  have r3_8 : (Operand.reg 8 : Operand 64).read t3 = v2.1 := (he3.agrees.read (n := 64) (r := 8) (by simp [setccR8Effect_components])).trans (r2_8)
  have code4 : CodeIn (codeRange 0x110017 [0x4c, 0x89, 0xc0]) t3 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem3) 0x10017 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t4, run4, ready4, he4⟩ :=
    (mov_r64_r64_effect_step 0x110017 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready3 code4 he3.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x1001a (by decide)))
  change (movR64R64Effect 0x110017 0 8 t3).Holds t3 t4 at he4
  have mem4 : t4.external = u.external :=
    (he4.agrees.external (by simp [movR64R64Effect_components, Component.Covers])).trans mem3
  have agg4 : AgreesExcept registers u t4 :=
    (agg3.trans he4.agrees).mono (by simp [movR64R64Effect_components, registers])
  have r4_0 : (Operand.reg 0 : Operand 64).read t4 = v2.1 := by
    have he : (Operand.reg 0 : Operand 64).read t4 = ((Operand.reg 8 : Operand 64).read t3) := he4.writes
    simp only [r3_8] at he
    exact he
  have r4_14 : (Operand.reg 14 : Operand 64).read t4 = 0xffffffffffffffff := (he4.agrees.read (n := 64) (r := 14) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 14) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 14) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 14) (by simp [xorR32R32Effect_components])).trans (input14))))
  let v5 := ((v2.1)*(0xffffffffffffffff), mulHigh64 (v2.1) (0xffffffffffffffff))
  have code5 : CodeIn (codeRange 0x11001a [0x49, 0xf7, 0xe6]) t4 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem4) 0x1001a _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t5, run5, ready5, he5⟩ :=
    (mul_r64_effect_step 0x11001a 0x49 0xe6 (by simp [RexWPrefix]) (by decide) (by decide)).advances ready4 code5 he4.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x1001d (by decide)))
  change (mulR64Effect 0x11001a 14 t4).Holds t4 t5 at he5
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
  have r5_8 : (Operand.reg 8 : Operand 64).read t5 = v2.1 := (he5.agrees.read (n := 64) (r := 8) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 8) (by simp [movR64R64Effect_components])).trans (r3_8))
  let v6 := addSpec (v5.1) (v2.1)
  have code6 : CodeIn (codeRange 0x11001d [0x4c, 0x1, 0xc0]) t5 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem5) 0x1001d _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t6, run6, ready6, he6⟩ :=
    (add_r64_r64_effect_step 0x11001d 0x4c 0xc0 (by simp [RexWPrefix]) (by decide)).advances ready5 code6 he5.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10020 (by decide)))
  change (addR64R64Effect 0x11001d 0 8 t5).Holds t5 t6 at he6
  have mem6 : t6.external = u.external :=
    (he6.agrees.external (by simp [addR64R64Effect_components, Component.Covers])).trans mem5
  have agg6 : AgreesExcept registers u t6 :=
    (agg5.trans he6.agrees).mono (by simp [addR64R64Effect_components, registers])
  have r6_0 : (Operand.reg 0 : Operand 64).read t6 = v6.1 := by
    have he : (Operand.reg 0 : Operand 64).read t6 = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 8 : Operand 64).read t5))).1 := he6.writes
    simp only [r5_0, r5_8] at he
    exact he
  have cf6 : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = v6.2.CF := by
    have he : (StatusFlags.ofRFLAGS t6.RFLAGS).CF = (addSpec ((Operand.reg 0 : Operand 64).read t5) (((Operand.reg 8 : Operand 64).read t5))).2.CF := he6.flags.1
    simp only [r5_0, r5_8] at he
    exact he
  have r6_6 : (Operand.reg 6 : Operand 64).read t6 = (BitVec.ofBool v2.2.CF).setWidth 64 := (he6.agrees.read (n := 64) (r := 6) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 6) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 6) (by simp [movR64R64Effect_components])).trans (r3_6)))
  have r6_2 : (Operand.reg 2 : Operand 64).read t6 = v5.2 := (he6.agrees.read (n := 64) (r := 2) (by simp [addR64R64Effect_components])).trans (r5_2)
  have carry7 := P256.Proofs.Sec1Serialize.Conversion.carry_extract cf6
  let v7 := adcSpec (((BitVec.ofBool v2.2.CF).setWidth 64).setWidth 32) ((v5.2).setWidth 32) (BitVec.ofBool v6.2.CF)
  have code7 : CodeIn (codeRange 0x110020 [0x11, 0xd6]) t6 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem6) 0x10020 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t7, run7, ready7, he7⟩ :=
    (adc_r32_r32_effect_step 0x110020 0xd6 (by decide)).advances ready6 code7 he6.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10022 (by decide)))
  change (adcR32R32Effect 0x110020 2 6 2 t6).Holds t6 t7 at he7
  have mem7 : t7.external = u.external :=
    (he7.agrees.external (by simp [adcR32R32Effect_components, Component.Covers])).trans mem6
  have agg7 : AgreesExcept registers u t7 :=
    (agg6.trans he7.agrees).mono (by simp [adcR32R32Effect_components, registers])
  have r7_6 : (Operand.reg 6 : Operand 64).read t7 = v7.1.setWidth 64 := by
    have he : (Operand.reg 6 : Operand 64).read t7 = (adcSpec ((Operand.reg 6 : Operand 32).read t6) (((Operand.reg 2 : Operand 32).read t6)) (t6.RFLAGS.extractLsb' 0 1)).1.setWidth 64 := he7.writes
    simp only [read32, r6_6, r6_2, carry7] at he
    exact he
  have cf7 : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = v7.2.CF := by
    have he : (StatusFlags.ofRFLAGS t7.RFLAGS).CF = (adcSpec ((Operand.reg 6 : Operand 32).read t6) (((Operand.reg 2 : Operand 32).read t6)) (t6.RFLAGS.extractLsb' 0 1)).2.CF := he7.flags.1
    simp only [read32, r6_6, r6_2, carry7] at he
    exact he
  have r7_8 : (Operand.reg 8 : Operand 64).read t7 = v2.1 := (he7.agrees.read (n := 64) (r := 8) (by simp [adcR32R32Effect_components])).trans ((he6.agrees.read (n := 64) (r := 8) (by simp [addR64R64Effect_components])).trans (r5_8))
  let v8 := addSpec ((v7.1.setWidth 64).setWidth 32) ((v2.1).setWidth 32)
  have code8 : CodeIn (codeRange 0x110022 [0x44, 0x1, 0xc6]) t7 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem7) 0x10022 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t8, run8, ready8, he8⟩ :=
    (add_r32_r32_rex_effect_step 0x110022 0x44 0xc6 (by simp [RexNoWPrefix]) (by decide)).advances ready7 code8 he7.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10025 (by decide)))
  change (addR32R32Effect 0x110022 3 6 8 t7).Holds t7 t8 at he8
  have mem8 : t8.external = u.external :=
    (he8.agrees.external (by simp [addR32R32Effect_components, Component.Covers])).trans mem7
  have agg8 : AgreesExcept registers u t8 :=
    (agg7.trans he8.agrees).mono (by simp [addR32R32Effect_components, registers])
  have r8_6 : (Operand.reg 6 : Operand 64).read t8 = v8.1.setWidth 64 := by
    have he : (Operand.reg 6 : Operand 64).read t8 = (addSpec ((Operand.reg 6 : Operand 32).read t7) (((Operand.reg 8 : Operand 32).read t7))).1.setWidth 64 := he8.writes
    simp only [read32, r7_6, r7_8] at he
    exact he
  have cf8 : (StatusFlags.ofRFLAGS t8.RFLAGS).CF = v8.2.CF := by
    have he : (StatusFlags.ofRFLAGS t8.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 32).read t7) (((Operand.reg 8 : Operand 32).read t7))).2.CF := he8.flags.1
    simp only [read32, r7_6, r7_8] at he
    exact he
  have r8_1 : (Operand.reg 1 : Operand 64).read t8 = b.setWidth 64 := (he8.agrees.read (n := 64) (r := 1) (by simp [addR32R32Effect_components])).trans ((he7.agrees.read (n := 64) (r := 1) (by simp [adcR32R32Effect_components])).trans ((he6.agrees.read (n := 64) (r := 1) (by simp [addR64R64Effect_components])).trans ((he5.agrees.read (n := 64) (r := 1) (by simp [mulR64Effect_components])).trans ((he4.agrees.read (n := 64) (r := 1) (by simp [movR64R64Effect_components])).trans ((he3.agrees.read (n := 64) (r := 1) (by simp [setccR8Effect_components])).trans ((he2.agrees.read (n := 64) (r := 1) (by simp [addR64M64Effect_components])).trans ((he1.agrees.read (n := 64) (r := 1) (by simp [xorR32R32Effect_components])).trans (input1))))))))
  let v9 := addSpec ((v8.1.setWidth 64).setWidth 32) ((b.setWidth 64).setWidth 32)
  have code9 : CodeIn (codeRange 0x110025 [0x1, 0xce]) t8 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem8) 0x10025 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t9, run9, ready9, he9⟩ :=
    (add_r32_r32_effect_step 0x110025 0xce (by decide)).advances ready8 code9 he8.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x10027 (by decide)))
  change (addR32R32Effect 0x110025 2 6 1 t8).Holds t8 t9 at he9
  have mem9 : t9.external = u.external :=
    (he9.agrees.external (by simp [addR32R32Effect_components, Component.Covers])).trans mem8
  have agg9 : AgreesExcept registers u t9 :=
    (agg8.trans he9.agrees).mono (by simp [addR32R32Effect_components, registers])
  have r9_6 : (Operand.reg 6 : Operand 64).read t9 = v9.1.setWidth 64 := by
    have he : (Operand.reg 6 : Operand 64).read t9 = (addSpec ((Operand.reg 6 : Operand 32).read t8) (((Operand.reg 1 : Operand 32).read t8))).1.setWidth 64 := he9.writes
    simp only [read32, r8_6, r8_1] at he
    exact he
  have cf9 : (StatusFlags.ofRFLAGS t9.RFLAGS).CF = v9.2.CF := by
    have he : (StatusFlags.ofRFLAGS t9.RFLAGS).CF = (addSpec ((Operand.reg 6 : Operand 32).read t8) (((Operand.reg 1 : Operand 32).read t8))).2.CF := he9.flags.1
    simp only [read32, r8_6, r8_1] at he
    exact he
  have code10 : CodeIn (codeRange 0x110027 [0x40, 0x80, 0xe6, 0x1]) t9 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem9) 0x10027 _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t10, run10, ready10, he10⟩ :=
    (and_sil_one_effect_step 0x110027).advances ready9 code10 he9.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x1002b (by decide)))
  change (andR8Imm8Effect 0x110027 4 6 1 t9).Holds t9 t10 at he10
  have mem10 : t10.external = u.external :=
    (he10.agrees.external (by simp [andR8Imm8Effect, Effect.components, Component.Covers])).trans mem9
  have agg10 : AgreesExcept registers u t10 :=
    (agg9.trans he10.agrees).mono (by simp [andR8Imm8Effect, Effect.components, registers])
  have r10_6 : (Operand.reg 6 : Operand 64).read t10 = mergeGPR 8 ((v9.1.setWidth 64).setWidth 8 &&& 1) (v9.1.setWidth 64) := by
    have he : (Operand.reg 6 : Operand 64).read t10 = mergeGPR 8 (((Operand.reg 6 : Operand 64).read t9).setWidth 8 &&& 1) ((Operand.reg 6 : Operand 64).read t9) := he10.writes
    simp only [r9_6] at he
    exact he
  have code11 : CodeIn (codeRange 0x11002b [0x40, 0xf, 0xb6, 0xfe]) t10 :=
    programText_slice ((programLoaded_codeIn loaded).of_external_eq mem10) 0x1002b _ (by decide +kernel) (by decide +kernel)
  obtain ⟨t11, run11, ready11, he11⟩ :=
    (movzx_r32_r8_rex_effect_step 0x11002b 0x40 0xfe (by simp [RexNoWPrefix]) (by decide)).advances ready10 code11 he10.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x1002f (by decide)))
  change (movzxR32R8Effect 0x11002b 4 7 6 t10).Holds t10 t11 at he11
  have mem11 : t11.external = u.external :=
    (he11.agrees.external (by simp [movzxR32R8Effect, Effect.components, Component.Covers])).trans mem10
  have agg11 : AgreesExcept registers u t11 :=
    (agg10.trans he11.agrees).mono (by simp [movzxR32R8Effect, Effect.components, registers])
  have r11_7 : (Operand.reg 7 : Operand 64).read t11 = ((mergeGPR 8 ((v9.1.setWidth 64).setWidth 8 &&& 1) (v9.1.setWidth 64)).setWidth 8).setWidth 64 := by
    have he : (Operand.reg 7 : Operand 64).read t11 = (((Operand.reg 6 : Operand 64).read t10).setWidth 8).setWidth 64 := he11.writes
    simp only [r10_6] at he
    exact he
  refine ⟨11, t11, ((((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11), ready11, he11.rip, agg11, ?_ ⟩
  · have h := r11_7
    simpa only [byte_merge_low, first, second, last, addSpec_low, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, v2, v5, v6, v7, v8, v9] using h


end P256.Proofs.Sec1.Decompress.Select.Parity
