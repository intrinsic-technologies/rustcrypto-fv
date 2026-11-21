import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopStatefulValues
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem decode_middle_stateful [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} {high : UInt8} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 84#64) (hret : ¬ InProgram boundary.rip)
    (hload : MemReadable s ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s
        (BitVec.add s.RIP (6#64))) 1)
    (hhigh : (Operand.reg 8#5 : Operand 32).read s = high.toBitVec.setWidth 32)
    (hmask : (Operand.reg 10#5 : Operand 32).read s =
      decodeRangeMask 47 58 (high.toBitVec.setWidth 32) >>> 8)
    (hwide : (Operand.reg 11#5 : Operand 32).read s = high.toBitVec.setWidth 32 + 0xfd1) :
    ∃ t, Advances boundary 13 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 138#64 ∧
      AgreesExcept [.reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s t ∧
      (Operand.reg 8#5 : Operand 32).read t = decodeHighNibble [alphabet] high ∧
      (Operand.reg 10#5 : Operand 32).read t =
        ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s
          (BitVec.add s.RIP (6#64))) : Operand 8).read s).setWidth 32 := by
  obtain ⟨s1, ha1, e1, he1⟩ :=
    decode_advanceNoMemReady hentry
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 84#64) (rex := 0x45)
        (modrm := 0xd3) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x21, 0xd3])
        (by intro i; change Fin 3 at i; finite_cases i <;> cases alphabet <;> decide +kernel))
      hp hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp1 : s1.RIP = (decodeAddress alphabet) + 87#64 := by
    have hh := he1.rip
    change s1.RIP = (decodeAddress alphabet) + 84#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 84#64 + 3#64 = (decodeAddress alphabet) + 87#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s2, ha2, e2, he2⟩ :=
    decode_advanceNoMemReady e1
      (mov_r32_imm32_rex_effect_step (p := (decodeAddress alphabet) + 87#64) (rex := 0x41)
        (op := 0xba) (imm := decodeLetterOffset alphabet) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (entry := decodeAddress alphabet) (offset := 87)
        (bytes := 0x41 :: 0xba :: immBytes 32 (decodeLetterOffset alphabet))
        (by cases alphabet <;> intro i <;> change Fin 6 at i <;> finite_cases i <;> decide +kernel)) hp1 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x45, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp2 : s2.RIP = (decodeAddress alphabet) + 93#64 := by
    have hh := he2.rip
    change s2.RIP = (decodeAddress alphabet) + 87#64 + 6#64 at hh
    rw [show (decodeAddress alphabet) + 87#64 + 6#64 = (decodeAddress alphabet) + 93#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s3, ha3, e3, he3⟩ :=
    decode_advanceNoMemReady e2
      (sub_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 93#64) (rex := 0x45)
        (modrm := 0xc2) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x29, 0xc2])
        (by intro i; change Fin 3 at i; finite_cases i <;> cases alphabet <;> decide +kernel)) hp2 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (subR32R32Effect_avoids _ _ _ _ _ _)
  have hp3 : s3.RIP = (decodeAddress alphabet) + 96#64 := by
    have hh := he3.rip
    change s3.RIP = (decodeAddress alphabet) + 93#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 93#64 + 3#64 = (decodeAddress alphabet) + 96#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s4, ha4, hr4, hc4, he4⟩ := decode_loop_lea_r11_r8 e3 hp3 hret
  have e4 : EntryReady programImage s4 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e3 hr4 hc4 he4.agrees
  have hp4 : s4.RIP = (decodeAddress alphabet) + 100#64 := by
    have hh := he4.rip
    rw [hp3] at hh
    change s4.RIP = (decodeAddress alphabet) + 96#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 96#64 + 4#64 = (decodeAddress alphabet) + 100#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s5, ha5, e5, he5⟩ :=
    decode_advanceNoMemReady e4
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 100#64) (rex := 0x44)
        (modrm := 0xd3) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0x21, 0xd3])
        (by intro i; change Fin 3 at i; finite_cases i <;> cases alphabet <;> decide +kernel)) hp4 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp5 : s5.RIP = (decodeAddress alphabet) + 103#64 := by
    have hh := he5.rip
    change s5.RIP = (decodeAddress alphabet) + 100#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 100#64 + 3#64 = (decodeAddress alphabet) + 103#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s6, ha6, e6, he6⟩ :=
    decode_advanceNoMemReady e5
      (Instructions.movsx_r32_r16_rex_effect_step (p := (decodeAddress alphabet) + 103#64) (rex := 0x44)
        (modrm := 0xd3) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0x0f, 0xbf, 0xd3])
        (by intro i; change Fin 4 at i; finite_cases i <;> cases alphabet <;> decide +kernel)) hp5 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp6 : s6.RIP = (decodeAddress alphabet) + 107#64 := by
    have hh := he6.rip
    change s6.RIP = (decodeAddress alphabet) + 103#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 103#64 + 4#64 = (decodeAddress alphabet) + 107#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s7, ha7, hr7, hc7, he7⟩ := decode_loop_shr_r9_second e6 hp6 hret
  have e7 : EntryReady programImage s7 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e6 hr7 hc7 he7.agrees
  have hp7 : s7.RIP = (decodeAddress alphabet) + 111#64 := by
    have hh := he7.rip
    rw [hp6] at hh
    change s7.RIP = (decodeAddress alphabet) + 107#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 107#64 + 4#64 = (decodeAddress alphabet) + 111#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s8, ha8, hr8, hc8, he8⟩ := decode_loop_add_r8_letterOffset e7 hp7 hret
  have e8 : EntryReady programImage s8 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e7 hr8 hc8 he8.agrees
  have hp8 : s8.RIP = (decodeAddress alphabet) + 118#64 := by
    have hh := he8.rip
    rw [hp7] at hh
    change s8.RIP = (decodeAddress alphabet) + 111#64 + 7#64 at hh
    rw [show (decodeAddress alphabet) + 111#64 + 7#64 = (decodeAddress alphabet) + 118#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s9, ha9, e9, he9⟩ :=
    decode_advanceNoMemReady e8
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 118#64) (rex := 0x45)
        (modrm := 0xd0) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x21, 0xd0])
        (by intro i; change Fin 3 at i; finite_cases i <;> cases alphabet <;> decide +kernel)) hp8 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x45, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp9 : s9.RIP = (decodeAddress alphabet) + 121#64 := by
    have hh := he9.rip
    change s9.RIP = (decodeAddress alphabet) + 118#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 118#64 + 3#64 = (decodeAddress alphabet) + 121#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s10, ha10, e10, he10⟩ :=
    decode_advanceNoMemReady e9
      (add_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 121#64) (rex := 0x45)
        (modrm := 0xd8) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x01, 0xd8])
        (by intro i; change Fin 3 at i; finite_cases i <;> cases alphabet <;> decide +kernel)) hp9 hret
      (by dsimp only [andR32R32Effect, movR32Imm32Effect, subR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (addR32R32Effect_avoids _ _ _ _ _ _)
  have hp10 : s10.RIP = (decodeAddress alphabet) + 124#64 := by
    have hh := he10.rip
    change s10.RIP = (decodeAddress alphabet) + 121#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 121#64 + 3#64 = (decodeAddress alphabet) + 124#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s11, ha11, hr11, hc11, he11⟩ := decode_loop_shl_r8 e10 hp10 hret
  have e11 : EntryReady programImage s11 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e10 hr11 hc11 he11.agrees
  have hp11 : s11.RIP = (decodeAddress alphabet) + 128#64 := by
    have hh := he11.rip
    rw [hp10] at hh
    change s11.RIP = (decodeAddress alphabet) + 124#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 124#64 + 4#64 = (decodeAddress alphabet) + 128#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s12, ha12, hr12, hc12, he12⟩ := decode_loop_add_r8_minus16 e11 hp11 hret
  have e12 : EntryReady programImage s12 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e11 hr12 hc12 he12.agrees
  have hp12 : s12.RIP = (decodeAddress alphabet) + 132#64 := by
    have hh := he12.rip
    rw [hp11] at hh
    change s12.RIP = (decodeAddress alphabet) + 128#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 128#64 + 4#64 = (decodeAddress alphabet) + 132#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  have h8_1 : (Operand.reg 8#5 : Operand 32).read s1 = high.toBitVec.setWidth 32 := by
    have hh := he1.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, andR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans hhigh
  have h8_2 : (Operand.reg 8#5 : Operand 32).read s2 = high.toBitVec.setWidth 32 := by
    have hh := he2.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_1
  have h8_3 : (Operand.reg 8#5 : Operand 32).read s3 = high.toBitVec.setWidth 32 := by
    have hh := he3.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_2
  have h8_4 : (Operand.reg 8#5 : Operand 32).read s4 = high.toBitVec.setWidth 32 := by
    have hh := he4.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_3
  have h8_5 : (Operand.reg 8#5 : Operand 32).read s5 = high.toBitVec.setWidth 32 := by
    have hh := he5.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, andR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_4
  have h8_6 : (Operand.reg 8#5 : Operand 32).read s6 = high.toBitVec.setWidth 32 := by
    have hh := he6.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, Instructions.movsxR32R16Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_5
  have h8_7 : (Operand.reg 8#5 : Operand 32).read s7 = high.toBitVec.setWidth 32 := by
    have hh := he7.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, shrR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_6
  have v1 : (Operand.reg 11#5 : Operand 32).read s1 =
      (high.toBitVec.setWidth 32 + 0xfd1) &&&
        (decodeRangeMask 47 58 (high.toBitVec.setWidth 32) >>> 8) := by
    have hh := tail_and_value he1
    change (Operand.reg 11#5 : Operand 32).read s1 =
      (Operand.reg 11#5 : Operand 32).read s &&& (Operand.reg 10#5 : Operand 32).read s at hh
    simpa [hwide, hmask] using hh
  have v2 : (Operand.reg 10#5 : Operand 32).read s2 = (decodeLetterOffset alphabet) := by
    simpa [gprNumber, opcodeReg, rexB] using tail_mov_value he2
  have v3 : (Operand.reg 10#5 : Operand 32).read s3 =
      (decodeLetterOffset alphabet) - high.toBitVec.setWidth 32 := by
    have hh := tail_bin_value he3
    change (Operand.reg 10#5 : Operand 32).read s3 =
      (Operand.reg 10#5 : Operand 32).read s2 - (Operand.reg 8#5 : Operand 32).read s2 at hh
    simpa only [v2, h8_2] using hh
  have v4 : (Operand.reg 3#5 : Operand 32).read s4 = high.toBitVec.setWidth 32 - (decodeLetterOffset alphabet + 7#32) := by
    have hh := tail_lea_value he4
    change (Operand.reg 3#5 : Operand 32).read s4 =
      (AddrMode.reg64 8 s3 + ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8).signExtend 64).extractLsb' 0 32 at hh
    rw [low32_add_signext8] at hh
    have hc : ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8).signExtend 32 = -(decodeLetterOffset alphabet + 7#32) := by cases alphabet <;> decide +kernel
    rw [hc] at hh
    change (Operand.reg 3#5 : Operand 32).read s4 =
      (Operand.reg 8#5 : Operand 32).read s3 + -(decodeLetterOffset alphabet + 7#32) at hh
    simpa only [h8_3, ← BitVec.sub_eq_add_neg] using hh
  have k94 : (Operand.reg 10#5 : Operand 32).read s4 =
      (Operand.reg 10#5 : Operand 32).read s3 := by
    exact he4.agrees.read (by simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR])
  have v5 : (Operand.reg 3#5 : Operand 32).read s5 =
      (high.toBitVec.setWidth 32 - (decodeLetterOffset alphabet + 7#32)) &&& ((decodeLetterOffset alphabet) - high.toBitVec.setWidth 32) := by
    have hh := tail_and_value he5
    change (Operand.reg 3#5 : Operand 32).read s5 =
      (Operand.reg 3#5 : Operand 32).read s4 &&& (Operand.reg 10#5 : Operand 32).read s4 at hh
    simpa only [v4, k94, v3] using hh
  have v5w : (Operand.reg 3#5 : Operand 16).read s5 =
      ((high.toBitVec.setWidth 32 - (decodeLetterOffset alphabet + 7#32)) &&& ((decodeLetterOffset alphabet) - high.toBitVec.setWidth 32)).setWidth 16 := by
    have hh := congrArg (fun x : BitVec 32 => x.setWidth 16) v5
    simpa only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32)] using hh
  have v6 := tail_movsx_value he6
  change (Operand.reg 10#5 : Operand 32).read s6 =
    ((Operand.reg 3#5 : Operand 16).read s5).signExtend 32 at v6
  rw [v5w] at v6
  have v7 : (Operand.reg 10#5 : Operand 32).read s7 =
      decodeRangeMask (decodeLetterOffset alphabet) (decodeLetterOffset alphabet + 7#32) (high.toBitVec.setWidth 32) >>> 8 := by
    have hw := he7.writes
    change s7.GPR[10] = (((Operand.reg 10#5 : Operand 32).read s6) >>> 8).setWidth 64 at hw
    change s7.GPR[10].setWidth 32 = _
    rw [hw, v6]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    simp [decodeRangeMask, BitVec.and_comm]
  have v8 : (Operand.reg 8#5 : Operand 32).read s8 = high.toBitVec.setWidth 32 + (0x100a#32 - decodeLetterOffset alphabet) := by
    have hw := he8.writes
    simp only [addR32Imm32Effect, Write.AllHold, BitVec.signExtend_eq] at hw
    change s8.GPR[8] = (((Operand.reg 8#5 : Operand 32).read s7) + (0x100a#32 - decodeLetterOffset alphabet)).setWidth 64 at hw
    change s8.GPR[8].setWidth 32 = _
    rw [hw, h8_7]
    simp
  have k98 : (Operand.reg 10#5 : Operand 32).read s8 =
      (Operand.reg 10#5 : Operand 32).read s7 := by
    exact he8.agrees.read (by simp [Effect.components, addR32Imm32Effect, gprNumber, modrmRm, rexB])
  have v9 := tail_and_value he9
  change (Operand.reg 8#5 : Operand 32).read s9 =
    (Operand.reg 8#5 : Operand 32).read s8 &&& (Operand.reg 10#5 : Operand 32).read s8 at v9
  rw [v8, k98, v7] at v9
  have k10_2 : (Operand.reg 11#5 : Operand 32).read s2 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he2.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh
  have k10_3 : (Operand.reg 11#5 : Operand 32).read s3 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he3.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_2
  have k10_4 : (Operand.reg 11#5 : Operand 32).read s4 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he4.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_3
  have k10_5 : (Operand.reg 11#5 : Operand 32).read s5 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he5.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, andR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_4
  have k10_6 : (Operand.reg 11#5 : Operand 32).read s6 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he6.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, Instructions.movsxR32R16Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_5
  have k10_7 : (Operand.reg 11#5 : Operand 32).read s7 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he7.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, shrR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_6
  have k10_8 : (Operand.reg 11#5 : Operand 32).read s8 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he8.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, addR32Imm32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_7
  have k10_9 : (Operand.reg 11#5 : Operand 32).read s9 =
      (Operand.reg 11#5 : Operand 32).read s1 := by
    have hh := he9.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, andR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans k10_8
  have v10 : (Operand.reg 8#5 : Operand 32).read s10 =
      (Operand.reg 8#5 : Operand 32).read s9 + (Operand.reg 11#5 : Operand 32).read s9 := by
    have hw := he10.writes
    change s10.GPR[8] = (((Operand.reg 8#5 : Operand 32).read s9) +
      (Operand.reg 11#5 : Operand 32).read s9).setWidth 64 at hw
    change s10.GPR[8].setWidth 32 = _
    rw [hw]
    simp
  rw [v9, k10_9, v1] at v10
  have v11 : (Operand.reg 8#5 : Operand 32).read s11 =
      (Operand.reg 8#5 : Operand 32).read s10 <<< 4 := by
    have hw := he11.writes
    change s11.GPR[8] = (((Operand.reg 8#5 : Operand 32).read s10) <<< 4).setWidth 64 at hw
    change s11.GPR[8].setWidth 32 = _
    rw [hw]
    simp
  have v12 := tail_add8_value he12
  change (Operand.reg 8#5 : Operand 32).read s12 =
    (Operand.reg 8#5 : Operand 32).read s11 + (240#8).signExtend 32 at v12
  rw [v11, v10] at v12
  have hhigh12 : (Operand.reg 8#5 : Operand 32).read s12 = decodeHighNibble [alphabet] high := by
    cases alphabet <;> simpa [decodeHighNibble, decodeLetterOffset, BitVec.and_comm, BitVec.add_comm,
      BitVec.sub_eq_add_neg] using v12
  have hagree12 : AgreesExcept [.reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s s12 := by
    have hf := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
      (he4.agrees.trans (he5.agrees.trans (he6.agrees.trans (he7.agrees.trans
      (he8.agrees.trans (he9.agrees.trans (he10.agrees.trans (he11.agrees.trans he12.agrees))))))))))
    apply hf.mono
    intro c hc
    simpa [Effect.components, andR32R32Effect, movR32Imm32Effect, subR32R32Effect,
      Instructions.leaR32Effect, Instructions.movsxR32R16Effect, shrR32Effect, addR32Imm32Effect,
      addR32R32Effect, Instructions.shlR32Effect, addR32Imm8Effect, gprNumber, rexR, rexB,
      modrmRm, modrmReg, opcodeReg, or_assoc, or_left_comm, or_comm] using hc
  have hmem12 : s12.external = s.external := by
    apply hagree12.external
    intro c hc x
    cases c <;> simp_all [Component.Covers]
  have hrdi : AddrMode.reg64 7 s12 = AddrMode.reg64 7 s := hagree12.read (by decide)
  have hrsi : AddrMode.reg64 0 s12 = AddrMode.reg64 0 s := hagree12.read (by decide)
  have haddr12 : (AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s12 (BitVec.add s12.RIP 6#64) =
      (AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s (BitVec.add s.RIP 6#64) := by
    simp only [AddrMode.addr, hrdi, hrsi]
  have hload12 : MemReadable s12
      ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s12 (BitVec.add s12.RIP 6#64)) 1 := by
    rw [haddr12]
    exact hload.of_external_eq hmem12
  obtain ⟨s13, ha13, hr13, hc13, he13⟩ := decode_loop_load_second e12 hp12 hload12 hret
  have e13 : EntryReady programImage s13 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e12 hr13 hc13 he13.agrees
  have hpt : s13.RIP = (decodeAddress alphabet) + 138#64 := by
    have hh := he13.rip
    rw [hp12] at hh
    simpa only [movzxR32M8Effect, BitVec.add_assoc, show 132#64 + 6#64 = 138#64 by decide +kernel] using hh
  have hframe : AgreesExcept [.reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s s13 := by
    apply (hagree12.trans he13.agrees).mono
    intro c hc
    simpa [Effect.components, movzxR32M8Effect, gprNumber, rexR,
      or_assoc, or_left_comm, or_comm] using hc
  have hkeep : (Operand.reg 8#5 : Operand 32).read s13 =
      (Operand.reg 8#5 : Operand 32).read s12 := by
    exact he13.agrees.read (by simp [Effect.components, movzxR32M8Effect, gprNumber, rexR])
  have hsecond : (Operand.reg 10#5 : Operand 32).read s13 =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s
        (BitVec.add s.RIP 6#64)) : Operand 8).read s).setWidth 32 := by
    have hw := he13.writes
    change s13.GPR[10] =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s12
        (BitVec.add s12.RIP 6#64)) : Operand 8).read s12).setWidth 64 at hw
    change s13.GPR[10].setWidth 32 = _
    rw [hw, haddr12]
    simp only [Operand.read, hmem12, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  refine ⟨s13, ?_, e13, hpt, hframe, hkeep.trans hhigh12, hsecond⟩
  exact ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans
    (ha7.trans (ha8.trans (ha9.trans (ha10.trans (ha11.trans (ha12.trans ha13)))))))))))

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
