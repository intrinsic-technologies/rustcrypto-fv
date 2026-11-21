import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.TailMath
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.LoopPremises
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem decode_tail_digits [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 138#64) (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 8 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 169#64 ∧
      AgreesExcept [.reg 11, .reg 3, .flags, .rip] s t ∧
      (Operand.reg 3#5 : Operand 32).read t =
        ((Operand.reg 10#5 : Operand 32).read s - 47) &&&
          ((BitVec.extractLsb' 0 16 (((Operand.reg 10#5 : Operand 32).read s - 58) &&&
            (47 - (Operand.reg 10#5 : Operand 32).read s))).signExtend 32).sshiftRight 8 := by
  obtain ⟨s1, ha1, e1, he1⟩ :=
    decode_advanceNoMemReady hentry
      (mov_r32_imm32_rex_effect_step (p := (decodeAddress alphabet) + 138#64) (rex := 0x41)
        (op := 0xbb) (imm := 0x2f#32) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x41, 0xbb, 0x2f, 0x0, 0x0, 0x0])
        (by intro i; change Fin 6 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x45, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp1 : s1.RIP = (decodeAddress alphabet) + 144#64 := by
    have hh := he1.rip
    change s1.RIP = (decodeAddress alphabet) + 138#64 + 6#64 at hh
    rw [show (decodeAddress alphabet) + 138#64 + 6#64 = (decodeAddress alphabet) + 144#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s2, ha2, e2, he2⟩ :=
    decode_advanceNoMemReady e1
      (sub_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 144#64) (rex := 0x45)
        (modrm := 0xd3) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x29, 0xd3])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp1 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (subR32R32Effect_avoids _ _ _ _ _ _)
  have hp2 : s2.RIP = (decodeAddress alphabet) + 147#64 := by
    have hh := he2.rip
    change s2.RIP = (decodeAddress alphabet) + 144#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 144#64 + 3#64 = (decodeAddress alphabet) + 147#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  let am3 : AddrMode := .base 10 (.d8 0xc6)
  have hs3 := Instructions.lea_r32_effect_step (p := (decodeAddress alphabet) + 147#64) (rex := 0x41)
      (reg := 3#3) (am := am3) (by unfold RexNoWPrefix; decide)
      (by unfold am3; decide) (by unfold am3; decide) (by unfold am3; decide)
  dsimp [am3] at hs3
  obtain ⟨s3, ha3, e3, he3⟩ :=
    decode_advanceNoMemReady e2 hs3
      (decode_codeRangeInImage (entry := (decodeAddress alphabet)) (offset := 147)
        (bytes := [0x41, 0x8d, 0x5a, 0xc6])
        (by intro i; change Fin 4 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp2 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by unfold Instructions.leaR32Effect; rfl) _)
  have hp3 : s3.RIP = (decodeAddress alphabet) + 151#64 := by
    have hh := he3.rip
    change s3.RIP = (decodeAddress alphabet) + 147#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 147#64 + 4#64 = (decodeAddress alphabet) + 151#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s4, ha4, e4, he4⟩ :=
    decode_advanceNoMemReady e3
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 151#64) (rex := 0x44)
        (modrm := 0xdb) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0x21, 0xdb])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp3 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp4 : s4.RIP = (decodeAddress alphabet) + 154#64 := by
    have hh := he4.rip
    change s4.RIP = (decodeAddress alphabet) + 151#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 151#64 + 3#64 = (decodeAddress alphabet) + 154#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s5, ha5, e5, he5⟩ :=
    decode_advanceNoMemReady e4
      (Instructions.movsx_r32_r16_rex_effect_step (p := (decodeAddress alphabet) + 154#64) (rex := 0x44)
        (modrm := 0xdb) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0xf, 0xbf, 0xdb])
        (by intro i; change Fin 4 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp4 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp5 : s5.RIP = (decodeAddress alphabet) + 158#64 := by
    have hh := he5.rip
    change s5.RIP = (decodeAddress alphabet) + 154#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 154#64 + 4#64 = (decodeAddress alphabet) + 158#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s6, ha6, hr6, hc6, he6⟩ := decode_loop_sar_r10_first e5 hp5 hret
  have e6 : EntryReady programImage s6 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e5 hr6 hc6 he6.agrees
  have hp6 : s6.RIP = (decodeAddress alphabet) + 162#64 := by
    have hh := he6.rip
    rw [hp5] at hh
    change s6.RIP = (decodeAddress alphabet) + 158#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 158#64 + 4#64 = (decodeAddress alphabet) + 162#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s7, ha7, hr7, hc7, he7⟩ := decode_loop_lea_r11_r9 e6 hp6 hret
  have e7 : EntryReady programImage s7 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e6 hr7 hc7 he7.agrees
  have hp7 : s7.RIP = (decodeAddress alphabet) + 166#64 := by
    have hh := he7.rip
    rw [hp6] at hh
    change s7.RIP = (decodeAddress alphabet) + 162#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 162#64 + 4#64 = (decodeAddress alphabet) + 166#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s8, ha8, e8, he8⟩ :=
    decode_advanceNoMemReady e7
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 166#64) (rex := 0x44)
        (modrm := 0xdb) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0x21, 0xdb])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp7 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp8 : s8.RIP = (decodeAddress alphabet) + 169#64 := by
    have hh := he8.rip
    change s8.RIP = (decodeAddress alphabet) + 166#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 166#64 + 3#64 = (decodeAddress alphabet) + 169#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  have h9_1 : (Operand.reg 10#5 : Operand 32).read s1 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := he1.agrees.read (r := 10#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, gprNumber, modrmRm, modrmReg, opcodeReg, rexB, rexR])
    simpa using hh
  have h9_2 : (Operand.reg 10#5 : Operand 32).read s2 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := he2.agrees.read (r := 10#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, gprNumber, modrmRm, modrmReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh.trans h9_1
  have hagree2_6 := he2.agrees.trans (he3.agrees.trans (he4.agrees.trans
    (he5.agrees.trans he6.agrees)))
  have h9_6 : (Operand.reg 10#5 : Operand 32).read s6 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := hagree2_6.read (r := 10#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect,
        Instructions.movsxR32R16Effect, Instructions.sarR32Effect, gprNumber, modrmRm, modrmReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh.trans h9_1
  have hagree2_8 := he2.agrees.trans (he3.agrees.trans (he4.agrees.trans
    (he5.agrees.trans (he6.agrees.trans (he7.agrees.trans he8.agrees)))))
  have h9_8 : (Operand.reg 10#5 : Operand 32).read s8 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := hagree2_8.read (r := 10#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect,
        Instructions.movsxR32R16Effect, Instructions.sarR32Effect, gprNumber, modrmRm, modrmReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh.trans h9_1
  have h10_1 : (Operand.reg 11#5 : Operand 32).read s1 = 0x2f#32 := by
    simpa [gprNumber, opcodeReg, rexB] using (tail_mov_value he1)
  have h10_2 : (Operand.reg 11#5 : Operand 32).read s2 =
      (0x2f#32 - (Operand.reg 10#5 : Operand 32).read s) := by
    have hh := tail_bin_value he2
    change (Operand.reg 11#5 : Operand 32).read s2 =
      (Operand.reg 11#5 : Operand 32).read s1 -
        (Operand.reg 10#5 : Operand 32).read s1 at hh
    rw [h10_1, h9_1] at hh
    exact hh
  have h11_3 : (Operand.reg 3#5 : Operand 32).read s3 =
      (Operand.reg 10#5 : Operand 32).read s2 - 0x3a#32 := by
    have hh := tail_lea_value he3
    dsimp [am3] at hh
    have hdst : gprNumber (0#1) (rexR (UInt8.toBitVec 65)) (3#3) = 3#5 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
    rw [hdst] at hh
    simp only [AddrMode.addr, AddrMode.reg64, Operand.read, Disp.value] at hh
    calc
      (Operand.reg 3#5 : Operand 32).read s3 =
          BitVec.extractLsb' 0 32
            (BitVec.setWidth 64 s2.GPR[gprIndex 10#5] + BitVec.signExtend 64 198#8) := hh
      _ = (Operand.reg 10#5 : Operand 32).read s2 - 0x3a#32 := by
        rw [low32_add_signext8]
        have hc : (198#8).signExtend 32 = -0x3a#32 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
        rw [hc, BitVec.sub_eq_add_neg]
        have hw : BitVec.setWidth 64 s2.GPR[gprIndex 10#5] = s2.GPR[gprIndex 10#5] := BitVec.setWidth_eq _
        rw [hw]
        simp only [Operand.read]

  have h11_4 : (Operand.reg 3#5 : Operand 32).read s4 =
      (Operand.reg 3#5 : Operand 32).read s3 &&& (Operand.reg 11#5 : Operand 32).read s3 := by
    have hh := tail_and_value he4
    change (Operand.reg 3#5 : Operand 32).read s4 =
      (Operand.reg 3#5 : Operand 32).read s3 &&&
        (Operand.reg 11#5 : Operand 32).read s3 at hh
    exact hh
  have h10_3 : (Operand.reg 11#5 : Operand 32).read s3 =
      (Operand.reg 11#5 : Operand 32).read s2 := by
    have hh := he3.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh
  have h11_4_16 : (Operand.reg 3#5 : Operand 16).read s4 =
      ((Operand.reg 3#5 : Operand 32).read s3 &&&
        (Operand.reg 11#5 : Operand 32).read s3).extractLsb' 0 16 := by
    have hh := congrArg (fun x : BitVec 32 => x.extractLsb' 0 16) h11_4
    simp only [Operand.read] at hh
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)] at hh
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)] at hh
    simpa only [Operand.read, gprIndex] using hh
  have h10_5 : (Operand.reg 11#5 : Operand 32).read s5 =
      ((Operand.reg 3#5 : Operand 16).read s4).signExtend 32 := by
    have hh := tail_movsx_value he5
    change (Operand.reg 11#5 : Operand 32).read s5 =
      ((Operand.reg 3#5 : Operand 16).read s4).signExtend 32 at hh
    exact hh
  have h10_6 : (Operand.reg 11#5 : Operand 32).read s6 =
      ((Operand.reg 11#5 : Operand 32).read s5).sshiftRight (shiftCount 32 8#8) := by
    have hh := tail_sar_value he6
    change (Operand.reg 11#5 : Operand 32).read s6 =
      ((Operand.reg 11#5 : Operand 32).read s5).sshiftRight (shiftCount 32 8#8) at hh
    exact hh
  have h11_7 : (Operand.reg 3#5 : Operand 32).read s7 =
      (Operand.reg 10#5 : Operand 32).read s6 - 0x2f#32 := by
    have hh := tail_lea_value he7
    have hdst : gprNumber 0 (rexR 65#8) (3#3) = 3#5 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
    rw [hdst] at hh
    simp only [AddrMode.addr, AddrMode.reg64, Operand.read, Disp.value] at hh
    calc
      (Operand.reg 3#5 : Operand 32).read s7 =
          BitVec.extractLsb' 0 32
            (BitVec.setWidth 64 s6.GPR[gprIndex 10#5] + BitVec.signExtend 64 209#8) := hh
      _ = (Operand.reg 10#5 : Operand 32).read s6 - 0x2f#32 := by
        rw [low32_add_signext8]
        have hc : (209#8).signExtend 32 = -0x2f#32 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
        rw [hc, BitVec.sub_eq_add_neg]
        have hw : BitVec.setWidth 64 s6.GPR[gprIndex 10#5] = s6.GPR[gprIndex 10#5] := BitVec.setWidth_eq _
        rw [hw]
        simp only [Operand.read]

  have h10_7 : (Operand.reg 11#5 : Operand 32).read s7 =
      (Operand.reg 11#5 : Operand 32).read s6 := by
    have hh := he7.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh
  have h11_8 : (Operand.reg 3#5 : Operand 32).read s8 =
      (Operand.reg 3#5 : Operand 32).read s7 &&& (Operand.reg 11#5 : Operand 32).read s7 := by
    have hh := tail_and_value he8
    change (Operand.reg 3#5 : Operand 32).read s8 =
      (Operand.reg 3#5 : Operand 32).read s7 &&&
        (Operand.reg 11#5 : Operand 32).read s7 at hh
    exact hh
  have hv : (Operand.reg 3#5 : Operand 32).read s8 =
      ((Operand.reg 10#5 : Operand 32).read s - 47) &&&
        ((BitVec.extractLsb' 0 16 (((Operand.reg 10#5 : Operand 32).read s - 58) &&&
          (47 - (Operand.reg 10#5 : Operand 32).read s))).signExtend 32).sshiftRight 8 := by
    rw [h11_8, h11_7, h10_7, h10_6, h10_5, h11_4_16, h11_3,
      h10_3, h10_2, h9_2, h9_6]
    rfl
  have hagree := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
    (he4.agrees.trans (he5.agrees.trans (he6.agrees.trans (he7.agrees.trans he8.agrees))))))
  have hframe : AgreesExcept [.reg 11, .reg 3, .flags, .rip] s s8 := by
    apply hagree.mono
    intro c hc
    simpa [Effect.components, movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect,
      andR32R32Effect, Instructions.movsxR32R16Effect, Instructions.sarR32Effect, gprNumber, modrmRm,
      modrmReg, opcodeReg, rexB, rexR, or_assoc, or_left_comm, or_comm] using hc
  have ha : Advances boundary 8 s s8 :=
    ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans (ha6.trans (ha7.trans ha8))))))
  exact ⟨s8, ha, e8, hp8, hframe, hv⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem decode_tail_letters [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 169#64) (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 8 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 200#64 ∧
      AgreesExcept [.reg 5, .reg 10, .reg 11, .flags, .rip] s t ∧
      (Operand.reg 10#5 : Operand 32).read t =
        ((Operand.reg 10#5 : Operand 32).read s + (((10#32 - decodeLetterOffset alphabet).setWidth 8)).signExtend 32) &&&
          ((BitVec.extractLsb' 0 16 (((Operand.reg 10#5 : Operand 32).read s - (decodeLetterOffset alphabet + 7#32)) &&&
            (decodeLetterOffset alphabet - (Operand.reg 10#5 : Operand 32).read s))).signExtend 32).sshiftRight 8 := by
  obtain ⟨s9, ha9, e9, he9⟩ :=
    decode_advanceNoMemReady hentry
      (mov_r32_imm32_rex_effect_step (p := (decodeAddress alphabet) + 169#64) (rex := 0x41)
        (op := 0xbb) (imm := (decodeLetterOffset alphabet)) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x41, 0xbb] ++ immBytes 32 (decodeLetterOffset alphabet))
        (by intro i; change Fin 6 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x45, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp9 : s9.RIP = (decodeAddress alphabet) + 175#64 := by
    have hh := he9.rip
    change s9.RIP = (decodeAddress alphabet) + 169#64 + 6#64 at hh
    rw [show (decodeAddress alphabet) + 169#64 + 6#64 = (decodeAddress alphabet) + 175#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s10, ha10, e10, he10⟩ :=
    decode_advanceNoMemReady e9
      (sub_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 175#64) (rex := 0x45)
        (modrm := 0xd3) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x29, 0xd3])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp9 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (subR32R32Effect_avoids _ _ _ _ _ _)
  have hp10 : s10.RIP = (decodeAddress alphabet) + 178#64 := by
    have hh := he10.rip
    change s10.RIP = (decodeAddress alphabet) + 175#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 175#64 + 3#64 = (decodeAddress alphabet) + 178#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s11, ha11, hr11, hc11, he11⟩ := decode_loop_lea_ebx_r9 e10 hp10 hret
  have e11 : EntryReady programImage s11 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e10 hr11 hc11 he11.agrees
  have hp11 : s11.RIP = (decodeAddress alphabet) + 182#64 := by
    have hh := he11.rip
    rw [hp10] at hh
    change s11.RIP = (decodeAddress alphabet) + 178#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 178#64 + 4#64 = (decodeAddress alphabet) + 182#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s12, ha12, e12, he12⟩ :=
    decode_advanceNoMemReady e11
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 182#64) (rex := 0x44)
        (modrm := 0xdd) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0x21, 0xdd])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp11 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp12 : s12.RIP = (decodeAddress alphabet) + 185#64 := by
    have hh := he12.rip
    change s12.RIP = (decodeAddress alphabet) + 182#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 182#64 + 3#64 = (decodeAddress alphabet) + 185#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s13, ha13, e13, he13⟩ :=
    decode_advanceNoMemReady e12
      (Instructions.movsx_r32_r16_rex_effect_step (p := (decodeAddress alphabet) + 185#64) (rex := 0x44)
        (modrm := 0xdd) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x44, 0xf, 0xbf, 0xdd])
        (by intro i; change Fin 4 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp12 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x41, by decide +kernel⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  have hp13 : s13.RIP = (decodeAddress alphabet) + 189#64 := by
    have hh := he13.rip
    change s13.RIP = (decodeAddress alphabet) + 185#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 185#64 + 4#64 = (decodeAddress alphabet) + 189#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s14, ha14, hr14, hc14, he14⟩ := decode_loop_sar_r10_second e13 hp13 hret
  have e14 : EntryReady programImage s14 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e13 hr14 hc14 he14.agrees
  have hp14 : s14.RIP = (decodeAddress alphabet) + 193#64 := by
    have hh := he14.rip
    rw [hp13] at hh
    change s14.RIP = (decodeAddress alphabet) + 189#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 189#64 + 4#64 = (decodeAddress alphabet) + 193#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s15, ha15, hr15, hc15, he15⟩ := decode_loop_add_r9_letterOffset e14 hp14 hret
  have e15 : EntryReady programImage s15 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e14 hr15 hc15 he15.agrees
  have hp15 : s15.RIP = (decodeAddress alphabet) + 197#64 := by
    have hh := he15.rip
    rw [hp14] at hh
    change s15.RIP = (decodeAddress alphabet) + 193#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 193#64 + 4#64 = (decodeAddress alphabet) + 197#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s16, ha16, e16, he16⟩ :=
    decode_advanceNoMemReady e15
      (and_r32_r32_rex_effect_step (p := (decodeAddress alphabet) + 197#64) (rex := 0x45)
        (modrm := 0xda) (by unfold RexNoWPrefix; decide) (by decide))
      (decode_codeRangeInImage (bytes := [0x45, 0x21, 0xda])
        (by intro i; change Fin 3 at i; finite_cases i <;> first | decide +kernel | (cases alphabet <;> decide +kernel))) hp15 hret
      (by dsimp only [movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect, addR32R32Effect]; cases alphabet <;> exact ⟨0x44, by decide +kernel⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  have hp16 : s16.RIP = (decodeAddress alphabet) + 200#64 := by
    have hh := he16.rip
    change s16.RIP = (decodeAddress alphabet) + 197#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 197#64 + 3#64 = (decodeAddress alphabet) + 200#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  have h9_9 : (Operand.reg 10#5 : Operand 32).read s9 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := he9.agrees.read (r := 10#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, gprNumber, modrmRm, modrmReg, opcodeReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh
  have h9_10 : (Operand.reg 10#5 : Operand 32).read s10 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := he9.agrees.trans he10.agrees
    have hr := hh.read (r := 10#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, subR32R32Effect,
        gprNumber, modrmRm, modrmReg, opcodeReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hr
  have h10_9 : (Operand.reg 11#5 : Operand 32).read s9 = (decodeLetterOffset alphabet) := by
    simpa [gprNumber, opcodeReg, rexB] using (tail_mov_value he9)
  have h10_10 : (Operand.reg 11#5 : Operand 32).read s10 =
      ((decodeLetterOffset alphabet) - (Operand.reg 10#5 : Operand 32).read s9) := by
    have hh := tail_bin_value he10
    change (Operand.reg 11#5 : Operand 32).read s10 =
      (Operand.reg 11#5 : Operand 32).read s9 -
        (Operand.reg 10#5 : Operand 32).read s9 at hh
    rw [h10_9] at hh
    exact hh
  have h3_11 : (Operand.reg 5#5 : Operand 32).read s11 =
      (Operand.reg 10#5 : Operand 32).read s10 - (decodeLetterOffset alphabet + 7#32) := by
    have hh := tail_lea_value he11
    have hdst : gprNumber 0 (rexR 65#8) (5#3) = 5#5 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
    rw [hdst] at hh
    simp only [AddrMode.addr, AddrMode.reg64, Operand.read, Disp.value, BitVec.shiftLeft_zero, BitVec.add_zero] at hh
    calc
      (Operand.reg 5#5 : Operand 32).read s11 =
          BitVec.extractLsb' 0 32
            (BitVec.setWidth 64 s10.GPR[gprIndex 10#5] + BitVec.signExtend 64 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8)) := hh
      _ = (Operand.reg 10#5 : Operand 32).read s10 - (decodeLetterOffset alphabet + 7#32) := by
        rw [low32_add_signext8]
        have hc : (((-(decodeLetterOffset alphabet + 7#32)).setWidth 8)).signExtend 32 = -(decodeLetterOffset alphabet + 7#32) := by first | decide +kernel | (cases alphabet <;> decide +kernel)
        rw [hc, BitVec.sub_eq_add_neg]
        congr 1

  have h3_12 : (Operand.reg 5#5 : Operand 32).read s12 =
      (Operand.reg 5#5 : Operand 32).read s11 &&& (Operand.reg 11#5 : Operand 32).read s11 := by
    have hh := tail_and_value he12
    change (Operand.reg 5#5 : Operand 32).read s12 =
      (Operand.reg 5#5 : Operand 32).read s11 &&&
        (Operand.reg 11#5 : Operand 32).read s11 at hh
    exact hh
  have h10_11 : (Operand.reg 11#5 : Operand 32).read s11 =
      (Operand.reg 11#5 : Operand 32).read s10 := by
    have hh := he11.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh
  have h3_12_16 : (Operand.reg 5#5 : Operand 16).read s12 =
      ((Operand.reg 5#5 : Operand 32).read s11 &&&
        (Operand.reg 11#5 : Operand 32).read s11).extractLsb' 0 16 := by
    have hh := congrArg (fun x : BitVec 32 => x.extractLsb' 0 16) h3_12
    simp only [Operand.read] at hh
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)] at hh
    rw [← BitVec.setWidth_eq_extractLsb' (by decide)] at hh
    simpa only [Operand.read, gprIndex] using hh
  have h10_13 : (Operand.reg 11#5 : Operand 32).read s13 =
      ((Operand.reg 5#5 : Operand 16).read s12).signExtend 32 := by
    have hh := tail_movsx_value he13
    change (Operand.reg 11#5 : Operand 32).read s13 =
      ((Operand.reg 5#5 : Operand 16).read s12).signExtend 32 at hh
    exact hh
  have h10_14 : (Operand.reg 11#5 : Operand 32).read s14 =
      ((Operand.reg 11#5 : Operand 32).read s13).sshiftRight (shiftCount 32 8#8) := by
    have hh := tail_sar_value he14
    change (Operand.reg 11#5 : Operand 32).read s14 =
      ((Operand.reg 11#5 : Operand 32).read s13).sshiftRight (shiftCount 32 8#8) at hh
    exact hh
  have h9_14 : (Operand.reg 10#5 : Operand 32).read s14 =
      (Operand.reg 10#5 : Operand 32).read s := by
    have hh := he11.agrees.trans (he12.agrees.trans (he13.agrees.trans he14.agrees))
    have hr := hh.read (r := 10#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect,
        Instructions.sarR32Effect, gprNumber, modrmRm, modrmReg, rexB, rexR] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hr.trans h9_10
  have h9_15 : (Operand.reg 10#5 : Operand 32).read s15 =
      (Operand.reg 10#5 : Operand 32).read s14 + (((10#32 - decodeLetterOffset alphabet).setWidth 8)).signExtend 32 := by
    have hh := tail_add8_value he15
    change (Operand.reg 10#5 : Operand 32).read s15 =
      (Operand.reg 10#5 : Operand 32).read s14 + (((10#32 - decodeLetterOffset alphabet).setWidth 8)).signExtend 32 at hh
    exact hh
  have h10_15 : (Operand.reg 11#5 : Operand 32).read s15 =
      (Operand.reg 11#5 : Operand 32).read s14 := by
    have hh := he15.agrees.read (r := 11#5) (n := 32) (by
      simp [Effect.components, addR32Imm8Effect, gprNumber, modrmRm, rexB] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
    exact hh
  have h9_16 : (Operand.reg 10#5 : Operand 32).read s16 =
      (Operand.reg 10#5 : Operand 32).read s15 &&& (Operand.reg 11#5 : Operand 32).read s15 := by
    have hh := tail_and_value he16
    change (Operand.reg 10#5 : Operand 32).read s16 =
      (Operand.reg 10#5 : Operand 32).read s15 &&&
        (Operand.reg 11#5 : Operand 32).read s15 at hh
    exact hh
  have hv : (Operand.reg 10#5 : Operand 32).read s16 =
      ((Operand.reg 10#5 : Operand 32).read s + (((10#32 - decodeLetterOffset alphabet).setWidth 8)).signExtend 32) &&&
        ((BitVec.extractLsb' 0 16 (((Operand.reg 10#5 : Operand 32).read s - (decodeLetterOffset alphabet + 7#32)) &&&
          (decodeLetterOffset alphabet - (Operand.reg 10#5 : Operand 32).read s))).signExtend 32).sshiftRight 8 := by
    rw [h9_16, h9_15, h10_15, h10_14, h10_13, h3_12_16, h3_11,
      h10_11, h10_10, h9_9, h9_10, h9_14]
    rfl
  have hagree := he9.agrees.trans (he10.agrees.trans (he11.agrees.trans
    (he12.agrees.trans (he13.agrees.trans (he14.agrees.trans (he15.agrees.trans he16.agrees))))))
  have hframe : AgreesExcept [.reg 5, .reg 10, .reg 11, .flags, .rip] s s16 := by
    apply hagree.mono
    intro c hc
    simpa [Effect.components, movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect,
      andR32R32Effect, Instructions.movsxR32R16Effect, Instructions.sarR32Effect, addR32Imm8Effect,
      gprNumber, modrmRm, modrmReg, opcodeReg, rexB, rexR,
      or_assoc, or_left_comm, or_comm] using hc
  have ha : Advances boundary 8 s s16 :=
    ha9.trans (ha10.trans (ha11.trans (ha12.trans (ha13.trans (ha14.trans (ha15.trans ha16))))))
  exact ⟨s16, ha, e16, hp16, hframe, hv⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem decode_tail_pair [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 200#64) (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 3 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 208#64 ∧
      AgreesExcept [.reg 3, .flags, .rip] s t ∧
      (Operand.reg 3#5 : Operand 32).read t =
        ((Operand.reg 3#5 : Operand 32).read s + (Operand.reg 10#5 : Operand 32).read s - 1) |||
          (Operand.reg 8#5 : Operand 32).read s := by
  obtain ⟨s17, ha17, hr17, hc17, he17⟩ := decode_loop_add_ebx_r10 hentry hp hret
  have e17 : EntryReady programImage s17 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hentry hr17 hc17 he17.agrees
  have hp17 : s17.RIP = (decodeAddress alphabet) + 203#64 := by
    have hh := he17.rip
    rw [hp] at hh
    change s17.RIP = (decodeAddress alphabet) + 200#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 200#64 + 3#64 = (decodeAddress alphabet) + 203#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s18, ha18, hr18, hc18, he18⟩ := decode_loop_dec_ebx e17 hp17 hret
  have e18 : EntryReady programImage s18 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e17 hr18 hc18 he18.agrees
  have hp18 : s18.RIP = (decodeAddress alphabet) + 205#64 := by
    have hh := he18.rip
    rw [hp17] at hh
    change s18.RIP = (decodeAddress alphabet) + 203#64 + 2#64 at hh
    rw [show (decodeAddress alphabet) + 203#64 + 2#64 = (decodeAddress alphabet) + 205#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s19, ha19, hr19, hc19, he19⟩ := decode_loop_or_r8_ebx e18 hp18 hret
  have e19 : EntryReady programImage s19 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e18 hr19 hc19 he19.agrees
  have hp19 : s19.RIP = (decodeAddress alphabet) + 208#64 := by
    have hh := he19.rip
    rw [hp18] at hh
    change s19.RIP = (decodeAddress alphabet) + 205#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 205#64 + 3#64 = (decodeAddress alphabet) + 208#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  have h3_17 : (Operand.reg 3#5 : Operand 32).read s17 =
      (Operand.reg 3#5 : Operand 32).read s + (Operand.reg 10#5 : Operand 32).read s := by
    have hw := he17.writes
    change s17.GPR[gprIndex 3#5] =
      ((Operand.reg 3#5 : Operand 32).read s +
        (Operand.reg 10#5 : Operand 32).read s).setWidth 64 at hw
    simp only [Operand.read]
    rw [hw]
    simp
  have h3_18 : (Operand.reg 3#5 : Operand 32).read s18 =
      (Operand.reg 3#5 : Operand 32).read s17 - 1 := by
    have hh := tail_dec_value he18
    change (Operand.reg 3#5 : Operand 32).read s18 =
      (Operand.reg 3#5 : Operand 32).read s17 - 1 at hh
    exact hh
  have h3_19 : (Operand.reg 3#5 : Operand 32).read s19 =
      (Operand.reg 3#5 : Operand 32).read s18 ||| (Operand.reg 8#5 : Operand 32).read s18 := by
    have hh := tail_or_value he19
    change (Operand.reg 3#5 : Operand 32).read s19 =
      (Operand.reg 3#5 : Operand 32).read s18 |||
        (Operand.reg 8#5 : Operand 32).read s18 at hh
    exact hh
  have h8 : (Operand.reg 8#5 : Operand 32).read s18 =
      (Operand.reg 8#5 : Operand 32).read s := by
    exact (he17.agrees.trans he18.agrees).read (r := 8#5) (n := 32) (by
      simp [Effect.components, addR32R32Effect, decR32Effect, gprNumber, rexR, rexB, modrmRm, modrmReg])
  have hv : (Operand.reg 3#5 : Operand 32).read s19 =
      ((Operand.reg 3#5 : Operand 32).read s + (Operand.reg 10#5 : Operand 32).read s - 1) |||
        (Operand.reg 8#5 : Operand 32).read s := by
    rw [h3_19, h3_18, h3_17, h8]
  have hframe : AgreesExcept [.reg 3, .flags, .rip] s s19 := by
    apply (he17.agrees.trans (he18.agrees.trans he19.agrees)).mono
    intro c hc
    simpa [Effect.components, addR32R32Effect, decR32Effect, Instructions.orR32R32Effect,
      gprNumber, modrmRm, modrmReg, rexB, rexR, or_assoc, or_left_comm, or_comm] using hc
  exact ⟨s19, ha17.trans (ha18.trans ha19), e19, hp19, hframe, hv⟩

set_option maxRecDepth 100000 in
theorem decode_tail_value [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} {high low : UInt8}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 138#64) (hret : ¬ InProgram boundary.rip)
    (hhigh : (Operand.reg 8#5 : Operand 32).read s = decodeHighNibble [alphabet] high)
    (hlow : (Operand.reg 10#5 : Operand 32).read s = low.toBitVec.setWidth 32) :
    ∃ t, Advances boundary 19 s t ∧ EntryReady programImage t ∧
      t.RIP = (decodeAddress alphabet) + 208#64 ∧
      AgreesExcept [.reg 5, .reg 10, .reg 11, .reg 3, .flags, .rip] s t ∧
      (Operand.reg 3#5 : Operand 32).read t = decodePair [alphabet] high low := by
  obtain ⟨u, hau, hu, hpu, hfu, hvu⟩ := decode_tail_digits hentry hp hret
  obtain ⟨v, hav, hv, hpv, hfv, hvv⟩ := decode_tail_letters hu hpu hret
  obtain ⟨t, hat, ht, hpt, hft, hvt⟩ := decode_tail_pair hv hpv hret
  have h9u : (Operand.reg 10#5 : Operand 32).read u =
      (Operand.reg 10#5 : Operand 32).read s := hfu.read (by decide)
  have h11v : (Operand.reg 3#5 : Operand 32).read v =
      (Operand.reg 3#5 : Operand 32).read u := hfv.read (by decide)
  have h8v : (Operand.reg 8#5 : Operand 32).read v =
      (Operand.reg 8#5 : Operand 32).read s :=
    (hfv.read (by decide)).trans (hfu.read (by decide))
  have hval : (Operand.reg 3#5 : Operand 32).read t = decodePair [alphabet] high low := by
    rw [hvt, h11v, hvu, hvv, h9u, h8v, hhigh, hlow]
    change decodeTailExpanded alphabet low ||| decodeHighNibble [alphabet] high = _
    rw [decodeTailExpanded_correct, BitVec.or_comm]
    rfl
  have hf : AgreesExcept [.reg 5, .reg 10, .reg 11, .reg 3, .flags, .rip] s t := by
    apply (hfu.trans (hfv.trans hft)).mono
    intro c hc
    simpa [or_assoc, or_left_comm, or_comm] using hc
  exact ⟨t, hau.trans (hav.trans hat), ht, hpt, hf, hval⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
