import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.TailMath
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
theorem decode_loop_prefix_value [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 48#64)
    (hload : MemReadable s
      ((AddrMode.sib 7 (some 0) 1#2 .none).addr s (BitVec.add s.RIP (5#64))) 1)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 8 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      t.RIP = (decodeAddress alphabet) + 84#64 ∧
      AgreesExcept [.reg 8#5, .reg 10#5, .reg 11#5, .flags, .rip] s t ∧
      (Operand.reg 8#5 : Operand 32).read t =
        ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addr s
          (BitVec.add s.RIP (5#64))) : Operand 8).read s).setWidth 32 ∧
      (Operand.reg 10#5 : Operand 32).read t =
        decodeRangeMask 47 58 ((Operand.reg 8#5 : Operand 32).read t) >>> 8 ∧
      (Operand.reg 11#5 : Operand 32).read t =
        (Operand.reg 8#5 : Operand 32).read t + 0xfd1 := by
  obtain ⟨s1, ha1, hr1, hc1, he1⟩ := decode_loop_load hentry hp hload hret
  have e1 : EntryReady programImage s1 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hentry hr1 hc1 he1.agrees
  have hp1 : s1.RIP = (decodeAddress alphabet) + 53#64 := by
    have hh := he1.rip
    rw [hp] at hh
    change s1.RIP = (decodeAddress alphabet) + 48#64 + 5#64 at hh
    rw [show (decodeAddress alphabet) + 48#64 + 5#64 = (decodeAddress alphabet) + 53#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s2, ha2, hr2, hc2, he2⟩ := decode_loop_mov_r9 e1 hp1 hret
  have e2 : EntryReady programImage s2 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e1 hr2 hc2 he2.agrees
  have hp2 : s2.RIP = (decodeAddress alphabet) + 59#64 := by
    have hh := he2.rip
    rw [hp1] at hh
    change s2.RIP = (decodeAddress alphabet) + 53#64 + 6#64 at hh
    rw [show (decodeAddress alphabet) + 53#64 + 6#64 = (decodeAddress alphabet) + 59#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s3, ha3, hr3, hc3, he3⟩ := decode_loop_sub_r9_r8 e2 hp2 hret
  have e3 : EntryReady programImage s3 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e2 hr3 hc3 he3.agrees
  have hp3 : s3.RIP = (decodeAddress alphabet) + 62#64 := by
    have hh := he3.rip
    rw [hp2] at hh
    change s3.RIP = (decodeAddress alphabet) + 59#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 59#64 + 3#64 = (decodeAddress alphabet) + 62#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s4, ha4, hr4, hc4, he4⟩ := decode_loop_lea_r10_r8 e3 hp3 hret
  have e4 : EntryReady programImage s4 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e3 hr4 hc4 he4.agrees
  have hp4 : s4.RIP = (decodeAddress alphabet) + 66#64 := by
    have hh := he4.rip
    rw [hp3] at hh
    change s4.RIP = (decodeAddress alphabet) + 62#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 62#64 + 4#64 = (decodeAddress alphabet) + 66#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s5, ha5, hr5, hc5, he5⟩ := decode_loop_and_r10_r9 e4 hp4 hret
  have e5 : EntryReady programImage s5 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e4 hr5 hc5 he5.agrees
  have hp5 : s5.RIP = (decodeAddress alphabet) + 69#64 := by
    have hh := he5.rip
    rw [hp4] at hh
    change s5.RIP = (decodeAddress alphabet) + 66#64 + 3#64 at hh
    rw [show (decodeAddress alphabet) + 66#64 + 3#64 = (decodeAddress alphabet) + 69#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s6, ha6, hr6, hc6, he6⟩ := decode_loop_movsx_r9_r10 e5 hp5 hret
  have e6 : EntryReady programImage s6 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e5 hr6 hc6 he6.agrees
  have hp6 : s6.RIP = (decodeAddress alphabet) + 73#64 := by
    have hh := he6.rip
    rw [hp5] at hh
    change s6.RIP = (decodeAddress alphabet) + 69#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 69#64 + 4#64 = (decodeAddress alphabet) + 73#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s7, ha7, hr7, hc7, he7⟩ := decode_loop_shr_r9_first e6 hp6 hret
  have e7 : EntryReady programImage s7 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter e6 hr7 hc7 he7.agrees
  have hp7 : s7.RIP = (decodeAddress alphabet) + 77#64 := by
    have hh := he7.rip
    rw [hp6] at hh
    change s7.RIP = (decodeAddress alphabet) + 73#64 + 4#64 at hh
    rw [show (decodeAddress alphabet) + 73#64 + 4#64 = (decodeAddress alphabet) + 77#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  obtain ⟨s8, ha8, hr8, hc8, he8⟩ := decode_loop_lea_r10_r8_wide e7 hp7 hret
  have hagree := he1.agrees.trans (he2.agrees.trans (he3.agrees.trans
    (he4.agrees.trans (he5.agrees.trans (he6.agrees.trans
    (he7.agrees.trans he8.agrees))))))
  have hagree' : AgreesExcept
      ([.reg 8#5, .reg 10#5, .reg 11#5, .flags, .rip] : List Component) s s8 := by
    apply hagree.narrow
    intro c hc hnot
    simp [Effect.components, movzxR32M8Effect, movR32Imm32Effect,
      subR32R32Effect, Instructions.leaR32Effect, andR32R32Effect, Instructions.movsxR32R16Effect,
      shrR32Effect, gprNumber, modrmRm, modrmReg, opcodeReg, rexB, rexR] at hc hnot
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals simp_all
  have ha : Advances boundary 8 s s8 := by
    exact ha1.trans (ha2.trans (ha3.trans (ha4.trans
      (ha5.trans (ha6.trans (ha7.trans ha8))))))
  have hpt : s8.RIP = (decodeAddress alphabet) + 84#64 := by
    have hh := he8.rip
    rw [hp7] at hh
    change s8.RIP = (decodeAddress alphabet) + 77#64 + 7#64 at hh
    rw [show (decodeAddress alphabet) + 77#64 + 7#64 = (decodeAddress alphabet) + 84#64 by rw [BitVec.add_assoc]; rfl] at hh
    exact hh
  have hafter : AgreesExcept ([.reg 10#5, .reg 11#5, .flags, .rip] : List Component) s1 s8 := by
    have hh := he2.agrees.trans (he3.agrees.trans (he4.agrees.trans
      (he5.agrees.trans (he6.agrees.trans (he7.agrees.trans he8.agrees)))))
    apply hh.narrow
    intro c hc hnot
    simp [Effect.components, movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect,
      andR32R32Effect, Instructions.movsxR32R16Effect, shrR32Effect, gprNumber, modrmRm,
      modrmReg, opcodeReg, rexB, rexR] at hc hnot
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals simp_all
  have hwrite := he1.writes
  simp [movzxR32M8Effect, Write.AllHold] at hwrite
  change s1.GPR[8] = _ at hwrite
  have hwrite32 : (Operand.reg 8#5 : Operand 32).read s1 =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addr s
        (BitVec.add s.RIP (5#64))) : Operand 8).read s).setWidth 32 := by
    change BitVec.setWidth 32 s1.GPR[8] = _
    have hh := congrArg (fun x : BitVec 64 => x.setWidth 32) hwrite
    simpa [Operand.read, gprIndex, BitVec.setWidth_setWidth] using hh
  have hkeep := hafter.read (n := 32) (r := 8#5) (by
    simp [Effect.components, movR32Imm32Effect, subR32R32Effect, Instructions.leaR32Effect,
      andR32R32Effect, Instructions.movsxR32R16Effect, shrR32Effect] <;> first | decide +kernel | (cases alphabet <;> decide +kernel))
  have hvalue : (Operand.reg 8#5 : Operand 32).read s8 =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1#2 .none).addr s
        (BitVec.add s.RIP (5#64))) : Operand 8).read s).setWidth 32 := by
    exact hkeep.trans hwrite32
  have h8_2 : (Operand.reg 8#5 : Operand 32).read s2 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he2.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, movR32Imm32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh
  have h8_3 : (Operand.reg 8#5 : Operand 32).read s3 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he3.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, subR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_2
  have h8_4 : (Operand.reg 8#5 : Operand 32).read s4 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he4.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_3
  have h8_5 : (Operand.reg 8#5 : Operand 32).read s5 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he5.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, andR32R32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_4
  have h8_6 : (Operand.reg 8#5 : Operand 32).read s6 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he6.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, Instructions.movsxR32R16Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_5
  have h8_7 : (Operand.reg 8#5 : Operand 32).read s7 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he7.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, shrR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_6
  have h8_8 : (Operand.reg 8#5 : Operand 32).read s8 =
      (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := he8.agrees.read (r := 8#5) (n := 32) (by
      simp [Effect.components, Instructions.leaR32Effect, gprNumber, modrmReg, modrmRm, opcodeReg, rexB, rexR])
    exact hh.trans h8_7
  have v2 : (Operand.reg 10#5 : Operand 32).read s2 = 47#32 := by
    simpa [gprNumber, opcodeReg, rexB] using tail_mov_value he2
  have v3 : (Operand.reg 10#5 : Operand 32).read s3 =
      47#32 - (Operand.reg 8#5 : Operand 32).read s1 := by
    have hh := tail_bin_value he3
    change (Operand.reg 10#5 : Operand 32).read s3 =
      (Operand.reg 10#5 : Operand 32).read s2 - (Operand.reg 8#5 : Operand 32).read s2 at hh
    simpa only [v2, h8_2] using hh
  have v4 : (Operand.reg 11#5 : Operand 32).read s4 =
      (Operand.reg 8#5 : Operand 32).read s1 - 58#32 := by
    have hh := tail_lea_value he4
    change (Operand.reg 11#5 : Operand 32).read s4 =
      (AddrMode.reg64 8 s3 + (198#8).signExtend 64).extractLsb' 0 32 at hh
    rw [low32_add_signext8] at hh
    have hc : (198#8).signExtend 32 = -58#32 := by first | decide +kernel | (cases alphabet <;> decide +kernel)
    rw [hc] at hh
    change (Operand.reg 11#5 : Operand 32).read s4 =
      (Operand.reg 8#5 : Operand 32).read s3 + -58#32 at hh
    simpa only [h8_3, ← BitVec.sub_eq_add_neg] using hh
  have k9 : (Operand.reg 10#5 : Operand 32).read s4 =
      (Operand.reg 10#5 : Operand 32).read s3 := he4.agrees.read (by simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR])
  have v5 : (Operand.reg 11#5 : Operand 32).read s5 =
      ((Operand.reg 8#5 : Operand 32).read s1 - 58#32) &&&
      (47#32 - (Operand.reg 8#5 : Operand 32).read s1) := by
    have hh := tail_and_value he5
    change (Operand.reg 11#5 : Operand 32).read s5 =
      (Operand.reg 11#5 : Operand 32).read s4 &&& (Operand.reg 10#5 : Operand 32).read s4 at hh
    simpa only [v4, k9, v3] using hh
  have v5w : (Operand.reg 11#5 : Operand 16).read s5 =
      (((Operand.reg 8#5 : Operand 32).read s1 - 58#32) &&&
        (47#32 - (Operand.reg 8#5 : Operand 32).read s1)).setWidth 16 := by
    have hh := congrArg (fun x : BitVec 32 => x.setWidth 16) v5
    simpa only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32)] using hh
  have v6 := tail_movsx_value he6
  change (Operand.reg 10#5 : Operand 32).read s6 =
    ((Operand.reg 11#5 : Operand 16).read s5).signExtend 32 at v6
  rw [v5w] at v6
  have v7 : (Operand.reg 10#5 : Operand 32).read s7 =
      (Operand.reg 10#5 : Operand 32).read s6 >>> 8 := by
    have hw := he7.writes
    change s7.GPR[10] = (((Operand.reg 10#5 : Operand 32).read s6) >>> 8).setWidth 64 at hw
    change s7.GPR[10].setWidth 32 = _
    rw [hw]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have k98 : (Operand.reg 10#5 : Operand 32).read s8 =
      (Operand.reg 10#5 : Operand 32).read s7 := he8.agrees.read (by simp [Effect.components, Instructions.leaR32Effect, gprNumber, rexR])
  have hmask : (Operand.reg 10#5 : Operand 32).read s8 =
      decodeRangeMask 47 58 ((Operand.reg 8#5 : Operand 32).read s8) >>> 8 := by
    rw [k98, v7, v6, h8_8]
    simp [decodeRangeMask, BitVec.and_comm]
  have hwide : (Operand.reg 11#5 : Operand 32).read s8 =
      (Operand.reg 8#5 : Operand 32).read s8 + 0xfd1 := by
    have hh := tail_lea_value he8
    change (Operand.reg 11#5 : Operand 32).read s8 =
      (AddrMode.reg64 8 s7 + (0xfd1#32).signExtend 64).extractLsb' 0 32 at hh
    rw [BitVec.extractLsb'_add (by decide)] at hh
    change (Operand.reg 11#5 : Operand 32).read s8 =
      (Operand.reg 8#5 : Operand 32).read s7 + 0xfd1 at hh
    simpa only [h8_7, h8_8] using hh
  exact ⟨s8, ha, hr8, hc8, hpt, hagree', hvalue, hmask, hwide⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
