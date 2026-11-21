import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l116d00 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111220

def bytes_l116d00 : List UInt8 := [0x55]

theorem code_l116d00 : ∀ x ∈ codeRange 0x111220 bytes_l116d00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11220 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1115d0 (pushR64Effect 0x1115d0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1115d0 (PushPre 0x1115d0 1) (pushR64Effect 0x1115d0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1115d1 (pushR64Effect 0x1115d1 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1115d1 (PushPre 0x1115d1 2) (pushR64Effect 0x1115d1 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1115d3 (pushR64Effect 0x1115d3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x1115d3 (PushPre 0x1115d3 1) (pushR64Effect 0x1115d3 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x1115d4 (subR64Imm8Effect 0x1115d4 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x1115d4 (fun s => s.RIP = 0x1115d4) (subR64Imm8Effect 0x1115d4 4 0x30) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x1115d8 (movR32R32Effect 0x1115d8 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 62) (.exec 0x1115d8 (fun s => s.RIP = 0x1115d8) (movR32R32Effect 0x1115d8 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 63) (.out 0x1115db (movR64R64Effect 0x1115db 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x1115db (fun s => s.RIP = 0x1115db) (movR64R64Effect 0x1115db 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x1115de (movR64R64Effect 0x1115de 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x1115de (fun s => s.RIP = 0x1115de) (movR64R64Effect 0x1115de 7 4) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x1115e1 (callEffect (fun _ => 0x111220) 0x1115e6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 68) (.exec 0x1115e1 (PushPre 0x1115e1 5) (callEffect (fun _ => 0x111220) 0x1115e6) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 69) (.const ⟨64, 0x1115e6⟩) #v[]
    (.terminate (.call ⟨.l116d00, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 63), (4, 67), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩ { target := .l1170c6, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l1170b0 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x44, 0x89, 0xCD, 0x48, 0x89, 0xFB, 0x48, 0x89,
    0xE7, 0xE8, 0x3A, 0xFC, 0xFF, 0xFF]

theorem code_l1170b0 : ∀ x ∈ codeRange 0x1115d0 bytes_l1170b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115d0 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170c6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1115e6 (movR32Imm32Effect 0x1115e6 5 0 0x40) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1115e6 (fun s => s.RIP = 0x1115e6) (movR32Imm32Effect 0x1115e6 5 0 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1115eb (subR32R32Effect 0x1115eb 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 56) (.exec 0x1115eb (fun s => s.RIP = 0x1115eb) (subR32R32Effect 0x1115eb 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 57) (.out 0x1115ed (cmpR32Imm8Effect 0x1115ed 3 0 0x40) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.exec 0x1115ed (fun s => s.RIP = 0x1115ed) (cmpR32Imm8Effect 0x1115ed 3 0 0x40) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l117172, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (51, 51)] 60⟩ ⟨.l1170d6, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (51, 51)] 60⟩))))))))

def bytes_l1170c6 : List UInt8 :=
  [0xB8, 0x40, 0x00, 0x00, 0x00, 0x29, 0xE8, 0x83, 0xF8, 0x40, 0x0F, 0x83, 0x9C, 0x00, 0x00, 0x00]

theorem code_l1170c6 : ∀ x ∈ codeRange 0x1115e6 bytes_l1170c6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115e6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170d6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1115f6 (cmpR32Imm8Effect 0x1115f6 3 5 0x40) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.exec 0x1115f6 (fun s => s.RIP = 0x1115f6) (cmpR32Imm8Effect 0x1115f6 3 5 0x40) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11715a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l1170db, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l1170d6 : List UInt8 :=
  [0x83, 0xFD, 0x40, 0x73, 0x7F]

theorem code_l1170d6 : ∀ x ∈ codeRange 0x1115f6 bytes_l1170d6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115f6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1115fb (testR32R32Effect 0x1115fb 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 54) (.exec 0x1115fb (fun s => s.RIP = 0x1115fb) (testR32R32Effect 0x1115fb 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l11718a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩ ⟨.l1170e3, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (51, 51)] 56⟩))))

def bytes_l1170db : List UInt8 :=
  [0x85, 0xED, 0x0F, 0x84, 0xA7, 0x00, 0x00, 0x00]

theorem code_l1170db : ∀ x ∈ codeRange 0x1115fb bytes_l1170db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x115fb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170e3_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x111646 (movR32R32Effect 0x111646 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 94) (.exec 0x111646 (fun s => s.RIP = 0x111646) (movR32R32Effect 0x111646 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 95) (.out 0x111648 (shrR64ClEffect 0x111648 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[91, 93]
    (.letOp (n := 96) (.exec 0x111648 (fun s => s.RIP = 0x111648) (shrR64ClEffect 0x111648 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 93]
    (.letOp (n := 97) (.out 0x11164b (movR32R32Effect 0x11164b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 98) (.exec 0x11164b (fun s => s.RIP = 0x11164b) (movR32R32Effect 0x11164b 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 99) (.out 0x11164d (shlR64ClEffect 0x11164d 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[55, 97]
    (.letOp (n := 100) (.exec 0x11164d (fun s => s.RIP = 0x11164d) (shlR64ClEffect 0x11164d 3 6) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55, 97]
    (.letOp (n := 101) (.out 0x111650 (movR32R32Effect 0x111650 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 102) (.exec 0x111650 (fun s => s.RIP = 0x111650) (movR32R32Effect 0x111650 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 103) (.out 0x111652 (shrR64ClEffect 0x111652 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53, 101]
    (.letOp (n := 104) (.exec 0x111652 (fun s => s.RIP = 0x111652) (shrR64ClEffect 0x111652 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 101]
    (.letOp (n := 105) (.out 0x111655 (orR64R64Effect 0x111655 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[85, 75]
    (.letOp (n := 106) (.exec 0x111655 (fun s => s.RIP = 0x111655) (orR64R64Effect 0x111655 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[85, 75]
    (.letOp (n := 107) (.out 0x111658 (orR64R64Effect 0x111658 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[95, 89]
    (.letOp (n := 108) (.exec 0x111658 (fun s => s.RIP = 0x111658) (orR64R64Effect 0x111658 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[95, 89]
    (.letOp (n := 109) (.out 0x11165b (orR64R64Effect 0x11165b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[103, 99]
    (.letOp (n := 110) (.exec 0x11165b (fun s => s.RIP = 0x11165b) (orR64R64Effect 0x11165b 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[103, 99]
    (.letOp (n := 111) (.exec 0x11165e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11165e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x11165e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11165e 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[109, 3]
    (.letOp (n := 112) (.exec 0x111661 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111661 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x111661 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111661 14 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[107, 3]
    (.letOp (n := 113) (.exec 0x111665 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111665 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x111665 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111665 11 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[105, 3]
    (.letOp (n := 114) (.exec 0x111669 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x111669 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x111669 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x111669 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 115) (.exec 0x11166d (StorePre 0x11166d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x11166d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11166d 4 10 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 116) (.out 0x111671 (addR64Imm8Effect 0x111671 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 117) (.exec 0x111671 (fun s => s.RIP = 0x111671) (addR64Imm8Effect 0x111671 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x111675 (popR64Effect 0x111675 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[116]
    (.letOp (n := 119) (.out 0x111675 (popR64Effect 0x111675 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[116]
    (.letOp (n := 120) (.exec 0x111675 (PopPre 0x111675) (popR64Effect 0x111675 1 3) (Reg.operands [.gpr 4] [])) #v[116]
    (.letOp (n := 121) (.out 0x111676 (popR64Effect 0x111676 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[119]
    (.letOp (n := 122) (.out 0x111676 (popR64Effect 0x111676 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x111676 (PopPre 0x111676) (popR64Effect 0x111676 2 14) (Reg.operands [.gpr 4] [])) #v[119]
    (.letOp (n := 124) (.out 0x111678 (popR64Effect 0x111678 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[122]
    (.letOp (n := 125) (.out 0x111678 (popR64Effect 0x111678 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[122]
    (.letOp (n := 126) (.exec 0x111678 (PopPre 0x111678) (popR64Effect 0x111678 1 5) (Reg.operands [.gpr 4] [])) #v[122]
    (.letOp (n := 127) (.out 0x111679 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[125]
    (.letOp (n := 128) (.out 0x111679 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[125]
    (.letOp (n := 129) (.exec 0x111679 (RetPre 0x111679) (retEffect) (Reg.operands [.gpr 4] [])) #v[125]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (51, 51)] 130) (some ⟨127, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1170e3_1 : List UInt8 :=
  [0x89, 0xE9, 0x49, 0xD3, 0xEE, 0x89, 0xC1, 0x48, 0xD3, 0xE6, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4D,
    0x09, 0xC3, 0x49, 0x09, 0xFE, 0x48, 0x09, 0xF2, 0x48, 0x89, 0x13, 0x4C, 0x89, 0x73, 0x08, 0x4C,
    0x89, 0x5B, 0x10, 0x4C, 0x89, 0x4B, 0x18, 0x44, 0x88, 0x53, 0x20, 0x48, 0x83, 0xC4, 0x30, 0x5B,
    0x41, 0x5E, 0x5D, 0xC3]

theorem code_l1170e3_1 : ∀ x ∈ codeRange 0x111646 bytes_l1170e3_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11646 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1170e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x111603 (movR64M64Effect 0x111603 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x111603 (LoadPre 0x111603 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x111603 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x111603 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x111607 (movR64M64Effect 0x111607 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x111607 (LoadPre 0x111607 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x111607 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111607 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11160c (movR64M64Effect 0x11160c 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x11160c (LoadPre 0x11160c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11160c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11160c 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x111611 (movR64M64Effect 0x111611 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x111611 (LoadPre 0x111611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x111611 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111611 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x111616 (movR64M64Effect 0x111616 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 62) (.exec 0x111616 (LoadPre 0x111616 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x111616 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x111616 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x11161b (movR32R32Effect 0x11161b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 64) (.exec 0x11161b (fun s => s.RIP = 0x11161b) (movR32R32Effect 0x11161b 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 65) (.out 0x11161d (shlR64ClEffect 0x11161d 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[61, 63]
    (.letOp (n := 66) (.exec 0x11161d (fun s => s.RIP = 0x11161d) (shlR64ClEffect 0x11161d 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61, 63]
    (.letOp (n := 67) (.out 0x111620 (movR64R64Effect 0x111620 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[59]
    (.letOp (n := 68) (.exec 0x111620 (fun s => s.RIP = 0x111620) (movR64R64Effect 0x111620 9 8) (Reg.operands [.gpr 8] [])) #v[59]
    (.letOp (n := 69) (.out 0x111623 (movR32R32Effect 0x111623 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 70) (.exec 0x111623 (fun s => s.RIP = 0x111623) (movR32R32Effect 0x111623 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x111625 (shrR64ClEffect 0x111625 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x111625 (fun s => s.RIP = 0x111625) (shrR64ClEffect 0x111625 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 69]
    (.letOp (n := 73) (.out 0x111628 (movR32R32Effect 0x111628 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 74) (.exec 0x111628 (fun s => s.RIP = 0x111628) (movR32R32Effect 0x111628 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 75) (.out 0x11162a (shlR64ClEffect 0x11162a 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[59, 73]
    (.letOp (n := 76) (.exec 0x11162a (fun s => s.RIP = 0x11162a) (shlR64ClEffect 0x11162a 3 8) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 73]
    (.letOp (n := 77) (.out 0x11162d (movzxR32M8Effect 0x11162d 6 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x11162d (LoadPre 0x11162d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11162d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x11162d 6 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x111633 (orR64R64Effect 0x111633 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[71, 65]
    (.letOp (n := 80) (.exec 0x111633 (fun s => s.RIP = 0x111633) (orR64R64Effect 0x111633 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[71, 65]
    (.letOp (n := 81) (.out 0x111636 (movR64R64Effect 0x111636 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 82) (.exec 0x111636 (fun s => s.RIP = 0x111636) (movR64R64Effect 0x111636 11 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 83) (.out 0x111639 (movR32R32Effect 0x111639 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 84) (.exec 0x111639 (fun s => s.RIP = 0x111639) (movR32R32Effect 0x111639 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 85) (.out 0x11163b (shrR64ClEffect 0x11163b 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[81, 83]
    (.letOp (n := 86) (.exec 0x11163b (fun s => s.RIP = 0x11163b) (shrR64ClEffect 0x11163b 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81, 83]
    (.letOp (n := 87) (.out 0x11163e (movR32R32Effect 0x11163e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 88) (.exec 0x11163e (fun s => s.RIP = 0x11163e) (movR32R32Effect 0x11163e 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 89) (.out 0x111640 (shlR64ClEffect 0x111640 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57, 87]
    (.letOp (n := 90) (.exec 0x111640 (fun s => s.RIP = 0x111640) (shlR64ClEffect 0x111640 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57, 87]
    (.letOp (n := 91) (.out 0x111643 (movR64R64Effect 0x111643 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 92) (.exec 0x111643 (fun s => s.RIP = 0x111643) (movR64R64Effect 0x111643 14 6) (Reg.operands [.gpr 6] [])) #v[55]
    (b_l1170e3_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1170e3 : List UInt8 :=
  [0x48, 0x8B, 0x14, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B,
    0x44, 0x24, 0x18, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x89, 0xC1, 0x49, 0xD3, 0xE3, 0x4D, 0x89, 0xC1,
    0x89, 0xE9, 0x49, 0xD3, 0xE9, 0x89, 0xC1, 0x49, 0xD3, 0xE0, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28,
    0x4D, 0x09, 0xD9, 0x49, 0x89, 0xFB, 0x89, 0xE9, 0x49, 0xD3, 0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7,
    0x49, 0x89, 0xF6] ++ bytes_l1170e3_1

theorem code_l1170e3 : ∀ x ∈ codeRange 0x111603 bytes_l1170e3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11603 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1170e3_1

@[cfg_block] def b_l11715a : Block Op Label signature Reg.count 53 :=
  cutBlock 0x11167a

def bytes_l11715a : List UInt8 := [0xbe]

theorem code_l11715a : ∀ x ∈ codeRange 0x11167a bytes_l11715a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1167a 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l117172 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x111692

def bytes_l117172 : List UInt8 := [0xbe]

theorem code_l117172 : ∀ x ∈ codeRange 0x111692 bytes_l117172, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11692 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11718a : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1116aa

def bytes_l11718a : List UInt8 := [0xbf]

theorem code_l11718a : ∀ x ∈ codeRange 0x1116aa bytes_l11718a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x116aa 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl


end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
