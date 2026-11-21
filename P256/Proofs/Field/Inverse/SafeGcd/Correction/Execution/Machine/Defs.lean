import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l1181a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1126c0 (pushR64Effect 0x1126c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x1126c0 (PushPre 0x1126c0 2) (pushR64Effect 0x1126c0 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x1126c2 (pushR64Effect 0x1126c2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1126c2 (PushPre 0x1126c2 2) (pushR64Effect 0x1126c2 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1126c4 (pushR64Effect 0x1126c4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x1126c4 (PushPre 0x1126c4 2) (pushR64Effect 0x1126c4 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x1126c6 (pushR64Effect 0x1126c6 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1126c6 (PushPre 0x1126c6 2) (pushR64Effect 0x1126c6 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1126c8 (pushR64Effect 0x1126c8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x1126c8 (PushPre 0x1126c8 1) (pushR64Effect 0x1126c8 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x1126c9 (subR64Imm8Effect 0x1126c9 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x1126c9 (fun s => s.RIP = 0x1126c9) (subR64Imm8Effect 0x1126c9 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.br ⟨.l1181ad, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 65⟩)))))))))))))

def bytes_l1181a0 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10]

theorem code_l1181a0 : ∀ x ∈ codeRange 0x1126c0 bytes_l1181a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x126c0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1181ad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1126cd (movR64M64Effect 0x1126cd 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 54) (.exec 0x1126cd (LoadPre 0x1126cd (fun s => AddrMode.addr (.base 6 .none) s (0x1126cd + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1126cd 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1126d0 (movR64M64Effect 0x1126d0 9 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 56) (.exec 0x1126d0 (LoadPre 0x1126d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1126d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d0 9 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1126d4 (movR64M64Effect 0x1126d4 8 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 58) (.exec 0x1126d4 (LoadPre 0x1126d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1126d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d4 8 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1126d8 (movR64M64Effect 0x1126d8 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 60) (.exec 0x1126d8 (LoadPre 0x1126d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1126d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1126d8 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1126dc (movR64M64Effect 0x1126dc 3 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 62) (.exec 0x1126dc (LoadPre 0x1126dc (fun s => AddrMode.addr (.base 1 .none) s (0x1126dc + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1126dc 3 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 63) (.out 0x1126df (movR64R64Effect 0x1126df 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 64) (.exec 0x1126df (fun s => s.RIP = 0x1126df) (movR64R64Effect 0x1126df 11 3) (Reg.operands [.gpr 3] [])) #v[61]
    (.letOp (n := 65) (.out 0x1126e2 (subR64R64Effect 0x1126e2 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[63, 53]
    (.letOp (n := 66) (.exec 0x1126e2 (fun s => s.RIP = 0x1126e2) (subR64R64Effect 0x1126e2 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[63, 53]
    (.letOp (n := 67) (.out 0x1126e5 (notR64Effect 0x1126e5 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[61]
    (.letOp (n := 68) (.exec 0x1126e5 (fun s => s.RIP = 0x1126e5) (notR64Effect 0x1126e5 3) (Reg.operands [.gpr 3] [])) #v[61]
    (.letOp (n := 69) (.out 0x1126e8 (movR64R64Effect 0x1126e8 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[53]
    (.letOp (n := 70) (.exec 0x1126e8 (fun s => s.RIP = 0x1126e8) (movR64R64Effect 0x1126e8 14 10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 71) (.out 0x1126eb (andR64R64Effect 0x1126eb 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x1126eb (fun s => s.RIP = 0x1126eb) (andR64R64Effect 0x1126eb 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[69, 67]
    (.letOp (n := 73) (.out 0x1126ee (orR64R64Effect 0x1126ee 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[67, 53]
    (.letOp (n := 74) (.exec 0x1126ee (fun s => s.RIP = 0x1126ee) (orR64R64Effect 0x1126ee 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[67, 53]
    (.letOp (n := 75) (.out 0x1126f1 (andR64R64Effect 0x1126f1 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[73, 65]
    (.letOp (n := 76) (.exec 0x1126f1 (fun s => s.RIP = 0x1126f1) (andR64R64Effect 0x1126f1 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[73, 65]
    (.letOp (n := 77) (.out 0x1126f4 (orR64R64Effect 0x1126f4 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x1126f4 (fun s => s.RIP = 0x1126f4) (orR64R64Effect 0x1126f4 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x1126f7 (shrR64Effect 0x1126f7 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[77]
    (.letOp (n := 80) (.exec 0x1126f7 (fun s => s.RIP = 0x1126f7) (shrR64Effect 0x1126f7 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x1126fb (xorR8M8Effect 0x1126fb 3 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 6]
    (.letOp (n := 82) (.exec 0x1126fb (LoadPre 0x1126fb (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1126fb + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x1126fb 3 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 83) (.exec 0x1126fe (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1126fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1126fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1126fe 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[79, 4]
    (.terminate (.br ⟨.l1181e3, RegMap.args [(0, 59), (1, 1), (2, 81), (3, 79), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 55), (10, 53), (11, 65), (14, 71), (22, 22), (39, 39), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l1181ad : List UInt8 :=
  [0x4C, 0x8B, 0x16, 0x4C, 0x8B, 0x4E, 0x08, 0x4C, 0x8B, 0x46, 0x10, 0x48, 0x8B, 0x46, 0x18, 0x48,
    0x8B, 0x19, 0x49, 0x89, 0xDB, 0x4D, 0x29, 0xD3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD6, 0x49, 0x21,
    0xDE, 0x4C, 0x09, 0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xF3, 0x48, 0xC1, 0xEB, 0x3F, 0x32, 0x56,
    0x20, 0x48, 0x89, 0x5C, 0x24, 0x08]

theorem code_l1181ad : ∀ x ∈ codeRange 0x1126cd bytes_l1181ad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x126cd 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1181e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112703 (fun s => s.RIP = 0x112703) (leaR64Effect 0x112703 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x112708 (xorR32R32Effect 0x112708 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 55) (.exec 0x112708 (fun s => s.RIP = 0x112708) (xorR32R32Effect 0x112708 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 56) (.out 0x11270b (xorR32R32Effect 0x11270b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 57) (.exec 0x11270b (fun s => s.RIP = 0x11270b) (xorR32R32Effect 0x11270b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 58) (.out 0x11270d (subR64M64Effect 0x11270d 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[56, 4]
    (.letOp (n := 59) (.exec 0x11270d (LoadPre 0x11270d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11270d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11270d 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x112712 (movR64M64Effect 0x112712 3 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 61) (.exec 0x112712 (LoadPre 0x112712 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x112712 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112712 3 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 62) (.out 0x112716 (movR64R64Effect 0x112716 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[60]
    (.letOp (n := 63) (.exec 0x112716 (fun s => s.RIP = 0x112716) (movR64R64Effect 0x112716 15 3) (Reg.operands [.gpr 3] [])) #v[60]
    (.letOp (n := 64) (.out 0x112719 (subR64R64Effect 0x112719 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[62, 9]
    (.letOp (n := 65) (.exec 0x112719 (fun s => s.RIP = 0x112719) (subR64R64Effect 0x112719 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[62, 9]
    (.letOp (n := 66) (.out 0x11271c (sarR64Effect 0x11271c 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[58]
    (.letOp (n := 67) (.exec 0x11271c (fun s => s.RIP = 0x11271c) (sarR64Effect 0x11271c 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 68) (.out 0x112720 (addR64R64Effect 0x112720 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[66, 64]
    (.letOp (n := 69) (.exec 0x112720 (fun s => s.RIP = 0x112720) (addR64R64Effect 0x112720 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[66, 64]
    (.letOp (n := 70) (.out 0x112723 (notR64Effect 0x112723 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 71) (.exec 0x112723 (fun s => s.RIP = 0x112723) (notR64Effect 0x112723 3) (Reg.operands [.gpr 3] [])) #v[60]
    (.letOp (n := 72) (.out 0x112726 (movR64R64Effect 0x112726 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[9]
    (.letOp (n := 73) (.exec 0x112726 (fun s => s.RIP = 0x112726) (movR64R64Effect 0x112726 15 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 74) (.out 0x112729 (andR64R64Effect 0x112729 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x112729 (fun s => s.RIP = 0x112729) (andR64R64Effect 0x112729 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x11272c (orR64R64Effect 0x11272c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[70, 9]
    (.letOp (n := 77) (.exec 0x11272c (fun s => s.RIP = 0x11272c) (orR64R64Effect 0x11272c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[70, 9]
    (.letOp (n := 78) (.out 0x11272f (andR64R64Effect 0x11272f 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[76, 68]
    (.letOp (n := 79) (.exec 0x11272f (fun s => s.RIP = 0x11272f) (andR64R64Effect 0x11272f 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[76, 68]
    (.letOp (n := 80) (.out 0x112732 (orR64R64Effect 0x112732 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[78, 74]
    (.letOp (n := 81) (.exec 0x112732 (fun s => s.RIP = 0x112732) (orR64R64Effect 0x112732 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[78, 74]
    (.letOp (n := 82) (.out 0x112735 (shrR64Effect 0x112735 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[80]
    (.letOp (n := 83) (.exec 0x112735 (fun s => s.RIP = 0x112735) (shrR64Effect 0x112735 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.letOp (n := 84) (.exec 0x112739 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112739 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112739 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112739 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[82, 4]
    (.terminate (.br ⟨.l11821e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 82), (4, 4), (5, 5), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 54), (15, 74), (22, 22), (39, 39), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l1181e3 : List UInt8 :=
  [0x4C, 0x8D, 0x64, 0x24, 0x08, 0x45, 0x31, 0xF6, 0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x08, 0x48,
    0x8B, 0x59, 0x08, 0x49, 0x89, 0xDF, 0x4D, 0x29, 0xCF, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE,
    0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xCF, 0x49, 0x21, 0xDF, 0x4C, 0x09, 0xCB, 0x48, 0x21, 0xF3, 0x4C,
    0x09, 0xFB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89, 0x5C, 0x24, 0x08]

theorem code_l1181e3 : ∀ x ∈ codeRange 0x112703 bytes_l1181e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12703 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11821e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11273e (xorR32R32Effect 0x11273e 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 54) (.exec 0x11273e (fun s => s.RIP = 0x11273e) (xorR32R32Effect 0x11273e 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.out 0x112740 (subR64M64Effect 0x112740 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x112740 (LoadPre 0x112740 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112740 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x112740 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x112745 (movR64M64Effect 0x112745 15 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 58) (.exec 0x112745 (LoadPre 0x112745 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x112745 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112745 15 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 59) (.out 0x112749 (movR64R64Effect 0x112749 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x112749 (fun s => s.RIP = 0x112749) (movR64R64Effect 0x112749 13 15) (Reg.operands [.gpr 15] [])) #v[57]
    (.letOp (n := 61) (.out 0x11274c (subR64R64Effect 0x11274c 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[59, 8]
    (.letOp (n := 62) (.exec 0x11274c (fun s => s.RIP = 0x11274c) (subR64R64Effect 0x11274c 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[59, 8]
    (.letOp (n := 63) (.out 0x11274f (sarR64Effect 0x11274f 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 64) (.exec 0x11274f (fun s => s.RIP = 0x11274f) (sarR64Effect 0x11274f 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 65) (.out 0x112753 (addR64R64Effect 0x112753 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x112753 (fun s => s.RIP = 0x112753) (addR64R64Effect 0x112753 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x112756 (notR64Effect 0x112756 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[57]
    (.letOp (n := 68) (.exec 0x112756 (fun s => s.RIP = 0x112756) (notR64Effect 0x112756 15) (Reg.operands [.gpr 15] [])) #v[57]
    (.letOp (n := 69) (.out 0x112759 (movR64R64Effect 0x112759 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[8]
    (.letOp (n := 70) (.exec 0x112759 (fun s => s.RIP = 0x112759) (movR64R64Effect 0x112759 13 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x11275c (andR64R64Effect 0x11275c 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x11275c (fun s => s.RIP = 0x11275c) (andR64R64Effect 0x11275c 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[69, 67]
    (.letOp (n := 73) (.out 0x11275f (orR64R64Effect 0x11275f 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[67, 8]
    (.letOp (n := 74) (.exec 0x11275f (fun s => s.RIP = 0x11275f) (orR64R64Effect 0x11275f 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[67, 8]
    (.letOp (n := 75) (.out 0x112762 (andR64R64Effect 0x112762 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[73, 65]
    (.letOp (n := 76) (.exec 0x112762 (fun s => s.RIP = 0x112762) (andR64R64Effect 0x112762 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[73, 65]
    (.letOp (n := 77) (.out 0x112765 (orR64R64Effect 0x112765 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x112765 (fun s => s.RIP = 0x112765) (orR64R64Effect 0x112765 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x112768 (shrR64Effect 0x112768 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[77]
    (.letOp (n := 80) (.exec 0x112768 (fun s => s.RIP = 0x112768) (shrR64Effect 0x112768 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x11276c (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11276c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11276c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11276c 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[79, 4]
    (.terminate (.br ⟨.l118251, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 71), (14, 14), (15, 79), (22, 22), (39, 39), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l11821e : List UInt8 :=
  [0x31, 0xDB, 0x48, 0x2B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x79, 0x10, 0x4D, 0x89, 0xFD, 0x4D, 0x29,
    0xC5, 0x48, 0xC1, 0xFB, 0x3F, 0x4C, 0x01, 0xEB, 0x49, 0xF7, 0xD7, 0x4D, 0x89, 0xC5, 0x4D, 0x21,
    0xFD, 0x4D, 0x09, 0xC7, 0x49, 0x21, 0xDF, 0x4D, 0x09, 0xEF, 0x49, 0xC1, 0xEF, 0x3F, 0x4C, 0x89,
    0x7C, 0x24, 0x08]

theorem code_l11821e : ∀ x ∈ codeRange 0x11273e bytes_l11821e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1273e 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118251 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112771 (movR64M64Effect 0x112771 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x112771 (LoadPre 0x112771 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112771 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112771 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112776 (xorR32R32Effect 0x112776 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 56) (.exec 0x112776 (fun s => s.RIP = 0x112776) (xorR32R32Effect 0x112776 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 57) (.out 0x112779 (subR64R64Effect 0x112779 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x112779 (fun s => s.RIP = 0x112779) (subR64R64Effect 0x112779 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x11277c (movR64M64Effect 0x11277c 1 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 60) (.exec 0x11277c (LoadPre 0x11277c (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x11277c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11277c 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 61) (.out 0x112780 (movR64R64Effect 0x112780 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.exec 0x112780 (fun s => s.RIP = 0x112780) (movR64R64Effect 0x112780 13 1) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 63) (.out 0x112783 (subR64R64Effect 0x112783 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[61, 0]
    (.letOp (n := 64) (.exec 0x112783 (fun s => s.RIP = 0x112783) (subR64R64Effect 0x112783 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[61, 0]
    (.letOp (n := 65) (.out 0x112786 (sarR64Effect 0x112786 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[57]
    (.letOp (n := 66) (.exec 0x112786 (fun s => s.RIP = 0x112786) (sarR64Effect 0x112786 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x11278a (addR64R64Effect 0x11278a 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x11278a (fun s => s.RIP = 0x11278a) (addR64R64Effect 0x11278a 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x11278d (notR64Effect 0x11278d 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 70) (.exec 0x11278d (fun s => s.RIP = 0x11278d) (notR64Effect 0x11278d 1) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 71) (.out 0x112790 (movR64R64Effect 0x112790 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[0]
    (.letOp (n := 72) (.exec 0x112790 (fun s => s.RIP = 0x112790) (movR64R64Effect 0x112790 13 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 73) (.out 0x112793 (andR64R64Effect 0x112793 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x112793 (fun s => s.RIP = 0x112793) (andR64R64Effect 0x112793 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x112796 (orR64R64Effect 0x112796 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[69, 0]
    (.letOp (n := 76) (.exec 0x112796 (fun s => s.RIP = 0x112796) (orR64R64Effect 0x112796 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[69, 0]
    (.letOp (n := 77) (.out 0x112799 (andR64R64Effect 0x112799 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[75, 67]
    (.letOp (n := 78) (.exec 0x112799 (fun s => s.RIP = 0x112799) (andR64R64Effect 0x112799 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[75, 67]
    (.letOp (n := 79) (.out 0x11279c (orR64R64Effect 0x11279c 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x11279c (fun s => s.RIP = 0x11279c) (orR64R64Effect 0x11279c 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x11279f (shrR64Effect 0x11279f 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x11279f (fun s => s.RIP = 0x11279f) (shrR64Effect 0x11279f 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x1127a3 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1127a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1127a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1127a3 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 4]
    (.terminate (.br ⟨.l118288, RegMap.args [(0, 0), (1, 81), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 73), (14, 14), (15, 67), (22, 22), (39, 39), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l118251 : List UInt8 :=
  [0x4C, 0x8B, 0x6C, 0x24, 0x08, 0x45, 0x31, 0xFF, 0x4D, 0x29, 0xEF, 0x48, 0x8B, 0x49, 0x18, 0x49,
    0x89, 0xCD, 0x49, 0x29, 0xC5, 0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x01, 0xEF, 0x48, 0xF7, 0xD1, 0x49,
    0x89, 0xC5, 0x49, 0x21, 0xCD, 0x48, 0x09, 0xC1, 0x4C, 0x21, 0xF9, 0x4C, 0x09, 0xE9, 0x48, 0xC1,
    0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08]

theorem code_l118251 : ∀ x ∈ codeRange 0x112771 bytes_l118251, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12771 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118288 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1127a8 (movR64R64Effect 0x1127a8 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[9]
    (.letOp (n := 54) (.exec 0x1127a8 (fun s => s.RIP = 0x1127a8) (movR64R64Effect 0x1127a8 1 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1127ab (orR64R64Effect 0x1127ab 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[53, 10]
    (.letOp (n := 56) (.exec 0x1127ab (fun s => s.RIP = 0x1127ab) (orR64R64Effect 0x1127ab 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[53, 10]
    (.letOp (n := 57) (.out 0x1127ae (orR64R64Effect 0x1127ae 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[55, 8]
    (.letOp (n := 58) (.exec 0x1127ae (fun s => s.RIP = 0x1127ae) (orR64R64Effect 0x1127ae 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[55, 8]
    (.letOp (n := 59) (.out 0x1127b1 (andR8Imm8Effect 0x1127b1 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x1127b1 (fun s => s.RIP = 0x1127b1) (andR8Imm8Effect 0x1127b1 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x1127b4 (orR64R64Effect 0x1127b4 1 0) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 0] []) (.flag .ZF)) #v[57, 0]
    (.letOp (n := 62) (.exec 0x1127b4 (fun s => s.RIP = 0x1127b4) (orR64R64Effect 0x1127b4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 0]
    (.letOp (n := 63) (.out 0x1127b7 (movzxR32R8Effect 0x1127b7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 64) (.exec 0x1127b7 (fun s => s.RIP = 0x1127b7) (movzxR32R8Effect 0x1127b7 3 2 2) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 65) (.out 0x1127ba (atFlags (condHolds 4) (cmovR32R32Effect 0x1127ba 4 2 14)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[63, 14, 61]
    (.letOp (n := 66) (.exec 0x1127ba (fun s => s.RIP = 0x1127ba) (atFlags (condHolds 4) (cmovR32R32Effect 0x1127ba 4 2 14)) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 14, 61]
    (.letOp (n := 67) (.exec 0x1127be (StorePre 0x1127be 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127be + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127be 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x1127c2 (fun s => s.RIP = 0x1127c2) (leaR64Effect 0x1127c2 14 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1182a7, RegMap.args [(0, 0), (2, 65), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 61), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l118288 : List UInt8 :=
  [0x4C, 0x89, 0xC9, 0x4C, 0x09, 0xD1, 0x4C, 0x09, 0xC1, 0x80, 0xE2, 0x01, 0x48, 0x09, 0xC1, 0x0F,
    0xB6, 0xD2, 0x41, 0x0F, 0x44, 0xD6, 0x88, 0x54, 0x24, 0x07, 0x4C, 0x8D, 0x74, 0x24, 0x07]

theorem code_l118288 : ∀ x ∈ codeRange 0x1127a8 bytes_l118288, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x127a8 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1182a7_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x11280f (negR64Effect 0x11280f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[86]
    (.letOp (n := 91) (.exec 0x11280f (fun s => s.RIP = 0x11280f) (negR64Effect 0x11280f 2) (Reg.operands [.gpr 2] [])) #v[86]
    (.letOp (n := 92) (.out 0x112812 (andR64R64Effect 0x112812 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[90, 88]
    (.letOp (n := 93) (.exec 0x112812 (fun s => s.RIP = 0x112812) (andR64R64Effect 0x112812 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[90, 88]
    (.letOp (n := 94) (.out 0x112815 (xorR64R64Effect 0x112815 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[92, 0]
    (.letOp (n := 95) (.exec 0x112815 (fun s => s.RIP = 0x112815) (xorR64R64Effect 0x112815 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[92, 0]
    (.terminate (.br ⟨.l1182f8, RegMap.args [(0, 0), (1, 61), (2, 94), (3, 77), (4, 4), (5, 5), (6, 83), (7, 7), (8, 8), (9, 9), (10, 72), (11, 55), (15, 88), (22, 22), (39, 39), (51, 51)] 96⟩)))))))

def bytes_l1182a7_1 : List UInt8 :=
  [0x48, 0xF7, 0xDA, 0x4C, 0x21, 0xFA, 0x48, 0x31, 0xC2]

theorem code_l1182a7_1 : ∀ x ∈ codeRange 0x11280f bytes_l1182a7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1280f 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1182a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1127c7 (movzxR32M8Effect 0x1127c7 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1127c7 (LoadPre 0x1127c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127c7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1127c7 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1127cc (xorR64R64Effect 0x1127cc 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[11, 10]
    (.letOp (n := 56) (.exec 0x1127cc (fun s => s.RIP = 0x1127cc) (xorR64R64Effect 0x1127cc 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 10]
    (.letOp (n := 57) (.out 0x1127cf (negR64Effect 0x1127cf 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 58) (.exec 0x1127cf (fun s => s.RIP = 0x1127cf) (negR64Effect 0x1127cf 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.out 0x1127d2 (andR64R64Effect 0x1127d2 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x1127d2 (fun s => s.RIP = 0x1127d2) (andR64R64Effect 0x1127d2 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x1127d5 (xorR64R64Effect 0x1127d5 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[59, 10]
    (.letOp (n := 62) (.exec 0x1127d5 (fun s => s.RIP = 0x1127d5) (xorR64R64Effect 0x1127d5 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[59, 10]
    (.letOp (n := 63) (.exec 0x1127d8 (StorePre 0x1127d8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127d8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127d8 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 64) (.out 0x1127dc (movzxR32M8Effect 0x1127dc 6 10 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 65) (.exec 0x1127dc (LoadPre 0x1127dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127dc + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1127dc 6 10 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1127e2 (xorR64R64Effect 0x1127e2 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[6, 9]
    (.letOp (n := 67) (.exec 0x1127e2 (fun s => s.RIP = 0x1127e2) (xorR64R64Effect 0x1127e2 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 9]
    (.letOp (n := 68) (.out 0x1127e5 (negR64Effect 0x1127e5 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[64]
    (.letOp (n := 69) (.exec 0x1127e5 (fun s => s.RIP = 0x1127e5) (negR64Effect 0x1127e5 10) (Reg.operands [.gpr 10] [])) #v[64]
    (.letOp (n := 70) (.out 0x1127e8 (andR64R64Effect 0x1127e8 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[68, 66]
    (.letOp (n := 71) (.exec 0x1127e8 (fun s => s.RIP = 0x1127e8) (andR64R64Effect 0x1127e8 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[68, 66]
    (.letOp (n := 72) (.out 0x1127eb (xorR64R64Effect 0x1127eb 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[70, 9]
    (.letOp (n := 73) (.exec 0x1127eb (fun s => s.RIP = 0x1127eb) (xorR64R64Effect 0x1127eb 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[70, 9]
    (.letOp (n := 74) (.exec 0x1127ee (StorePre 0x1127ee 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127ee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1127ee 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 75) (.out 0x1127f2 (movzxR32M8Effect 0x1127f2 5 6 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 76) (.exec 0x1127f2 (LoadPre 0x1127f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1127f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1127f2 5 6 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1127f7 (xorR64R64Effect 0x1127f7 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[3, 8]
    (.letOp (n := 78) (.exec 0x1127f7 (fun s => s.RIP = 0x1127f7) (xorR64R64Effect 0x1127f7 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[3, 8]
    (.letOp (n := 79) (.out 0x1127fa (negR64Effect 0x1127fa 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[75]
    (.letOp (n := 80) (.exec 0x1127fa (fun s => s.RIP = 0x1127fa) (negR64Effect 0x1127fa 6) (Reg.operands [.gpr 6] [])) #v[75]
    (.letOp (n := 81) (.out 0x1127fd (andR64R64Effect 0x1127fd 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x1127fd (fun s => s.RIP = 0x1127fd) (andR64R64Effect 0x1127fd 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x112800 (xorR64R64Effect 0x112800 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[81, 8]
    (.letOp (n := 84) (.exec 0x112800 (fun s => s.RIP = 0x112800) (xorR64R64Effect 0x112800 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[81, 8]
    (.letOp (n := 85) (.exec 0x112803 (StorePre 0x112803 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112803 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x112803 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 86) (.out 0x112807 (movzxR32M8Effect 0x112807 5 2 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 87) (.exec 0x112807 (LoadPre 0x112807 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x112807 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112807 5 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.out 0x11280c (xorR64R64Effect 0x11280c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 0]
    (.letOp (n := 89) (.exec 0x11280c (fun s => s.RIP = 0x11280c) (xorR64R64Effect 0x11280c 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 0]
    (b_l1182a7_1)))))))))))))))))))))))))))))))))))))

def bytes_l1182a7 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x07, 0x4D, 0x31, 0xD3, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x4C, 0x31,
    0xD1, 0x88, 0x54, 0x24, 0x07, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x4C, 0x31, 0xCE, 0x49, 0xF7,
    0xDA, 0x49, 0x21, 0xF2, 0x4D, 0x31, 0xCA, 0x88, 0x54, 0x24, 0x07, 0x0F, 0xB6, 0x74, 0x24, 0x07,
    0x4C, 0x31, 0xC3, 0x48, 0xF7, 0xDE, 0x48, 0x21, 0xDE, 0x4C, 0x31, 0xC6, 0x88, 0x54, 0x24, 0x07,
    0x0F, 0xB6, 0x54, 0x24, 0x07, 0x49, 0x31, 0xC7] ++ bytes_l1182a7_1

theorem code_l1182a7 : ∀ x ∈ codeRange 0x1127c7 bytes_l1182a7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x127c7 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1182a7_1

@[cfg_block] def b_l1182f8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112818 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112818 3 (fun s => AddrMode.addr (.base 7 .none) s (0x112818 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x112818 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 7]
    (.letOp (n := 54) (.exec 0x11281b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11281b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x11281b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11281b 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 7]
    (.letOp (n := 55) (.exec 0x11281f (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11281f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x11281f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11281f 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 7]
    (.letOp (n := 56) (.exec 0x112823 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112823 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x112823 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112823 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[2, 7]
    (.letOp (n := 57) (.out 0x112827 (addR64Imm8Effect 0x112827 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x112827 (fun s => s.RIP = 0x112827) (addR64Imm8Effect 0x112827 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11282b (popR64Effect 0x11282b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.out 0x11282b (popR64Effect 0x11282b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x11282b (PopPre 0x11282b) (popR64Effect 0x11282b 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x11282c (popR64Effect 0x11282c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[60]
    (.letOp (n := 63) (.out 0x11282c (popR64Effect 0x11282c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x11282c (PopPre 0x11282c) (popR64Effect 0x11282c 2 12) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x11282e (popR64Effect 0x11282e 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 66) (.out 0x11282e (popR64Effect 0x11282e 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x11282e (PopPre 0x11282e) (popR64Effect 0x11282e 2 13) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x112830 (popR64Effect 0x112830 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[66]
    (.letOp (n := 69) (.out 0x112830 (popR64Effect 0x112830 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x112830 (PopPre 0x112830) (popR64Effect 0x112830 2 14) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x112832 (popR64Effect 0x112832 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 72) (.out 0x112832 (popR64Effect 0x112832 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x112832 (PopPre 0x112832) (popR64Effect 0x112832 2 15) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x112834 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[72]
    (.letOp (n := 75) (.out 0x112834 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x112834 (RetPre 0x112834) (retEffect) (Reg.operands [.gpr 4] [])) #v[72]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 75), (5, 5), (6, 6), (7, 7), (10, 10), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (51, 51)] 77) (some ⟨74, by decide⟩))))))))))))))))))))))))))

def bytes_l1182f8 : List UInt8 :=
  [0x48, 0x89, 0x0F, 0x4C, 0x89, 0x57, 0x08, 0x48, 0x89, 0x77, 0x10, 0x48, 0x89, 0x57, 0x18, 0x48,
    0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l1182f8 : ∀ x ∈ codeRange 0x112818 bytes_l1182f8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12818 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
