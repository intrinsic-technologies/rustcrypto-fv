import K256.Proofs.Sec1.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Sec1.LIR.Generated.Footprints

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

@[cfg_block] def b_l1268a2_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.exec 0x1268f1 (StorePre 0x1268f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1268f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f1 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 84) (.exec 0x1268f5 (StorePre 0x1268f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1268f5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268f5 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1268f9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 75), (8, 77), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))

def bytes_l1268a2_1 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l1268a2_1 : ∀ x ∈ codeRange 0x1268f1 bytes_l1268a2_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x268f1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1268a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1268a2 (movR32R32Effect 0x1268a2 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x1268a2 (fun s => s.RIP = 0x1268a2) (movR32R32Effect 0x1268a2 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1268a4 (orR64R64Effect 0x1268a4 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x1268a4 (fun s => s.RIP = 0x1268a4) (orR64R64Effect 0x1268a4 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x1268a7 (movR32M32LowEffect 0x1268a7 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1268a7 (LoadPre 0x1268a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1268a7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268a7 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1268ab (StorePre 0x1268ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268ab + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1268ab 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x1268af (movR64M64Effect 0x1268af 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x1268af (LoadPre 0x1268af (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1268af + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268af 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1268b4 (movR64M64Effect 0x1268b4 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 63) (.exec 0x1268b4 (LoadPre 0x1268b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1268b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268b4 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1268b9 (StorePre 0x1268b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268b9 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1268be (StorePre 0x1268be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1268be 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 66) (.out 0x1268c3 (movR32M32LowEffect 0x1268c3 7 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1268c3 (LoadPre 0x1268c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1268c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268c3 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1268c7 (StorePre 0x1268c7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x34)) s (0x1268c7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268c7 7 (.base 3 (.d8 0x34))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.out 0x1268ca (movR64M64Effect 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1268ca (LoadPre 0x1268ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1268ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268ca 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1268cf (StorePre 0x1268cf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x2c)) s (0x1268cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268cf 7 (.base 3 (.d8 0x2c))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 72) (.out 0x1268d3 (movR32M32LowEffect 0x1268d3 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x1268d3 (LoadPre 0x1268d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1268d3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1268d3 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1268d7 (StorePre 0x1268d7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1268d7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268d7 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 75) (.out 0x1268da (movR64M64Effect 0x1268da 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x1268da (LoadPre 0x1268da (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1268da + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268da 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1268df (movR64M64Effect 0x1268df 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 78) (.exec 0x1268df (LoadPre 0x1268df (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1268df + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1268df 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x1268e4 (StorePre 0x1268e4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1268e4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e4 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 80) (.exec 0x1268e8 (StorePre 0x1268e8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1268e8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1268e8 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 81) (.exec 0x1268ec (StorePre 0x1268ec 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1268ec + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1268ec 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 82) (.exec 0x1268ee (StorePre 0x1268ee 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1268ee + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1268ee 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (b_l1268a2_1))))))))))))))))))))))))))))))

def bytes_l1268a2 : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x8B, 0x7C, 0x24, 0x18, 0x89, 0x7C, 0x24, 0x38, 0x48, 0x8B, 0x7C,
    0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24,
    0x28, 0x8B, 0x7C, 0x24, 0x24, 0x89, 0x7B, 0x34, 0x48, 0x8B, 0x7C, 0x24, 0x1C, 0x48, 0x89, 0x7B,
    0x2C, 0x8B, 0x7C, 0x24, 0x38, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x44,
    0x24, 0x30, 0x4C, 0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x13, 0x89, 0x4B, 0x04] ++ bytes_l1268a2_1

theorem code_l1268a2 : ∀ x ∈ codeRange 0x1268a2 bytes_l1268a2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x268a2 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1268a2_1

@[cfg_block] def b_l1268f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1268f9 (movR64R64Effect 0x1268f9 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1268f9 (fun s => s.RIP = 0x1268f9) (movR64R64Effect 0x1268f9 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1268fc (addR64Imm32Effect 0x1268fc 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1268fc (fun s => s.RIP = 0x1268fc) (addR64Imm32Effect 0x1268fc 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126903 (popR64Effect 0x126903 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x126903 (popR64Effect 0x126903 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x126903 (PopPre 0x126903) (popR64Effect 0x126903 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x126904 (popR64Effect 0x126904 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x126904 (popR64Effect 0x126904 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x126904 (PopPre 0x126904) (popR64Effect 0x126904 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x126906 (popR64Effect 0x126906 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x126906 (popR64Effect 0x126906 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x126906 (PopPre 0x126906) (popR64Effect 0x126906 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126908 (popR64Effect 0x126908 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126908 (popR64Effect 0x126908 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126908 (PopPre 0x126908) (popR64Effect 0x126908 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x12690a (popR64Effect 0x12690a 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x12690a (popR64Effect 0x12690a 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x12690a (PopPre 0x12690a) (popR64Effect 0x12690a 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x12690c (popR64Effect 0x12690c 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x12690c (popR64Effect 0x12690c 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x12690c (PopPre 0x12690c) (popR64Effect 0x12690c 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x12690d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x12690d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x12690d (RetPre 0x12690d) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1268f9 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1268f9 : ∀ x ∈ codeRange 0x1268f9 bytes_l1268f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x268f9 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12690e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12690e (StorePre 0x12690e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12690e + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12690e 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x126912 (leaR64Effect 0x126912 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x126912 (fun s => s.RIP = 0x126912) (leaR64Effect 0x126912 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x12691a (movR64M64Effect 0x12691a 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 57) (.exec 0x12691a (LoadPre 0x12691a (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x12691a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691a 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.out 0x12691e (movR64M64Effect 0x12691e 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 59) (.exec 0x12691e (LoadPre 0x12691e (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x12691e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12691e 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.exec 0x126922 (StorePre 0x126922 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126922 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126922 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x12692a (StorePre 0x12692a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x12692a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x12692a 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x126932 (StorePre 0x126932 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126932 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126932 14 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 63) (.out 0x12693a (leaR64Effect 0x12693a 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x12693a (fun s => s.RIP = 0x12693a) (leaR64Effect 0x12693a 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x12693f (movR64R64Effect 0x12693f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 66) (.exec 0x12693f (fun s => s.RIP = 0x12693f) (movR64R64Effect 0x12693f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x126942 (callEffect (fun _ => 0x1248c0) 0x126947) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x126942 (PushPre 0x126942 5) (callEffect (fun _ => 0x1248c0) 0x126947) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x126947⟩) #v[]
    (.terminate (.call ⟨.l1248c0, RegMap.args [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l126947, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l12690e : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x45, 0x00,
    0x49, 0x8B, 0x4D, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24,
    0x40, 0x4C, 0x89, 0xF6, 0xE8, 0x79, 0xDF, 0xFF, 0xFF]

theorem code_l12690e : ∀ x ∈ codeRange 0x12690e bytes_l12690e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2690e 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126947 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126947 (movR32M32Effect 0x126947 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x126947 (LoadPre 0x126947 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126947 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126947 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x12694b (movR32M32Effect 0x12694b 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x12694b (LoadPre 0x12694b (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x12694b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12694b 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x12694f (subR32R32Effect 0x12694f 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x12694f (fun s => s.RIP = 0x12694f) (subR32R32Effect 0x12694f 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126951 (atFlags (condHolds 6) (setccR8Effect 0x126951 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x126951 (fun s => s.RIP = 0x126951) (atFlags (condHolds 6) (setccR8Effect 0x126951 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x126954 (movR64M64Effect 0x126954 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x126954 (LoadPre 0x126954 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126954 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126954 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126959 (StorePre 0x126959 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126959 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126959 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x12695c (StorePre 0x12695c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12695c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12695c 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x126960 (StorePre 0x126960 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126960 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126960 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x126964 (movR64M64Effect 0x126964 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x126964 (LoadPre 0x126964 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126964 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126964 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x126968 (cmpR64Imm8Effect 0x126968 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x126968 (fun s => s.RIP = 0x126968) (cmpR64Imm8Effect 0x126968 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x12696c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12696c 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x12696c (fun s => s.RIP = 0x12696c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12696c 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x126970 (StorePre 0x126970 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126970 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126970 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x126974 (movR32M32LowEffect 0x126974 2 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x126974 (LoadPre 0x126974 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126974 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126974 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x126978 (cmpR32Imm8Effect 0x126978 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[75]
    (.letOp (n := 78) (.exec 0x126978 (fun s => s.RIP = 0x126978) (cmpR32Imm8Effect 0x126978 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[75]
    (.letOp (n := 79) (.out 0x12697b (atFlags (condHolds 5) (setccR8Effect 0x12697b 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 77]
    (.letOp (n := 80) (.exec 0x12697b (fun s => s.RIP = 0x12697b) (atFlags (condHolds 5) (setccR8Effect 0x12697b 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 77]
    (.letOp (n := 81) (.out 0x12697f (orR8R8Effect 0x12697f 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[79, 61]
    (.letOp (n := 82) (.out 0x12697f (orR8R8Effect 0x12697f 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 83) (.exec 0x12697f (fun s => s.RIP = 0x12697f) (orR8R8Effect 0x12697f 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[79, 61]
    (.letOp (n := 84) (.pure (condOp 4)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l126a00, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l126984, RegMap.args [(0, 61), (1, 55), (2, 75), (3, 3), (4, 4), (6, 57), (7, 81), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126947 : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x54,
    0x24, 0x78, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x49, 0x8B, 0x56,
    0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10, 0x8B, 0x54, 0x24,
    0x40, 0x83, 0xFA, 0x02, 0x40, 0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x7C]

theorem code_l126947 : ∀ x ∈ codeRange 0x126947 bytes_l126947, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26947 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126984 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126984 (movR32M32LowEffect 0x126984 1 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126984 (LoadPre 0x126984 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x126984 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126984 1 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126988 (movR64M64Effect 0x126988 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126988 (LoadPre 0x126988 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126988 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126988 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12698d (movR64M64Effect 0x12698d 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x12698d (LoadPre 0x12698d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12698d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12698d 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126992 (movR64M64Effect 0x126992 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126992 (LoadPre 0x126992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126992 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126992 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126997 (StorePre 0x126997 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126997 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126997 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x12699c (movR64M64Effect 0x12699c 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x12699c (LoadPre 0x12699c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12699c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12699c 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1269a1 (StorePre 0x1269a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269a1 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1269a6 (movR64M64Effect 0x1269a6 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x1269a6 (LoadPre 0x1269a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1269a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269a6 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1269ab (StorePre 0x1269ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269ab 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1269b0 (movR64M64Effect 0x1269b0 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x1269b0 (LoadPre 0x1269b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1269b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269b0 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1269b5 (StorePre 0x1269b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1269b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269b5 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1269ba (cmpR32Imm8Effect 0x1269ba 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x1269ba (fun s => s.RIP = 0x1269ba) (cmpR32Imm8Effect 0x1269ba 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l126866, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l1269c3, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (9, 9), (10, 10), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126984 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x44, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x50, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C,
    0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24,
    0x70, 0x48, 0x89, 0x7C, 0x24, 0x20, 0x83, 0xFA, 0x02, 0x0F, 0x85, 0xA3, 0xFE, 0xFF, 0xFF]

theorem code_l126984 : ∀ x ∈ codeRange 0x126984 bytes_l126984, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26984 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1269c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1269c3 (movR32M32LowEffect 0x1269c3 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1269c3 (LoadPre 0x1269c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1269c3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1269c3 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1269c7 (StorePre 0x1269c7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1269c7 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1269c7 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1269cb (movR64M64Effect 0x1269cb 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x1269cb (LoadPre 0x1269cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1269cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269cb 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1269d0 (movR64M64Effect 0x1269d0 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 59) (.exec 0x1269d0 (LoadPre 0x1269d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1269d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1269d0 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1269d5 (StorePre 0x1269d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1269d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269d5 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x1269da (StorePre 0x1269da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1269da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1269da 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x1269df (StorePre 0x1269df 3 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1269df + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269df 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 63) (.exec 0x1269e2 (StorePre 0x1269e2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1269e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e2 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[58, 3]
    (.letOp (n := 64) (.exec 0x1269e6 (StorePre 0x1269e6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1269e6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269e6 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 65) (.exec 0x1269ea (StorePre 0x1269ea 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1269ea + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1269ea 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 66) (.exec 0x1269ed (StorePre 0x1269ed 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1269ed + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269ed 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 67) (.exec 0x1269f1 (StorePre 0x1269f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1269f1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1269f1 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 68) (.exec 0x1269f5 (StorePre 0x1269f5 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1269f5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1269f5 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1268f9, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 56), (8, 58), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1269c3 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x18, 0x89, 0x54, 0x24, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x4C, 0x8B, 0x44,
    0x24, 0x10, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x89, 0x53, 0x28, 0x4C,
    0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x4B, 0x04, 0x48, 0x89, 0x43, 0x08, 0x48, 0x89,
    0x73, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0xF9, 0xFE, 0xFF, 0xFF]

theorem code_l1269c3 : ∀ x ∈ codeRange 0x1269c3 bytes_l1269c3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x269c3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126a00 (StorePre 0x126a00 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126a00 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126a00 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x126a05 (movR64R64Effect 0x126a05 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x126a05 (fun s => s.RIP = 0x126a05) (movR64R64Effect 0x126a05 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x126a08 (shlR64Effect 0x126a08 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x126a08 (fun s => s.RIP = 0x126a08) (shlR64Effect 0x126a08 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x126a0c (orR64Imm8Effect 0x126a0c 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x126a0c (fun s => s.RIP = 0x126a0c) (orR64Imm8Effect 0x126a0c 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x126a10 (movR32Imm32Effect 0x126a10 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x126a10 (fun s => s.RIP = 0x126a10) (movR32Imm32Effect 0x126a10 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x126a15 (xorR32R32Effect 0x126a15 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x126a15 (fun s => s.RIP = 0x126a15) (xorR32R32Effect 0x126a15 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l126a00 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x86, 0xFE, 0xFF, 0xFF]

theorem code_l126a00 : ∀ x ∈ codeRange 0x126a00 bytes_l126a00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a00 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a1c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a1c (xorR32R32Effect 0x126a1c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x126a1c (fun s => s.RIP = 0x126a1c) (xorR32R32Effect 0x126a1c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x126a1e (movR32Imm32Effect 0x126a1e 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126a1e (fun s => s.RIP = 0x126a1e) (movR32Imm32Effect 0x126a1e 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126a23 (xorR32R32Effect 0x126a23 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x126a23 (fun s => s.RIP = 0x126a23) (xorR32R32Effect 0x126a23 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1268a2, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126a1c : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x78, 0xFE, 0xFF, 0xFF]

theorem code_l126a1c : ∀ x ∈ codeRange 0x126a1c bytes_l126a1c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a1c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a30 (pushR64Effect 0x126a30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x126a30 (PushPre 0x126a30 1) (pushR64Effect 0x126a30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x126a31 (pushR64Effect 0x126a31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x126a31 (PushPre 0x126a31 2) (pushR64Effect 0x126a31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x126a33 (pushR64Effect 0x126a33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x126a33 (PushPre 0x126a33 2) (pushR64Effect 0x126a33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126a35 (pushR64Effect 0x126a35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x126a35 (PushPre 0x126a35 2) (pushR64Effect 0x126a35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x126a37 (pushR64Effect 0x126a37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x126a37 (PushPre 0x126a37 2) (pushR64Effect 0x126a37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x126a39 (pushR64Effect 0x126a39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x126a39 (PushPre 0x126a39 1) (pushR64Effect 0x126a39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x126a3a (subR64Imm32Effect 0x126a3a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x126a3a (fun s => s.RIP = 0x126a3a) (subR64Imm32Effect 0x126a3a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x126a41 (movR64R64Effect 0x126a41 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x126a41 (fun s => s.RIP = 0x126a41) (movR64R64Effect 0x126a41 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x126a44 (movR32M32Effect 0x126a44 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x126a44 (LoadPre 0x126a44 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126a44 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126a44 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x126a48 (movR32M32LowEffect 0x126a48 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x126a48 (LoadPre 0x126a48 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126a48 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126a48 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x126a4b (addR32R32Effect 0x126a4b 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x126a4b (addR32R32Effect 0x126a4b 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x126a4b (fun s => s.RIP = 0x126a4b) (addR32R32Effect 0x126a4b 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l126d10, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l126a54, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l126a30 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82,
    0xBC, 0x02, 0x00, 0x00]

theorem code_l126a30 : ∀ x ∈ codeRange 0x126a30 bytes_l126a30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a30 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a54 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a54 (movR64R64Effect 0x126a54 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x126a54 (fun s => s.RIP = 0x126a54) (movR64R64Effect 0x126a54 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x126a57 (movR64R64Effect 0x126a57 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x126a57 (fun s => s.RIP = 0x126a57) (movR64R64Effect 0x126a57 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x126a5a (movR64M64Effect 0x126a5a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x126a5a (LoadPre 0x126a5a (fun s => AddrMode.addr (.base 6 .none) s (0x126a5a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126a5a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x126a5d (movR64M64Effect 0x126a5d 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x126a5d (LoadPre 0x126a5d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a5d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x126a61 (leaR64Effect 0x126a61 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x126a61 (fun s => s.RIP = 0x126a61) (leaR64Effect 0x126a61 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126a66 (StorePre 0x126a66 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126a66 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126a66 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x126a6e (movR64R64Effect 0x126a6e 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x126a6e (fun s => s.RIP = 0x126a6e) (movR64R64Effect 0x126a6e 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x126a71 (movR32R32Effect 0x126a71 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x126a71 (fun s => s.RIP = 0x126a71) (movR32R32Effect 0x126a71 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x126a73 (callEffect (fun _ => 0x127c50) 0x126a78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x126a73 (PushPre 0x126a73 5) (callEffect (fun _ => 0x127c50) 0x126a78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x126a78⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l126a78, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l126a54 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x48, 0x48, 0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8,
    0xD8, 0x11, 0x00, 0x00]

theorem code_l126a54 : ∀ x ∈ codeRange 0x126a54 bytes_l126a54, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a54 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a78 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a78 (movR32M32LowEffect 0x126a78 2 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126a78 (LoadPre 0x126a78 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126a78 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126a78 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126a7c (cmpR32Imm8Effect 0x126a7c 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126a7c (fun s => s.RIP = 0x126a7c) (cmpR32Imm8Effect 0x126a7c 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126aa3, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126a81, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126a78 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x48, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l126a78 : ∀ x ∈ codeRange 0x126a78 bytes_l126a78, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a78 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a81 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a81 (movR64M64Effect 0x126a81 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126a81 (LoadPre 0x126a81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126a81 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a81 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126a86 (movR64M64Effect 0x126a86 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126a86 (LoadPre 0x126a86 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126a86 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126a86 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126a8b (StorePre 0x126a8b 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126a8b + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126a8b 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x126a8e (StorePre 0x126a8e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126a8e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126a8e 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126a92 (movR64M64Effect 0x126a92 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x126a92 (LoadPre 0x126a92 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126a92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126a92 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x126a96 (cmpR64Imm8Effect 0x126a96 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x126a96 (cmpR64Imm8Effect 0x126a96 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x126a96 (fun s => s.RIP = 0x126a96) (cmpR64Imm8Effect 0x126a96 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l126ae8, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l126a9c, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l126a81 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4C]

theorem code_l126a81 : ∀ x ∈ codeRange 0x126a81 bytes_l126a81, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a81 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126a9c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126a9c (movR32Imm32Effect 0x126a9c 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126a9c (fun s => s.RIP = 0x126a9c) (movR32Imm32Effect 0x126a9c 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126b08, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126a9c : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x65]

theorem code_l126a9c : ∀ x ∈ codeRange 0x126a9c bytes_l126a9c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a9c 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126aa3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126aa3 (movR32M32LowEffect 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x126aa3 (LoadPre 0x126aa3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x126aa3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126aa3 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126aa7 (movR64M64Effect 0x126aa7 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126aa7 (LoadPre 0x126aa7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126aa7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aa7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126aac (movR64M64Effect 0x126aac 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x126aac (LoadPre 0x126aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126aac 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126ab1 (movR64M64Effect 0x126ab1 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126ab1 (LoadPre 0x126ab1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126ab1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ab1 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126ab6 (StorePre 0x126ab6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126ab6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ab6 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x126abb (movR64M64Effect 0x126abb 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x126abb (LoadPre 0x126abb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126abb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126abb 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x126ac0 (StorePre 0x126ac0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126ac0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ac0 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x126ac5 (movR64M64Effect 0x126ac5 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x126ac5 (LoadPre 0x126ac5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126ac5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ac5 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126aca (StorePre 0x126aca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126aca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126aca 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126acf (movR64M64Effect 0x126acf 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x126acf (LoadPre 0x126acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126acf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126acf 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126ad4 (StorePre 0x126ad4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ad4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126ad4 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l126ad9, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 57), (7, 68), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l126aa3 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x4C, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x8B,
    0x7C, 0x24, 0x60, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x68, 0x48, 0x89, 0x7C,
    0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8B, 0x7C, 0x24,
    0x78, 0x48, 0x89, 0x7C, 0x24, 0x20]

theorem code_l126aa3 : ∀ x ∈ codeRange 0x126aa3 bytes_l126aa3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26aa3 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ad9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ad9 (movR64Imm64Effect 0x126ad9 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x126ad9 (fun s => s.RIP = 0x126ad9) (movR64Imm64Effect 0x126ad9 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126ae3 (andR64R64Effect 0x126ae3 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x126ae3 (fun s => s.RIP = 0x126ae3) (andR64R64Effect 0x126ae3 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 55), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126ad9 : List UInt8 :=
  [0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0x21, 0xF7, 0xEB, 0x2D]

theorem code_l126ad9 : ∀ x ∈ codeRange 0x126ad9 bytes_l126ad9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ad9 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ae8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ae8 (incR64Effect 0x126ae8 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x126ae8 (fun s => s.RIP = 0x126ae8) (incR64Effect 0x126ae8 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x126aeb (StorePre 0x126aeb 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126aeb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126aeb 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x126aef (movR32M32Effect 0x126aef 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x126aef (LoadPre 0x126aef (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126aef + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126aef 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126af3 (cmpR32R32Effect 0x126af3 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x126af3 (cmpR32R32Effect 0x126af3 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x126af3 (fun s => s.RIP = 0x126af3) (cmpR32R32Effect 0x126af3 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l126b7c, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l126afc, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126ae8 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x0F, 0x86,
    0x80, 0x00, 0x00, 0x00]

theorem code_l126ae8 : ∀ x ∈ codeRange 0x126ae8 bytes_l126ae8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ae8 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126afc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126afc (leaR32Effect 0x126afc 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x126afc (fun s => s.RIP = 0x126afc) (leaR32Effect 0x126afc 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x126b00 (shlR64Effect 0x126b00 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x126b00 (fun s => s.RIP = 0x126b00) (shlR64Effect 0x126b00 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x126b04 (orR64Imm8Effect 0x126b04 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x126b04 (fun s => s.RIP = 0x126b04) (orR64Imm8Effect 0x126b04 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l126b08, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126afc : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l126afc : ∀ x ∈ codeRange 0x126afc bytes_l126afc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26afc 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b08 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b08 (movR32Imm32Effect 0x126b08 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x126b08 (fun s => s.RIP = 0x126b08) (movR32Imm32Effect 0x126b08 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126b0d (xorR32R32Effect 0x126b0d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x126b0d (fun s => s.RIP = 0x126b0d) (xorR32R32Effect 0x126b0d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x126b0f (movR32R32Effect 0x126b0f 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 58) (.exec 0x126b0f (fun s => s.RIP = 0x126b0f) (movR32R32Effect 0x126b0f 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x126b12 (movR32R32Effect 0x126b12 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 60) (.exec 0x126b12 (fun s => s.RIP = 0x126b12) (movR32R32Effect 0x126b12 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 0), (1, 57), (2, 53), (3, 3), (4, 4), (6, 59), (7, 55), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l126b08 : List UInt8 :=
  [0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9, 0x44, 0x89, 0xFE]

theorem code_l126b08 : ∀ x ∈ codeRange 0x126b08 bytes_l126b08, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b08 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b15 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b15 (movR32R32Effect 0x126b15 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x126b15 (fun s => s.RIP = 0x126b15) (movR32R32Effect 0x126b15 2 6 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x126b17 (orR64R64Effect 0x126b17 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x126b17 (fun s => s.RIP = 0x126b17) (orR64R64Effect 0x126b17 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x126b1a (movR64M64Effect 0x126b1a 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x126b1a (LoadPre 0x126b1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126b1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b1a 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126b1f (StorePre 0x126b1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126b1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b1f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x126b24 (movR64M64Effect 0x126b24 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 61) (.exec 0x126b24 (LoadPre 0x126b24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126b24 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b24 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x126b29 (StorePre 0x126b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b29 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x126b2e (movR64M64Effect 0x126b2e 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x126b2e (LoadPre 0x126b2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126b2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b2e 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x126b33 (movR64M64Effect 0x126b33 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x126b33 (LoadPre 0x126b33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126b33 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126b33 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126b38 (StorePre 0x126b38 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126b38 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b38 10 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.exec 0x126b3d (StorePre 0x126b3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126b3d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126b3d 9 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 69) (.exec 0x126b42 (StorePre 0x126b42 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126b42 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b42 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 70) (.exec 0x126b46 (StorePre 0x126b46 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126b46 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b46 8 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 71) (.exec 0x126b4a (StorePre 0x126b4a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126b4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4a 10 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 72) (.exec 0x126b4e (StorePre 0x126b4e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126b4e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b4e 9 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 73) (.exec 0x126b52 (StorePre 0x126b52 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126b52 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b52 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 74) (.exec 0x126b55 (StorePre 0x126b55 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126b55 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126b55 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 75) (.exec 0x126b58 (StorePre 0x126b58 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126b58 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b58 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 76) (.exec 0x126b5c (StorePre 0x126b5c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126b5c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126b5c 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 77) (.exec 0x126b60 (StorePre 0x126b60 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126b60 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126b60 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126b67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 57), (8, 60), (9, 63), (10, 65), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l126b15 : List UInt8 :=
  [0x89, 0xF6, 0x48, 0x09, 0xFE, 0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x4C,
    0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x4C, 0x24, 0x08, 0x4C, 0x8B,
    0x54, 0x24, 0x10, 0x4C, 0x89, 0x54, 0x24, 0x30, 0x4C, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x89, 0x7B,
    0x38, 0x4C, 0x89, 0x43, 0x30, 0x4C, 0x89, 0x53, 0x28, 0x4C, 0x89, 0x4B, 0x20, 0x89, 0x53, 0x08,
    0x89, 0x4B, 0x0C, 0x48, 0x89, 0x43, 0x10, 0x48, 0x89, 0x73, 0x18, 0x48, 0xC7, 0x03, 0x01, 0x00,
    0x00, 0x00]

theorem code_l126b15 : ∀ x ∈ codeRange 0x126b15 bytes_l126b15, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b15 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126b67 (movR64R64Effect 0x126b67 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x126b67 (fun s => s.RIP = 0x126b67) (movR64R64Effect 0x126b67 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x126b6a (addR64Imm32Effect 0x126b6a 4 0xd8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x126b6a (fun s => s.RIP = 0x126b6a) (addR64Imm32Effect 0x126b6a 4 0xd8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126b71 (popR64Effect 0x126b71 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x126b71 (popR64Effect 0x126b71 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x126b71 (PopPre 0x126b71) (popR64Effect 0x126b71 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x126b72 (popR64Effect 0x126b72 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x126b72 (popR64Effect 0x126b72 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x126b72 (PopPre 0x126b72) (popR64Effect 0x126b72 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x126b74 (popR64Effect 0x126b74 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x126b74 (popR64Effect 0x126b74 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x126b74 (PopPre 0x126b74) (popR64Effect 0x126b74 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x126b76 (popR64Effect 0x126b76 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x126b76 (popR64Effect 0x126b76 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x126b76 (PopPre 0x126b76) (popR64Effect 0x126b76 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x126b78 (popR64Effect 0x126b78 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x126b78 (popR64Effect 0x126b78 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x126b78 (PopPre 0x126b78) (popR64Effect 0x126b78 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x126b7a (popR64Effect 0x126b7a 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x126b7a (popR64Effect 0x126b7a 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x126b7a (PopPre 0x126b7a) (popR64Effect 0x126b7a 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x126b7b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x126b7b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x126b7b (RetPre 0x126b7b) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l126b67 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xD8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l126b67 : ∀ x ∈ codeRange 0x126b67 bytes_l126b67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b67 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126b7c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126b7c (StorePre 0x126b7c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126b7c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126b7c 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.exec 0x126b80 (fun s => s.RIP = 0x126b80) (leaR64Effect 0x126b80 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126b88 (movR64M64Effect 0x126b88 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 56) (.exec 0x126b88 (LoadPre 0x126b88 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x126b88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b88 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x126b8c (movR64M64Effect 0x126b8c 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 58) (.exec 0x126b8c (LoadPre 0x126b8c (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x126b8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126b8c 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.exec 0x126b90 (StorePre 0x126b90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x126b90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b90 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x126b98 (StorePre 0x126b98 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x126b98 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126b98 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.exec 0x126ba0 (StorePre 0x126ba0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x126ba0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ba0 14 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 62) (.out 0x126ba8 (leaR64Effect 0x126ba8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x126ba8 (fun s => s.RIP = 0x126ba8) (leaR64Effect 0x126ba8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x126bad (movR64R64Effect 0x126bad 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 65) (.exec 0x126bad (fun s => s.RIP = 0x126bad) (movR64R64Effect 0x126bad 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x126bb0 (callEffect (fun _ => 0x124de0) 0x126bb5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x126bb0 (PushPre 0x126bb0 5) (callEffect (fun _ => 0x124de0) 0x126bb5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x126bb5⟩) #v[]
    (.terminate (.call ⟨.l124de0, RegMap.args [(0, 55), (1, 57), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l126bb5, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l126b7c : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x45, 0x00,
    0x49, 0x8B, 0x4D, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24,
    0x48, 0x4C, 0x89, 0xF6, 0xE8, 0x2B, 0xE2, 0xFF, 0xFF]

theorem code_l126b7c : ∀ x ∈ codeRange 0x126b7c bytes_l126b7c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26b7c 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126bb5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126bb5 (movR32M32Effect 0x126bb5 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 54) (.exec 0x126bb5 (LoadPre 0x126bb5 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bb5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb5 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126bb9 (movR32M32Effect 0x126bb9 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x126bb9 (LoadPre 0x126bb9 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126bb9 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126bb9 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[53, 55]
    (.letOp (n := 58) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x126bbd (subR32R32Effect 0x126bbd 2 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x126bbd (fun s => s.RIP = 0x126bbd) (subR32R32Effect 0x126bbd 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126bbf (atFlags (condHolds 6) (setccR8Effect 0x126bbf 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 58, 59]
    (.letOp (n := 62) (.exec 0x126bbf (fun s => s.RIP = 0x126bbf) (atFlags (condHolds 6) (setccR8Effect 0x126bbf 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 58, 59]
    (.letOp (n := 63) (.out 0x126bc2 (movR64M64Effect 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x126bc2 (LoadPre 0x126bc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126bc2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126bc2 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126bca (StorePre 0x126bca 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126bca + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126bca 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.exec 0x126bcd (StorePre 0x126bcd 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126bcd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126bcd 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 67) (.exec 0x126bd1 (StorePre 0x126bd1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126bd1 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126bd1 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 68) (.out 0x126bd5 (movR64M64Effect 0x126bd5 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 69) (.exec 0x126bd5 (LoadPre 0x126bd5 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126bd5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126bd5 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.out 0x126bd9 (cmpR64Imm8Effect 0x126bd9 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[68]
    (.letOp (n := 71) (.exec 0x126bd9 (fun s => s.RIP = 0x126bd9) (cmpR64Imm8Effect 0x126bd9 2 0x1) (Reg.operands [.gpr 2] [])) #v[68]
    (.letOp (n := 72) (.out 0x126bdd (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126bdd 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[68, 70]
    (.letOp (n := 73) (.exec 0x126bdd (fun s => s.RIP = 0x126bdd) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126bdd 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 70]
    (.letOp (n := 74) (.exec 0x126be1 (StorePre 0x126be1 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126be1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126be1 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[72, 14]
    (.letOp (n := 75) (.out 0x126be5 (movR64M64Effect 0x126be5 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x126be5 (LoadPre 0x126be5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126be5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126be5 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x126bea (movR32R32Effect 0x126bea 2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[75]
    (.letOp (n := 78) (.exec 0x126bea (fun s => s.RIP = 0x126bea) (movR32R32Effect 0x126bea 2 2 7) (Reg.operands [.gpr 7] [])) #v[75]
    (.letOp (n := 79) (.out 0x126bec (orR8R8Effect 0x126bec 2 2 0) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 0] []) (.flag .ZF)) #v[77, 61]
    (.letOp (n := 80) (.exec 0x126bec (fun s => s.RIP = 0x126bec) (orR8R8Effect 0x126bec 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[77, 61]
    (.letOp (n := 81) (.pure (condOp 4)) #v[79]
    (.terminate (.condBr (Fin.last 81) ⟨.l126cf4, RegMap.args [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ ⟨.l126bf4, RegMap.args [(0, 61), (1, 55), (3, 3), (4, 4), (6, 57), (7, 75), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 79), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l126bb5 : List UInt8 :=
  [0x41, 0x8B, 0x76, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x29, 0xCE, 0x0F, 0x96, 0xC0, 0x48, 0x8B, 0x94,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18,
    0x49, 0x8B, 0x56, 0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10,
    0x48, 0x8B, 0x7C, 0x24, 0x48, 0x89, 0xFA, 0x08, 0xC2, 0x0F, 0x84, 0x00, 0x01, 0x00, 0x00]

theorem code_l126bb5 : ∀ x ∈ codeRange 0x126bb5 bytes_l126bb5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26bb5 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126bf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126bf4 (movR32M32LowEffect 0x126bf4 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126bf4 (LoadPre 0x126bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126bf4 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf4 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126bf8 (movR32M32LowEffect 0x126bf8 1 (.sib 4 none 0 (.d8 0x54))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126bf8 (LoadPre 0x126bf8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x126bf8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126bf8 1 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126bfc (movR64M64Effect 0x126bfc 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x126bfc (LoadPre 0x126bfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126bfc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126bfc 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126c01 (movR64M64Effect 0x126c01 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x126c01 (LoadPre 0x126c01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126c01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c01 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126c06 (movR64M64Effect 0x126c06 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x126c06 (LoadPre 0x126c06 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126c06 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c06 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126c0b (StorePre 0x126c0b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c0b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c0b 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x126c10 (movR64M64Effect 0x126c10 8 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x126c10 (LoadPre 0x126c10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x126c10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c10 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x126c15 (StorePre 0x126c15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c15 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x126c1a (movR64M64Effect 0x126c1a 8 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 68) (.exec 0x126c1a (LoadPre 0x126c1a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126c1a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c1a 8 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x126c1f (StorePre 0x126c1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c1f 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x126c24 (movR64M64Effect 0x126c24 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 71) (.exec 0x126c24 (LoadPre 0x126c24 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126c24 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c24 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126c2c (StorePre 0x126c2c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c2c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c2c 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x126c31 (movR64M64Effect 0x126c31 8 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x126c31 (LoadPre 0x126c31 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126c31 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c31 8 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x126c39 (StorePre 0x126c39 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c39 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c39 8 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x126c41 (movR64M64Effect 0x126c41 8 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 77) (.exec 0x126c41 (LoadPre 0x126c41 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x126c41 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c41 8 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x126c49 (StorePre 0x126c49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126c49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c49 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x126c51 (movR64M64Effect 0x126c51 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 80) (.exec 0x126c51 (LoadPre 0x126c51 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126c51 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c51 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x126c59 (StorePre 0x126c59 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c59 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126c59 8 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x126c61 (testR64R64Effect 0x126c61 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[7, 7]
    (.letOp (n := 83) (.exec 0x126c61 (fun s => s.RIP = 0x126c61) (testR64R64Effect 0x126c61 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 84) (.pure (condOp 5)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l126ad9, RegMap.args [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l126c6a, RegMap.args [(0, 57), (1, 55), (2, 53), (3, 3), (4, 4), (6, 59), (7, 7), (8, 79), (9, 9), (10, 10), (11, 11), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l126bf4 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x50, 0x8B, 0x4C, 0x24, 0x54, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x74,
    0x24, 0x60, 0x4C, 0x8B, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x44, 0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24,
    0x70, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x44, 0x24, 0x78, 0x4C, 0x89, 0x44, 0x24, 0x18,
    0x4C, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8B, 0x84,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x85, 0xFF,
    0x0F, 0x85, 0x6F, 0xFE, 0xFF, 0xFF]

theorem code_l126bf4 : ∀ x ∈ codeRange 0x126bf4 bytes_l126bf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26bf4 118 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126c6a_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x126cd2 (StorePre 0x126cd2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126cd2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd2 8 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 85) (.exec 0x126cd6 (StorePre 0x126cd6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126cd6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cd6 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[80, 3]
    (.letOp (n := 86) (.exec 0x126cda (StorePre 0x126cda 3 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126cda + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cda 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 87) (.exec 0x126cdd (StorePre 0x126cdd 3 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x126cdd + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126cdd 1 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 88) (.exec 0x126ce0 (StorePre 0x126ce0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126ce0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce0 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 89) (.exec 0x126ce4 (StorePre 0x126ce4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126ce4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126ce4 6 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 90) (.exec 0x126ce8 (StorePre 0x126ce8 7 (fun s => AddrMode.addr (.base 3 .none) s (0x126ce8 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x126ce8 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126b67, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 80), (8, 82), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩))))))))

def bytes_l126c6a_1 : List UInt8 :=
  [0x4C, 0x89, 0x43, 0x28, 0x48, 0x89, 0x7B, 0x20, 0x89, 0x53, 0x08, 0x89, 0x4B, 0x0C, 0x48, 0x89,
    0x43, 0x10, 0x48, 0x89, 0x73, 0x18, 0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xE9, 0x73, 0xFE,
    0xFF, 0xFF]

theorem code_l126c6a_1 : ∀ x ∈ codeRange 0x126cd2 bytes_l126c6a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26cd2 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126c6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126c6a (movR64M64Effect 0x126c6a 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126c6a (LoadPre 0x126c6a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126c6a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c6a 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x126c6f (StorePre 0x126c6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126c6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c6f 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x126c74 (movR64M64Effect 0x126c74 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x126c74 (LoadPre 0x126c74 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126c74 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c74 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x126c79 (StorePre 0x126c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c79 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x126c7e (movR64M64Effect 0x126c7e 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126c7e (LoadPre 0x126c7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x126c7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c7e 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126c83 (movR64M64Effect 0x126c83 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 62) (.exec 0x126c83 (LoadPre 0x126c83 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126c83 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126c83 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126c88 (StorePre 0x126c88 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126c88 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c88 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x126c8d (StorePre 0x126c8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126c8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126c8d 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x126c92 (movR64M64Effect 0x126c92 7 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x126c92 (LoadPre 0x126c92 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x126c92 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c92 7 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126c9a (StorePre 0x126c9a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x126c9a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126c9a 7 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.out 0x126c9e (movR64M64Effect 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x126c9e (LoadPre 0x126c9e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x126c9e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126c9e 7 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x126ca6 (movR64M64Effect 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 71) (.exec 0x126ca6 (LoadPre 0x126ca6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x126ca6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126ca6 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126cae (StorePre 0x126cae 4 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x126cae + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cae 8 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 73) (.exec 0x126cb2 (StorePre 0x126cb2 4 (fun s => AddrMode.addr (.base 3 (.d8 0x40)) s (0x126cb2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cb2 7 (.base 3 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 74) (.out 0x126cb6 (movR64M64Effect 0x126cb6 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x126cb6 (LoadPre 0x126cb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x126cb6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cb6 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x126cbb (StorePre 0x126cbb 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x126cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cbb 7 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[74, 3]
    (.letOp (n := 77) (.out 0x126cbf (movR64M64Effect 0x126cbf 7 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 78) (.exec 0x126cbf (LoadPre 0x126cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x126cbf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cbf 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x126cc4 (StorePre 0x126cc4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126cc4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126cc4 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 80) (.out 0x126cc8 (movR64M64Effect 0x126cc8 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 81) (.exec 0x126cc8 (LoadPre 0x126cc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126cc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126cc8 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x126ccd (movR64M64Effect 0x126ccd 8 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 83) (.exec 0x126ccd (LoadPre 0x126ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126ccd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ccd 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l126c6a_1)))))))))))))))))))))))))))))))

def bytes_l126c6a : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x20, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48,
    0x89, 0x7C, 0x24, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89,
    0x44, 0x24, 0x30, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x48, 0x8B, 0xBC, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x7B, 0x50, 0x48, 0x8B, 0xBC, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x84, 0x24,
    0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x43, 0x48, 0x48, 0x89, 0x7B, 0x40, 0x48, 0x8B, 0x7C, 0x24,
    0x40, 0x48, 0x89, 0x7B, 0x38, 0x48, 0x8B, 0x7C, 0x24, 0x38, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x28, 0x4C, 0x8B, 0x44, 0x24, 0x30] ++ bytes_l126c6a_1

theorem code_l126c6a : ∀ x ∈ codeRange 0x126c6a bytes_l126c6a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x26c6a 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l126c6a_1

@[cfg_block] def b_l126cf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126cf4 (StorePre 0x126cf4 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x126cf4 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x126cf4 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x126cf9 (movR64R64Effect 0x126cf9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 55) (.exec 0x126cf9 (fun s => s.RIP = 0x126cf9) (movR64R64Effect 0x126cf9 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 56) (.out 0x126cfc (shlR64Effect 0x126cfc 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x126cfc (fun s => s.RIP = 0x126cfc) (shlR64Effect 0x126cfc 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x126d00 (orR64Imm8Effect 0x126d00 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x126d00 (fun s => s.RIP = 0x126d00) (orR64Imm8Effect 0x126d00 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x126d04 (movR32Imm32Effect 0x126d04 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 61) (.exec 0x126d04 (fun s => s.RIP = 0x126d04) (movR32Imm32Effect 0x126d04 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x126d09 (xorR32R32Effect 0x126d09 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 63) (.exec 0x126d09 (fun s => s.RIP = 0x126d09) (xorR32R32Effect 0x126d09 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 58), (1, 1), (2, 60), (3, 3), (4, 4), (6, 6), (7, 62), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l126cf4 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0x05, 0xFE, 0xFF, 0xFF]

theorem code_l126cf4 : ∀ x ∈ codeRange 0x126cf4 bytes_l126cf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26cf4 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d10 (xorR32R32Effect 0x126d10 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x126d10 (fun s => s.RIP = 0x126d10) (xorR32R32Effect 0x126d10 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x126d12 (movR32Imm32Effect 0x126d12 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126d12 (fun s => s.RIP = 0x126d12) (movR32Imm32Effect 0x126d12 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126d17 (xorR32R32Effect 0x126d17 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x126d17 (fun s => s.RIP = 0x126d17) (xorR32R32Effect 0x126d17 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126b15, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126d10 : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xF7, 0xFD, 0xFF, 0xFF]

theorem code_l126d10 : ∀ x ∈ codeRange 0x126d10 bytes_l126d10, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d10 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d20 (pushR64Effect 0x126d20 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x126d20 (PushPre 0x126d20 1) (pushR64Effect 0x126d20 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x126d21 (pushR64Effect 0x126d21 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x126d21 (PushPre 0x126d21 2) (pushR64Effect 0x126d21 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x126d23 (pushR64Effect 0x126d23 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x126d23 (PushPre 0x126d23 2) (pushR64Effect 0x126d23 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126d25 (pushR64Effect 0x126d25 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x126d25 (PushPre 0x126d25 2) (pushR64Effect 0x126d25 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x126d27 (pushR64Effect 0x126d27 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x126d27 (PushPre 0x126d27 2) (pushR64Effect 0x126d27 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x126d29 (pushR64Effect 0x126d29 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x126d29 (PushPre 0x126d29 1) (pushR64Effect 0x126d29 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x126d2a (subR64Imm32Effect 0x126d2a 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x126d2a (fun s => s.RIP = 0x126d2a) (subR64Imm32Effect 0x126d2a 4 0xa8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x126d31 (movR64R64Effect 0x126d31 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x126d31 (fun s => s.RIP = 0x126d31) (movR64R64Effect 0x126d31 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x126d34 (movR32M32LowEffect 0x126d34 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 70) (.exec 0x126d34 (LoadPre 0x126d34 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x126d34 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x126d34 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x126d37 (movR32M32Effect 0x126d37 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 72) (.exec 0x126d37 (LoadPre 0x126d37 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x126d37 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126d37 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x126d3b (movR32R32Effect 0x126d3b 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.exec 0x126d3b (fun s => s.RIP = 0x126d3b) (movR32R32Effect 0x126d3b 3 13 15) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 75) (.out 0x126d3e (addR32R32Effect 0x126d3e 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[73, 69]
    (.letOp (n := 76) (.out 0x126d3e (addR32R32Effect 0x126d3e 3 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[73, 69]
    (.letOp (n := 77) (.exec 0x126d3e (fun s => s.RIP = 0x126d3e) (addR32R32Effect 0x126d3e 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[73, 69]
    (.letOp (n := 78) (.pure (condOp 2)) #v[76]
    (.terminate (.condBr (Fin.last 78) ⟨.l127126, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ ⟨.l126d47, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l126d20 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x8B, 0x6A, 0x08, 0x44, 0x8B, 0x7E, 0x1C, 0x45, 0x89, 0xFD, 0x41, 0x01,
    0xED, 0x0F, 0x82, 0xDF, 0x03, 0x00, 0x00]

theorem code_l126d20 : ∀ x ∈ codeRange 0x126d20 bytes_l126d20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d20 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d47 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d47 (movR64R64Effect 0x126d47 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 54) (.exec 0x126d47 (fun s => s.RIP = 0x126d47) (movR64R64Effect 0x126d47 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x126d4a (movR64M64Effect 0x126d4a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x126d4a (LoadPre 0x126d4a (fun s => AddrMode.addr (.base 6 .none) s (0x126d4a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x126d4a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x126d4d (movR64M64Effect 0x126d4d 2 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 58) (.exec 0x126d4d (LoadPre 0x126d4d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d4d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d4d 2 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x126d51 (leaR64Effect 0x126d51 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126d51 (fun s => s.RIP = 0x126d51) (leaR64Effect 0x126d51 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126d56 (StorePre 0x126d56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126d56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d56 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 62) (.exec 0x126d5e (StorePre 0x126d5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126d5e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126d5e 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 63) (.out 0x126d66 (movR32R32Effect 0x126d66 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 64) (.exec 0x126d66 (fun s => s.RIP = 0x126d66) (movR32R32Effect 0x126d66 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 65) (.out 0x126d69 (callEffect (fun _ => 0x127c50) 0x126d6e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x126d69 (PushPre 0x126d69 5) (callEffect (fun _ => 0x127c50) 0x126d6e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x126d6e⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 63), (2, 57), (3, 3), (4, 65), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l126d6e, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l126d47 : List UInt8 :=
  [0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x49, 0x8B, 0x56, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x18, 0x48,
    0x89, 0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x44,
    0x89, 0xE9, 0xE8, 0xE2, 0x0E, 0x00, 0x00]

theorem code_l126d47 : ∀ x ∈ codeRange 0x126d47 bytes_l126d47, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d47 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d6e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d6e (movR32M32Effect 0x126d6e 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x126d6e (LoadPre 0x126d6e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126d6e + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126d6e 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126d73 (cmpR32Imm8Effect 0x126d73 4 12 0x2) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126d73 (fun s => s.RIP = 0x126d73) (cmpR32Imm8Effect 0x126d73 4 12 0x2) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126da9, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126d79, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126d6e : List UInt8 :=
  [0x44, 0x8B, 0x64, 0x24, 0x18, 0x41, 0x83, 0xFC, 0x02, 0x75, 0x30]

theorem code_l126d6e : ∀ x ∈ codeRange 0x126d6e bytes_l126d6e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d6e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d79 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d79 (movR64M64Effect 0x126d79 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x126d79 (LoadPre 0x126d79 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126d79 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d79 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126d7e (movR64M64Effect 0x126d7e 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126d7e (LoadPre 0x126d7e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126d7e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126d7e 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x126d83 (StorePre 0x126d83 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126d83 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126d83 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x126d86 (StorePre 0x126d86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126d86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126d86 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x126d8a (movR64M64Effect 0x126d8a 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x126d8a (LoadPre 0x126d8a (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126d8a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126d8a 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x126d8e (movR32Imm32Effect 0x126d8e 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 62) (.exec 0x126d8e (fun s => s.RIP = 0x126d8e) (movR32Imm32Effect 0x126d8e 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x126d94 (cmpR64Imm8Effect 0x126d94 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 64) (.out 0x126d94 (cmpR64Imm8Effect 0x126d94 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 65) (.exec 0x126d94 (fun s => s.RIP = 0x126d94) (cmpR64Imm8Effect 0x126d94 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 66) (.pure (condOp 6)) #v[63, 64]
    (.terminate (.condBr (Fin.last 66) ⟨.l126e83, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l126d9e, RegMap.args [(0, 59), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 14), (15, 15), (16, 63), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l126d79 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xF8, 0x3F, 0x0F,
    0x86, 0xE5, 0x00, 0x00, 0x00]

theorem code_l126d79 : ∀ x ∈ codeRange 0x126d79 bytes_l126d79, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d79 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126d9e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126d9e (movR32Imm32Effect 0x126d9e 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126d9e (fun s => s.RIP = 0x126d9e) (movR32Imm32Effect 0x126d9e 5 0 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126da3 (xorR32R32Effect 0x126da3 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x126da3 (fun s => s.RIP = 0x126da3) (xorR32R32Effect 0x126da3 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.out 0x126da5 (xorR32R32Effect 0x126da5 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 58) (.exec 0x126da5 (fun s => s.RIP = 0x126da5) (xorR32R32Effect 0x126da5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 53), (1, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l126d9e : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x31, 0xC9, 0xEB, 0x5D]

theorem code_l126d9e : ∀ x ∈ codeRange 0x126d9e bytes_l126d9e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26d9e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126da9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126da9 (movR32M32Effect 0x126da9 15 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x126da9 (LoadPre 0x126da9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126da9 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x126da9 15 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126dae (movR64M64Effect 0x126dae 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126dae (LoadPre 0x126dae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126dae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dae 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126db3 (movR64M64Effect 0x126db3 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 58) (.exec 0x126db3 (LoadPre 0x126db3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126db3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126db3 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x126db8 (movzxR32M8Effect 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x126db8 (LoadPre 0x126db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126db8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126db8 6 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126dbe (movR64M64Effect 0x126dbe 1 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x126dbe (LoadPre 0x126dbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126dbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dbe 1 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x126dc3 (StorePre 0x126dc3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126dc3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126dc3 1 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x126dc8 (movR64M64Effect 0x126dc8 1 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x126dc8 (LoadPre 0x126dc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126dc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dc8 1 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x126dcd (StorePre 0x126dcd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x126dcd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dcd 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x126dd5 (movR64M64Effect 0x126dd5 1 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x126dd5 (LoadPre 0x126dd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126dd5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126dd5 1 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x126dda (StorePre 0x126dda 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x126dda + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126dda 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x126de2 (movR64M64Effect 0x126de2 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x126de2 (LoadPre 0x126de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126de2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126de2 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x126de7 (StorePre 0x126de7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126de7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126de7 1 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x126def (movR64R64Effect 0x126def 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 74) (.exec 0x126def (fun s => s.RIP = 0x126def) (movR64R64Effect 0x126def 5 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 75) (.out 0x126df2 (shrR64Effect 0x126df2 4 5 32) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[73]
    (.letOp (n := 76) (.exec 0x126df2 (fun s => s.RIP = 0x126df2) (shrR64Effect 0x126df2 4 5 32) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x126df6 (movR64Imm64Effect 0x126df6 6 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x126df6 (fun s => s.RIP = 0x126df6) (movR64Imm64Effect 0x126df6 6 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x126e00 (andR64R64Effect 0x126e00 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[77, 57]
    (.letOp (n := 80) (.exec 0x126e00 (fun s => s.RIP = 0x126e00) (andR64R64Effect 0x126e00 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[77, 57]
    (.letOp (n := 81) (.out 0x126e03 (movR64R64Effect 0x126e03 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 82) (.exec 0x126e03 (fun s => s.RIP = 0x126e03) (movR64R64Effect 0x126e03 1 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 81), (3, 3), (4, 4), (5, 75), (6, 79), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 59), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l126da9 : List UInt8 :=
  [0x44, 0x8B, 0x7C, 0x24, 0x1C, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x4C, 0x8B, 0x54, 0x24, 0x28, 0x44,
    0x0F, 0xB6, 0x6C, 0x24, 0x30, 0x48, 0x8B, 0x4C, 0x24, 0x31, 0x48, 0x89, 0x4C, 0x24, 0x78, 0x48,
    0x8B, 0x4C, 0x24, 0x39, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24,
    0x41, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89,
    0x8C, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC5, 0x48, 0xC1, 0xED, 0x20, 0x48, 0xBE, 0x00,
    0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4C, 0x21, 0xD6, 0x48, 0x89, 0xC1]

theorem code_l126da9 : ∀ x ∈ codeRange 0x126da9 bytes_l126da9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26da9 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e06_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x126e5b (StorePre 0x126e5b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x126e5b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e5b 2 (.base 3 (.d8 0x19))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 88) (.exec 0x126e5e (StorePre 0x126e5e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x126e5e + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x126e5e 12 (.base 3 .none)) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 89) (.exec 0x126e61 (StorePre 0x126e61 4 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x126e61 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126e61 15 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 90) (.exec 0x126e65 (StorePre 0x126e65 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x126e65 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e65 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 91) (.exec 0x126e69 (StorePre 0x126e69 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x126e69 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e69 1 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 92) (.exec 0x126e6d (StorePre 0x126e6d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x126e6d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x126e6d 4 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.terminate (.br ⟨.l126e71, RegMap.args [(0, 61), (1, 65), (2, 82), (3, 3), (4, 4), (5, 53), (6, 84), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))))

def bytes_l126e06_1 : List UInt8 :=
  [0x89, 0x53, 0x19, 0x44, 0x89, 0x23, 0x44, 0x89, 0x7B, 0x04, 0x48, 0x89, 0x43, 0x08, 0x48, 0x89,
    0x4B, 0x10, 0x44, 0x88, 0x6B, 0x18]

theorem code_l126e06_1 : ∀ x ∈ codeRange 0x126e5b bytes_l126e06_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e5b 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e06 (shlR64Effect 0x126e06 4 5 32) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x126e06 (fun s => s.RIP = 0x126e06) (shlR64Effect 0x126e06 4 5 32) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x126e0a (andR32Imm32Effect 0x126e0a 6 1 0xffffff00) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x126e0a (fun s => s.RIP = 0x126e0a) (andR32Imm32Effect 0x126e0a 6 1 0xffffff00) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x126e10 (orR64R64Effect 0x126e10 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x126e10 (fun s => s.RIP = 0x126e10) (orR64R64Effect 0x126e10 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x126e13 (movzxR32R8Effect 0x126e13 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x126e13 (fun s => s.RIP = 0x126e13) (movzxR32R8Effect 0x126e13 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x126e16 (orR64R64Effect 0x126e16 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x126e16 (fun s => s.RIP = 0x126e16) (orR64R64Effect 0x126e16 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x126e19 (movR32R32Effect 0x126e19 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[10]
    (.letOp (n := 64) (.exec 0x126e19 (fun s => s.RIP = 0x126e19) (movR32R32Effect 0x126e19 3 1 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 65) (.out 0x126e1c (orR64R64Effect 0x126e1c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[63, 6]
    (.letOp (n := 66) (.exec 0x126e1c (fun s => s.RIP = 0x126e1c) (orR64R64Effect 0x126e1c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 67) (.out 0x126e1f (movR32M32LowEffect 0x126e1f 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x126e1f (LoadPre 0x126e1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x126e1f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e1f 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x126e23 (movR32M32LowEffect 0x126e23 6 (.sib 4 none 0 (.d8 0x7b))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x126e23 (LoadPre 0x126e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7b)) s (0x126e23 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e23 6 (.sib 4 none 0 (.d8 0x7b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x126e27 (StorePre 0x126e27 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e27 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e27 6 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x126e2b (StorePre 0x126e2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e2b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126e2b 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 73) (.out 0x126e2f (movR64M64Effect 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 74) (.exec 0x126e2f (LoadPre 0x126e2f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126e2f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e2f 2 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x126e37 (StorePre 0x126e37 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x126e37 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e37 2 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.out 0x126e3b (movR64M64Effect 0x126e3b 2 (.sib 4 none 0 (.d32 0x87))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 77) (.exec 0x126e3b (LoadPre 0x126e3b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x87)) s (0x126e3b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126e3b 2 (.sib 4 none 0 (.d32 0x87))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x126e43 (StorePre 0x126e43 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x126e43 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e43 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[76, 3]
    (.letOp (n := 79) (.out 0x126e47 (movR64M64Effect 0x126e47 2 (.sib 4 none 0 (.d8 0x7f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 80) (.exec 0x126e47 (LoadPre 0x126e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7f)) s (0x126e47 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126e47 2 (.sib 4 none 0 (.d8 0x7f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x126e4c (StorePre 0x126e4c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x126e4c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e4c 2 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 82) (.out 0x126e50 (movR32M32LowEffect 0x126e50 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 83) (.exec 0x126e50 (LoadPre 0x126e50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x126e50 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e50 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x126e54 (movR32M32LowEffect 0x126e54 6 (.sib 4 none 0 (.d8 0x53))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 85) (.exec 0x126e54 (LoadPre 0x126e54 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x53)) s (0x126e54 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126e54 6 (.sib 4 none 0 (.d8 0x53))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x126e58 (StorePre 0x126e58 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x126e58 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x126e58 6 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[84, 3]
    (b_l126e06_1))))))))))))))))))))))))))))))))))

def bytes_l126e06 : List UInt8 :=
  [0x48, 0xC1, 0xE5, 0x20, 0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF, 0x48, 0x09, 0xE9, 0x0F, 0xB6, 0xC0,
    0x48, 0x09, 0xC8, 0x44, 0x89, 0xD1, 0x48, 0x09, 0xF1, 0x8B, 0x54, 0x24, 0x78, 0x8B, 0x74, 0x24,
    0x7B, 0x89, 0x74, 0x24, 0x53, 0x89, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x94, 0x24, 0x8F, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x53, 0x30, 0x48, 0x8B, 0x94, 0x24, 0x87, 0x00, 0x00, 0x00, 0x48, 0x89, 0x53,
    0x28, 0x48, 0x8B, 0x54, 0x24, 0x7F, 0x48, 0x89, 0x53, 0x20, 0x8B, 0x54, 0x24, 0x50, 0x8B, 0x74,
    0x24, 0x53, 0x89, 0x73, 0x1C] ++ bytes_l126e06_1

theorem code_l126e06 : ∀ x ∈ codeRange 0x126e06 bytes_l126e06, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x26e06 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l126e06_1

@[cfg_block] def b_l126e71 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e71 (addR64Imm32Effect 0x126e71 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x126e71 (fun s => s.RIP = 0x126e71) (addR64Imm32Effect 0x126e71 4 0xa8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126e78 (popR64Effect 0x126e78 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x126e78 (popR64Effect 0x126e78 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x126e78 (PopPre 0x126e78) (popR64Effect 0x126e78 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x126e79 (popR64Effect 0x126e79 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x126e79 (popR64Effect 0x126e79 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x126e79 (PopPre 0x126e79) (popR64Effect 0x126e79 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x126e7b (popR64Effect 0x126e7b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x126e7b (popR64Effect 0x126e7b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x126e7b (PopPre 0x126e7b) (popR64Effect 0x126e7b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x126e7d (popR64Effect 0x126e7d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x126e7d (popR64Effect 0x126e7d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x126e7d (PopPre 0x126e7d) (popR64Effect 0x126e7d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x126e7f (popR64Effect 0x126e7f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x126e7f (popR64Effect 0x126e7f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x126e7f (PopPre 0x126e7f) (popR64Effect 0x126e7f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x126e81 (popR64Effect 0x126e81 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x126e81 (popR64Effect 0x126e81 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x126e81 (PopPre 0x126e81) (popR64Effect 0x126e81 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x126e82 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x126e82 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x126e82 (RetPre 0x126e82) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l126e71 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l126e71 : ∀ x ∈ codeRange 0x126e71 bytes_l126e71, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e71 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e83 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e83 (incR64Effect 0x126e83 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x126e83 (fun s => s.RIP = 0x126e83) (incR64Effect 0x126e83 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x126e86 (StorePre 0x126e86 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126e86 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126e86 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x126e8a (movR32M32Effect 0x126e8a 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x126e8a (LoadPre 0x126e8a (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126e8a + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126e8a 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x126e8e (cmpR32R32Effect 0x126e8e 3 13 15) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 15] []) (.flag .CF)) #v[13, 56]
    (.letOp (n := 59) (.out 0x126e8e (cmpR32R32Effect 0x126e8e 3 13 15) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 15] []) (.flag .ZF)) #v[13, 56]
    (.letOp (n := 60) (.exec 0x126e8e (fun s => s.RIP = 0x126e8e) (cmpR32R32Effect 0x126e8e 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l126ea8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l126e93, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126e83 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x45, 0x39, 0xFD, 0x76, 0x15]

theorem code_l126e83 : ∀ x ∈ codeRange 0x126e83 bytes_l126e83, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e83 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126e93 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126e93 (leaR32Effect 0x126e93 4 5 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[15]
    (.letOp (n := 54) (.exec 0x126e93 (fun s => s.RIP = 0x126e93) (leaR32Effect 0x126e93 4 5 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x126e97 (movR32Imm32Effect 0x126e97 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x126e97 (fun s => s.RIP = 0x126e97) (movR32Imm32Effect 0x126e97 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x126e9c (xorR32R32Effect 0x126e9c 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x126e9c (fun s => s.RIP = 0x126e9c) (xorR32R32Effect 0x126e9c 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x126e9e (movR32R32Effect 0x126e9e 3 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 15] []) (.reg (.gpr 10))) #v[15]
    (.letOp (n := 60) (.exec 0x126e9e (fun s => s.RIP = 0x126e9e) (movR32R32Effect 0x126e9e 3 10 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x126ea1 (xorR32R32Effect 0x126ea1 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 62) (.exec 0x126ea1 (fun s => s.RIP = 0x126ea1) (xorR32R32Effect 0x126ea1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 61), (3, 3), (4, 4), (5, 53), (6, 57), (7, 7), (8, 8), (9, 9), (10, 59), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l126e93 : List UInt8 :=
  [0x41, 0x8D, 0x6F, 0x01, 0xB8, 0x03, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x45, 0x89, 0xFA, 0x31, 0xC9,
    0xE9, 0x5E, 0xFF, 0xFF, 0xFF]

theorem code_l126e93 : ∀ x ∈ codeRange 0x126e93 bytes_l126e93, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26e93 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ea8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126ea8 (StorePre 0x126ea8 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126ea8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126ea8 13 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 54) (.out 0x126eac (testR32R32Effect 0x126eac 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 55) (.exec 0x126eac (fun s => s.RIP = 0x126eac) (testR32R32Effect 0x126eac 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l126f85, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l126eb4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126ea8 : List UInt8 :=
  [0x45, 0x89, 0x6E, 0x18, 0x85, 0xED, 0x0F, 0x84, 0xD1, 0x00, 0x00, 0x00]

theorem code_l126ea8 : ∀ x ∈ codeRange 0x126ea8 bytes_l126ea8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ea8 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126eb4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126eb4 (leaR64Effect 0x126eb4 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126eb4 (fun s => s.RIP = 0x126eb4) (leaR64Effect 0x126eb4 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126eb9 (movR64R64Effect 0x126eb9 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x126eb9 (fun s => s.RIP = 0x126eb9) (movR64R64Effect 0x126eb9 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126ebc (movR32Imm32Effect 0x126ebc 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x126ebc (fun s => s.RIP = 0x126ebc) (movR32Imm32Effect 0x126ebc 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x126ec1 (callEffect (fun _ => 0x127b80) 0x126ec6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x126ec1 (PushPre 0x126ec1 5) (callEffect (fun _ => 0x127b80) 0x126ec6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x126ec6⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l126ec6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l126eb4 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF6, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xBA, 0x0C,
    0x00, 0x00]

theorem code_l126eb4 : ∀ x ∈ codeRange 0x126eb4 bytes_l126eb4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26eb4 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ec6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ec6 (movR32M32LowEffect 0x126ec6 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126ec6 (LoadPre 0x126ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ec6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ec6 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126eca (cmpR32Imm8Effect 0x126eca 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126eca (fun s => s.RIP = 0x126eca) (cmpR32Imm8Effect 0x126eca 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126f21, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126ecf, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ec6 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x18, 0x83, 0xFF, 0x02, 0x75, 0x52]

theorem code_l126ec6 : ∀ x ∈ codeRange 0x126ec6 bytes_l126ec6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ec6 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ecf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ecf (movR64M64Effect 0x126ecf 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x126ecf (LoadPre 0x126ecf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126ecf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ecf 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126ed4 (cmpR64Imm8Effect 0x126ed4 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126ed4 (fun s => s.RIP = 0x126ed4) (cmpR64Imm8Effect 0x126ed4 6 0x1) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l127137, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126ede, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ecf : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x83, 0xFE, 0x01, 0x0F, 0x85, 0x59, 0x02, 0x00, 0x00]

theorem code_l126ecf : ∀ x ∈ codeRange 0x126ecf bytes_l126ecf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ecf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ede : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ede (decR32Effect 0x126ede 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x126ede (fun s => s.RIP = 0x126ede) (decR32Effect 0x126ede 2 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 55) (.out 0x126ee0 (movR64M64Effect 0x126ee0 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x126ee0 (LoadPre 0x126ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126ee0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ee0 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126ee5 (movzxR32M8Effect 0x126ee5 4 13 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[55]
    (.letOp (n := 58) (.exec 0x126ee5 (LoadPre 0x126ee5 (fun s => AddrMode.addr (.base 0 .none) s (0x126ee5 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x126ee5 4 13 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x126ee9 (leaR64Effect 0x126ee9 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x126ee9 (fun s => s.RIP = 0x126ee9) (leaR64Effect 0x126ee9 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x126eee (movR64R64Effect 0x126eee 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 62) (.exec 0x126eee (fun s => s.RIP = 0x126eee) (movR64R64Effect 0x126eee 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x126ef1 (movR32R32Effect 0x126ef1 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 64) (.exec 0x126ef1 (fun s => s.RIP = 0x126ef1) (movR32R32Effect 0x126ef1 2 2 5) (Reg.operands [.gpr 5] [])) #v[53]
    (.letOp (n := 65) (.out 0x126ef3 (callEffect (fun _ => 0x127b80) 0x126ef8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x126ef3 (PushPre 0x126ef3 5) (callEffect (fun _ => 0x127b80) 0x126ef8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x126ef8⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(0, 55), (2, 63), (3, 3), (4, 65), (5, 53), (6, 61), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l126ef8, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l126ede : List UInt8 :=
  [0xFF, 0xCD, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x44, 0x0F, 0xB6, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x18,
    0x4C, 0x89, 0xF6, 0x89, 0xEA, 0xE8, 0x88, 0x0C, 0x00, 0x00]

theorem code_l126ede : ∀ x ∈ codeRange 0x126ede bytes_l126ede, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ede 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126ef8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126ef8 (movR32M32LowEffect 0x126ef8 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x126ef8 (LoadPre 0x126ef8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x126ef8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126ef8 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126efc (cmpR32Imm8Effect 0x126efc 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x126efc (fun s => s.RIP = 0x126efc) (cmpR32Imm8Effect 0x126efc 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l126f21, RegMap.args [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l126f01, RegMap.args [(1, 1), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126ef8 : List UInt8 :=
  [0x8B, 0x7C, 0x24, 0x18, 0x83, 0xFF, 0x02, 0x75, 0x20]

theorem code_l126ef8 : ∀ x ∈ codeRange 0x126ef8 bytes_l126ef8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ef8 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f01 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f01 (movR64M64Effect 0x126f01 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126f01 (LoadPre 0x126f01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f01 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126f06 (movR64R64Effect 0x126f06 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x126f06 (fun s => s.RIP = 0x126f06) (movR64R64Effect 0x126f06 0 2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x126f09 (shrR64Effect 0x126f09 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 58) (.exec 0x126f09 (fun s => s.RIP = 0x126f09) (shrR64Effect 0x126f09 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1270a3, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l126f13, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126f01 : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x20, 0x0F, 0x84, 0x90, 0x01,
    0x00, 0x00]

theorem code_l126f01 : ∀ x ∈ codeRange 0x126f01 bytes_l126f01, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f01 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f13 (StorePre 0x126f13 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f13 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f13 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x126f18 (movR32Imm32Effect 0x126f18 5 1 0xc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 55) (.exec 0x126f18 (fun s => s.RIP = 0x126f18) (movR32Imm32Effect 0x126f18 5 1 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x126f1d (xorR32R32Effect 0x126f1d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 57) (.exec 0x126f1d (fun s => s.RIP = 0x126f1d) (xorR32R32Effect 0x126f1d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126f62, RegMap.args [(1, 54), (2, 2), (3, 3), (4, 4), (7, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l126f13 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x10, 0xB9, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xEB, 0x41]

theorem code_l126f13 : ∀ x ∈ codeRange 0x126f13 bytes_l126f13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f13 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f21 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f21 (movR32M32LowEffect 0x126f21 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x126f21 (LoadPre 0x126f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x126f21 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x126f21 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x126f25 (movR64M64Effect 0x126f25 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x126f25 (LoadPre 0x126f25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x126f25 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f25 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x126f2a (movR64M64Effect 0x126f2a 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x126f2a (LoadPre 0x126f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x126f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f2a 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x126f2f (StorePre 0x126f2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x126f2f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f2f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x126f34 (movzxR32M8Effect 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 61) (.exec 0x126f34 (LoadPre 0x126f34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x126f34 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x126f34 6 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x126f3a (movR64M64Effect 0x126f3a 0 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x126f3a (LoadPre 0x126f3a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x126f3a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f3a 0 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x126f3f (StorePre 0x126f3f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x126f3f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f3f 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x126f44 (movR64M64Effect 0x126f44 0 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x126f44 (LoadPre 0x126f44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x126f44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f44 0 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x126f49 (StorePre 0x126f49 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x126f49 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f49 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x126f4e (movR64M64Effect 0x126f4e 0 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x126f4e (LoadPre 0x126f4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x126f4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f4e 0 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x126f53 (StorePre 0x126f53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x126f53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f53 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x126f58 (movR64M64Effect 0x126f58 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x126f58 (LoadPre 0x126f58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x126f58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126f58 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x126f5d (StorePre 0x126f5d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126f5d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x126f5d 0 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.terminate (.br ⟨.l126f62, RegMap.args [(0, 71), (1, 55), (2, 53), (3, 3), (4, 4), (7, 7), (12, 12), (13, 60), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126f21 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x1C, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89,
    0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x31, 0x48, 0x89,
    0x44, 0x24, 0x58, 0x48, 0x8B, 0x44, 0x24, 0x39, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x44,
    0x24, 0x41, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x44, 0x24,
    0x6F]

theorem code_l126f21 : ∀ x ∈ codeRange 0x126f21 bytes_l126f21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f21 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f62 (StorePre 0x126f62 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f62 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x126f62 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x126f66 (movR32R32Effect 0x126f66 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 55) (.exec 0x126f66 (fun s => s.RIP = 0x126f66) (movR32R32Effect 0x126f66 3 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.out 0x126f69 (andR32Imm32Effect 0x126f69 7 8 0xffffff00) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[54]
    (.letOp (n := 57) (.exec 0x126f69 (fun s => s.RIP = 0x126f69) (andR32Imm32Effect 0x126f69 7 8 0xffffff00) (Reg.operands [.gpr 8] [])) #v[54]
    (.letOp (n := 58) (.out 0x126f70 (movR64Imm64Effect 0x126f70 11 0xffffff0000000000) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 59) (.exec 0x126f70 (fun s => s.RIP = 0x126f70) (movR64Imm64Effect 0x126f70 11 0xffffff0000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x126f7a (andR64R64Effect 0x126f7a 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[58, 1]
    (.letOp (n := 61) (.exec 0x126f7a (fun s => s.RIP = 0x126f7a) (andR64R64Effect 0x126f7a 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[58, 1]
    (.terminate (.br ⟨.l126f7d, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 56), (11, 60), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l126f62 : List UInt8 :=
  [0x89, 0x54, 0x24, 0x0C, 0x41, 0x89, 0xD0, 0x41, 0x81, 0xE0, 0x00, 0xFF, 0xFF, 0xFF, 0x49, 0xBB,
    0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xCB]

theorem code_l126f62 : ∀ x ∈ codeRange 0x126f62 bytes_l126f62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f62 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f7d (movR64R64Effect 0x126f7d 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[1]
    (.letOp (n := 54) (.exec 0x126f7d (fun s => s.RIP = 0x126f7d) (movR64R64Effect 0x126f7d 9 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x126f80 (movR64R64Effect 0x126f80 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x126f80 (fun s => s.RIP = 0x126f80) (movR64R64Effect 0x126f80 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l126f9f, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126f7d : List UInt8 :=
  [0x49, 0x89, 0xC9, 0x48, 0x89, 0xC8, 0xEB, 0x1A]

theorem code_l126f7d : ∀ x ∈ codeRange 0x126f7d bytes_l126f7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f7d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f85 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f85 (movR32Imm32Effect 0x126f85 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x126f85 (fun s => s.RIP = 0x126f85) (movR32Imm32Effect 0x126f85 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126f8a (xorR32R32Effect 0x126f8a 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x126f8a (fun s => s.RIP = 0x126f8a) (xorR32R32Effect 0x126f8a 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l126f8d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l126f85 : List UInt8 :=
  [0xB8, 0x0C, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0]

theorem code_l126f85 : ∀ x ∈ codeRange 0x126f85 bytes_l126f85, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f85 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f8d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x126f8d (StorePre 0x126f8d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x126f8d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x126f8d 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x126f95 (xorR32R32Effect 0x126f95 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 55) (.exec 0x126f95 (fun s => s.RIP = 0x126f95) (xorR32R32Effect 0x126f95 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 56) (.out 0x126f97 (xorR32R32Effect 0x126f97 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 57) (.exec 0x126f97 (fun s => s.RIP = 0x126f97) (xorR32R32Effect 0x126f97 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.letOp (n := 58) (.out 0x126f9a (xorR32R32Effect 0x126f9a 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 59) (.exec 0x126f9a (fun s => s.RIP = 0x126f9a) (xorR32R32Effect 0x126f9a 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.terminate (.br ⟨.l126f9d, RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 58), (11, 56), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l126f8d : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x45, 0x31, 0xDB, 0x45, 0x31, 0xC9]

theorem code_l126f8d : ∀ x ∈ codeRange 0x126f8d bytes_l126f8d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f8d 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f9d (xorR32R32Effect 0x126f9d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x126f9d (fun s => s.RIP = 0x126f9d) (xorR32R32Effect 0x126f9d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l126f9f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (7, 53), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l126f9d : List UInt8 :=
  [0x31, 0xFF]

theorem code_l126f9d : ∀ x ∈ codeRange 0x126f9d bytes_l126f9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f9d 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126f9f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126f9f (movR32M32Effect 0x126f9f 10 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[14]
    (.letOp (n := 54) (.exec 0x126f9f (LoadPre 0x126f9f (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126f9f + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126f9f 10 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x126fa3 (movR32M32Effect 0x126fa3 5 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[14]
    (.letOp (n := 56) (.exec 0x126fa3 (LoadPre 0x126fa3 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x126fa3 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x126fa3 5 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[53, 55]
    (.letOp (n := 58) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 5] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x126fa7 (subR32R32Effect 0x126fa7 3 10 5) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 5] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x126fa7 (fun s => s.RIP = 0x126fa7) (subR32R32Effect 0x126fa7 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x126faa (atFlags (condHolds 6) (setccR8Effect 0x126faa 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 2))) #v[2, 58, 59]
    (.letOp (n := 62) (.exec 0x126faa (fun s => s.RIP = 0x126faa) (atFlags (condHolds 6) (setccR8Effect 0x126faa 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[2, 58, 59]
    (.letOp (n := 63) (.out 0x126fad (movR64M64Effect 0x126fad 6 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x126fad (LoadPre 0x126fad (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x126fad + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fad 6 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x126fb5 (StorePre 0x126fb5 3 (fun s => AddrMode.addr (.base 14 .none) s (0x126fb5 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x126fb5 6 (.base 14 .none)) (Reg.operands [.gpr 6, .gpr 14] [])) #v[63, 14]
    (.letOp (n := 66) (.out 0x126fb8 (movR64M64Effect 0x126fb8 6 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 67) (.exec 0x126fb8 (LoadPre 0x126fb8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x126fb8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x126fb8 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x126fc0 (StorePre 0x126fc0 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x126fc0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fc0 6 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.exec 0x126fc4 (StorePre 0x126fc4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x126fc4 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x126fc4 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 70) (.out 0x126fc8 (movR64M64Effect 0x126fc8 15 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 71) (.exec 0x126fc8 (LoadPre 0x126fc8 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x126fc8 15 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.out 0x126fcc (cmpR64Imm8Effect 0x126fcc 15 0x1) (EffectPart.reads (.flag .CF) [.gpr 15] []) (.flag .CF)) #v[70]
    (.letOp (n := 73) (.exec 0x126fcc (fun s => s.RIP = 0x126fcc) (cmpR64Imm8Effect 0x126fcc 15 0x1) (Reg.operands [.gpr 15] [])) #v[70]
    (.letOp (n := 74) (.out 0x126fd0 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126fd0 15 0xff)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[70, 72]
    (.letOp (n := 75) (.exec 0x126fd0 (fun s => s.RIP = 0x126fd0) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x126fd0 15 0xff)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[70, 72]
    (.letOp (n := 76) (.exec 0x126fd4 (StorePre 0x126fd4 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x126fd4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x126fd4 15 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[74, 14]
    (.letOp (n := 77) (.out 0x126fd8 (cmpR32Imm8Effect 0x126fd8 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 78) (.exec 0x126fd8 (fun s => s.RIP = 0x126fd8) (cmpR32Imm8Effect 0x126fd8 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 79) (.out 0x126fdb (atFlags (condHolds 5) (setccR8Effect 0x126fdb 4 15)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 15))) #v[74, 77]
    (.letOp (n := 80) (.exec 0x126fdb (fun s => s.RIP = 0x126fdb) (atFlags (condHolds 5) (setccR8Effect 0x126fdb 4 15)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[74, 77]
    (.letOp (n := 81) (.out 0x126fdf (orR8R8Effect 0x126fdf 3 15 2) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 2] []) (.flag .ZF)) #v[79, 61]
    (.letOp (n := 82) (.exec 0x126fdf (fun s => s.RIP = 0x126fdf) (orR8R8Effect 0x126fdf 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[79, 61]
    (.letOp (n := 83) (.pure (condOp 4)) #v[81]
    (.terminate (.condBr (Fin.last 83) ⟨.l127063, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ ⟨.l126fe4, RegMap.args [(0, 0), (1, 1), (2, 61), (3, 3), (4, 4), (5, 55), (6, 66), (7, 7), (8, 8), (9, 9), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (19, 81), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l126f9f : List UInt8 :=
  [0x45, 0x8B, 0x56, 0x18, 0x41, 0x8B, 0x6E, 0x1C, 0x41, 0x29, 0xEA, 0x0F, 0x96, 0xC2, 0x48, 0x8B,
    0xB4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49, 0x89, 0x36, 0x48, 0x8B, 0xB4, 0x24, 0x98, 0x00, 0x00,
    0x00, 0x49, 0x89, 0x76, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x4D, 0x8B, 0x7E, 0x10, 0x49, 0x83, 0xFF,
    0x01, 0x49, 0x83, 0xD7, 0xFF, 0x4D, 0x89, 0x7E, 0x10, 0x83, 0xFF, 0x02, 0x41, 0x0F, 0x95, 0xC7,
    0x41, 0x08, 0xD7, 0x74, 0x7F]

theorem code_l126f9f : ∀ x ∈ codeRange 0x126f9f bytes_l126f9f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26f9f 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l126fe4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x126fe4 (movR64Imm64Effect 0x126fe4 2 0xff00000000) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x126fe4 (fun s => s.RIP = 0x126fe4) (movR64Imm64Effect 0x126fe4 2 0xff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x126fee (andR64R64Effect 0x126fee 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[9, 53]
    (.letOp (n := 56) (.exec 0x126fee (fun s => s.RIP = 0x126fee) (andR64R64Effect 0x126fee 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[9, 53]
    (.letOp (n := 57) (.out 0x126ff1 (orR64R64Effect 0x126ff1 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[55, 11]
    (.letOp (n := 58) (.exec 0x126ff1 (fun s => s.RIP = 0x126ff1) (orR64R64Effect 0x126ff1 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[55, 11]
    (.letOp (n := 59) (.out 0x126ff4 (movR64M64Effect 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x126ff4 (LoadPre 0x126ff4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6f)) s (0x126ff4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x126ff4 2 (.sib 4 none 0 (.d8 0x6f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x126ff9 (StorePre 0x126ff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f)) s (0x126ff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x126ff9 2 (.sib 4 none 0 (.d32 0x8f))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x127001 (movR64M64Effect 0x127001 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x127001 (LoadPre 0x127001 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x127001 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127001 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x127006 (StorePre 0x127006 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x127006 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127006 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x12700e (movR64M64Effect 0x12700e 2 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x12700e (LoadPre 0x12700e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12700e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12700e 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x127013 (movR64M64Effect 0x127013 10 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 68) (.exec 0x127013 (LoadPre 0x127013 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127013 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127013 10 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x127018 (StorePre 0x127018 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x127018 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x127018 10 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x127020 (StorePre 0x127020 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x127020 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127020 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 71) (.out 0x127025 (cmpR32Imm8Effect 0x127025 3 7 0x2) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 72) (.exec 0x127025 (fun s => s.RIP = 0x127025) (cmpR32Imm8Effect 0x127025 3 7 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l127079, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l12702a, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 57), (10, 67), (11, 11), (13, 13), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l126fe4 : List UInt8 :=
  [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0x49, 0x21, 0xD1, 0x4D, 0x09, 0xD9,
    0x48, 0x8B, 0x54, 0x24, 0x6F, 0x48, 0x89, 0x94, 0x24, 0x8F, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54,
    0x24, 0x68, 0x48, 0x89, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x58, 0x4C,
    0x8B, 0x54, 0x24, 0x60, 0x4C, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24,
    0x78, 0x83, 0xFF, 0x02, 0x75, 0x4F]

theorem code_l126fe4 : ∀ x ∈ codeRange 0x126fe4 bytes_l126fe4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26fe4 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12702a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12702a (andR32Imm32Effect 0x12702a 6 1 0xffffff00) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x12702a (fun s => s.RIP = 0x12702a) (andR32Imm32Effect 0x12702a 6 1 0xffffff00) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x127030 (movzxR32R8Effect 0x127030 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x127030 (fun s => s.RIP = 0x127030) (movzxR32R8Effect 0x127030 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x127033 (orR64R64Effect 0x127033 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x127033 (fun s => s.RIP = 0x127033) (orR64R64Effect 0x127033 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x127036 (orR64R64Effect 0x127036 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[57, 9]
    (.letOp (n := 60) (.exec 0x127036 (fun s => s.RIP = 0x127036) (orR64R64Effect 0x127036 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[57, 9]
    (.letOp (n := 61) (.out 0x127039 (movR32M32LowEffect 0x127039 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x127039 (LoadPre 0x127039 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127039 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127039 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x12703d (movR32M32LowEffect 0x12703d 2 (.sib 4 none 0 (.d8 0x5b))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x12703d (LoadPre 0x12703d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x12703d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12703d 2 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x127041 (StorePre 0x127041 3 (fun s => AddrMode.addr (.base 3 (.d8 0x1c)) s (0x127041 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127041 2 (.base 3 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.exec 0x127044 (StorePre 0x127044 3 (fun s => AddrMode.addr (.base 3 (.d8 0x19)) s (0x127044 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127044 1 (.base 3 (.d8 0x19))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 67) (.exec 0x127047 (StorePre 0x127047 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x127047 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127047 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 68) (.out 0x12704b (movR64M64Effect 0x12704b 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x12704b (LoadPre 0x12704b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12704b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12704b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x127050 (StorePre 0x127050 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127050 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127050 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[68, 3]
    (.letOp (n := 71) (.exec 0x127054 (StorePre 0x127054 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x127054 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127054 4 13 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 72) (.exec 0x127058 (StorePre 0x127058 6 (fun s => AddrMode.addr (.base 3 .none) s (0x127058 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127058 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l126e71, RegMap.args [(0, 68), (1, 61), (2, 63), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l12702a : List UInt8 :=
  [0x81, 0xE1, 0x00, 0xFF, 0xFF, 0xFF, 0x0F, 0xB6, 0xC0, 0x48, 0x09, 0xC8, 0x4C, 0x09, 0xC8, 0x8B,
    0x4C, 0x24, 0x58, 0x8B, 0x54, 0x24, 0x5B, 0x89, 0x53, 0x1C, 0x89, 0x4B, 0x19, 0x48, 0x89, 0x43,
    0x08, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x43, 0x10, 0x44, 0x88, 0x6B, 0x18, 0xC7, 0x03,
    0x02, 0x00, 0x00, 0x00, 0xE9, 0x0E, 0xFE, 0xFF, 0xFF]

theorem code_l12702a : ∀ x ∈ codeRange 0x12702a bytes_l12702a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2702a 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127063 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127063 (StorePre 0x127063 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x127063 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x127063 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x127068 (movR32Imm32Effect 0x127068 5 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x127068 (fun s => s.RIP = 0x127068) (movR32Imm32Effect 0x127068 5 0 0x13) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x12706d (xorR32R32Effect 0x12706d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 57) (.exec 0x12706d (fun s => s.RIP = 0x12706d) (xorR32R32Effect 0x12706d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 58) (.out 0x12706f (movR32R32Effect 0x12706f 3 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 59) (.exec 0x12706f (fun s => s.RIP = 0x12706f) (movR32R32Effect 0x12706f 3 15 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x127072 (xorR32R32Effect 0x127072 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 61) (.exec 0x127072 (fun s => s.RIP = 0x127072) (xorR32R32Effect 0x127072 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 54), (1, 60), (3, 3), (4, 4), (5, 5), (6, 56), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l127063 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0xB8, 0x13, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x41, 0x89, 0xEF, 0x31,
    0xC9, 0xE9, 0x8D, 0xFD, 0xFF, 0xFF]

theorem code_l127063 : ∀ x ∈ codeRange 0x127063 bytes_l127063, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27063 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127079 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127079 (movzxR32M8Effect 0x127079 6 15 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x127079 (LoadPre 0x127079 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127079 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x127079 6 15 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12707f (orR32R32Effect 0x12707f 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[53, 8]
    (.letOp (n := 56) (.exec 0x12707f (fun s => s.RIP = 0x12707f) (orR32R32Effect 0x12707f 3 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[53, 8]
    (.letOp (n := 57) (.out 0x127082 (shrR64Effect 0x127082 4 9 32) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 58) (.exec 0x127082 (fun s => s.RIP = 0x127082) (shrR64Effect 0x127082 4 9 32) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 59) (.out 0x127086 (movR64Imm64Effect 0x127086 6 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x127086 (fun s => s.RIP = 0x127086) (movR64Imm64Effect 0x127086 6 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x127090 (movR64M64Effect 0x127090 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x127090 (LoadPre 0x127090 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127090 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127090 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x127095 (andR64R64Effect 0x127095 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[59, 61]
    (.letOp (n := 64) (.exec 0x127095 (fun s => s.RIP = 0x127095) (andR64R64Effect 0x127095 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[59, 61]
    (.letOp (n := 65) (.out 0x127098 (movR32R32Effect 0x127098 3 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 66) (.exec 0x127098 (fun s => s.RIP = 0x127098) (movR32R32Effect 0x127098 3 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x12709b (movR32R32Effect 0x12709b 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[57]
    (.letOp (n := 68) (.exec 0x12709b (fun s => s.RIP = 0x12709b) (movR32R32Effect 0x12709b 3 5 9) (Reg.operands [.gpr 9] [])) #v[57]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 67), (6, 63), (7, 7), (8, 8), (9, 57), (10, 61), (11, 11), (12, 65), (13, 13), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l127079 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x0C, 0x45, 0x09, 0xC7, 0x49, 0xC1, 0xE9, 0x20, 0x48, 0xBE, 0x00,
    0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4C, 0x8B, 0x54, 0x24, 0x10, 0x4C, 0x21, 0xD6, 0x41,
    0x89, 0xFC, 0x44, 0x89, 0xCD, 0xE9, 0x63, 0xFD, 0xFF, 0xFF]

theorem code_l127079 : ∀ x ∈ codeRange 0x127079 bytes_l127079, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27079 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270a3 (movR64Imm64Effect 0x1270a3 9 0x200000000) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x1270a3 (fun s => s.RIP = 0x1270a3) (movR64Imm64Effect 0x1270a3 9 0x200000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1270ad (movR32Imm32Effect 0x1270ad 5 0 0x15) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1270ad (fun s => s.RIP = 0x1270ad) (movR32Imm32Effect 0x1270ad 5 0 0x15) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1270b2 (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 58) (.out 0x1270b2 (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 59) (.exec 0x1270b2 (fun s => s.RIP = 0x1270b2) (cmpR8Imm8Effect 0x1270b2 4 13 0x7) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.pure (condOp 7)) #v[57, 58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1270ca, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1270b8, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1270a3 : List UInt8 :=
  [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0xB8, 0x15, 0x00, 0x00, 0x00, 0x41,
    0x80, 0xFD, 0x07, 0x77, 0x12]

theorem code_l1270a3 : ∀ x ∈ codeRange 0x1270a3 bytes_l1270a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270a3 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270b8 (testR8R8Effect 0x1270b8 3 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 54) (.exec 0x1270b8 (fun s => s.RIP = 0x1270b8) (testR8R8Effect 0x1270b8 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.out 0x1270bb (atFlags (condHolds 5) (setccR8Effect 0x1270bb 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[1, 53]
    (.letOp (n := 56) (.exec 0x1270bb (fun s => s.RIP = 0x1270bb) (atFlags (condHolds 5) (setccR8Effect 0x1270bb 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1, 53]
    (.letOp (n := 57) (.out 0x1270be (testR64R64Effect 0x1270be 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 58) (.exec 0x1270be (fun s => s.RIP = 0x1270be) (testR64R64Effect 0x1270be 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x1270c1 (atFlags (condHolds 4) (setccR8Effect 0x1270c1 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 60) (.exec 0x1270c1 (fun s => s.RIP = 0x1270c1) (atFlags (condHolds 4) (setccR8Effect 0x1270c1 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[6, 57]
    (.letOp (n := 61) (.out 0x1270c5 (testR8R8Effect 0x1270c5 3 1 6) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 6] []) (.flag .ZF)) #v[55, 59]
    (.letOp (n := 62) (.exec 0x1270c5 (fun s => s.RIP = 0x1270c5) (testR8R8Effect 0x1270c5 3 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[55, 59]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l1270df, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1270ca, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 59), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1270b8 : List UInt8 :=
  [0x45, 0x84, 0xED, 0x0F, 0x95, 0xC1, 0x48, 0x85, 0xD2, 0x40, 0x0F, 0x94, 0xC6, 0x40, 0x84, 0xF1,
    0x74, 0x15]

theorem code_l1270b8 : ∀ x ∈ codeRange 0x1270b8 bytes_l1270b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270b8 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270ca (xorR32R32Effect 0x1270ca 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x1270ca (fun s => s.RIP = 0x1270ca) (xorR32R32Effect 0x1270ca 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.exec 0x1270cd (StorePre 0x1270cd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1270cd + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1270cd 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1270d5 (xorR32R32Effect 0x1270d5 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 57) (.exec 0x1270d5 (fun s => s.RIP = 0x1270d5) (xorR32R32Effect 0x1270d5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 58) (.out 0x1270d7 (xorR32R32Effect 0x1270d7 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 59) (.exec 0x1270d7 (fun s => s.RIP = 0x1270d7) (xorR32R32Effect 0x1270d7 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.terminate (.br ⟨.l126f9d, RegMap.args [(0, 0), (1, 56), (2, 2), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1270ca : List UInt8 :=
  [0x45, 0x31, 0xC0, 0xC7, 0x44, 0x24, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x45, 0x31, 0xDB,
    0xE9, 0xBE, 0xFE, 0xFF, 0xFF]

theorem code_l1270ca : ∀ x ∈ codeRange 0x1270ca bytes_l1270ca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270ca 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270df (movzxR32R8Effect 0x1270df 4 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x1270df (fun s => s.RIP = 0x1270df) (movzxR32R8Effect 0x1270df 4 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1270e3 (leaR64Effect 0x1270e3 1 (.abs (some 2) 3 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 56) (.exec 0x1270e3 (fun s => s.RIP = 0x1270e3) (leaR64Effect 0x1270e3 1 (.abs (some 2) 3 0x0)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x1270eb (xorR32R32Effect 0x1270eb 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 58) (.exec 0x1270eb (fun s => s.RIP = 0x1270eb) (xorR32R32Effect 0x1270eb 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 59) (.out 0x1270ee (cmpR64R64Effect 0x1270ee 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[55, 53]
    (.letOp (n := 60) (.exec 0x1270ee (fun s => s.RIP = 0x1270ee) (cmpR64R64Effect 0x1270ee 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 53]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1270fd, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l1270f3, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (7, 7), (8, 57), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1270df : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0xC5, 0x48, 0x8D, 0x0C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC0, 0x48,
    0x39, 0xC1, 0x73, 0x0A]

theorem code_l1270df : ∀ x ∈ codeRange 0x1270df bytes_l1270df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270df 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1270f3 (movR32Imm32Effect 0x1270f3 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1270f3 (fun s => s.RIP = 0x1270f3) (movR32Imm32Effect 0x1270f3 5 0 0xc) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l126f8d, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1270f3 : List UInt8 :=
  [0xB8, 0x0C, 0x00, 0x00, 0x00, 0xE9, 0x90, 0xFE, 0xFF, 0xFF]

theorem code_l1270f3 : ∀ x ∈ codeRange 0x1270f3 bytes_l1270f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270f3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1270fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1270fd (StorePre 0x1270fd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1270fd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1270fd 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.out 0x127102 (movR64M64Effect 0x127102 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 55) (.exec 0x127102 (LoadPre 0x127102 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127102 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127102 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x127107 (movR64Imm64Effect 0x127107 11 0xffffff0000000000) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 57) (.exec 0x127107 (fun s => s.RIP = 0x127107) (movR64Imm64Effect 0x127107 11 0xffffff0000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x127111 (andR64R64Effect 0x127111 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[56, 54]
    (.letOp (n := 59) (.exec 0x127111 (fun s => s.RIP = 0x127111) (andR64R64Effect 0x127111 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[56, 54]
    (.letOp (n := 60) (.out 0x127114 (movR32Imm32Effect 0x127114 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 61) (.exec 0x127114 (fun s => s.RIP = 0x127114) (movR32Imm32Effect 0x127114 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.exec 0x127119 (StorePre 0x127119 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x127119 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x127119 8 (.sib 4 none 0 (.d8 0xc)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l126f7d, RegMap.args [(1, 54), (2, 2), (3, 3), (4, 4), (7, 60), (8, 8), (11, 58), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1270fd : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x20, 0x49, 0xBB, 0x00, 0x00, 0x00, 0x00,
    0x00, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xCB, 0xBF, 0x02, 0x00, 0x00, 0x00, 0xC7, 0x44, 0x24, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0xE9, 0x57, 0xFE, 0xFF, 0xFF]

theorem code_l1270fd : ∀ x ∈ codeRange 0x1270fd bytes_l1270fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270fd 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127126 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127126 (xorR32R32Effect 0x127126 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 54) (.exec 0x127126 (fun s => s.RIP = 0x127126) (xorR32R32Effect 0x127126 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 55) (.out 0x127129 (movR32Imm32Effect 0x127129 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x127129 (fun s => s.RIP = 0x127129) (movR32Imm32Effect 0x127129 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x12712e (xorR32R32Effect 0x12712e 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 58) (.exec 0x12712e (fun s => s.RIP = 0x12712e) (xorR32R32Effect 0x12712e 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 59) (.out 0x127130 (xorR32R32Effect 0x127130 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 60) (.exec 0x127130 (fun s => s.RIP = 0x127130) (xorR32R32Effect 0x127130 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.terminate (.br ⟨.l126e06, RegMap.args [(0, 55), (1, 59), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127126 : List UInt8 :=
  [0x45, 0x31, 0xE4, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x31, 0xC9, 0xE9, 0xCF, 0xFC, 0xFF,
    0xFF]

theorem code_l127126 : ∀ x ∈ codeRange 0x127126 bytes_l127126, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27126 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127137 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127137 (movR32Imm32Effect 0x127137 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x127137 (fun s => s.RIP = 0x127137) (movR32Imm32Effect 0x127137 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12713c (movR64Imm32Effect 0x12713c 2 0x2036e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x12713c (fun s => s.RIP = 0x12713c) (movR64Imm32Effect 0x12713c 2 0x2036e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x127143 (callEffect (fun _ => 0x129c90) 0x127148) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x127143 (PushPre 0x127143 5) (callEffect (fun _ => 0x129c90) 0x127148) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x127148⟩) #v[]
    (.terminate (.call ⟨.l129c90, RegMap.args [(2, 55), (4, 57), (5, 5), (6, 6), (7, 53)] 60⟩ { target := .l127148, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l127137 : List UInt8 :=
  [0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0xE0, 0x36, 0x20, 0x00, 0xE8, 0x48, 0x2B, 0x00,
    0x00]

theorem code_l127137 : ∀ x ∈ codeRange 0x127137 bytes_l127137, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27137 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127148 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127148 (fun s => s.RIP = 0x127148) (fun _ => nopEffect 0x127148 8) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127150, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l127148 : List UInt8 :=
  [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l127148 : ∀ x ∈ codeRange 0x127148 bytes_l127148, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27148 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127150 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127150 (pushR64Effect 0x127150 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x127150 (PushPre 0x127150 1) (pushR64Effect 0x127150 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x127151 (pushR64Effect 0x127151 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x127151 (PushPre 0x127151 2) (pushR64Effect 0x127151 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x127153 (pushR64Effect 0x127153 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x127153 (PushPre 0x127153 2) (pushR64Effect 0x127153 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x127155 (pushR64Effect 0x127155 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x127155 (PushPre 0x127155 2) (pushR64Effect 0x127155 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x127157 (pushR64Effect 0x127157 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x127157 (PushPre 0x127157 2) (pushR64Effect 0x127157 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x127159 (pushR64Effect 0x127159 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x127159 (PushPre 0x127159 1) (pushR64Effect 0x127159 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x12715a (subR64Imm32Effect 0x12715a 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x12715a (fun s => s.RIP = 0x12715a) (subR64Imm32Effect 0x12715a 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x127161 (movR64R64Effect 0x127161 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x127161 (fun s => s.RIP = 0x127161) (movR64R64Effect 0x127161 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x127164 (movR32M32LowEffect 0x127164 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 70) (.exec 0x127164 (LoadPre 0x127164 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x127164 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127164 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x127167 (movR32M32Effect 0x127167 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 72) (.exec 0x127167 (LoadPre 0x127167 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127167 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127167 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x12716b (movR32R32Effect 0x12716b 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 74) (.exec 0x12716b (fun s => s.RIP = 0x12716b) (movR32R32Effect 0x12716b 3 13 15) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 75) (.out 0x12716e (addR32R32Effect 0x12716e 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[73, 69]
    (.letOp (n := 76) (.out 0x12716e (addR32R32Effect 0x12716e 3 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[73, 69]
    (.letOp (n := 77) (.exec 0x12716e (fun s => s.RIP = 0x12716e) (addR32R32Effect 0x12716e 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[73, 69]
    (.letOp (n := 78) (.pure (condOp 2)) #v[76]
    (.terminate (.condBr (Fin.last 78) ⟨.l1273aa, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ ⟨.l127177, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 75), (14, 14), (15, 71), (16, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l127150 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x8B, 0x6A, 0x08, 0x44, 0x8B, 0x7E, 0x1C, 0x45, 0x89, 0xFD, 0x41, 0x01,
    0xED, 0x0F, 0x82, 0x33, 0x02, 0x00, 0x00]

theorem code_l127150 : ∀ x ∈ codeRange 0x127150 bytes_l127150, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27150 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127177 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127177 (movR64R64Effect 0x127177 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 54) (.exec 0x127177 (fun s => s.RIP = 0x127177) (movR64R64Effect 0x127177 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12717a (movR64M64Effect 0x12717a 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x12717a (LoadPre 0x12717a (fun s => AddrMode.addr (.base 6 .none) s (0x12717a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12717a 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x12717d (movR64M64Effect 0x12717d 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 58) (.exec 0x12717d (LoadPre 0x12717d (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12717d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12717d 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x127181 (leaR64Effect 0x127181 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x127181 (fun s => s.RIP = 0x127181) (leaR64Effect 0x127181 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x127186 (StorePre 0x127186 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127186 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127186 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 62) (.out 0x12718b (movR64R64Effect 0x12718b 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 63) (.exec 0x12718b (fun s => s.RIP = 0x12718b) (movR64R64Effect 0x12718b 2 12) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 64) (.out 0x12718e (movR32R32Effect 0x12718e 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 65) (.exec 0x12718e (fun s => s.RIP = 0x12718e) (movR32R32Effect 0x12718e 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x127191 (callEffect (fun _ => 0x127c50) 0x127196) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x127191 (PushPre 0x127191 5) (callEffect (fun _ => 0x127c50) 0x127196) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x127196⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 64), (2, 62), (3, 3), (4, 66), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l127196, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l127177 : List UInt8 :=
  [0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48,
    0x89, 0x74, 0x24, 0x40, 0x4C, 0x89, 0xE2, 0x44, 0x89, 0xE9, 0xE8, 0xBA, 0x0A, 0x00, 0x00]

theorem code_l127177 : ∀ x ∈ codeRange 0x127177 bytes_l127177, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27177 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127196 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127196 (movR32M32LowEffect 0x127196 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x127196 (LoadPre 0x127196 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127196 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127196 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12719a (cmpR32Imm8Effect 0x12719a 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12719a (fun s => s.RIP = 0x12719a) (cmpR32Imm8Effect 0x12719a 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1271c1, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12719f, RegMap.args [(1, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l127196 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x83, 0xF9, 0x02, 0x75, 0x22]

theorem code_l127196 : ∀ x ∈ codeRange 0x127196 bytes_l127196, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27196 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12719f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12719f (movR64M64Effect 0x12719f 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12719f (LoadPre 0x12719f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x12719f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12719f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1271a4 (movR64M64Effect 0x1271a4 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1271a4 (LoadPre 0x1271a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1271a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271a4 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1271a9 (StorePre 0x1271a9 3 (fun s => AddrMode.addr (.base 14 .none) s (0x1271a9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1271a9 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x1271ac (StorePre 0x1271ac 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1271ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1271ac 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1271b0 (movR64M64Effect 0x1271b0 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x1271b0 (LoadPre 0x1271b0 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1271b0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1271b0 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1271b4 (cmpR64Imm8Effect 0x1271b4 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x1271b4 (cmpR64Imm8Effect 0x1271b4 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x1271b4 (fun s => s.RIP = 0x1271b4) (cmpR64Imm8Effect 0x1271b4 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l127206, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1271ba, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12719f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x4C]

theorem code_l12719f : ∀ x ∈ codeRange 0x12719f bytes_l12719f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2719f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1271ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1271ba (movR32Imm32Effect 0x1271ba 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1271ba (fun s => s.RIP = 0x1271ba) (movR32Imm32Effect 0x1271ba 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127222, RegMap.args [(0, 53), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1271ba : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x61]

theorem code_l1271ba : ∀ x ∈ codeRange 0x1271ba bytes_l1271ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x271ba 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1271c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1271c1 (movR32M32LowEffect 0x1271c1 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1271c1 (LoadPre 0x1271c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1271c1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1271c1 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1271c5 (movR64M64Effect 0x1271c5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1271c5 (LoadPre 0x1271c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1271c5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271c5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1271ca (movR64M64Effect 0x1271ca 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1271ca (LoadPre 0x1271ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1271ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271ca 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1271cf (movR64M64Effect 0x1271cf 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1271cf (LoadPre 0x1271cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1271cf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271cf 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1271d4 (StorePre 0x1271d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1271d4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271d4 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1271d9 (movR64M64Effect 0x1271d9 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x1271d9 (LoadPre 0x1271d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1271d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271d9 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1271de (StorePre 0x1271de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1271de + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271de 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1271e3 (movR64M64Effect 0x1271e3 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x1271e3 (LoadPre 0x1271e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1271e3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271e3 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1271e8 (StorePre 0x1271e8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1271e8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271e8 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1271ed (movR64M64Effect 0x1271ed 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x1271ed (LoadPre 0x1271ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1271ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1271ed 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1271f2 (StorePre 0x1271f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1271f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1271f2 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1271f7 (movR64Imm64Effect 0x1271f7 9 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 72) (.exec 0x1271f7 (fun s => s.RIP = 0x1271f7) (movR64Imm64Effect 0x1271f7 9 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x127201 (andR64R64Effect 0x127201 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[71, 57]
    (.letOp (n := 74) (.exec 0x127201 (fun s => s.RIP = 0x127201) (andR64R64Effect 0x127201 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[71, 57]
    (.terminate (.br ⟨.l127230, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 68), (7, 57), (9, 73), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l1271c1 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x8B,
    0x74, 0x24, 0x20, 0x48, 0x89, 0x74, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x89, 0x74,
    0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x89, 0x74, 0x24, 0x58, 0x48, 0x8B, 0x74, 0x24,
    0x38, 0x48, 0x89, 0x74, 0x24, 0x60, 0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF,
    0x49, 0x21, 0xF9, 0xEB, 0x2A]

theorem code_l1271c1 : ∀ x ∈ codeRange 0x1271c1 bytes_l1271c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x271c1 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127206 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127206 (incR64Effect 0x127206 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x127206 (fun s => s.RIP = 0x127206) (incR64Effect 0x127206 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x127209 (StorePre 0x127209 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127209 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127209 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x12720d (movR32M32Effect 0x12720d 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x12720d (LoadPre 0x12720d (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12720d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12720d 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x127211 (cmpR32R32Effect 0x127211 3 13 15) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 15] []) (.flag .CF)) #v[13, 56]
    (.letOp (n := 59) (.out 0x127211 (cmpR32R32Effect 0x127211 3 13 15) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 15] []) (.flag .ZF)) #v[13, 56]
    (.letOp (n := 60) (.exec 0x127211 (fun s => s.RIP = 0x127211) (cmpR32R32Effect 0x127211 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l12727b, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l127216, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l127206 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x45, 0x39, 0xFD, 0x76, 0x65]

theorem code_l127206 : ∀ x ∈ codeRange 0x127206 bytes_l127206, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27206 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127216 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127216 (leaR32Effect 0x127216 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x127216 (fun s => s.RIP = 0x127216) (leaR32Effect 0x127216 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x12721a (shlR64Effect 0x12721a 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12721a (fun s => s.RIP = 0x12721a) (shlR64Effect 0x12721a 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12721e (orR64Imm8Effect 0x12721e 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x12721e (fun s => s.RIP = 0x12721e) (orR64Imm8Effect 0x12721e 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l127222, RegMap.args [(0, 57), (3, 3), (4, 4), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l127216 : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l127216 : ∀ x ∈ codeRange 0x127216 bytes_l127216, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27216 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127222 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127222 (movR32Imm32Effect 0x127222 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x127222 (fun s => s.RIP = 0x127222) (movR32Imm32Effect 0x127222 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x127227 (xorR32R32Effect 0x127227 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 56) (.exec 0x127227 (fun s => s.RIP = 0x127227) (xorR32R32Effect 0x127227 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 57) (.out 0x12722a (movR32R32Effect 0x12722a 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x12722a (fun s => s.RIP = 0x12722a) (movR32R32Effect 0x12722a 3 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x12722d (movR32R32Effect 0x12722d 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 60) (.exec 0x12722d (fun s => s.RIP = 0x12722d) (movR32R32Effect 0x12722d 3 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l127230, RegMap.args [(0, 0), (1, 53), (2, 57), (3, 3), (4, 4), (7, 59), (9, 55), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127222 : List UInt8 :=
  [0xB9, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC9, 0x44, 0x89, 0xFA, 0x44, 0x89, 0xFF]

theorem code_l127222 : ∀ x ∈ codeRange 0x127222 bytes_l127222, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27222 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127230 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127230 (movR32R32Effect 0x127230 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 54) (.exec 0x127230 (fun s => s.RIP = 0x127230) (movR32R32Effect 0x127230 2 6 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127232 (orR64R64Effect 0x127232 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[53, 9]
    (.letOp (n := 56) (.exec 0x127232 (fun s => s.RIP = 0x127232) (orR64R64Effect 0x127232 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[53, 9]
    (.letOp (n := 57) (.out 0x127235 (movR64M64Effect 0x127235 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x127235 (LoadPre 0x127235 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127235 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127235 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x12723a (StorePre 0x12723a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x12723a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12723a 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x12723e (movR64M64Effect 0x12723e 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x12723e (LoadPre 0x12723e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x12723e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12723e 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x127243 (StorePre 0x127243 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x127243 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127243 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x127247 (movR64M64Effect 0x127247 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x127247 (LoadPre 0x127247 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127247 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127247 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x12724c (movR64M64Effect 0x12724c 8 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 66) (.exec 0x12724c (LoadPre 0x12724c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12724c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12724c 8 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x127251 (StorePre 0x127251 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x127251 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127251 8 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.exec 0x127255 (StorePre 0x127255 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x127255 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127255 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 69) (.exec 0x127259 (StorePre 0x127259 2 (fun s => AddrMode.addr (.base 3 .none) s (0x127259 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x127259 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 70) (.exec 0x12725b (StorePre 0x12725b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12725b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12725b 2 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 71) (.exec 0x12725e (StorePre 0x12725e 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12725e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12725e 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 72) (.exec 0x127262 (StorePre 0x127262 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127262 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127262 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l127266, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 63), (8, 65), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l127230 : List UInt8 :=
  [0x89, 0xFE, 0x4C, 0x09, 0xCE, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7B, 0x30, 0x48, 0x8B,
    0x7C, 0x24, 0x58, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24, 0x48, 0x4C, 0x8B, 0x44, 0x24,
    0x50, 0x4C, 0x89, 0x43, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x0B, 0x89, 0x53, 0x04, 0x48, 0x89,
    0x43, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l127230 : ∀ x ∈ codeRange 0x127230 bytes_l127230, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27230 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127266 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127266 (movR64R64Effect 0x127266 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x127266 (fun s => s.RIP = 0x127266) (movR64R64Effect 0x127266 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x127269 (addR64Imm32Effect 0x127269 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x127269 (fun s => s.RIP = 0x127269) (addR64Imm32Effect 0x127269 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x127270 (popR64Effect 0x127270 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x127270 (popR64Effect 0x127270 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x127270 (PopPre 0x127270) (popR64Effect 0x127270 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x127271 (popR64Effect 0x127271 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x127271 (popR64Effect 0x127271 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x127271 (PopPre 0x127271) (popR64Effect 0x127271 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x127273 (popR64Effect 0x127273 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x127273 (popR64Effect 0x127273 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x127273 (PopPre 0x127273) (popR64Effect 0x127273 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x127275 (popR64Effect 0x127275 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x127275 (popR64Effect 0x127275 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x127275 (PopPre 0x127275) (popR64Effect 0x127275 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x127277 (popR64Effect 0x127277 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x127277 (popR64Effect 0x127277 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x127277 (PopPre 0x127277) (popR64Effect 0x127277 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x127279 (popR64Effect 0x127279 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x127279 (popR64Effect 0x127279 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x127279 (PopPre 0x127279) (popR64Effect 0x127279 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x12727a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x12727a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x12727a (RetPre 0x12727a) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l127266 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l127266 : ∀ x ∈ codeRange 0x127266 bytes_l127266, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27266 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12727b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12727b (StorePre 0x12727b 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12727b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12727b 13 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 54) (.out 0x12727f (leaR64Effect 0x12727f 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x12727f (fun s => s.RIP = 0x12727f) (leaR64Effect 0x12727f 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x127284 (movR64R64Effect 0x127284 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 57) (.exec 0x127284 (fun s => s.RIP = 0x127284) (movR64R64Effect 0x127284 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x127287 (movR32R32Effect 0x127287 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 59) (.exec 0x127287 (fun s => s.RIP = 0x127287) (movR32R32Effect 0x127287 2 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x127289 (callEffect (fun _ => 0x127b80) 0x12728e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x127289 (PushPre 0x127289 5) (callEffect (fun _ => 0x127b80) 0x12728e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x12728e⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l12728e, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l12727b : List UInt8 :=
  [0x45, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0x89, 0xEA, 0xE8, 0xF2,
    0x08, 0x00, 0x00]

theorem code_l12727b : ∀ x ∈ codeRange 0x12727b bytes_l12727b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2727b 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12728e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12728e (movR32M32LowEffect 0x12728e 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12728e (LoadPre 0x12728e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12728e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12728e 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127292 (cmpR32Imm8Effect 0x127292 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x127292 (fun s => s.RIP = 0x127292) (cmpR32Imm8Effect 0x127292 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1272bf, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l127297, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12728e : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x83, 0xF9, 0x02, 0x75, 0x28]

theorem code_l12728e : ∀ x ∈ codeRange 0x12728e bytes_l12728e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2728e 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127297 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127297 (movR64M64Effect 0x127297 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x127297 (LoadPre 0x127297 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x127297 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127297 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12729c (xorR32R32Effect 0x12729c 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 56) (.exec 0x12729c (fun s => s.RIP = 0x12729c) (xorR32R32Effect 0x12729c 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 57) (.out 0x12729e (movR64R64Effect 0x12729e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x12729e (fun s => s.RIP = 0x12729e) (movR64R64Effect 0x12729e 0 6) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 59) (.out 0x1272a1 (shrR64Effect 0x1272a1 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[57]
    (.letOp (n := 60) (.exec 0x1272a1 (fun s => s.RIP = 0x1272a1) (shrR64Effect 0x1272a1 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x1272a5 (atFlags (condHolds 4) (setccR8Effect 0x1272a5 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[2, 59]
    (.letOp (n := 62) (.exec 0x1272a5 (fun s => s.RIP = 0x1272a5) (atFlags (condHolds 4) (setccR8Effect 0x1272a5 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[2, 59]
    (.letOp (n := 63) (.out 0x1272a8 (movR32Imm32Effect 0x1272a8 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 64) (.exec 0x1272a8 (fun s => s.RIP = 0x1272a8) (movR32Imm32Effect 0x1272a8 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1272ad (movR64M64Effect 0x1272ad 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x1272ad (LoadPre 0x1272ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1272ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ad 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 67) ⟨.l1272b9, RegMap.args [(0, 63), (1, 55), (2, 61), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1272b4, RegMap.args [(0, 63), (1, 55), (2, 61), (3, 3), (4, 4), (6, 53), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l127297 : List UInt8 :=
  [0x48, 0x8B, 0x74, 0x24, 0x18, 0x31, 0xC9, 0x48, 0x89, 0xF0, 0x48, 0xC1, 0xE8, 0x20, 0x0F, 0x94,
    0xC2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x54, 0x24, 0x40, 0x75, 0x05]

theorem code_l127297 : ∀ x ∈ codeRange 0x127297 bytes_l127297, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27297 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1272b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1272b4 (movR64M64Effect 0x1272b4 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1272b4 (LoadPre 0x1272b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1272b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272b4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1272b9, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1272b4 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10]

theorem code_l1272b4 : ∀ x ∈ codeRange 0x1272b4 bytes_l1272b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x272b4 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1272b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1272b9 (movR8R8Effect 0x1272b9 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[2, 1]
    (.letOp (n := 54) (.exec 0x1272b9 (fun s => s.RIP = 0x1272b9) (movR8R8Effect 0x1272b9 2 1 2) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 55) (.out 0x1272bb (addR32R32Effect 0x1272bb 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1272bb (fun s => s.RIP = 0x1272bb) (addR32R32Effect 0x1272bb 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.terminate (.br ⟨.l1272fe, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1272b9 : List UInt8 :=
  [0x88, 0xD1, 0x01, 0xC9, 0xEB, 0x3F]

theorem code_l1272b9 : ∀ x ∈ codeRange 0x1272b9 bytes_l1272b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x272b9 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1272bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1272bf (movR32M32Effect 0x1272bf 8 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x1272bf (LoadPre 0x1272bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1272bf + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1272bf 8 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1272c4 (movR64M64Effect 0x1272c4 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1272c4 (LoadPre 0x1272c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1272c4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272c4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1272c9 (movR64M64Effect 0x1272c9 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x1272c9 (LoadPre 0x1272c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1272c9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272c9 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1272ce (movR64M64Effect 0x1272ce 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1272ce (LoadPre 0x1272ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1272ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ce 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1272d3 (StorePre 0x1272d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1272d3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272d3 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1272d8 (movR64M64Effect 0x1272d8 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x1272d8 (LoadPre 0x1272d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1272d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272d8 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1272dd (StorePre 0x1272dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1272dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272dd 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1272e2 (movR64M64Effect 0x1272e2 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x1272e2 (LoadPre 0x1272e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1272e2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272e2 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1272e7 (StorePre 0x1272e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1272e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1272e7 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1272ec (movR64M64Effect 0x1272ec 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 69) (.exec 0x1272ec (LoadPre 0x1272ec (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1272ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272ec 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1272f1 (StorePre 0x1272f1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1272f1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1272f1 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1272f9 (movR64M64Effect 0x1272f9 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 72) (.exec 0x1272f9 (LoadPre 0x1272f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1272f9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1272f9 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1272fe, RegMap.args [(0, 55), (1, 1), (2, 68), (3, 3), (4, 4), (6, 57), (8, 53), (9, 9), (10, 71), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l1272bf : List UInt8 :=
  [0x44, 0x8B, 0x44, 0x24, 0x0C, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48,
    0x8B, 0x54, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x68, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89,
    0x54, 0x24, 0x70, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x8B, 0x54,
    0x24, 0x38, 0x48, 0x89, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x54, 0x24, 0x40]

theorem code_l1272bf : ∀ x ∈ codeRange 0x1272bf bytes_l1272bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x272bf 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1272fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1272fe (movR32M32Effect 0x1272fe 7 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x1272fe (LoadPre 0x1272fe (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1272fe + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1272fe 7 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x127302 (movR32M32Effect 0x127302 2 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 56) (.exec 0x127302 (LoadPre 0x127302 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x127302 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127302 2 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x127306 (subR32R32Effect 0x127306 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[53, 55]
    (.letOp (n := 58) (.out 0x127306 (subR32R32Effect 0x127306 2 7 2) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 2] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 59) (.out 0x127306 (subR32R32Effect 0x127306 2 7 2) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 2] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 60) (.exec 0x127306 (fun s => s.RIP = 0x127306) (subR32R32Effect 0x127306 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[53, 55]
    (.letOp (n := 61) (.out 0x127308 (atFlags (condHolds 6) (setccR8Effect 0x127308 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 9))) #v[9, 58, 59]
    (.letOp (n := 62) (.exec 0x127308 (fun s => s.RIP = 0x127308) (atFlags (condHolds 6) (setccR8Effect 0x127308 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[9, 58, 59]
    (.letOp (n := 63) (.exec 0x12730c (StorePre 0x12730c 3 (fun s => AddrMode.addr (.base 14 .none) s (0x12730c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12730c 10 (.base 14 .none)) (Reg.operands [.gpr 10, .gpr 14] [])) #v[10, 14]
    (.letOp (n := 64) (.exec 0x12730f (StorePre 0x12730f 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x12730f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12730f 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 65) (.exec 0x127313 (StorePre 0x127313 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x127313 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x127313 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 66) (.out 0x127317 (movR64M64Effect 0x127317 10 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[14]
    (.letOp (n := 67) (.exec 0x127317 (LoadPre 0x127317 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127317 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127317 10 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.out 0x12731b (cmpR64Imm8Effect 0x12731b 10 0x1) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[66]
    (.letOp (n := 69) (.exec 0x12731b (fun s => s.RIP = 0x12731b) (cmpR64Imm8Effect 0x12731b 10 0x1) (Reg.operands [.gpr 10] [])) #v[66]
    (.letOp (n := 70) (.out 0x12731f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12731f 10 0xff)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[66, 68]
    (.letOp (n := 71) (.exec 0x12731f (fun s => s.RIP = 0x12731f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x12731f 10 0xff)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[66, 68]
    (.letOp (n := 72) (.exec 0x127323 (StorePre 0x127323 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127323 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127323 10 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 14] [])) #v[70, 14]
    (.letOp (n := 73) (.out 0x127327 (cmpR32Imm8Effect 0x127327 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 74) (.exec 0x127327 (fun s => s.RIP = 0x127327) (cmpR32Imm8Effect 0x127327 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 75) (.out 0x12732a (atFlags (condHolds 5) (setccR8Effect 0x12732a 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 10))) #v[70, 73]
    (.letOp (n := 76) (.exec 0x12732a (fun s => s.RIP = 0x12732a) (atFlags (condHolds 5) (setccR8Effect 0x12732a 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[70, 73]
    (.letOp (n := 77) (.out 0x12732e (orR8R8Effect 0x12732e 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[75, 61]
    (.letOp (n := 78) (.out 0x12732e (orR8R8Effect 0x12732e 3 10 9) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 9] []) (.flag .ZF)) #v[75, 61]
    (.letOp (n := 79) (.exec 0x12732e (fun s => s.RIP = 0x12732e) (orR8R8Effect 0x12732e 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[75, 61]
    (.letOp (n := 80) (.pure (condOp 4)) #v[78]
    (.terminate (.condBr (Fin.last 80) ⟨.l127376, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 77), (11, 11), (12, 12), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ ⟨.l127333, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (6, 6), (7, 57), (8, 8), (9, 61), (10, 77), (11, 11), (12, 12), (14, 14), (15, 15), (19, 78), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩)))))))))))))))))))))))))))))

def bytes_l1272fe : List UInt8 :=
  [0x41, 0x8B, 0x7E, 0x18, 0x41, 0x8B, 0x56, 0x1C, 0x29, 0xD7, 0x41, 0x0F, 0x96, 0xC1, 0x4D, 0x89,
    0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x4D, 0x8B, 0x56, 0x10, 0x49, 0x83, 0xFA,
    0x01, 0x49, 0x83, 0xD2, 0xFF, 0x4D, 0x89, 0x56, 0x10, 0x83, 0xF9, 0x02, 0x41, 0x0F, 0x95, 0xC2,
    0x45, 0x08, 0xCA, 0x74, 0x43]

theorem code_l1272fe : ∀ x ∈ codeRange 0x1272fe bytes_l1272fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x272fe 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127333 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127333 (movR64M64Effect 0x127333 2 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x127333 (LoadPre 0x127333 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x127333 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x127333 2 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x12733b (StorePre 0x12733b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x12733b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12733b 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x127340 (movR64M64Effect 0x127340 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x127340 (LoadPre 0x127340 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x127340 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127340 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x127345 (StorePre 0x127345 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127345 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127345 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x12734a (movR64M64Effect 0x12734a 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x12734a (LoadPre 0x12734a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12734a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12734a 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12734f (movR64M64Effect 0x12734f 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x12734f (LoadPre 0x12734f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x12734f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12734f 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x127354 (StorePre 0x127354 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x127354 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127354 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x127359 (StorePre 0x127359 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127359 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127359 2 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x12735e (cmpR32Imm8Effect 0x12735e 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 66) (.exec 0x12735e (fun s => s.RIP = 0x12735e) (cmpR32Imm8Effect 0x12735e 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 67) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l127393, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l127363, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 3), (4, 4), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l127333 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x8B, 0x54,
    0x24, 0x78, 0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x8B, 0x54, 0x24, 0x68, 0x48, 0x8B, 0x7C, 0x24,
    0x70, 0x48, 0x89, 0x7C, 0x24, 0x50, 0x48, 0x89, 0x54, 0x24, 0x48, 0x83, 0xF9, 0x02, 0x75, 0x30]

theorem code_l127333 : ∀ x ∈ codeRange 0x127333 bytes_l127333, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27333 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127363 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127363 (StorePre 0x127363 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x127363 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127363 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.exec 0x127367 (StorePre 0x127367 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x127367 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127367 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 55) (.exec 0x12736b (StorePre 0x12736b 6 (fun s => AddrMode.addr (.base 3 .none) s (0x12736b + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12736b 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l127266, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127363 : List UInt8 :=
  [0x48, 0x89, 0x43, 0x08, 0x48, 0x89, 0x73, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0xF0,
    0xFE, 0xFF, 0xFF]

theorem code_l127363 : ∀ x ∈ codeRange 0x127363 bytes_l127363, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27363 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127376 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127376 (StorePre 0x127376 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x127376 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x127376 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x12737b (movR64R64Effect 0x12737b 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 55) (.exec 0x12737b (fun s => s.RIP = 0x12737b) (movR64R64Effect 0x12737b 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.out 0x12737e (shlR64Effect 0x12737e 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 57) (.exec 0x12737e (fun s => s.RIP = 0x12737e) (shlR64Effect 0x12737e 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[54]
    (.letOp (n := 58) (.out 0x127382 (orR64Imm8Effect 0x127382 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x127382 (fun s => s.RIP = 0x127382) (orR64Imm8Effect 0x127382 0 0x13) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.out 0x127386 (movR32Imm32Effect 0x127386 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x127386 (fun s => s.RIP = 0x127386) (movR32Imm32Effect 0x127386 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x12738b (xorR32R32Effect 0x12738b 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 63) (.exec 0x12738b (fun s => s.RIP = 0x12738b) (xorR32R32Effect 0x12738b 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.terminate (.br ⟨.l127230, RegMap.args [(0, 58), (1, 60), (2, 2), (3, 3), (4, 4), (7, 7), (9, 62), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l127376 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13,
    0xB9, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC9, 0xE9, 0x9D, 0xFE, 0xFF, 0xFF]

theorem code_l127376 : ∀ x ∈ codeRange 0x127376 bytes_l127376, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27376 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127393 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127393 (movR64Imm64Effect 0x127393 9 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x127393 (fun s => s.RIP = 0x127393) (movR64Imm64Effect 0x127393 9 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12739d (andR64R64Effect 0x12739d 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x12739d (fun s => s.RIP = 0x12739d) (andR64R64Effect 0x12739d 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.out 0x1273a0 (movR32R32Effect 0x1273a0 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 58) (.exec 0x1273a0 (fun s => s.RIP = 0x1273a0) (movR32R32Effect 0x1273a0 3 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 59) (.out 0x1273a3 (movR32R32Effect 0x1273a3 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 60) (.exec 0x1273a3 (fun s => s.RIP = 0x1273a3) (movR32R32Effect 0x1273a3 2 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l127230, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (6, 6), (7, 59), (8, 8), (9, 55), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127393 : List UInt8 :=
  [0x49, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xF1, 0x44, 0x89, 0xC2,
    0x89, 0xF7, 0xE9, 0x86, 0xFE, 0xFF, 0xFF]

theorem code_l127393 : ∀ x ∈ codeRange 0x127393 bytes_l127393, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27393 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1273aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1273aa (xorR32R32Effect 0x1273aa 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x1273aa (fun s => s.RIP = 0x1273aa) (xorR32R32Effect 0x1273aa 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.out 0x1273ac (movR32Imm32Effect 0x1273ac 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1273ac (fun s => s.RIP = 0x1273ac) (movR32Imm32Effect 0x1273ac 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1273b1 (xorR32R32Effect 0x1273b1 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 58) (.exec 0x1273b1 (fun s => s.RIP = 0x1273b1) (xorR32R32Effect 0x1273b1 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.terminate (.br ⟨.l127230, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (7, 7), (9, 57), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1273aa : List UInt8 :=
  [0x31, 0xC9, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x45, 0x31, 0xC9, 0xE9, 0x77, 0xFE, 0xFF, 0xFF]

theorem code_l1273aa : ∀ x ∈ codeRange 0x1273aa bytes_l1273aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x273aa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1273c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1273c0 (pushR64Effect 0x1273c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1273c0 (PushPre 0x1273c0 1) (pushR64Effect 0x1273c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1273c1 (pushR64Effect 0x1273c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1273c1 (PushPre 0x1273c1 2) (pushR64Effect 0x1273c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1273c3 (pushR64Effect 0x1273c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1273c3 (PushPre 0x1273c3 2) (pushR64Effect 0x1273c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1273c5 (pushR64Effect 0x1273c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1273c5 (PushPre 0x1273c5 2) (pushR64Effect 0x1273c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1273c7 (pushR64Effect 0x1273c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1273c7 (PushPre 0x1273c7 2) (pushR64Effect 0x1273c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1273c9 (pushR64Effect 0x1273c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1273c9 (PushPre 0x1273c9 1) (pushR64Effect 0x1273c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1273ca (subR64Imm8Effect 0x1273ca 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1273ca (fun s => s.RIP = 0x1273ca) (subR64Imm8Effect 0x1273ca 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1273ce (movR64R64Effect 0x1273ce 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x1273ce (fun s => s.RIP = 0x1273ce) (movR64R64Effect 0x1273ce 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1273d1 (movR32M32Effect 0x1273d1 15 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x1273d1 (LoadPre 0x1273d1 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x1273d1 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1273d1 15 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1273d5 (movR32M32LowEffect 0x1273d5 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 72) (.exec 0x1273d5 (LoadPre 0x1273d5 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1273d5 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1273d5 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x1273d8 (addR32R32Effect 0x1273d8 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[71, 69]
    (.letOp (n := 74) (.out 0x1273d8 (addR32R32Effect 0x1273d8 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x1273d8 (fun s => s.RIP = 0x1273d8) (addR32R32Effect 0x1273d8 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[71, 69]
    (.letOp (n := 76) (.pure (condOp 2)) #v[74]
    (.terminate (.condBr (Fin.last 76) ⟨.l1275d4, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩ ⟨.l1273e1, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 65), (5, 73), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (16, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1273c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x48, 0x89,
    0xFB, 0x44, 0x8B, 0x7E, 0x1C, 0x8B, 0x6A, 0x08, 0x44, 0x01, 0xFD, 0x0F, 0x82, 0xF3, 0x01, 0x00,
    0x00]

theorem code_l1273c0 : ∀ x ∈ codeRange 0x1273c0 bytes_l1273c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x273c0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1273e1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1273e1 (movR64R64Effect 0x1273e1 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 54) (.exec 0x1273e1 (fun s => s.RIP = 0x1273e1) (movR64R64Effect 0x1273e1 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1273e4 (movR64R64Effect 0x1273e4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 56) (.exec 0x1273e4 (fun s => s.RIP = 0x1273e4) (movR64R64Effect 0x1273e4 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1273e7 (movR64M64Effect 0x1273e7 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 58) (.exec 0x1273e7 (LoadPre 0x1273e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1273e7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1273e7 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1273ea (movR64M64Effect 0x1273ea 12 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 60) (.exec 0x1273ea (LoadPre 0x1273ea (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1273ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1273ea 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 61) (.out 0x1273ee (leaR64Effect 0x1273ee 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x1273ee (fun s => s.RIP = 0x1273ee) (leaR64Effect 0x1273ee 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1273f3 (StorePre 0x1273f3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1273f3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1273f3 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 64) (.out 0x1273f8 (movR64R64Effect 0x1273f8 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 65) (.exec 0x1273f8 (fun s => s.RIP = 0x1273f8) (movR64R64Effect 0x1273f8 2 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 66) (.out 0x1273fb (movR32R32Effect 0x1273fb 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 67) (.exec 0x1273fb (fun s => s.RIP = 0x1273fb) (movR32R32Effect 0x1273fb 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.out 0x1273fd (callEffect (fun _ => 0x127c50) 0x127402) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x1273fd (PushPre 0x1273fd 5) (callEffect (fun _ => 0x127c50) 0x127402) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x127402⟩) #v[]
    (.terminate (.call ⟨.l127c50, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 68), (5, 5), (6, 57), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l127402, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l1273e1 : List UInt8 :=
  [0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x48, 0x8B, 0x36, 0x4D, 0x8B, 0x66, 0x08, 0x48, 0x8D, 0x7C,
    0x24, 0x20, 0x48, 0x89, 0x74, 0x24, 0x58, 0x4C, 0x89, 0xE2, 0x89, 0xE9, 0xE8, 0x4E, 0x08, 0x00,
    0x00]

theorem code_l1273e1 : ∀ x ∈ codeRange 0x1273e1 bytes_l1273e1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x273e1 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127402 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127402 (movR32M32LowEffect 0x127402 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x127402 (LoadPre 0x127402 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127402 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127402 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127406 (cmpR32Imm8Effect 0x127406 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x127406 (fun s => s.RIP = 0x127406) (cmpR32Imm8Effect 0x127406 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12742d, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l12740b, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l127402 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x20, 0x83, 0xFA, 0x02, 0x75, 0x22]

theorem code_l127402 : ∀ x ∈ codeRange 0x127402 bytes_l127402, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27402 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12740b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12740b (movR64M64Effect 0x12740b 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x12740b (LoadPre 0x12740b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x12740b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12740b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127410 (movR64M64Effect 0x127410 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x127410 (LoadPre 0x127410 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x127410 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127410 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x127415 (StorePre 0x127415 3 (fun s => AddrMode.addr (.base 14 .none) s (0x127415 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x127415 0 (.base 14 .none)) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x127418 (StorePre 0x127418 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x127418 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127418 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x12741c (movR64M64Effect 0x12741c 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 60) (.exec 0x12741c (LoadPre 0x12741c (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12741c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12741c 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x127420 (cmpR64Imm8Effect 0x127420 0 0x3f) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x127420 (cmpR64Imm8Effect 0x127420 0 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x127420 (fun s => s.RIP = 0x127420) (cmpR64Imm8Effect 0x127420 0 0x3f) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l127476, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l127426, RegMap.args [(0, 59), (1, 55), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12740b : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x49, 0x89, 0x06, 0x49, 0x89, 0x4E,
    0x08, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x83, 0xF8, 0x3F, 0x76, 0x50]

theorem code_l12740b : ∀ x ∈ codeRange 0x12740b bytes_l12740b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2740b 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127426 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127426 (movR32Imm32Effect 0x127426 5 0 0x6) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x127426 (fun s => s.RIP = 0x127426) (movR32Imm32Effect 0x127426 5 0 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127492, RegMap.args [(0, 53), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l127426 : List UInt8 :=
  [0xB8, 0x06, 0x00, 0x00, 0x00, 0xEB, 0x65]

theorem code_l127426 : ∀ x ∈ codeRange 0x127426 bytes_l127426, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27426 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12742d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12742d (movR32M32LowEffect 0x12742d 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x12742d (LoadPre 0x12742d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x12742d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x12742d 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127431 (movR64M64Effect 0x127431 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x127431 (LoadPre 0x127431 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x127431 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127431 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x127436 (movR64M64Effect 0x127436 15 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x127436 (LoadPre 0x127436 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x127436 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127436 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12743b (movR64M64Effect 0x12743b 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x12743b (LoadPre 0x12743b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12743b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12743b 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x127440 (StorePre 0x127440 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127440 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127440 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x127444 (movR64M64Effect 0x127444 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x127444 (LoadPre 0x127444 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127444 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127444 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x127449 (StorePre 0x127449 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x127449 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127449 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x12744e (movR64M64Effect 0x12744e 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x12744e (LoadPre 0x12744e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x12744e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12744e 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x127453 (StorePre 0x127453 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127453 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127453 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x127458 (movR64M64Effect 0x127458 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x127458 (LoadPre 0x127458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x127458 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127458 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x12745d (StorePre 0x12745d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x12745d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12745d 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l127462, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (10, 10), (11, 11), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l12742d : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x8B,
    0x74, 0x24, 0x38, 0x48, 0x89, 0x34, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x89, 0x74, 0x24,
    0x08, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x50,
    0x48, 0x89, 0x74, 0x24, 0x18]

theorem code_l12742d : ∀ x ∈ codeRange 0x12742d bytes_l12742d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2742d 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127462 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127462 (movR32R32Effect 0x127462 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 54) (.exec 0x127462 (fun s => s.RIP = 0x127462) (movR32R32Effect 0x127462 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x127464 (shrR32Effect 0x127464 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x127464 (fun s => s.RIP = 0x127464) (shrR32Effect 0x127464 3 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x127467 (movR64Imm64Effect 0x127467 7 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x127467 (fun s => s.RIP = 0x127467) (movR64Imm64Effect 0x127467 7 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x127471 (andR64R64Effect 0x127471 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[57, 15]
    (.letOp (n := 60) (.exec 0x127471 (fun s => s.RIP = 0x127471) (andR64R64Effect 0x127471 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[57, 15]
    (.terminate (.br ⟨.l1274a2, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 55), (7, 59), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127462 : List UInt8 :=
  [0x89, 0xCE, 0xC1, 0xEE, 0x08, 0x48, 0xBF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x4C,
    0x21, 0xFF, 0xEB, 0x2C]

theorem code_l127462 : ∀ x ∈ codeRange 0x127462 bytes_l127462, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27462 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127476 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127476 (incR64Effect 0x127476 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x127476 (fun s => s.RIP = 0x127476) (incR64Effect 0x127476 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 55) (.exec 0x127479 (StorePre 0x127479 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127479 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127479 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x12747d (movR32M32Effect 0x12747d 15 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 57) (.exec 0x12747d (LoadPre 0x12747d (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12747d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x12747d 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.out 0x127481 (cmpR32R32Effect 0x127481 3 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[5, 56]
    (.letOp (n := 59) (.out 0x127481 (cmpR32R32Effect 0x127481 3 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 56]
    (.letOp (n := 60) (.exec 0x127481 (fun s => s.RIP = 0x127481) (cmpR32R32Effect 0x127481 3 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 56]
    (.letOp (n := 61) (.pure (condOp 6)) #v[58, 59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1274f6, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l127486, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 56), (16, 58), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l127476 : List UInt8 :=
  [0x48, 0xFF, 0xC0, 0x49, 0x89, 0x46, 0x10, 0x45, 0x8B, 0x7E, 0x18, 0x44, 0x39, 0xFD, 0x76, 0x70]

theorem code_l127476 : ∀ x ∈ codeRange 0x127476 bytes_l127476, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27476 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127486 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127486 (leaR32Effect 0x127486 4 0 (.base 15 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x127486 (fun s => s.RIP = 0x127486) (leaR32Effect 0x127486 4 0 (.base 15 (.d8 0x1))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x12748a (shlR64Effect 0x12748a 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x12748a (fun s => s.RIP = 0x12748a) (shlR64Effect 0x12748a 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12748e (orR64Imm8Effect 0x12748e 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x12748e (fun s => s.RIP = 0x12748e) (orR64Imm8Effect 0x12748e 0 0x3) (Reg.operands [.gpr 0] [])) #v[55]
    (.terminate (.br ⟨.l127492, RegMap.args [(0, 57), (3, 3), (4, 4), (7, 7), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l127486 : List UInt8 :=
  [0x41, 0x8D, 0x47, 0x01, 0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x03]

theorem code_l127486 : ∀ x ∈ codeRange 0x127486 bytes_l127486, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27486 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127492 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127492 (movR32R32Effect 0x127492 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 54) (.exec 0x127492 (fun s => s.RIP = 0x127492) (movR32R32Effect 0x127492 3 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x127495 (shrR32Effect 0x127495 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x127495 (fun s => s.RIP = 0x127495) (shrR32Effect 0x127495 3 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x127498 (movR32Imm32Effect 0x127498 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x127498 (fun s => s.RIP = 0x127498) (movR32Imm32Effect 0x127498 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x12749d (xorR32R32Effect 0x12749d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 60) (.exec 0x12749d (fun s => s.RIP = 0x12749d) (xorR32R32Effect 0x12749d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 61) (.out 0x12749f (movR32R32Effect 0x12749f 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 62) (.exec 0x12749f (fun s => s.RIP = 0x12749f) (movR32R32Effect 0x12749f 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l1274a2, RegMap.args [(0, 0), (1, 61), (2, 57), (3, 3), (4, 4), (6, 55), (7, 59), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l127492 : List UInt8 :=
  [0x44, 0x89, 0xFE, 0xC1, 0xEE, 0x08, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x44, 0x89, 0xF9]

theorem code_l127492 : ∀ x ∈ codeRange 0x127492 bytes_l127492, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27492 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1274a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1274a2 (movR32R32Effect 0x1274a2 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 54) (.exec 0x1274a2 (fun s => s.RIP = 0x1274a2) (movR32R32Effect 0x1274a2 3 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1274a5 (orR64R64Effect 0x1274a5 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x1274a5 (fun s => s.RIP = 0x1274a5) (orR64R64Effect 0x1274a5 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x1274a8 (movR64M64Effect 0x1274a8 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1274a8 (LoadPre 0x1274a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1274a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274a8 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1274ad (StorePre 0x1274ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1274ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274ad 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x1274b1 (movR64M64Effect 0x1274b1 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x1274b1 (LoadPre 0x1274b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1274b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274b1 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1274b6 (StorePre 0x1274b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1274b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274b6 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x1274ba (movR64M64Effect 0x1274ba 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1274ba (LoadPre 0x1274ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1274ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1274ba 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1274be (movR64M64Effect 0x1274be 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 66) (.exec 0x1274be (LoadPre 0x1274be (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1274be + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1274be 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1274c3 (StorePre 0x1274c3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1274c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274c3 9 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 68) (.exec 0x1274c7 (StorePre 0x1274c7 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1274c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274c7 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 69) (.exec 0x1274cb (StorePre 0x1274cb 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1274cb + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1274cb 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 70) (.exec 0x1274cd (StorePre 0x1274cd 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1274cd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1274cd 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 71) (.out 0x1274d0 (movR32R32Effect 0x1274d0 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 72) (.exec 0x1274d0 (fun s => s.RIP = 0x1274d0) (movR32R32Effect 0x1274d0 2 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x1274d2 (shrR32Effect 0x1274d2 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x1274d2 (fun s => s.RIP = 0x1274d2) (shrR32Effect 0x1274d2 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.exec 0x1274d5 (StorePre 0x1274d5 3 (fun s => AddrMode.addr (.base 3 (.d8 0x7)) s (0x1274d5 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1274d5 3 1 (.base 3 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[73, 3]
    (.letOp (n := 76) (.exec 0x1274d8 (StorePre 0x1274d8 4 (fun s => AddrMode.addr (.base 3 (.d8 0x5)) s (0x1274d8 + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1274d8 4 6 (.base 3 (.d8 0x5))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 3]
    (.letOp (n := 77) (.exec 0x1274dc (StorePre 0x1274dc 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1274dc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274dc 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 78) (.exec 0x1274e0 (StorePre 0x1274e0 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1274e0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1274e0 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l1274e4, RegMap.args [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 63), (8, 55), (9, 65), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩)))))))))))))))))))))))))))

def bytes_l1274a2 : List UInt8 :=
  [0x45, 0x89, 0xF8, 0x49, 0x09, 0xF8, 0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x89, 0x7B, 0x30, 0x48,
    0x8B, 0x7C, 0x24, 0x10, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x3C, 0x24, 0x4C, 0x8B, 0x4C, 0x24,
    0x08, 0x4C, 0x89, 0x4B, 0x20, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x13, 0x88, 0x4B, 0x04, 0x89, 0xF1,
    0xC1, 0xE9, 0x10, 0x88, 0x4B, 0x07, 0x66, 0x89, 0x73, 0x05, 0x48, 0x89, 0x43, 0x08, 0x4C, 0x89,
    0x43, 0x10]

theorem code_l1274a2 : ∀ x ∈ codeRange 0x1274a2 bytes_l1274a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x274a2 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1274e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1274e4 (movR64R64Effect 0x1274e4 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1274e4 (fun s => s.RIP = 0x1274e4) (movR64R64Effect 0x1274e4 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1274e7 (addR64Imm8Effect 0x1274e7 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1274e7 (fun s => s.RIP = 0x1274e7) (addR64Imm8Effect 0x1274e7 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1274eb (popR64Effect 0x1274eb 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1274eb (popR64Effect 0x1274eb 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1274eb (PopPre 0x1274eb) (popR64Effect 0x1274eb 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1274ec (popR64Effect 0x1274ec 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1274ec (popR64Effect 0x1274ec 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1274ec (PopPre 0x1274ec) (popR64Effect 0x1274ec 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1274ee (popR64Effect 0x1274ee 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1274ee (popR64Effect 0x1274ee 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1274ee (PopPre 0x1274ee) (popR64Effect 0x1274ee 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1274f0 (popR64Effect 0x1274f0 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1274f0 (popR64Effect 0x1274f0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1274f0 (PopPre 0x1274f0) (popR64Effect 0x1274f0 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1274f2 (popR64Effect 0x1274f2 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1274f2 (popR64Effect 0x1274f2 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1274f2 (PopPre 0x1274f2) (popR64Effect 0x1274f2 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1274f4 (popR64Effect 0x1274f4 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1274f4 (popR64Effect 0x1274f4 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1274f4 (PopPre 0x1274f4) (popR64Effect 0x1274f4 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1274f5 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1274f5 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1274f5 (RetPre 0x1274f5) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1274e4 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x78, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1274e4 : ∀ x ∈ codeRange 0x1274e4 bytes_l1274e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x274e4 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1274f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1274f6 (StorePre 0x1274f6 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1274f6 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1274f6 5 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 14]
    (.letOp (n := 54) (.out 0x1274fa (leaR64Effect 0x1274fa 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x1274fa (fun s => s.RIP = 0x1274fa) (leaR64Effect 0x1274fa 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1274ff (movR64M64Effect 0x1274ff 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 57) (.exec 0x1274ff (LoadPre 0x1274ff (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1274ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1274ff 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.out 0x127503 (movR64M64Effect 0x127503 1 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 59) (.exec 0x127503 (LoadPre 0x127503 (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x127503 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127503 1 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 60) (.exec 0x127507 (StorePre 0x127507 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x127507 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127507 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.exec 0x12750c (StorePre 0x12750c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x12750c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12750c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 62) (.exec 0x127511 (StorePre 0x127511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x127511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127511 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 63) (.out 0x127516 (leaR64Effect 0x127516 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x127516 (fun s => s.RIP = 0x127516) (leaR64Effect 0x127516 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x12751b (movR64R64Effect 0x12751b 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 66) (.exec 0x12751b (fun s => s.RIP = 0x12751b) (movR64R64Effect 0x12751b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x12751e (callEffect (fun _ => 0x124be0) 0x127523) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x12751e (PushPre 0x12751e 5) (callEffect (fun _ => 0x124be0) 0x127523) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x127523⟩) #v[]
    (.terminate (.call ⟨.l124be0, RegMap.args [(0, 56), (1, 58), (2, 54), (3, 3), (4, 67), (5, 5), (6, 65), (7, 63), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l127523, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l1274f6 : List UInt8 :=
  [0x41, 0x89, 0x6E, 0x18, 0x48, 0x8D, 0x54, 0x24, 0x68, 0x49, 0x8B, 0x45, 0x00, 0x49, 0x8B, 0x4D,
    0x08, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x74, 0x24, 0x60,
    0x48, 0x8D, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xF6, 0xE8, 0xBD, 0xD6, 0xFF, 0xFF]

theorem code_l1274f6 : ∀ x ∈ codeRange 0x1274f6 bytes_l1274f6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x274f6 45 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127523 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127523 (movR32M32Effect 0x127523 8 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[14]
    (.letOp (n := 54) (.exec 0x127523 (LoadPre 0x127523 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x127523 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127523 8 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x127527 (movR32M32Effect 0x127527 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 56) (.exec 0x127527 (LoadPre 0x127527 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x127527 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x127527 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x12752b (cmpR32R32Effect 0x12752b 3 8 1) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 1] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.out 0x12752b (cmpR32R32Effect 0x12752b 3 8 1) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 1] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 59) (.exec 0x12752b (fun s => s.RIP = 0x12752b) (cmpR32R32Effect 0x12752b 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 60) (.out 0x12752e (atFlags (condHolds 6) (setccR8Effect 0x12752e 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 57, 58]
    (.letOp (n := 61) (.exec 0x12752e (fun s => s.RIP = 0x12752e) (atFlags (condHolds 6) (setccR8Effect 0x12752e 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 57, 58]
    (.letOp (n := 62) (.out 0x127531 (movR64M64Effect 0x127531 2 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x127531 (LoadPre 0x127531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x127531 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127531 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x127536 (StorePre 0x127536 3 (fun s => AddrMode.addr (.base 14 .none) s (0x127536 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x127536 2 (.base 14 .none)) (Reg.operands [.gpr 2, .gpr 14] [])) #v[62, 14]
    (.letOp (n := 65) (.exec 0x127539 (StorePre 0x127539 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x127539 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127539 12 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 14] [])) #v[12, 14]
    (.letOp (n := 66) (.exec 0x12753d (StorePre 0x12753d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x12753d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x12753d 15 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 67) (.out 0x127541 (movR64M64Effect 0x127541 2 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 68) (.exec 0x127541 (LoadPre 0x127541 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x127541 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127541 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 69) (.out 0x127545 (cmpR64Imm8Effect 0x127545 2 0x1) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[67]
    (.letOp (n := 70) (.exec 0x127545 (fun s => s.RIP = 0x127545) (cmpR64Imm8Effect 0x127545 2 0x1) (Reg.operands [.gpr 2] [])) #v[67]
    (.letOp (n := 71) (.out 0x127549 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x127549 2 0xff)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x127549 (fun s => s.RIP = 0x127549) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x127549 2 0xff)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[67, 69]
    (.letOp (n := 73) (.exec 0x12754d (StorePre 0x12754d 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x12754d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12754d 2 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 14] [])) #v[71, 14]
    (.letOp (n := 74) (.out 0x127551 (movR32M32LowEffect 0x127551 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 75) (.exec 0x127551 (LoadPre 0x127551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x127551 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127551 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x127555 (cmpR32Imm8Effect 0x127555 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[74]
    (.letOp (n := 77) (.exec 0x127555 (fun s => s.RIP = 0x127555) (cmpR32Imm8Effect 0x127555 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[74]
    (.letOp (n := 78) (.out 0x127558 (atFlags (condHolds 5) (setccR8Effect 0x127558 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[6, 76]
    (.letOp (n := 79) (.exec 0x127558 (fun s => s.RIP = 0x127558) (atFlags (condHolds 5) (setccR8Effect 0x127558 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[6, 76]
    (.letOp (n := 80) (.out 0x12755c (orR8R8Effect 0x12755c 3 6 0) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 0] []) (.flag .ZF)) #v[78, 60]
    (.letOp (n := 81) (.exec 0x12755c (fun s => s.RIP = 0x12755c) (orR8R8Effect 0x12755c 3 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[78, 60]
    (.letOp (n := 82) (.pure (condOp 4)) #v[80]
    (.terminate (.condBr (Fin.last 82) ⟨.l1275ad, RegMap.args [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩ ⟨.l127561, RegMap.args [(0, 60), (1, 55), (2, 74), (3, 3), (4, 4), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l127523 : List UInt8 :=
  [0x45, 0x8B, 0x46, 0x18, 0x41, 0x8B, 0x4E, 0x1C, 0x41, 0x39, 0xC8, 0x0F, 0x96, 0xC0, 0x48, 0x8B,
    0x54, 0x24, 0x58, 0x49, 0x89, 0x16, 0x4D, 0x89, 0x66, 0x08, 0x45, 0x89, 0x7E, 0x18, 0x49, 0x8B,
    0x56, 0x10, 0x48, 0x83, 0xFA, 0x01, 0x48, 0x83, 0xD2, 0xFF, 0x49, 0x89, 0x56, 0x10, 0x8B, 0x54,
    0x24, 0x20, 0x83, 0xFA, 0x02, 0x40, 0x0F, 0x95, 0xC6, 0x40, 0x08, 0xC6, 0x74, 0x4C]

theorem code_l127523 : ∀ x ∈ codeRange 0x127523 bytes_l127523, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27523 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127561 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127561 (movR32M32LowEffect 0x127561 1 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x127561 (LoadPre 0x127561 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x127561 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x127561 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127565 (movR64M64Effect 0x127565 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x127565 (LoadPre 0x127565 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x127565 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127565 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x12756a (movR64M64Effect 0x12756a 15 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x12756a (LoadPre 0x12756a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x12756a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12756a 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x12756f (movR64M64Effect 0x12756f 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x12756f (LoadPre 0x12756f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x12756f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12756f 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x127574 (StorePre 0x127574 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127574 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127574 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x127578 (movR64M64Effect 0x127578 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x127578 (LoadPre 0x127578 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x127578 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127578 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x12757d (StorePre 0x12757d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x12757d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x12757d 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x127582 (movR64M64Effect 0x127582 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x127582 (LoadPre 0x127582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x127582 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x127582 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x127587 (StorePre 0x127587 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x127587 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127587 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x12758c (movR64M64Effect 0x12758c 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x12758c (LoadPre 0x12758c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x12758c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x12758c 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x127591 (StorePre 0x127591 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x127591 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x127591 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x127596 (cmpR32Imm8Effect 0x127596 3 2 0x2) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 72) (.exec 0x127596 (fun s => s.RIP = 0x127596) (cmpR32Imm8Effect 0x127596 3 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l127462, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l12759f, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 57), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l127561 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x24, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0x7C, 0x24, 0x30, 0x48, 0x8B,
    0x74, 0x24, 0x38, 0x48, 0x89, 0x34, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x89, 0x74, 0x24,
    0x08, 0x48, 0x8B, 0x74, 0x24, 0x48, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x50,
    0x48, 0x89, 0x74, 0x24, 0x18, 0x83, 0xFA, 0x02, 0x0F, 0x85, 0xC3, 0xFE, 0xFF, 0xFF]

theorem code_l127561 : ∀ x ∈ codeRange 0x127561 bytes_l127561, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27561 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12759f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12759f (StorePre 0x12759f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x12759f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12759f 3 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 54) (.exec 0x1275a2 (StorePre 0x1275a2 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1275a2 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1275a2 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l1274e4, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12759f : List UInt8 :=
  [0x88, 0x4B, 0x04, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x37, 0xFF, 0xFF, 0xFF]

theorem code_l12759f : ∀ x ∈ codeRange 0x12759f bytes_l12759f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2759f 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1275ad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1275ad (subR32R32Effect 0x1275ad 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[8, 1]
    (.letOp (n := 54) (.exec 0x1275ad (fun s => s.RIP = 0x1275ad) (subR32R32Effect 0x1275ad 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[8, 1]
    (.letOp (n := 55) (.exec 0x1275b0 (StorePre 0x1275b0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1275b0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1275b0 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1275b5 (movR32R32Effect 0x1275b5 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 57) (.exec 0x1275b5 (fun s => s.RIP = 0x1275b5) (movR32R32Effect 0x1275b5 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 58) (.out 0x1275b7 (shrR32Effect 0x1275b7 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[56]
    (.letOp (n := 59) (.exec 0x1275b7 (fun s => s.RIP = 0x1275b7) (shrR32Effect 0x1275b7 3 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 60) (.out 0x1275ba (movR64R64Effect 0x1275ba 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 61) (.exec 0x1275ba (fun s => s.RIP = 0x1275ba) (movR64R64Effect 0x1275ba 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 62) (.out 0x1275bd (shlR64Effect 0x1275bd 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x1275bd (fun s => s.RIP = 0x1275bd) (shlR64Effect 0x1275bd 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 64) (.out 0x1275c1 (orR64Imm8Effect 0x1275c1 0 0x13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 65) (.exec 0x1275c1 (fun s => s.RIP = 0x1275c1) (orR64Imm8Effect 0x1275c1 0 0x13) (Reg.operands [.gpr 0] [])) #v[62]
    (.letOp (n := 66) (.out 0x1275c5 (movR32Imm32Effect 0x1275c5 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 67) (.exec 0x1275c5 (fun s => s.RIP = 0x1275c5) (movR32Imm32Effect 0x1275c5 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x1275ca (xorR32R32Effect 0x1275ca 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 69) (.exec 0x1275ca (fun s => s.RIP = 0x1275ca) (xorR32R32Effect 0x1275ca 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 70) (.out 0x1275cc (movR32R32Effect 0x1275cc 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 71) (.exec 0x1275cc (fun s => s.RIP = 0x1275cc) (movR32R32Effect 0x1275cc 3 15 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.terminate (.br ⟨.l1274a2, RegMap.args [(0, 64), (1, 1), (2, 66), (3, 3), (4, 4), (6, 58), (7, 68), (8, 53), (10, 10), (11, 11), (14, 14), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1275ad : List UInt8 :=
  [0x41, 0x29, 0xC8, 0x41, 0xC6, 0x46, 0x20, 0x01, 0x89, 0xCE, 0xC1, 0xEE, 0x08, 0x48, 0x89, 0xC8,
    0x48, 0xC1, 0xE0, 0x20, 0x48, 0x83, 0xC8, 0x13, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x45,
    0x89, 0xC7, 0xE9, 0xCE, 0xFE, 0xFF, 0xFF]

theorem code_l1275ad : ∀ x ∈ codeRange 0x1275ad bytes_l1275ad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x275ad 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1275d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1275d4 (xorR32R32Effect 0x1275d4 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1275d4 (fun s => s.RIP = 0x1275d4) (xorR32R32Effect 0x1275d4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x1275d6 (movR32Imm32Effect 0x1275d6 5 0 0xc) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1275d6 (fun s => s.RIP = 0x1275d6) (movR32Imm32Effect 0x1275d6 5 0 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1275db (xorR32R32Effect 0x1275db 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 58) (.exec 0x1275db (fun s => s.RIP = 0x1275db) (xorR32R32Effect 0x1275db 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.terminate (.br ⟨.l1274a2, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (6, 6), (7, 57), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1275d4 : List UInt8 :=
  [0x31, 0xD2, 0xB8, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xFF, 0xE9, 0xC0, 0xFE, 0xFF, 0xFF]

theorem code_l1275d4 : ∀ x ∈ codeRange 0x1275d4 bytes_l1275d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x275d4 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127670 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127670 (movR64R64Effect 0x127670 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x127670 (fun s => s.RIP = 0x127670) (movR64R64Effect 0x127670 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127673 (movzxR32M8Effect 0x127673 3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x127673 (LoadPre 0x127673 (fun s => AddrMode.addr (.base 6 .none) s (0x127673 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x127673 3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x127676 (shrR32Effect 0x127676 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x127676 (fun s => s.RIP = 0x127676) (shrR32Effect 0x127676 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x127679 (incR32Effect 0x127679 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x127679 (fun s => s.RIP = 0x127679) (incR32Effect 0x127679 2 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.exec 0x12767b (StorePre 0x12767b 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x12767b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x12767b 1 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[59, 7]
    (.letOp (n := 62) (.exec 0x12767e (StorePre 0x12767e 6 (fun s => AddrMode.addr (.base 7 .none) s (0x12767e + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12767e 6 (.base 7 .none) 0x2) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x127684 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 64) (.out 0x127684 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x127684 (RetPre 0x127684) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 59), (2, 2), (3, 3), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l127670 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x0F, 0xB6, 0x0E, 0xC1, 0xE9, 0x07, 0xFF, 0xC1, 0x89, 0x4F, 0x04, 0xC7, 0x07,
    0x02, 0x00, 0x00, 0x00, 0xC3]

theorem code_l127670 : ∀ x ∈ codeRange 0x127670 bytes_l127670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27670 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127690 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127690 (movR64R64Effect 0x127690 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x127690 (fun s => s.RIP = 0x127690) (movR64R64Effect 0x127690 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127693 (movR64R64Effect 0x127693 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 56) (.exec 0x127693 (fun s => s.RIP = 0x127693) (movR64R64Effect 0x127693 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x127696 (shrR64Effect 0x127696 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.out 0x127696 (shrR64Effect 0x127696 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x127696 (fun s => s.RIP = 0x127696) (shrR64Effect 0x127696 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 4)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1276aa, RegMap.args [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l12769c, RegMap.args [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l127690 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x20, 0x74, 0x0E]

theorem code_l127690 : ∀ x ∈ codeRange 0x127690 bytes_l127690, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27690 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12769c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12769c (movR32Imm32Effect 0x12769c 5 6 0xc) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x12769c (fun s => s.RIP = 0x12769c) (movR32Imm32Effect 0x12769c 5 6 0xc) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1276a1 (xorR32R32Effect 0x1276a1 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 56) (.exec 0x1276a1 (fun s => s.RIP = 0x1276a1) (xorR32R32Effect 0x1276a1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 57) (.exec 0x1276a3 (StorePre 0x1276a3 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276a3 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276a3 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 58) (.exec 0x1276a5 (StorePre 0x1276a5 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276a5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276a5 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 59) (.out 0x1276a9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 60) (.out 0x1276a9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x1276a9 (RetPre 0x1276a9) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 60), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l12769c : List UInt8 :=
  [0xBE, 0x0C, 0x00, 0x00, 0x00, 0x31, 0xC9, 0x89, 0x08, 0x48, 0x89, 0x70, 0x08, 0xC3]

theorem code_l12769c : ∀ x ∈ codeRange 0x12769c bytes_l12769c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2769c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1276aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1276aa (StorePre 0x1276aa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x1276aa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276aa 2 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 54) (.exec 0x1276ae (StorePre 0x1276ae 8 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x1276ae + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1276ae (.base 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x1276b6 (StorePre 0x1276b6 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x1276b6 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1276b6 2 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 56) (.exec 0x1276b9 (StorePre 0x1276b9 7 (fun s => AddrMode.addr (.base 0 (.d8 0x24)) s (0x1276b9 + BitVec.ofNat 64 7)) 4) (movM32Imm32Effect 0x1276b9 7 (.base 0 (.d8 0x24)) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.exec 0x1276c0 (StorePre 0x1276c0 4 (fun s => AddrMode.addr (.base 0 (.d8 0x28)) s (0x1276c0 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1276c0 (.base 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 58) (.out 0x1276c4 (movR32Imm32Effect 0x1276c4 5 1 0x2) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x1276c4 (fun s => s.RIP = 0x1276c4) (movR32Imm32Effect 0x1276c4 5 1 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x1276c9 (StorePre 0x1276c9 2 (fun s => AddrMode.addr (.base 0 .none) s (0x1276c9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1276c9 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 61) (.exec 0x1276cb (StorePre 0x1276cb 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1276cb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1276cb 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 62) (.out 0x1276cf (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 63) (.out 0x1276cf (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1276cf (RetPre 0x1276cf) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 58), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65) (some ⟨62, by decide⟩))))))))))))))

def bytes_l1276aa : List UInt8 :=
  [0x48, 0x89, 0x50, 0x10, 0x48, 0xC7, 0x40, 0x18, 0x00, 0x00, 0x00, 0x00, 0x89, 0x50, 0x20, 0xC7,
    0x40, 0x24, 0x00, 0x00, 0x00, 0x00, 0xC6, 0x40, 0x28, 0x00, 0xB9, 0x02, 0x00, 0x00, 0x00, 0x89,
    0x08, 0x48, 0x89, 0x70, 0x08, 0xC3]

theorem code_l1276aa : ∀ x ∈ codeRange 0x1276aa bytes_l1276aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x276aa 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1276d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1276d0 (movR64R64Effect 0x1276d0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1276d0 (fun s => s.RIP = 0x1276d0) (movR64R64Effect 0x1276d0 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1276d3 (cmpR8R8Effect 0x1276d3 3 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 2]
    (.letOp (n := 56) (.exec 0x1276d3 (fun s => s.RIP = 0x1276d3) (cmpR8R8Effect 0x1276d3 3 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 2]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l127726, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1276d8, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1276d0 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x40, 0x38, 0xD6, 0x75, 0x4E]

theorem code_l1276d0 : ∀ x ∈ codeRange 0x1276d0 bytes_l1276d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x276d0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1276d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1276d8 (movR32R32Effect 0x1276d8 3 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 54) (.exec 0x1276d8 (fun s => s.RIP = 0x1276d8) (movR32R32Effect 0x1276d8 3 8 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1276db (shrR32Effect 0x1276db 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x1276db (fun s => s.RIP = 0x1276db) (shrR32Effect 0x1276db 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x1276df (movR64R64Effect 0x1276df 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x1276df (fun s => s.RIP = 0x1276df) (movR64R64Effect 0x1276df 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1276e2 (shrR64Effect 0x1276e2 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x1276e2 (fun s => s.RIP = 0x1276e2) (shrR64Effect 0x1276e2 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x1276e6 (movR32R32Effect 0x1276e6 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 62) (.exec 0x1276e6 (fun s => s.RIP = 0x1276e6) (movR32R32Effect 0x1276e6 3 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x1276e9 (shrR32Effect 0x1276e9 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 64) (.exec 0x1276e9 (fun s => s.RIP = 0x1276e9) (shrR32Effect 0x1276e9 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x1276ed (movR64R64Effect 0x1276ed 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[2]
    (.letOp (n := 66) (.exec 0x1276ed (fun s => s.RIP = 0x1276ed) (movR64R64Effect 0x1276ed 7 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.out 0x1276f0 (shrR64Effect 0x1276f0 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 68) (.exec 0x1276f0 (fun s => s.RIP = 0x1276f0) (shrR64Effect 0x1276f0 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x1276f4 (cmpR8Imm8Effect 0x1276f4 4 6 0x18) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 70) (.exec 0x1276f4 (fun s => s.RIP = 0x1276f4) (cmpR8Imm8Effect 0x1276f4 4 6 0x18) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.pure (condOp 4)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l12770a, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l1276fa, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 67), (8, 55), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1276d8 : List UInt8 :=
  [0x41, 0x89, 0xF0, 0x41, 0xC1, 0xE8, 0x08, 0x48, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x20, 0x41, 0x89,
    0xD1, 0x41, 0xC1, 0xE9, 0x08, 0x48, 0x89, 0xD7, 0x48, 0xC1, 0xEF, 0x20, 0x40, 0x80, 0xFE, 0x18,
    0x74, 0x10]

theorem code_l1276d8 : ∀ x ∈ codeRange 0x1276d8 bytes_l1276d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x276d8 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1276fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1276fa (movzxR32R8Effect 0x1276fa 4 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 54) (.exec 0x1276fa (fun s => s.RIP = 0x1276fa) (movzxR32R8Effect 0x1276fa 4 10 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1276fe (cmpR32Imm8Effect 0x1276fe 4 10 0x17) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1276fe (fun s => s.RIP = 0x1276fe) (cmpR32Imm8Effect 0x1276fe 4 10 0x17) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12770a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l127704, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1276fa : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0xD6, 0x41, 0x83, 0xFA, 0x17, 0x74, 0x06]

theorem code_l1276fa : ∀ x ∈ codeRange 0x1276fa bytes_l1276fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x276fa 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127704 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127704 (cmpR32Imm8Effect 0x127704 4 10 0x16) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[10]
    (.letOp (n := 54) (.exec 0x127704 (fun s => s.RIP = 0x127704) (cmpR32Imm8Effect 0x127704 4 10 0x16) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12771b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12770a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127704 : List UInt8 :=
  [0x41, 0x83, 0xFA, 0x16, 0x75, 0x11]

theorem code_l127704 : ∀ x ∈ codeRange 0x127704 bytes_l127704, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27704 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12770a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12770a (cmpR8R8Effect 0x12770a 3 8 9) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 9] []) (.flag .ZF)) #v[8, 9]
    (.letOp (n := 54) (.exec 0x12770a (fun s => s.RIP = 0x12770a) (cmpR8R8Effect 0x12770a 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[8, 9]
    (.letOp (n := 55) (.out 0x12770d (atFlags (condHolds 4) (setccR8Effect 0x12770d 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[8, 53]
    (.letOp (n := 56) (.exec 0x12770d (fun s => s.RIP = 0x12770d) (atFlags (condHolds 4) (setccR8Effect 0x12770d 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[8, 53]
    (.letOp (n := 57) (.out 0x127711 (cmpR32R32Effect 0x127711 2 1 7) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 7] []) (.flag .ZF)) #v[1, 7]
    (.letOp (n := 58) (.exec 0x127711 (fun s => s.RIP = 0x127711) (cmpR32R32Effect 0x127711 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 7]
    (.letOp (n := 59) (.out 0x127713 (atFlags (condHolds 4) (setccR8Effect 0x127713 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[1, 57]
    (.letOp (n := 60) (.exec 0x127713 (fun s => s.RIP = 0x127713) (atFlags (condHolds 4) (setccR8Effect 0x127713 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1, 57]
    (.letOp (n := 61) (.out 0x127716 (testR8R8Effect 0x127716 3 1 8) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 8] []) (.flag .ZF)) #v[59, 55]
    (.letOp (n := 62) (.exec 0x127716 (fun s => s.RIP = 0x127716) (testR8R8Effect 0x127716 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[59, 55]
    (.letOp (n := 63) (.pure (condOp 4)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l127726, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l12771b, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l12770a : List UInt8 :=
  [0x45, 0x38, 0xC8, 0x41, 0x0F, 0x94, 0xC0, 0x39, 0xF9, 0x0F, 0x94, 0xC1, 0x44, 0x84, 0xC1, 0x74,
    0x0B]

theorem code_l12770a : ∀ x ∈ codeRange 0x12770a bytes_l12770a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2770a 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12771b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12771b (StorePre 0x12771b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x12771b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12771b 6 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 54) (.exec 0x12771f (StorePre 0x12771f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x12771f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x12771f 6 (.base 0 .none) 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x127725 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 56) (.out 0x127725 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x127725 (RetPre 0x127725) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l12771b : List UInt8 :=
  [0x48, 0x89, 0x70, 0x04, 0xC7, 0x00, 0x02, 0x00, 0x00, 0x00, 0xC3]

theorem code_l12771b : ∀ x ∈ codeRange 0x12771b bytes_l12771b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2771b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127726 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127726 (StorePre 0x127726 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127726 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127726 6 (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 54) (.exec 0x12772c (StorePre 0x12772c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12772c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12772c (.base 0 (.d8 0x8)) 0x11) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x127730 (StorePre 0x127730 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127730 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127730 2 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 56) (.exec 0x127734 (StorePre 0x127734 4 (fun s => AddrMode.addr (.base 0 (.d8 0x14)) s (0x127734 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127734 6 (.base 0 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 57) (.out 0x127738 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 58) (.out 0x127738 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x127738 (RetPre 0x127738) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60) (some ⟨57, by decide⟩)))))))))

def bytes_l127726 : List UInt8 :=
  [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00, 0xC6, 0x40, 0x08, 0x11, 0x48, 0x89, 0x50, 0x0C, 0x48, 0x89,
    0x70, 0x14, 0xC3]

theorem code_l127726 : ∀ x ∈ codeRange 0x127726 bytes_l127726, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27726 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127b80 (movR64R64Effect 0x127b80 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x127b80 (fun s => s.RIP = 0x127b80) (movR64R64Effect 0x127b80 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127b83 (cmpM8Imm8Effect 0x127b83 4 (.base 6 (.d8 0x20)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 56) (.exec 0x127b83 (LoadPre 0x127b83 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b83 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x127b83 4 (.base 6 (.d8 0x20)) 0x0) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l127b9e, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l127b89, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l127b80 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x80, 0x7E, 0x20, 0x00, 0x74, 0x15]

theorem code_l127b80 : ∀ x ∈ codeRange 0x127b80 bytes_l127b80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b80 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127b89 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127b89 (StorePre 0x127b89 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127b89 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b89 (.base 6 (.d8 0x20)) 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 54) (.out 0x127b8d (movR32M32LowEffect 0x127b8d 1 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 55) (.exec 0x127b8d (LoadPre 0x127b8d (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127b8d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127b8d 1 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.exec 0x127b90 (StorePre 0x127b90 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127b90 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127b90 6 (.base 0 .none) 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.exec 0x127b96 (StorePre 0x127b96 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127b96 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127b96 1 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[54, 0]
    (.letOp (n := 58) (.exec 0x127b99 (StorePre 0x127b99 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127b99 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127b99 (.base 0 (.d8 0x8)) 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x127b9d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 60) (.out 0x127b9d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x127b9d (RetPre 0x127b9d) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l127b89 : List UInt8 :=
  [0xC6, 0x46, 0x20, 0x01, 0x8B, 0x4E, 0x1C, 0xC7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x89, 0x48, 0x04,
    0xC6, 0x40, 0x08, 0x02, 0xC3]

theorem code_l127b89 : ∀ x ∈ codeRange 0x127b89 bytes_l127b89, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b89 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127b9e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127b9e (movR64M64Effect 0x127b9e 7 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 54) (.exec 0x127b9e (LoadPre 0x127b9e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x127b9e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127b9e 7 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x127ba2 (movR32M32LowEffect 0x127ba2 1 (.base 6 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x127ba2 (LoadPre 0x127ba2 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127ba2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127ba2 1 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x127ba5 (movR64R64Effect 0x127ba5 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 58) (.exec 0x127ba5 (fun s => s.RIP = 0x127ba5) (movR64R64Effect 0x127ba5 9 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 59) (.out 0x127ba8 (subR64R64Effect 0x127ba8 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[57, 55]
    (.letOp (n := 60) (.out 0x127ba8 (subR64R64Effect 0x127ba8 9 1) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 1] []) (.flag .CF)) #v[57, 55]
    (.letOp (n := 61) (.exec 0x127ba8 (fun s => s.RIP = 0x127ba8) (subR64R64Effect 0x127ba8 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 62) (.pure (condOp 3)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l127bd3, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l127bad, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 59), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l127b9e : List UInt8 :=
  [0x48, 0x8B, 0x7E, 0x08, 0x8B, 0x4E, 0x1C, 0x49, 0x89, 0xF9, 0x49, 0x29, 0xC9, 0x73, 0x26]

theorem code_l127b9e : ∀ x ∈ codeRange 0x127b9e bytes_l127b9e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b9e 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127bad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127bad (movR64R64Effect 0x127bad 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 54) (.exec 0x127bad (fun s => s.RIP = 0x127bad) (movR64R64Effect 0x127bad 1 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127bb0 (shlR64Effect 0x127bb0 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x127bb0 (fun s => s.RIP = 0x127bb0) (shlR64Effect 0x127bb0 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x127bb4 (movR64Imm64Effect 0x127bb4 2 0x100000003) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x127bb4 (fun s => s.RIP = 0x127bb4) (movR64Imm64Effect 0x127bb4 2 0x100000003) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x127bbe (addR64R64Effect 0x127bbe 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x127bbe (fun s => s.RIP = 0x127bbe) (addR64R64Effect 0x127bbe 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.exec 0x127bc1 (StorePre 0x127bc1 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127bc1 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127bc1 6 (.base 0 .none) 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 62) (.exec 0x127bc7 (StorePre 0x127bc7 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127bc7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bc7 7 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 63) (.exec 0x127bca (StorePre 0x127bca 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bca + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bca 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 0]
    (.letOp (n := 64) (.exec 0x127bce (StorePre 0x127bce 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127bce 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 65) (.out 0x127bd2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 66) (.out 0x127bd2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x127bd2 (RetPre 0x127bd2) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 55), (2, 59), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68) (some ⟨65, by decide⟩)))))))))))))))))

def bytes_l127bad : List UInt8 :=
  [0x48, 0x89, 0xF9, 0x48, 0xC1, 0xE1, 0x20, 0x48, 0xBA, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x01, 0xCA, 0xC7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x89, 0x78, 0x04, 0x48, 0x89, 0x50,
    0x08, 0x48, 0x89, 0x78, 0x10, 0xC3]

theorem code_l127bad : ∀ x ∈ codeRange 0x127bad bytes_l127bad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bad 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127bd3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127bd3 (movR32R32Effect 0x127bd3 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[2]
    (.letOp (n := 54) (.exec 0x127bd3 (fun s => s.RIP = 0x127bd3) (movR32R32Effect 0x127bd3 3 8 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x127bd6 (addR32R32Effect 0x127bd6 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2, 1]
    (.letOp (n := 56) (.exec 0x127bd6 (fun s => s.RIP = 0x127bd6) (addR32R32Effect 0x127bd6 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 57) (.out 0x127bd8 (cmpR64R64Effect 0x127bd8 9 8) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 8] []) (.flag .CF)) #v[9, 53]
    (.letOp (n := 58) (.exec 0x127bd8 (fun s => s.RIP = 0x127bd8) (cmpR64R64Effect 0x127bd8 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[9, 53]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l127bf9, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l127bdd, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l127bd3 : List UInt8 :=
  [0x41, 0x89, 0xD0, 0x01, 0xCA, 0x4D, 0x39, 0xC1, 0x73, 0x1C]

theorem code_l127bd3 : ∀ x ∈ codeRange 0x127bd3 bytes_l127bd3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bd3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127bdd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127bdd (cmpR32R32Effect 0x127bdd 2 2 1) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 1] []) (.flag .CF)) #v[2, 1]
    (.letOp (n := 54) (.exec 0x127bdd (fun s => s.RIP = 0x127bdd) (cmpR32R32Effect 0x127bdd 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l127c36, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l127be1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127bdd : List UInt8 :=
  [0x39, 0xCA, 0x72, 0x55]

theorem code_l127bdd : ∀ x ∈ codeRange 0x127bdd bytes_l127bdd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bdd 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127be1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127be1 (StorePre 0x127be1 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x127be1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127be1 (.base 6 (.d8 0x20)) 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 54) (.exec 0x127be5 (StorePre 0x127be5 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127be5 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127be5 6 (.base 0 .none) 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.exec 0x127beb (StorePre 0x127beb 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127beb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127beb 1 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 0]
    (.letOp (n := 56) (.exec 0x127bee (StorePre 0x127bee 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127bee + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127bee (.base 0 (.d8 0x8)) 0x3) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.exec 0x127bf2 (StorePre 0x127bf2 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127bf2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf2 2 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 58) (.exec 0x127bf5 (StorePre 0x127bf5 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127bf5 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127bf5 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 59) (.out 0x127bf8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 60) (.out 0x127bf8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x127bf8 (RetPre 0x127bf8) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 60), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62) (some ⟨59, by decide⟩)))))))))))

def bytes_l127be1 : List UInt8 :=
  [0xC6, 0x46, 0x20, 0x01, 0xC7, 0x00, 0x01, 0x00, 0x00, 0x00, 0x89, 0x48, 0x04, 0xC6, 0x40, 0x08,
    0x03, 0x89, 0x50, 0x0C, 0x89, 0x78, 0x10, 0xC3]

theorem code_l127be1 : ∀ x ∈ codeRange 0x127be1 bytes_l127be1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27be1 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127bf9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127bf9 (cmpR32R32Effect 0x127bf9 2 2 1) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 1] []) (.flag .CF)) #v[2, 1]
    (.letOp (n := 54) (.exec 0x127bf9 (fun s => s.RIP = 0x127bf9) (cmpR32R32Effect 0x127bf9 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l127c41, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l127bfd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127bf9 : List UInt8 :=
  [0x39, 0xCA, 0x72, 0x44]

theorem code_l127bf9 : ∀ x ∈ codeRange 0x127bf9 bytes_l127bf9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bf9 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127bfd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127bfd (movR32M32LowEffect 0x127bfd 7 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 54) (.exec 0x127bfd (LoadPre 0x127bfd (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x127bfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x127bfd 7 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x127c00 (cmpR32R32Effect 0x127c00 2 2 7) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 7] []) (.flag .CF)) #v[2, 53]
    (.letOp (n := 56) (.out 0x127c00 (cmpR32R32Effect 0x127c00 2 2 7) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 7] []) (.flag .ZF)) #v[2, 53]
    (.letOp (n := 57) (.exec 0x127c00 (fun s => s.RIP = 0x127c00) (cmpR32R32Effect 0x127c00 2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[2, 53]
    (.letOp (n := 58) (.pure (condOp 6)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l127c1e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l127c04, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l127bfd : List UInt8 :=
  [0x8B, 0x7E, 0x18, 0x39, 0xFA, 0x76, 0x1A]

theorem code_l127bfd : ∀ x ∈ codeRange 0x127bfd bytes_l127bfd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bfd 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c04 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127c04 (movR32Imm32Effect 0x127c04 6 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 54) (.exec 0x127c04 (fun s => s.RIP = 0x127c04) (movR32Imm32Effect 0x127c04 6 8 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x127c0a (movR8Imm8Effect 0x127c0a 3 6 0x3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x127c0a (fun s => s.RIP = 0x127c0a) (movR8Imm8Effect 0x127c0a 3 6 0x3) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l127c0d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l127c04 : List UInt8 :=
  [0x41, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x40, 0xB6, 0x03]

theorem code_l127c04 : ∀ x ∈ codeRange 0x127c04 bytes_l127c04, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c04 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c0d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127c0d (StorePre 0x127c0d 3 (fun s => AddrMode.addr (.base 0 .none) s (0x127c0d + BitVec.ofNat 64 3)) 4) (movM32R32Effect 0x127c0d 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 0]
    (.letOp (n := 54) (.exec 0x127c10 (StorePre 0x127c10 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c10 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c10 1 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 0]
    (.letOp (n := 55) (.exec 0x127c13 (StorePre 0x127c13 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c13 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127c13 4 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 56) (.exec 0x127c17 (StorePre 0x127c17 3 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x127c17 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c17 2 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 57) (.exec 0x127c1a (StorePre 0x127c1a 3 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c1a + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c1a 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 58) (.out 0x127c1d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 59) (.out 0x127c1d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x127c1d (RetPre 0x127c1d) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61) (some ⟨58, by decide⟩))))))))))

def bytes_l127c0d : List UInt8 :=
  [0x44, 0x89, 0x00, 0x89, 0x48, 0x04, 0x40, 0x88, 0x70, 0x08, 0x89, 0x50, 0x0C, 0x89, 0x78, 0x10,
    0xC3]

theorem code_l127c0d : ∀ x ∈ codeRange 0x127c0d bytes_l127c0d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c0d 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c1e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127c1e (movR64M64Effect 0x127c1e 7 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 54) (.exec 0x127c1e (LoadPre 0x127c1e (fun s => AddrMode.addr (.base 6 .none) s (0x127c1e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x127c1e 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x127c21 (addR64R64Effect 0x127c21 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[53, 1]
    (.letOp (n := 56) (.exec 0x127c21 (fun s => s.RIP = 0x127c21) (addR64R64Effect 0x127c21 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[53, 1]
    (.letOp (n := 57) (.exec 0x127c24 (StorePre 0x127c24 3 (fun s => AddrMode.addr (.base 6 (.d8 0x1c)) s (0x127c24 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c24 2 (.base 6 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 58) (.exec 0x127c27 (StorePre 0x127c27 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c27 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c27 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.exec 0x127c2b (StorePre 0x127c2b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c2b 8 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 0]
    (.letOp (n := 60) (.exec 0x127c2f (StorePre 0x127c2f 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c2f + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c2f 6 (.base 0 .none) 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x127c35 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 62) (.out 0x127c35 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x127c35 (RetPre 0x127c35) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 62), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l127c1e : List UInt8 :=
  [0x48, 0x8B, 0x3E, 0x48, 0x01, 0xCF, 0x89, 0x56, 0x1C, 0x48, 0x89, 0x78, 0x08, 0x4C, 0x89, 0x40,
    0x10, 0xC7, 0x00, 0x02, 0x00, 0x00, 0x00, 0xC3]

theorem code_l127c1e : ∀ x ∈ codeRange 0x127c1e bytes_l127c1e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c1e 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c36 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127c36 (StorePre 0x127c36 6 (fun s => AddrMode.addr (.base 0 .none) s (0x127c36 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x127c36 6 (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 54) (.exec 0x127c3c (StorePre 0x127c3c 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c3c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x127c3c (.base 0 (.d8 0x8)) 0xc) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x127c40 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 56) (.out 0x127c40 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x127c40 (RetPre 0x127c40) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l127c36 : List UInt8 :=
  [0xC7, 0x00, 0x00, 0x00, 0x00, 0x00, 0xC6, 0x40, 0x08, 0x0C, 0xC3]

theorem code_l127c36 : ∀ x ∈ codeRange 0x127c36 bytes_l127c36, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c36 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c41 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127c41 (xorR32R32Effect 0x127c41 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x127c41 (fun s => s.RIP = 0x127c41) (xorR32R32Effect 0x127c41 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.out 0x127c44 (movR8Imm8Effect 0x127c44 3 6 0xc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x127c44 (fun s => s.RIP = 0x127c44) (movR8Imm8Effect 0x127c44 3 6 0xc) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l127c0d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 55), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l127c41 : List UInt8 :=
  [0x45, 0x31, 0xC0, 0x40, 0xB6, 0x0C, 0xEB, 0xC4]

theorem code_l127c41 : ∀ x ∈ codeRange 0x127c41 bytes_l127c41, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c41 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127c50 (movR64R64Effect 0x127c50 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x127c50 (fun s => s.RIP = 0x127c50) (movR64R64Effect 0x127c50 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127c53 (movR32R32Effect 0x127c53 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 56) (.exec 0x127c53 (fun s => s.RIP = 0x127c53) (movR32R32Effect 0x127c53 2 1 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x127c55 (movR32Imm32Effect 0x127c55 5 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x127c55 (fun s => s.RIP = 0x127c55) (movR32Imm32Effect 0x127c55 5 7 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x127c5a (cmpR64R64Effect 0x127c5a 2 1) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 1] []) (.flag .CF)) #v[2, 55]
    (.letOp (n := 60) (.exec 0x127c5a (fun s => s.RIP = 0x127c5a) (cmpR64R64Effect 0x127c5a 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 55]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l127c7e, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l127c5f, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l127c50 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x89, 0xC9, 0xBF, 0x02, 0x00, 0x00, 0x00, 0x48, 0x39, 0xCA, 0x73, 0x1F]

theorem code_l127c50 : ∀ x ∈ codeRange 0x127c50 bytes_l127c50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c50 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c5f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127c5f (movR64R64Effect 0x127c5f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x127c5f (fun s => s.RIP = 0x127c5f) (movR64R64Effect 0x127c5f 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x127c62 (shlR64Effect 0x127c62 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x127c62 (fun s => s.RIP = 0x127c62) (shlR64Effect 0x127c62 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x127c66 (movR64Imm64Effect 0x127c66 6 0x100000003) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x127c66 (fun s => s.RIP = 0x127c66) (movR64Imm64Effect 0x127c66 6 0x100000003) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x127c70 (addR64R64Effect 0x127c70 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x127c70 (fun s => s.RIP = 0x127c70) (addR64R64Effect 0x127c70 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.exec 0x127c73 (StorePre 0x127c73 3 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x127c73 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x127c73 2 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 62) (.out 0x127c76 (movR32Imm32Effect 0x127c76 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 63) (.exec 0x127c76 (fun s => s.RIP = 0x127c76) (movR32Imm32Effect 0x127c76 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x127c7b (movR64R64Effect 0x127c7b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 65) (.exec 0x127c7b (fun s => s.RIP = 0x127c7b) (movR64R64Effect 0x127c7b 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l127c7e, RegMap.args [(0, 0), (1, 64), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l127c5f : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE1, 0x20, 0x48, 0xBE, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x01, 0xCE, 0x89, 0x50, 0x04, 0xBF, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD1]

theorem code_l127c5f : ∀ x ∈ codeRange 0x127c5f bytes_l127c5f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c5f 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127c7e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x127c7e (StorePre 0x127c7e 2 (fun s => AddrMode.addr (.base 0 .none) s (0x127c7e + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x127c7e 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 54) (.exec 0x127c80 (StorePre 0x127c80 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x127c80 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c80 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 55) (.exec 0x127c84 (StorePre 0x127c84 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x127c84 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x127c84 1 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 0]
    (.letOp (n := 56) (.out 0x127c88 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 57) (.out 0x127c88 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x127c88 (RetPre 0x127c88) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59) (some ⟨56, by decide⟩))))))))

def bytes_l127c7e : List UInt8 :=
  [0x89, 0x38, 0x48, 0x89, 0x70, 0x08, 0x48, 0x89, 0x48, 0x10, 0xC3]

theorem code_l127c7e : ∀ x ∈ codeRange 0x127c7e bytes_l127c7e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27c7e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127cd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127cd0 (pushR64Effect 0x127cd0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x127cd0 (PushPre 0x127cd0 2) (pushR64Effect 0x127cd0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x127cd2 (pushR64Effect 0x127cd2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x127cd2 (PushPre 0x127cd2 1) (pushR64Effect 0x127cd2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x127cd3 (subR64Imm8Effect 0x127cd3 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x127cd3 (fun s => s.RIP = 0x127cd3) (subR64Imm8Effect 0x127cd3 4 0x18) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x127cd7 (movR64R64Effect 0x127cd7 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 60) (.exec 0x127cd7 (fun s => s.RIP = 0x127cd7) (movR64R64Effect 0x127cd7 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x127cda (movR64R64Effect 0x127cda 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[57]
    (.letOp (n := 62) (.exec 0x127cda (fun s => s.RIP = 0x127cda) (movR64R64Effect 0x127cda 14 4) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 63) (.out 0x127cdd (movR32Imm32Effect 0x127cdd 5 1 0x6) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 64) (.exec 0x127cdd (fun s => s.RIP = 0x127cdd) (movR32Imm32Effect 0x127cdd 5 1 0x6) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x127ce2 (movR64R64Effect 0x127ce2 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 66) (.exec 0x127ce2 (fun s => s.RIP = 0x127ce2) (movR64R64Effect 0x127ce2 7 14) (Reg.operands [.gpr 14] [])) #v[61]
    (.letOp (n := 67) (.out 0x127ce5 (movR64Imm32Effect 0x127ce5 2 0x2039a5) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x127ce5 (fun s => s.RIP = 0x127ce5) (movR64Imm32Effect 0x127ce5 2 0x2039a5) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x127cec (callEffect (fun _ => 0x128ad0) 0x127cf1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 70) (.exec 0x127cec (PushPre 0x127cec 5) (callEffect (fun _ => 0x128ad0) 0x127cf1) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 71) (.const ⟨64, 0x127cf1⟩) #v[]
    (.terminate (.call ⟨.l128ad0, RegMap.args [(0, 0), (1, 63), (2, 67), (3, 59), (4, 69), (5, 5), (6, 6), (7, 65), (14, 61), (15, 15)] 72⟩ { target := .l127cf1, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l127cd0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x48, 0x89, 0xFB, 0x49, 0x89, 0xE6, 0xB9, 0x06, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0xC7, 0xC2, 0xA5, 0x39, 0x20, 0x00, 0xE8, 0xDF, 0x0D, 0x00,
    0x00]

theorem code_l127cd0 : ∀ x ∈ codeRange 0x127cd0 bytes_l127cd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27cd0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127cf1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127cf1 (movR64R64Effect 0x127cf1 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x127cf1 (fun s => s.RIP = 0x127cf1) (movR64R64Effect 0x127cf1 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x127cf4 (movR64R64Effect 0x127cf4 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x127cf4 (fun s => s.RIP = 0x127cf4) (movR64R64Effect 0x127cf4 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x127cf7 (movR64Imm32Effect 0x127cf7 2 0x2039b0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x127cf7 (fun s => s.RIP = 0x127cf7) (movR64Imm32Effect 0x127cf7 2 0x2039b0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x127cfe (callEffect (fun _ => 0x128910) 0x127d03) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x127cfe (PushPre 0x127cfe 5) (callEffect (fun _ => 0x128910) 0x127d03) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x127d03⟩) #v[]
    (.terminate (.call ⟨.l128910, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l127d03, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l127cf1 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x89, 0xDE, 0x48, 0xC7, 0xC2, 0xB0, 0x39, 0x20, 0x00, 0xE8, 0x0D, 0x0C,
    0x00, 0x00]

theorem code_l127cf1 : ∀ x ∈ codeRange 0x127cf1 bytes_l127cf1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27cf1 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127d03 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127d03 (movR64R64Effect 0x127d03 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[0]
    (.letOp (n := 54) (.exec 0x127d03 (fun s => s.RIP = 0x127d03) (movR64R64Effect 0x127d03 7 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x127d06 (callEffect (fun _ => 0x128a40) 0x127d0b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x127d06 (PushPre 0x127d06 5) (callEffect (fun _ => 0x128a40) 0x127d0b) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x127d0b⟩) #v[]
    (.terminate (.call ⟨.l128a40, RegMap.args [(0, 0), (3, 3), (4, 55), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l127d0b, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l127d03 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0xE8, 0x35, 0x0D, 0x00, 0x00]

theorem code_l127d03 : ∀ x ∈ codeRange 0x127d03 bytes_l127d03, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27d03 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127d0b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127d0b (addR64Imm8Effect 0x127d0b 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x127d0b (fun s => s.RIP = 0x127d0b) (addR64Imm8Effect 0x127d0b 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x127d0f (popR64Effect 0x127d0f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x127d0f (popR64Effect 0x127d0f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x127d0f (PopPre 0x127d0f) (popR64Effect 0x127d0f 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x127d10 (popR64Effect 0x127d10 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[56]
    (.letOp (n := 59) (.out 0x127d10 (popR64Effect 0x127d10 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x127d10 (PopPre 0x127d10) (popR64Effect 0x127d10 2 14) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x127d12 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x127d12 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x127d12 (RetPre 0x127d12) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 58), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l127d0b : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x18, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l127d0b : ∀ x ∈ codeRange 0x127d0b bytes_l127d0b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27d0b 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127d50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127d50 (subR64Imm8Effect 0x127d50 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x127d50 (fun s => s.RIP = 0x127d50) (subR64Imm8Effect 0x127d50 4 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x127d54 (StorePre 0x127d54 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d54 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x127d54 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 53]
    (.letOp (n := 56) (.out 0x127d58 (movzxR32M8Effect 0x127d58 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x127d58 (LoadPre 0x127d58 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x127d58 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x127d58 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x127d5c (addR64Imm8Effect 0x127d5c 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 59) (.exec 0x127d5c (fun s => s.RIP = 0x127d5c) (addR64Imm8Effect 0x127d5c 4 0x1) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.out 0x127d60 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x127d60 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x127d60 (RetPre 0x127d60) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 56), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l127d50 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x01, 0x40, 0x88, 0x3C, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x48, 0x83, 0xC4, 0x01,
    0xC3]

theorem code_l127d50 : ∀ x ∈ codeRange 0x127d50 bytes_l127d50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27d50 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127fc0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127fc0 (pushR64Effect 0x127fc0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x127fc0 (PushPre 0x127fc0 1) (pushR64Effect 0x127fc0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x127fc1 (movR64R64Effect 0x127fc1 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x127fc1 (fun s => s.RIP = 0x127fc1) (movR64R64Effect 0x127fc1 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x127fc4 (testR64R64Effect 0x127fc4 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 58) (.exec 0x127fc4 (fun s => s.RIP = 0x127fc4) (testR64R64Effect 0x127fc4 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128165, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l127fcd, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 53), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l127fc0 : List UInt8 :=
  [0x53, 0x48, 0x89, 0xF8, 0x48, 0x85, 0xD2, 0x0F, 0x84, 0x98, 0x01, 0x00, 0x00]

theorem code_l127fc0 : ∀ x ∈ codeRange 0x127fc0 bytes_l127fc0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27fc0 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127fcd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127fcd (movzxR32M8Effect 0x127fcd 3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x127fcd (LoadPre 0x127fcd (fun s => AddrMode.addr (.base 6 .none) s (0x127fcd + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x127fcd 3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x127fd0 (imulR32R32Imm32Effect 0x127fd0 6 7 1 0xcd) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x127fd0 (fun s => s.RIP = 0x127fd0) (imulR32R32Imm32Effect 0x127fd0 6 7 1 0xcd) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x127fd6 (shrR32Effect 0x127fd6 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x127fd6 (fun s => s.RIP = 0x127fd6) (shrR32Effect 0x127fd6 3 7 13) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x127fd9 (shlR64Effect 0x127fd9 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x127fd9 (fun s => s.RIP = 0x127fd9) (shlR64Effect 0x127fd9 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x127fdd (cmpR16Imm8Effect 0x127fdd 4 1 0x77) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 62) (.out 0x127fdd (cmpR16Imm8Effect 0x127fdd 4 1 0x77) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 63) (.exec 0x127fdd (fun s => s.RIP = 0x127fdd) (cmpR16Imm8Effect 0x127fdd 4 1 0x77) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 64) (.pure (condOp 7)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l128177, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l127fe7, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l127fcd : List UInt8 :=
  [0x0F, 0xB6, 0x0E, 0x69, 0xF9, 0xCD, 0x00, 0x00, 0x00, 0xC1, 0xEF, 0x0D, 0x48, 0xC1, 0xE7, 0x20,
    0x66, 0x83, 0xF9, 0x77, 0x0F, 0x87, 0x90, 0x01, 0x00, 0x00]

theorem code_l127fcd : ∀ x ∈ codeRange 0x127fcd bytes_l127fcd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27fcd 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127fe7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127fe7 (orR64Imm8Effect 0x127fe7 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x127fe7 (fun s => s.RIP = 0x127fe7) (orR64Imm8Effect 0x127fe7 7 0x1) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x127feb (xorR32R32Effect 0x127feb 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x127feb (fun s => s.RIP = 0x127feb) (xorR32R32Effect 0x127feb 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 57) (.out 0x127fee (movR64Imm64Effect 0x127fee 1 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x127fee (fun s => s.RIP = 0x127fee) (movR64Imm64Effect 0x127fee 1 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128012, RegMap.args [(0, 0), (1, 57), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l127fe7 : List UInt8 :=
  [0x48, 0x83, 0xCF, 0x01, 0x45, 0x31, 0xC0, 0x48, 0xB9, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF,
    0xFF, 0xEB, 0x18]

theorem code_l127fe7 : ∀ x ∈ codeRange 0x127fe7 bytes_l127fe7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27fe7 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128000 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128000 (andR64R64Effect 0x128000 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[7, 1]
    (.letOp (n := 54) (.exec 0x128000 (fun s => s.RIP = 0x128000) (andR64R64Effect 0x128000 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[7, 1]
    (.letOp (n := 55) (.out 0x128003 (movR64R64Effect 0x128003 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x128003 (fun s => s.RIP = 0x128003) (movR64R64Effect 0x128003 9 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.terminate (.br ⟨.l128006, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l128000 : List UInt8 :=
  [0x48, 0x21, 0xCF, 0x49, 0x89, 0xF9]

theorem code_l128000 : ∀ x ∈ codeRange 0x128000 bytes_l128000, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28000 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128006 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128006 (movR64R64Effect 0x128006 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[9]
    (.letOp (n := 54) (.exec 0x128006 (fun s => s.RIP = 0x128006) (movR64R64Effect 0x128006 7 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x128009 (testR32R32Effect 0x128009 3 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[9, 9]
    (.letOp (n := 56) (.exec 0x128009 (fun s => s.RIP = 0x128009) (testR32R32Effect 0x128009 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12818a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128012, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128006 : List UInt8 :=
  [0x4C, 0x89, 0xCF, 0x45, 0x85, 0xC9, 0x0F, 0x84, 0x78, 0x01, 0x00, 0x00]

theorem code_l128006 : ∀ x ∈ codeRange 0x128006 bytes_l128006, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28006 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128012 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128012 (testR64R64Effect 0x128012 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 54) (.exec 0x128012 (fun s => s.RIP = 0x128012) (testR64R64Effect 0x128012 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128130, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12801b, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128012 : List UInt8 :=
  [0x4D, 0x85, 0xC0, 0x0F, 0x84, 0x15, 0x01, 0x00, 0x00]

theorem code_l128012 : ∀ x ∈ codeRange 0x128012 bytes_l128012, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28012 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12801b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12801b (cmpR64R64Effect 0x12801b 8 2) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 2] []) (.flag .CF)) #v[8, 2]
    (.letOp (n := 54) (.exec 0x12801b (fun s => s.RIP = 0x12801b) (cmpR64R64Effect 0x12801b 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[8, 2]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128000, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128020, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12801b : List UInt8 :=
  [0x49, 0x39, 0xD0, 0x73, 0xE0]

theorem code_l12801b : ∀ x ∈ codeRange 0x12801b bytes_l12801b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2801b 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128020 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128020 (movzxR32M8Effect 0x128020 5 9 (.sib 6 (some 8) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6, .gpr 8] []) (.reg (.gpr 9))) #v[6, 8]
    (.letOp (n := 54) (.exec 0x128020 (LoadPre 0x128020 (fun s => AddrMode.addr (.sib 6 (some 8) 0 .none) s (0x128020 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x128020 5 9 (.sib 6 (some 8) 0 .none)) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 8]
    (.letOp (n := 55) (.out 0x128025 (movR32R32Effect 0x128025 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 56) (.exec 0x128025 (fun s => s.RIP = 0x128025) (movR32R32Effect 0x128025 3 11 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 57) (.out 0x128028 (andR32Imm8Effect 0x128028 4 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 58) (.exec 0x128028 (fun s => s.RIP = 0x128028) (andR32Imm8Effect 0x128028 4 9 0x7f) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 59) (.out 0x12802c (movR32Imm32Effect 0x12802c 6 10 0x1) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 60) (.exec 0x12802c (fun s => s.RIP = 0x12802c) (movR32Imm32Effect 0x12802c 6 10 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x128032 (testR8R8Effect 0x128032 3 11 11) (EffectPart.reads (.flag .SF) [.gpr 11, .gpr 11] []) (.flag .SF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x128032 (fun s => s.RIP = 0x128032) (testR8R8Effect 0x128032 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[55, 55]
    (.letOp (n := 63) (.pure (condOp 9)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 59), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l12803b, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 57), (10, 59), (11, 55), (12, 12), (13, 13), (14, 14), (15, 15), (20, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l128020 : List UInt8 :=
  [0x46, 0x0F, 0xB6, 0x0C, 0x06, 0x45, 0x89, 0xCB, 0x41, 0x83, 0xE1, 0x7F, 0x41, 0xBA, 0x01, 0x00,
    0x00, 0x00, 0x45, 0x84, 0xDB, 0x0F, 0x89, 0xE5, 0x00, 0x00, 0x00]

theorem code_l128020 : ∀ x ∈ codeRange 0x128020 bytes_l128020, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28020 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12803b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12803b (leaR64Effect 0x12803b 10 (.base 8 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 54) (.exec 0x12803b (fun s => s.RIP = 0x12803b) (leaR64Effect 0x12803b 10 (.base 8 (.d8 0x1))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x12803f (cmpR64R64Effect 0x12803f 10 2) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[53, 2]
    (.letOp (n := 56) (.exec 0x12803f (fun s => s.RIP = 0x12803f) (cmpR64R64Effect 0x12803f 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281a0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128048, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12803b : List UInt8 :=
  [0x4D, 0x8D, 0x50, 0x01, 0x49, 0x39, 0xD2, 0x0F, 0x83, 0x58, 0x01, 0x00, 0x00]

theorem code_l12803b : ∀ x ∈ codeRange 0x12803b bytes_l12803b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2803b 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128048 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128048 (movR32R32Effect 0x128048 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[9]
    (.letOp (n := 54) (.exec 0x128048 (fun s => s.RIP = 0x128048) (movR32R32Effect 0x128048 3 11 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x12804b (movzxR32M8Effect 0x12804b 5 9 (.sib 6 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6, .gpr 10] []) (.reg (.gpr 9))) #v[6, 10]
    (.letOp (n := 56) (.exec 0x12804b (LoadPre 0x12804b (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x12804b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12804b 5 9 (.sib 6 (some 10) 0 .none)) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 10]
    (.letOp (n := 57) (.out 0x128050 (movR32R32Effect 0x128050 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x128050 (fun s => s.RIP = 0x128050) (movR32R32Effect 0x128050 3 3 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x128053 (shlR32Effect 0x128053 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 60) (.exec 0x128053 (fun s => s.RIP = 0x128053) (shlR32Effect 0x128053 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 61) (.out 0x128057 (andR32Imm8Effect 0x128057 4 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 62) (.exec 0x128057 (fun s => s.RIP = 0x128057) (andR32Imm8Effect 0x128057 4 9 0x7f) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 63) (.out 0x12805b (orR32R32Effect 0x12805b 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x12805b (fun s => s.RIP = 0x12805b) (orR32R32Effect 0x12805b 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x12805e (movR32Imm32Effect 0x12805e 6 10 0x2) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 66) (.exec 0x12805e (fun s => s.RIP = 0x12805e) (movR32Imm32Effect 0x12805e 6 10 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x128064 (testR8R8Effect 0x128064 2 3 3) (EffectPart.reads (.flag .SF) [.gpr 3, .gpr 3] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 68) (.exec 0x128064 (fun s => s.RIP = 0x128064) (testR8R8Effect 0x128064 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[57, 57]
    (.letOp (n := 69) (.pure (condOp 9)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l12806c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l128048 : List UInt8 :=
  [0x45, 0x89, 0xCB, 0x46, 0x0F, 0xB6, 0x0C, 0x16, 0x44, 0x89, 0xCB, 0x41, 0xC1, 0xE3, 0x07, 0x41,
    0x83, 0xE1, 0x7F, 0x45, 0x09, 0xD9, 0x41, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x84, 0xDB, 0x0F, 0x89,
    0xB4, 0x00, 0x00, 0x00]

theorem code_l128048 : ∀ x ∈ codeRange 0x128048 bytes_l128048, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28048 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12806c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12806c (leaR64Effect 0x12806c 10 (.base 8 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 54) (.exec 0x12806c (fun s => s.RIP = 0x12806c) (leaR64Effect 0x12806c 10 (.base 8 (.d8 0x2))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x128070 (cmpR64R64Effect 0x128070 10 2) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[53, 2]
    (.letOp (n := 56) (.exec 0x128070 (fun s => s.RIP = 0x128070) (cmpR64R64Effect 0x128070 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281a0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128079, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12806c : List UInt8 :=
  [0x4D, 0x8D, 0x50, 0x02, 0x49, 0x39, 0xD2, 0x0F, 0x83, 0x27, 0x01, 0x00, 0x00]

theorem code_l12806c : ∀ x ∈ codeRange 0x12806c bytes_l12806c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2806c 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128079 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128079 (movR32R32Effect 0x128079 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[9]
    (.letOp (n := 54) (.exec 0x128079 (fun s => s.RIP = 0x128079) (movR32R32Effect 0x128079 3 11 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x12807c (movzxR32M8Effect 0x12807c 5 9 (.sib 6 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6, .gpr 10] []) (.reg (.gpr 9))) #v[6, 10]
    (.letOp (n := 56) (.exec 0x12807c (LoadPre 0x12807c (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x12807c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12807c 5 9 (.sib 6 (some 10) 0 .none)) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 10]
    (.letOp (n := 57) (.out 0x128081 (movR32R32Effect 0x128081 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x128081 (fun s => s.RIP = 0x128081) (movR32R32Effect 0x128081 3 3 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x128084 (shlR32Effect 0x128084 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 60) (.exec 0x128084 (fun s => s.RIP = 0x128084) (shlR32Effect 0x128084 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 61) (.out 0x128088 (andR32Imm8Effect 0x128088 4 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 62) (.exec 0x128088 (fun s => s.RIP = 0x128088) (andR32Imm8Effect 0x128088 4 9 0x7f) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 63) (.out 0x12808c (orR32R32Effect 0x12808c 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x12808c (fun s => s.RIP = 0x12808c) (orR32R32Effect 0x12808c 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x12808f (movR32Imm32Effect 0x12808f 6 10 0x3) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 66) (.exec 0x12808f (fun s => s.RIP = 0x12808f) (movR32Imm32Effect 0x12808f 6 10 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x128095 (testR8R8Effect 0x128095 2 3 3) (EffectPart.reads (.flag .SF) [.gpr 3, .gpr 3] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 68) (.exec 0x128095 (fun s => s.RIP = 0x128095) (testR8R8Effect 0x128095 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[57, 57]
    (.letOp (n := 69) (.pure (condOp 9)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l12809d, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l128079 : List UInt8 :=
  [0x45, 0x89, 0xCB, 0x46, 0x0F, 0xB6, 0x0C, 0x16, 0x44, 0x89, 0xCB, 0x41, 0xC1, 0xE3, 0x07, 0x41,
    0x83, 0xE1, 0x7F, 0x45, 0x09, 0xD9, 0x41, 0xBA, 0x03, 0x00, 0x00, 0x00, 0x84, 0xDB, 0x0F, 0x89,
    0x83, 0x00, 0x00, 0x00]

theorem code_l128079 : ∀ x ∈ codeRange 0x128079 bytes_l128079, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28079 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12809d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12809d (leaR64Effect 0x12809d 10 (.base 8 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 54) (.exec 0x12809d (fun s => s.RIP = 0x12809d) (leaR64Effect 0x12809d 10 (.base 8 (.d8 0x3))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x1280a1 (cmpR64R64Effect 0x1280a1 10 2) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[53, 2]
    (.letOp (n := 56) (.exec 0x1280a1 (fun s => s.RIP = 0x1280a1) (cmpR64R64Effect 0x1280a1 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281a0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1280aa, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12809d : List UInt8 :=
  [0x4D, 0x8D, 0x50, 0x03, 0x49, 0x39, 0xD2, 0x0F, 0x83, 0xF6, 0x00, 0x00, 0x00]

theorem code_l12809d : ∀ x ∈ codeRange 0x12809d bytes_l12809d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2809d 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1280aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1280aa (movR32R32Effect 0x1280aa 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[9]
    (.letOp (n := 54) (.exec 0x1280aa (fun s => s.RIP = 0x1280aa) (movR32R32Effect 0x1280aa 3 11 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1280ad (movzxR32M8Effect 0x1280ad 5 9 (.sib 6 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6, .gpr 10] []) (.reg (.gpr 9))) #v[6, 10]
    (.letOp (n := 56) (.exec 0x1280ad (LoadPre 0x1280ad (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x1280ad + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1280ad 5 9 (.sib 6 (some 10) 0 .none)) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 10]
    (.letOp (n := 57) (.out 0x1280b2 (movR32R32Effect 0x1280b2 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x1280b2 (fun s => s.RIP = 0x1280b2) (movR32R32Effect 0x1280b2 3 3 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x1280b5 (shlR32Effect 0x1280b5 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 60) (.exec 0x1280b5 (fun s => s.RIP = 0x1280b5) (shlR32Effect 0x1280b5 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 61) (.out 0x1280b9 (andR32Imm8Effect 0x1280b9 4 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 62) (.exec 0x1280b9 (fun s => s.RIP = 0x1280b9) (andR32Imm8Effect 0x1280b9 4 9 0x7f) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 63) (.out 0x1280bd (orR32R32Effect 0x1280bd 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x1280bd (fun s => s.RIP = 0x1280bd) (orR32R32Effect 0x1280bd 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x1280c0 (movR32Imm32Effect 0x1280c0 6 10 0x4) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 66) (.exec 0x1280c0 (fun s => s.RIP = 0x1280c0) (movR32Imm32Effect 0x1280c0 6 10 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x1280c6 (testR8R8Effect 0x1280c6 2 3 3) (EffectPart.reads (.flag .SF) [.gpr 3, .gpr 3] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 68) (.exec 0x1280c6 (fun s => s.RIP = 0x1280c6) (testR8R8Effect 0x1280c6 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[57, 57]
    (.letOp (n := 69) (.pure (condOp 9)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1280ca, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1280aa : List UInt8 :=
  [0x45, 0x89, 0xCB, 0x46, 0x0F, 0xB6, 0x0C, 0x16, 0x44, 0x89, 0xCB, 0x41, 0xC1, 0xE3, 0x07, 0x41,
    0x83, 0xE1, 0x7F, 0x45, 0x09, 0xD9, 0x41, 0xBA, 0x04, 0x00, 0x00, 0x00, 0x84, 0xDB, 0x79, 0x56]

theorem code_l1280aa : ∀ x ∈ codeRange 0x1280aa bytes_l1280aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x280aa 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1280ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1280ca (leaR64Effect 0x1280ca 10 (.base 8 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 54) (.exec 0x1280ca (fun s => s.RIP = 0x1280ca) (leaR64Effect 0x1280ca 10 (.base 8 (.d8 0x4))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x1280ce (cmpR64R64Effect 0x1280ce 10 2) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[53, 2]
    (.letOp (n := 56) (.exec 0x1280ce (fun s => s.RIP = 0x1280ce) (cmpR64R64Effect 0x1280ce 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281a0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1280d7, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1280ca : List UInt8 :=
  [0x4D, 0x8D, 0x50, 0x04, 0x49, 0x39, 0xD2, 0x0F, 0x83, 0xC9, 0x00, 0x00, 0x00]

theorem code_l1280ca : ∀ x ∈ codeRange 0x1280ca bytes_l1280ca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x280ca 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1280d7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1280d7 (movR32R32Effect 0x1280d7 3 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[9]
    (.letOp (n := 54) (.exec 0x1280d7 (fun s => s.RIP = 0x1280d7) (movR32R32Effect 0x1280d7 3 11 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1280da (movzxR32M8Effect 0x1280da 5 9 (.sib 6 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6, .gpr 10] []) (.reg (.gpr 9))) #v[6, 10]
    (.letOp (n := 56) (.exec 0x1280da (LoadPre 0x1280da (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x1280da + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1280da 5 9 (.sib 6 (some 10) 0 .none)) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 10]
    (.letOp (n := 57) (.out 0x1280df (movR32R32Effect 0x1280df 3 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x1280df (fun s => s.RIP = 0x1280df) (movR32R32Effect 0x1280df 3 3 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x1280e2 (shlR32Effect 0x1280e2 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 60) (.exec 0x1280e2 (fun s => s.RIP = 0x1280e2) (shlR32Effect 0x1280e2 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 61) (.out 0x1280e6 (andR32Imm8Effect 0x1280e6 4 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 62) (.exec 0x1280e6 (fun s => s.RIP = 0x1280e6) (andR32Imm8Effect 0x1280e6 4 9 0x7f) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 63) (.out 0x1280ea (orR32R32Effect 0x1280ea 3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x1280ea (fun s => s.RIP = 0x1280ea) (orR32R32Effect 0x1280ea 3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x1280ed (movR32Imm32Effect 0x1280ed 6 10 0x5) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 66) (.exec 0x1280ed (fun s => s.RIP = 0x1280ed) (movR32Imm32Effect 0x1280ed 6 10 0x5) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x1280f3 (testR8R8Effect 0x1280f3 2 3 3) (EffectPart.reads (.flag .SF) [.gpr 3, .gpr 3] []) (.flag .SF)) #v[57, 57]
    (.letOp (n := 68) (.exec 0x1280f3 (fun s => s.RIP = 0x1280f3) (testR8R8Effect 0x1280f3 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[57, 57]
    (.letOp (n := 69) (.pure (condOp 9)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1280f7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 65), (11, 59), (12, 12), (13, 13), (14, 14), (15, 15), (20, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1280d7 : List UInt8 :=
  [0x45, 0x89, 0xCB, 0x46, 0x0F, 0xB6, 0x0C, 0x16, 0x44, 0x89, 0xCB, 0x41, 0xC1, 0xE3, 0x07, 0x41,
    0x83, 0xE1, 0x7F, 0x45, 0x09, 0xD9, 0x41, 0xBA, 0x05, 0x00, 0x00, 0x00, 0x84, 0xDB, 0x79, 0x29]

theorem code_l1280d7 : ∀ x ∈ codeRange 0x1280d7 bytes_l1280d7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x280d7 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1280f7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1280f7 (leaR64Effect 0x1280f7 10 (.base 8 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[8]
    (.letOp (n := 54) (.exec 0x1280f7 (fun s => s.RIP = 0x1280f7) (leaR64Effect 0x1280f7 10 (.base 8 (.d8 0x5))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x1280fb (cmpR64R64Effect 0x1280fb 10 2) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[53, 2]
    (.letOp (n := 56) (.exec 0x1280fb (fun s => s.RIP = 0x1280fb) (cmpR64R64Effect 0x1280fb 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281a0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128104, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1280f7 : List UInt8 :=
  [0x4D, 0x8D, 0x50, 0x05, 0x49, 0x39, 0xD2, 0x0F, 0x83, 0x9C, 0x00, 0x00, 0x00]

theorem code_l1280f7 : ∀ x ∈ codeRange 0x1280f7 bytes_l1280f7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x280f7 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128104 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128104 (movzxR32M8Effect 0x128104 5 10 (.sib 6 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6, .gpr 10] []) (.reg (.gpr 10))) #v[6, 10]
    (.letOp (n := 54) (.exec 0x128104 (LoadPre 0x128104 (fun s => AddrMode.addr (.sib 6 (some 10) 0 .none) s (0x128104 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x128104 5 10 (.sib 6 (some 10) 0 .none)) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 10]
    (.letOp (n := 55) (.out 0x128109 (cmpR32Imm8Effect 0x128109 4 10 0x10) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x128109 (fun s => s.RIP = 0x128109) (cmpR32Imm8Effect 0x128109 4 10 0x10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1281b8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128113, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128104 : List UInt8 :=
  [0x46, 0x0F, 0xB6, 0x14, 0x16, 0x41, 0x83, 0xFA, 0x10, 0x0F, 0x83, 0xA5, 0x00, 0x00, 0x00]

theorem code_l128104 : ∀ x ∈ codeRange 0x128104 bytes_l128104, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28104 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128113 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128113 (shlR32Effect 0x128113 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 54) (.exec 0x128113 (fun s => s.RIP = 0x128113) (shlR32Effect 0x128113 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 55) (.out 0x128117 (orR32R32Effect 0x128117 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[53, 10]
    (.letOp (n := 56) (.exec 0x128117 (fun s => s.RIP = 0x128117) (orR32R32Effect 0x128117 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[53, 10]
    (.letOp (n := 57) (.out 0x12811a (movR32Imm32Effect 0x12811a 6 10 0x6) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 58) (.exec 0x12811a (fun s => s.RIP = 0x12811a) (movR32Imm32Effect 0x12811a 6 10 0x6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128120, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 55), (10, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l128113 : List UInt8 :=
  [0x41, 0xC1, 0xE1, 0x07, 0x45, 0x09, 0xD1, 0x41, 0xBA, 0x06, 0x00, 0x00, 0x00]

theorem code_l128113 : ∀ x ∈ codeRange 0x128113 bytes_l128113, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28113 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128120 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128120 (addR64R64Effect 0x128120 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[8, 10]
    (.letOp (n := 54) (.exec 0x128120 (fun s => s.RIP = 0x128120) (addR64R64Effect 0x128120 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[8, 10]
    (.letOp (n := 55) (.out 0x128123 (shlR64Effect 0x128123 4 9 32) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 56) (.exec 0x128123 (fun s => s.RIP = 0x128123) (shlR64Effect 0x128123 4 9 32) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 57) (.out 0x128127 (incR64Effect 0x128127 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x128127 (fun s => s.RIP = 0x128127) (incR64Effect 0x128127 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.terminate (.br ⟨.l128006, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 53), (9, 57), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l128120 : List UInt8 :=
  [0x4D, 0x01, 0xD0, 0x49, 0xC1, 0xE1, 0x20, 0x49, 0xFF, 0xC1, 0xE9, 0xD7, 0xFE, 0xFF, 0xFF]

theorem code_l128120 : ∀ x ∈ codeRange 0x128120 bytes_l128120, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28120 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128130 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128130 (movzxR32M8Effect 0x128130 3 7 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 54) (.exec 0x128130 (LoadPre 0x128130 (fun s => AddrMode.addr (.base 6 .none) s (0x128130 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x128130 3 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x128133 (imulR32R32Imm32Effect 0x128133 7 8 7 0xcd) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x128133 (fun s => s.RIP = 0x128133) (imulR32R32Imm32Effect 0x128133 7 8 7 0xcd) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x12813a (shrR32Effect 0x12813a 4 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x12813a (fun s => s.RIP = 0x12813a) (shrR32Effect 0x12813a 4 8 13) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x12813e (cmpR16Imm8Effect 0x12813e 4 7 0x78) (EffectPart.reads (.flag .CF) [.gpr 7] []) (.flag .CF)) #v[53]
    (.letOp (n := 60) (.exec 0x12813e (fun s => s.RIP = 0x12813e) (cmpR16Imm8Effect 0x12813e 4 7 0x78) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 61) (.pure (condOp 3)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l128193, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l128144, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l128130 : List UInt8 :=
  [0x0F, 0xB6, 0x3E, 0x44, 0x69, 0xC7, 0xCD, 0x00, 0x00, 0x00, 0x41, 0xC1, 0xE8, 0x0D, 0x66, 0x83,
    0xFF, 0x78, 0x73, 0x4F]

theorem code_l128130 : ∀ x ∈ codeRange 0x128130 bytes_l128130, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28130 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128144 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128144 (shlR32Effect 0x128144 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 54) (.exec 0x128144 (fun s => s.RIP = 0x128144) (shlR32Effect 0x128144 4 8 3) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 55) (.out 0x128148 (leaR32Effect 0x128148 4 8 (.sib 8 (some 8) 2 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[53, 53]
    (.letOp (n := 56) (.exec 0x128148 (fun s => s.RIP = 0x128148) (leaR32Effect 0x128148 4 8 (.sib 8 (some 8) 2 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[53, 53]
    (.letOp (n := 57) (.out 0x12814c (subR8R8Effect 0x12814c 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[7, 55]
    (.letOp (n := 58) (.exec 0x12814c (fun s => s.RIP = 0x12814c) (subR8R8Effect 0x12814c 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 55]
    (.letOp (n := 59) (.out 0x12814f (movzxR32R8Effect 0x12814f 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 60) (.exec 0x12814f (fun s => s.RIP = 0x12814f) (movzxR32R8Effect 0x12814f 4 9 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 61) (.out 0x128153 (shlR64Effect 0x128153 4 9 32) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[59]
    (.letOp (n := 62) (.exec 0x128153 (fun s => s.RIP = 0x128153) (shlR64Effect 0x128153 4 9 32) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x128157 (incR64Effect 0x128157 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 64) (.exec 0x128157 (fun s => s.RIP = 0x128157) (incR64Effect 0x128157 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x12815a (movR32Imm32Effect 0x12815a 6 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 66) (.exec 0x12815a (fun s => s.RIP = 0x12815a) (movR32Imm32Effect 0x12815a 6 8 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128006, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 65), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l128144 : List UInt8 :=
  [0x41, 0xC1, 0xE0, 0x03, 0x47, 0x8D, 0x04, 0x80, 0x44, 0x28, 0xC7, 0x44, 0x0F, 0xB6, 0xCF, 0x49,
    0xC1, 0xE1, 0x20, 0x49, 0xFF, 0xC1, 0x41, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xE9, 0xA1, 0xFE, 0xFF,
    0xFF]

theorem code_l128144 : ∀ x ∈ codeRange 0x128144 bytes_l128144, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28144 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128165 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128165 (movR32Imm32Effect 0x128165 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x128165 (fun s => s.RIP = 0x128165) (movR32Imm32Effect 0x128165 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x12816a (StorePre 0x12816a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12816a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12816a 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 56) (.exec 0x12816e (StorePre 0x12816e 7 (fun s => AddrMode.addr (.base 0 .none) s (0x12816e + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x12816e (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x128175 (popR64Effect 0x128175 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 58) (.out 0x128175 (popR64Effect 0x128175 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x128175 (PopPre 0x128175) (popR64Effect 0x128175 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x128176 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x128176 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x128176 (RetPre 0x128176) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l128165 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0x78, 0x08, 0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x5B, 0xC3]

theorem code_l128165 : ∀ x ∈ codeRange 0x128165 bytes_l128165, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28165 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128177 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128177 (shlR32Effect 0x128177 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x128177 (fun s => s.RIP = 0x128177) (shlR32Effect 0x128177 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.terminate (.br ⟨.l12817a, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128177 : List UInt8 :=
  [0xC1, 0xE1, 0x08]

theorem code_l128177 : ∀ x ∈ codeRange 0x128177 bytes_l128177, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28177 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12817a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12817a (orR64R64Effect 0x12817a 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[7, 1]
    (.letOp (n := 54) (.exec 0x12817a (fun s => s.RIP = 0x12817a) (orR64R64Effect 0x12817a 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[7, 1]
    (.letOp (n := 55) (.exec 0x12817d (StorePre 0x12817d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12817d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12817d 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 56) (.exec 0x128181 (StorePre 0x128181 7 (fun s => AddrMode.addr (.base 0 .none) s (0x128181 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x128181 (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x128188 (popR64Effect 0x128188 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 58) (.out 0x128188 (popR64Effect 0x128188 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x128188 (PopPre 0x128188) (popR64Effect 0x128188 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x128189 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x128189 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x128189 (RetPre 0x128189) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 61), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l12817a : List UInt8 :=
  [0x48, 0x09, 0xCF, 0x48, 0x89, 0x78, 0x08, 0x48, 0xC7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5B, 0xC3]

theorem code_l12817a : ∀ x ∈ codeRange 0x12817a bytes_l12817a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2817a 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12818a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12818a (StorePre 0x12818a 3 (fun s => AddrMode.addr (.base 0 .none) s (0x12818a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12818a 6 (.base 0 .none)) (Reg.operands [.gpr 6, .gpr 0] [])) #v[6, 0]
    (.letOp (n := 54) (.exec 0x12818d (StorePre 0x12818d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x12818d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12818d 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 0]
    (.letOp (n := 55) (.out 0x128191 (popR64Effect 0x128191 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 56) (.out 0x128191 (popR64Effect 0x128191 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x128191 (PopPre 0x128191) (popR64Effect 0x128191 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x128192 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[56]
    (.letOp (n := 59) (.out 0x128192 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x128192 (RetPre 0x128192) (retEffect) (Reg.operands [.gpr 4] [])) #v[56]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 59), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61) (some ⟨58, by decide⟩))))))))))

def bytes_l12818a : List UInt8 :=
  [0x48, 0x89, 0x30, 0x48, 0x89, 0x50, 0x08, 0x5B, 0xC3]

theorem code_l12818a : ∀ x ∈ codeRange 0x12818a bytes_l12818a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2818a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128193 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128193 (movzxR32R8Effect 0x128193 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 54) (.exec 0x128193 (fun s => s.RIP = 0x128193) (movzxR32R8Effect 0x128193 4 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x128197 (shlR64Effect 0x128197 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x128197 (fun s => s.RIP = 0x128197) (shlR64Effect 0x128197 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12819b (shlR32Effect 0x12819b 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 58) (.exec 0x12819b (fun s => s.RIP = 0x12819b) (shlR32Effect 0x12819b 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7]
    (.terminate (.br ⟨.l12817a, RegMap.args [(0, 0), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l128193 : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0xC8, 0x48, 0xC1, 0xE1, 0x20, 0xC1, 0xE7, 0x08, 0xEB, 0xDA]

theorem code_l128193 : ∀ x ∈ codeRange 0x128193 bytes_l128193, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28193 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1281a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1281a0 (andR64Imm32Effect 0x1281a0 7 0xffffff00) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x1281a0 (fun s => s.RIP = 0x1281a0) (andR64Imm32Effect 0x1281a0 7 0xffffff00) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1281a7 (orR64Imm8Effect 0x1281a7 7 0x2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1281a7 (fun s => s.RIP = 0x1281a7) (orR64Imm8Effect 0x1281a7 7 0x2) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1281ab (StorePre 0x1281ab 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1281ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1281ab 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 58) (.exec 0x1281af (StorePre 0x1281af 7 (fun s => AddrMode.addr (.base 0 .none) s (0x1281af + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1281af (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1281b6 (popR64Effect 0x1281b6 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 60) (.out 0x1281b6 (popR64Effect 0x1281b6 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x1281b6 (PopPre 0x1281b6) (popR64Effect 0x1281b6 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1281b7 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[60]
    (.letOp (n := 63) (.out 0x1281b7 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x1281b7 (RetPre 0x1281b7) (retEffect) (Reg.operands [.gpr 4] [])) #v[60]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 63), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65) (some ⟨62, by decide⟩))))))))))))))

def bytes_l1281a0 : List UInt8 :=
  [0x48, 0x81, 0xE7, 0x00, 0xFF, 0xFF, 0xFF, 0x48, 0x83, 0xCF, 0x02, 0x48, 0x89, 0x78, 0x08, 0x48,
    0xC7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5B, 0xC3]

theorem code_l1281a0 : ∀ x ∈ codeRange 0x1281a0 bytes_l1281a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x281a0 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1281b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1281b8 (andR64Imm32Effect 0x1281b8 7 0xffffff00) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x1281b8 (fun s => s.RIP = 0x1281b8) (andR64Imm32Effect 0x1281b8 7 0xffffff00) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1281bf (incR64Effect 0x1281bf 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1281bf (fun s => s.RIP = 0x1281bf) (incR64Effect 0x1281bf 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1281c2 (StorePre 0x1281c2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1281c2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1281c2 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 58) (.exec 0x1281c6 (StorePre 0x1281c6 7 (fun s => AddrMode.addr (.base 0 .none) s (0x1281c6 + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x1281c6 (.base 0 .none) 0x0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1281cd (popR64Effect 0x1281cd 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 60) (.out 0x1281cd (popR64Effect 0x1281cd 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x1281cd (PopPre 0x1281cd) (popR64Effect 0x1281cd 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1281ce (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[60]
    (.letOp (n := 63) (.out 0x1281ce (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x1281ce (RetPre 0x1281ce) (retEffect) (Reg.operands [.gpr 4] [])) #v[60]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 59), (4, 63), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 65) (some ⟨62, by decide⟩))))))))))))))

def bytes_l1281b8 : List UInt8 :=
  [0x48, 0x81, 0xE7, 0x00, 0xFF, 0xFF, 0xFF, 0x48, 0xFF, 0xC7, 0x48, 0x89, 0x78, 0x08, 0x48, 0xC7,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x5B, 0xC3]

theorem code_l1281b8 : ∀ x ∈ codeRange 0x1281b8 bytes_l1281b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x281b8 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128910 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128910 (pushR64Effect 0x128910 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x128910 (PushPre 0x128910 1) (pushR64Effect 0x128910 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x128911 (movR64R64Effect 0x128911 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x128911 (fun s => s.RIP = 0x128911) (movR64R64Effect 0x128911 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x128914 (pushR64Effect 0x128914 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 58) (.exec 0x128914 (PushPre 0x128914 2) (pushR64Effect 0x128914 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 59) (.out 0x128916 (pushR64Effect 0x128916 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x128916 (PushPre 0x128916 2) (pushR64Effect 0x128916 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x128918 (pushR64Effect 0x128918 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x128918 (PushPre 0x128918 2) (pushR64Effect 0x128918 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x12891a (pushR64Effect 0x12891a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x12891a (PushPre 0x12891a 2) (pushR64Effect 0x12891a 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x12891c (pushR64Effect 0x12891c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x12891c (PushPre 0x12891c 1) (pushR64Effect 0x12891c 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x12891d (subR64Imm8Effect 0x12891d 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x12891d (fun s => s.RIP = 0x12891d) (subR64Imm8Effect 0x12891d 4 0x38) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x128921 (movR64R64Effect 0x128921 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x128921 (fun s => s.RIP = 0x128921) (movR64R64Effect 0x128921 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x128924 (movR64M64Effect 0x128924 15 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 72) (.exec 0x128924 (LoadPre 0x128924 (fun s => AddrMode.addr (.base 7 .none) s (0x128924 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128924 15 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x128927 (movR8Imm8Effect 0x128927 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 74) (.exec 0x128927 (fun s => s.RIP = 0x128927) (movR8Imm8Effect 0x128927 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 75) (.out 0x128929 (cmpM8Imm8Effect 0x128929 4 (.base 7 (.d8 0x10)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 76) (.exec 0x128929 (LoadPre 0x128929 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128929 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128929 4 (.base 7 (.d8 0x10)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 77) (.pure (condOp 4)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l12894a, RegMap.args [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l12892f, RegMap.args [(0, 73), (1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 71), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l128910 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC,
    0x38, 0x48, 0x89, 0xFB, 0x4C, 0x8B, 0x3F, 0xB0, 0x01, 0x80, 0x7F, 0x10, 0x00, 0x74, 0x1B]

theorem code_l128910 : ∀ x ∈ codeRange 0x128910 bytes_l128910, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28910 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12892f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12892f (StorePre 0x12892f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x12892f + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x12892f 3 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.out 0x128932 (incR64Effect 0x128932 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 55) (.exec 0x128932 (fun s => s.RIP = 0x128932) (incR64Effect 0x128932 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 56) (.exec 0x128935 (StorePre 0x128935 3 (fun s => AddrMode.addr (.base 3 .none) s (0x128935 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x128935 15 (.base 3 .none)) (Reg.operands [.gpr 15, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 57) (.out 0x128938 (movR64R64Effect 0x128938 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 58) (.exec 0x128938 (fun s => s.RIP = 0x128938) (movR64R64Effect 0x128938 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x12893b (addR64Imm8Effect 0x12893b 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12893b (fun s => s.RIP = 0x12893b) (addR64Imm8Effect 0x12893b 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12893f (popR64Effect 0x12893f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[59]
    (.letOp (n := 62) (.out 0x12893f (popR64Effect 0x12893f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12893f (PopPre 0x12893f) (popR64Effect 0x12893f 1 3) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x128940 (popR64Effect 0x128940 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[62]
    (.letOp (n := 65) (.out 0x128940 (popR64Effect 0x128940 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x128940 (PopPre 0x128940) (popR64Effect 0x128940 2 12) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x128942 (popR64Effect 0x128942 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 68) (.out 0x128942 (popR64Effect 0x128942 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x128942 (PopPre 0x128942) (popR64Effect 0x128942 2 13) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x128944 (popR64Effect 0x128944 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[68]
    (.letOp (n := 71) (.out 0x128944 (popR64Effect 0x128944 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x128944 (PopPre 0x128944) (popR64Effect 0x128944 2 14) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x128946 (popR64Effect 0x128946 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[71]
    (.letOp (n := 74) (.out 0x128946 (popR64Effect 0x128946 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x128946 (PopPre 0x128946) (popR64Effect 0x128946 2 15) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x128948 (popR64Effect 0x128948 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[74]
    (.letOp (n := 77) (.out 0x128948 (popR64Effect 0x128948 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x128948 (PopPre 0x128948) (popR64Effect 0x128948 1 5) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x128949 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[77]
    (.letOp (n := 80) (.out 0x128949 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x128949 (RetPre 0x128949) (retEffect) (Reg.operands [.gpr 4] [])) #v[77]
    (.terminate (.ret (RegMap.args [(0, 57), (1, 1), (2, 2), (3, 61), (4, 80), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 64), (13, 67), (14, 70), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 82) (some ⟨79, by decide⟩)))))))))))))))))))))))))))))))

def bytes_l12892f : List UInt8 :=
  [0x88, 0x43, 0x10, 0x49, 0xFF, 0xC7, 0x4C, 0x89, 0x3B, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x38,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l12892f : ∀ x ∈ codeRange 0x12892f bytes_l12892f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2892f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12894a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12894a (movR64M64Effect 0x12894a 14 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[3]
    (.letOp (n := 54) (.exec 0x12894a (LoadPre 0x12894a (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x12894a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12894a 14 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x12894e (testM8Imm8Effect 0x12894e 5 (.base 14 (.d8 0x12)) 0x80) (EffectPart.reads (.flag .ZF) [.gpr 14] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x12894e (LoadPre 0x12894e (fun s => AddrMode.addr (.base 14 (.d8 0x12)) s (0x12894e + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x12894e 5 (.base 14 (.d8 0x12)) 0x80) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12899d, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (14, 53), (15, 15), (19, 55)] 58⟩ ⟨.l128955, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (14, 53), (15, 15), (19, 55)] 58⟩))))))

def bytes_l12894a : List UInt8 :=
  [0x4C, 0x8B, 0x73, 0x08, 0x41, 0xF6, 0x46, 0x12, 0x80, 0x75, 0x48]

theorem code_l12894a : ∀ x ∈ codeRange 0x12894a bytes_l12894a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2894a 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128955 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128955 (xorR32R32Effect 0x128955 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x128955 (fun s => s.RIP = 0x128955) (xorR32R32Effect 0x128955 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x128957 (testR64R64Effect 0x128957 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 56) (.exec 0x128957 (fun s => s.RIP = 0x128957) (testR64R64Effect 0x128957 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 57) (.out 0x12895a (leaR64Effect 0x12895a 7 (.rip 0xdb2cf)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 58) (.exec 0x12895a (fun s => s.RIP = 0x12895a) (leaR64Effect 0x12895a 7 (.rip 0xdb2cf)) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x128961 (leaR64Effect 0x128961 1 (.rip 0xdb2bf)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x128961 (fun s => s.RIP = 0x128961) (leaR64Effect 0x128961 1 (.rip 0xdb2bf)) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x128968 (atFlags (condHolds 4) (cmovR64R64Effect 0x128968 4 1 7)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[59, 57, 55]
    (.letOp (n := 62) (.exec 0x128968 (fun s => s.RIP = 0x128968) (atFlags (condHolds 4) (cmovR64R64Effect 0x128968 4 1 7)) (Reg.operands [.gpr 1, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 57, 55]
    (.letOp (n := 63) (.out 0x12896c (atFlags (condHolds 5) (setccR8Effect 0x12896c 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[53, 55]
    (.letOp (n := 64) (.exec 0x12896c (fun s => s.RIP = 0x12896c) (atFlags (condHolds 5) (setccR8Effect 0x12896c 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[53, 55]
    (.letOp (n := 65) (.out 0x12896f (incR64Effect 0x12896f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x12896f (fun s => s.RIP = 0x12896f) (incR64Effect 0x12896f 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.exec 0x128972 (LoadPre 0x128972 (fun s => AddrMode.addr (.base 14 .none) s (0x128972 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128972 7 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.exec 0x128975 (LoadPre 0x128975 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x128975 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128975 8 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 69) (.exec 0x128979 (fun s => s.RIP = 0x128979) (movR64R64Effect 0x128979 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.exec 0x12897c (fun s => s.RIP = 0x12897c) (movR64R64Effect 0x12897c 6 1) (Reg.operands [.gpr 1] [])) #v[61]
    (.letOp (n := 71) (.exec 0x12897f (fun s => s.RIP = 0x12897f) (movR64R64Effect 0x12897f 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 72) (.exec 0x128982 (fun s => s.RIP = 0x128982) (movR64R64Effect 0x128982 2 0) (Reg.operands [.gpr 0] [])) #v[65]
    (cutBlock 0x128985))))))))))))))))))))

def bytes_l128955 : List UInt8 :=
  [0x31, 0xC0, 0x4D, 0x85, 0xFF, 0x48, 0x8D, 0x3D, 0xCF, 0xB2, 0x0D, 0x00, 0x48, 0x8D, 0x0D, 0xBF,
    0xB2, 0x0D, 0x00, 0x48, 0x0F, 0x44, 0xCF, 0x0F, 0x95, 0xC0, 0x48, 0xFF, 0xC0, 0x49, 0x8B, 0x3E,
    0x4D, 0x8B, 0x46, 0x08, 0x49, 0x89, 0xF4, 0x48, 0x89, 0xCE, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC2,
    0x41, 0xFF, 0x50, 0x18]

theorem code_l128955 : ∀ x ∈ codeRange 0x128955 bytes_l128955, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28955 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128989 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128989 (movR32R32Effect 0x128989 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x128989 (fun s => s.RIP = 0x128989) (movR32R32Effect 0x128989 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x12898b (movR8Imm8Effect 0x12898b 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x12898b (fun s => s.RIP = 0x12898b) (movR8Imm8Effect 0x12898b 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x12898d (testR8R8Effect 0x12898d 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x12898d (fun s => s.RIP = 0x12898d) (testR8R8Effect 0x12898d 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l12892f, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128991, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128989 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x75, 0x9E]

theorem code_l128989 : ∀ x ∈ codeRange 0x128989 bytes_l128989, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28989 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128991 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128991 (fun s => s.RIP = 0x128991) (movR64R64Effect 0x128991 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.exec 0x128994 (fun s => s.RIP = 0x128994) (movR64R64Effect 0x128994 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (cutBlock 0x128997))

def bytes_l128991 : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0x41, 0xFF, 0x55, 0x18]

theorem code_l128991 : ∀ x ∈ codeRange 0x128991 bytes_l128991, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28991 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12899b : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l12892f, RegMap.args (entryMap (live .l12899b)) 53⟩)

def bytes_l12899b : List UInt8 :=
  [0xEB, 0x92]

theorem code_l12899b : ∀ x ∈ codeRange 0x12899b bytes_l12899b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2899b 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12899d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12899d (testR64R64Effect 0x12899d 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x12899d (fun s => s.RIP = 0x12899d) (testR64R64Effect 0x12899d 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1289d3, RegMap.args [(2, 2), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l1289a2, RegMap.args [(2, 2), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l12899d : List UInt8 :=
  [0x4D, 0x85, 0xFF, 0x75, 0x31]

theorem code_l12899d : ∀ x ∈ codeRange 0x12899d bytes_l12899d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2899d 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1289a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1289a2 (LoadPre 0x1289a2 (fun s => AddrMode.addr (.base 14 .none) s (0x1289a2 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1289a2 7 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.exec 0x1289a5 (LoadPre 0x1289a5 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1289a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289a5 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1289a9 (leaR64Effect 0x1289a9 0 (.rip 0xdb281)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1289a9 (fun s => s.RIP = 0x1289a9) (leaR64Effect 0x1289a9 0 (.rip 0xdb281)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x1289b0 (fun s => s.RIP = 0x1289b0) (movR64R64Effect 0x1289b0 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 58) (.exec 0x1289b3 (fun s => s.RIP = 0x1289b3) (movR32Imm32Effect 0x1289b3 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x1289b8 (fun s => s.RIP = 0x1289b8) (movR64R64Effect 0x1289b8 13 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.exec 0x1289bb (fun s => s.RIP = 0x1289bb) (movR64R64Effect 0x1289bb 6 0) (Reg.operands [.gpr 0] [])) #v[55]
    (cutBlock 0x1289be))))))))

def bytes_l1289a2 : List UInt8 :=
  [0x49, 0x8B, 0x3E, 0x49, 0x8B, 0x4E, 0x08, 0x48, 0x8D, 0x05, 0x81, 0xB2, 0x0D, 0x00, 0x49, 0x89,
    0xD4, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x49, 0x89, 0xF5, 0x48, 0x89, 0xC6, 0xFF, 0x51, 0x18]

theorem code_l1289a2 : ∀ x ∈ codeRange 0x1289a2 bytes_l1289a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x289a2 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1289c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1289c1 (movR64R64Effect 0x1289c1 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 54) (.exec 0x1289c1 (fun s => s.RIP = 0x1289c1) (movR64R64Effect 0x1289c1 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1289c4 (movR64R64Effect 0x1289c4 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 56) (.exec 0x1289c4 (fun s => s.RIP = 0x1289c4) (movR64R64Effect 0x1289c4 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1289c7 (movR32R32Effect 0x1289c7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 58) (.exec 0x1289c7 (fun s => s.RIP = 0x1289c7) (movR32R32Effect 0x1289c7 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1289c9 (movR8Imm8Effect 0x1289c9 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x1289c9 (fun s => s.RIP = 0x1289c9) (movR8Imm8Effect 0x1289c9 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x1289cb (testR8R8Effect 0x1289cb 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 62) (.exec 0x1289cb (fun s => s.RIP = 0x1289cb) (testR8R8Effect 0x1289cb 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[57, 57]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l12892f, RegMap.args [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l1289d3, RegMap.args [(0, 59), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1289c1 : List UInt8 :=
  [0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xE2, 0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x0F, 0x85, 0x5C, 0xFF,
    0xFF, 0xFF]

theorem code_l1289c1 : ∀ x ∈ codeRange 0x1289c1 bytes_l1289c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x289c1 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1289d3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1289d3 (StorePre 0x1289d3 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd7)) s (0x1289d3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1289d3 (.base 5 (.d8 0xd7)) 0x1) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 54) (.out 0x1289d7 (movR64M64Effect 0x1289d7 0 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1289d7 (LoadPre 0x1289d7 (fun s => AddrMode.addr (.base 14 .none) s (0x1289d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1289d7 0 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1289da (movR64M64Effect 0x1289da 1 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 57) (.exec 0x1289da (LoadPre 0x1289da (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1289da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289da 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 58) (.exec 0x1289de (StorePre 0x1289de 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x1289de + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289de 0 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[54, 5]
    (.letOp (n := 59) (.exec 0x1289e2 (StorePre 0x1289e2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x1289e2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289e2 1 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[56, 5]
    (.letOp (n := 60) (.out 0x1289e6 (leaR64Effect 0x1289e6 0 (.base 5 (.d8 0xd7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 61) (.exec 0x1289e6 (fun s => s.RIP = 0x1289e6) (leaR64Effect 0x1289e6 0 (.base 5 (.d8 0xd7))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 62) (.exec 0x1289ea (StorePre 0x1289ea 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1289ea + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289ea 0 (.base 5 (.d8 0xb0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[60, 5]
    (.letOp (n := 63) (.out 0x1289ee (movR64M64Effect 0x1289ee 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 64) (.exec 0x1289ee (LoadPre 0x1289ee (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1289ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1289ee 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.exec 0x1289f2 (StorePre 0x1289f2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1289f2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289f2 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[63, 5]
    (.letOp (n := 66) (.out 0x1289f6 (leaR64Effect 0x1289f6 0 (.base 5 (.d8 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 67) (.exec 0x1289f6 (fun s => s.RIP = 0x1289f6) (leaR64Effect 0x1289f6 0 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 68) (.exec 0x1289fa (StorePre 0x1289fa 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1289fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1289fa 0 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[66, 5]
    (.letOp (n := 69) (.out 0x1289fe (leaR64Effect 0x1289fe 0 (.rip 0xdb383)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 70) (.exec 0x1289fe (fun s => s.RIP = 0x1289fe) (leaR64Effect 0x1289fe 0 (.rip 0xdb383)) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.exec 0x128a05 (StorePre 0x128a05 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128a05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128a05 0 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[69, 5]
    (.letOp (n := 72) (.out 0x128a09 (leaR64Effect 0x128a09 0 (.base 5 (.d8 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 73) (.exec 0x128a09 (fun s => s.RIP = 0x128a09) (leaR64Effect 0x128a09 0 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 74) (.exec 0x128a0d (fun s => s.RIP = 0x128a0d) (movR64R64Effect 0x128a0d 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.exec 0x128a10 (fun s => s.RIP = 0x128a10) (movR64R64Effect 0x128a10 6 0) (Reg.operands [.gpr 0] [])) #v[72]
    (cutBlock 0x128a13)))))))))))))))))))))))

def bytes_l1289d3 : List UInt8 :=
  [0xC6, 0x45, 0xD7, 0x01, 0x49, 0x8B, 0x06, 0x49, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x45, 0xA0, 0x48,
    0x89, 0x4D, 0xA8, 0x48, 0x8D, 0x45, 0xD7, 0x48, 0x89, 0x45, 0xB0, 0x49, 0x8B, 0x46, 0x10, 0x48,
    0x89, 0x45, 0xC8, 0x48, 0x8D, 0x45, 0xA0, 0x48, 0x89, 0x45, 0xB8, 0x48, 0x8D, 0x05, 0x83, 0xB3,
    0x0D, 0x00, 0x48, 0x89, 0x45, 0xC0, 0x48, 0x8D, 0x45, 0xB8, 0x48, 0x89, 0xF7, 0x48, 0x89, 0xC6,
    0xFF, 0x52, 0x18]

theorem code_l1289d3 : ∀ x ∈ codeRange 0x1289d3 bytes_l1289d3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x289d3 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a16 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a16 (testR8R8Effect 0x128a16 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x128a16 (fun s => s.RIP = 0x128a16) (testR8R8Effect 0x128a16 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128a21, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128a1a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128a16 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0x07]

theorem code_l128a16 : ∀ x ∈ codeRange 0x128a16 bytes_l128a16, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a16 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a1a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a1a (movR8Imm8Effect 0x128a1a 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x128a1a (fun s => s.RIP = 0x128a1a) (movR8Imm8Effect 0x128a1a 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l12892f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128a1a : List UInt8 :=
  [0xB0, 0x01, 0xE9, 0x0E, 0xFF, 0xFF, 0xFF]

theorem code_l128a1a : ∀ x ∈ codeRange 0x128a1a bytes_l128a1a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a1a 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a21 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128a21 (LoadPre 0x128a21 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128a21 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a21 7 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 54) (.exec 0x128a25 (LoadPre 0x128a25 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128a25 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a25 0 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x128a29 (fun s => s.RIP = 0x128a29) (leaR64Effect 0x128a29 6 (.rip 0xdb1fe)) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x128a30 (fun s => s.RIP = 0x128a30) (movR32Imm32Effect 0x128a30 5 2 0x2) (Reg.operands [] [])) #v[]
    (cutBlock 0x128a35))))

def bytes_l128a21 : List UInt8 :=
  [0x48, 0x8B, 0x7D, 0xB8, 0x48, 0x8B, 0x45, 0xC0, 0x48, 0x8D, 0x35, 0xFE, 0xB1, 0x0D, 0x00, 0xBA,
    0x02, 0x00, 0x00, 0x00, 0xFF, 0x50, 0x18]

theorem code_l128a21 : ∀ x ∈ codeRange 0x128a21 bytes_l128a21, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a21 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a38 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l12892f, RegMap.args (entryMap (live .l128a38)) 53⟩)

def bytes_l128a38 : List UInt8 :=
  [0xE9, 0xF2, 0xFE, 0xFF, 0xFF]

theorem code_l128a38 : ∀ x ∈ codeRange 0x128a38 bytes_l128a38, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a38 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a40 (movR64M64Effect 0x128a40 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 54) (.exec 0x128a40 (LoadPre 0x128a40 (fun s => AddrMode.addr (.base 7 .none) s (0x128a40 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a40 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x128a43 (movzxR32M8Effect 0x128a43 4 1 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 56) (.exec 0x128a43 (LoadPre 0x128a43 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128a43 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x128a43 4 1 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x128a47 (testR64R64Effect 0x128a47 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x128a47 (fun s => s.RIP = 0x128a47) (testR64R64Effect 0x128a47 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128abe, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128a4c, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128a40 : List UInt8 :=
  [0x48, 0x8B, 0x17, 0x0F, 0xB6, 0x4F, 0x10, 0x48, 0x85, 0xD2, 0x74, 0x72]

theorem code_l128a40 : ∀ x ∈ codeRange 0x128a40 bytes_l128a40, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a40 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a4c (movR8Imm8Effect 0x128a4c 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x128a4c (fun s => s.RIP = 0x128a4c) (movR8Imm8Effect 0x128a4c 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x128a4e (testR8R8Effect 0x128a4e 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 56) (.exec 0x128a4e (fun s => s.RIP = 0x128a4e) (testR8R8Effect 0x128a4e 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l128ab9, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128a52, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128a4c : List UInt8 :=
  [0xB0, 0x01, 0x84, 0xC9, 0x75, 0x67]

theorem code_l128a4c : ∀ x ∈ codeRange 0x128a4c bytes_l128a4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a4c 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a52 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a52 (pushR64Effect 0x128a52 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x128a52 (PushPre 0x128a52 1) (pushR64Effect 0x128a52 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x128a53 (fun s => s.RIP = 0x128a53) (movR64R64Effect 0x128a53 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 56) (.out 0x128a56 (pushR64Effect 0x128a56 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 57) (.exec 0x128a56 (PushPre 0x128a56 2) (pushR64Effect 0x128a56 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 58) (.exec 0x128a58 (PushPre 0x128a58 1) (pushR64Effect 0x128a58 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x128a59 (movR64M64Effect 0x128a59 3 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 60) (.exec 0x128a59 (LoadPre 0x128a59 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x128a59 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a59 3 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x128a5d (cmpR64Imm8Effect 0x128a5d 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 62) (.exec 0x128a5d (fun s => s.RIP = 0x128a5d) (cmpR64Imm8Effect 0x128a5d 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l128a96, RegMap.args [(2, 2), (3, 59), (7, 7), (14, 14), (19, 61)] 64⟩ ⟨.l128a63, RegMap.args [(2, 2), (3, 59), (7, 7), (14, 14), (19, 61)] 64⟩))))))))))))

def bytes_l128a52 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x56, 0x53, 0x48, 0x8B, 0x5F, 0x08, 0x48, 0x83, 0xFA, 0x01, 0x75,
    0x33]

theorem code_l128a52 : ∀ x ∈ codeRange 0x128a52 bytes_l128a52, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a52 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a63 (cmpM8Imm8Effect 0x128a63 4 (.base 7 (.d8 0x11)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 54) (.exec 0x128a63 (LoadPre 0x128a63 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x128a63 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128a63 4 (.base 7 (.d8 0x11)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128a96, RegMap.args [(3, 3), (7, 7), (19, 53)] 56⟩ ⟨.l128a69, RegMap.args [(3, 3), (7, 7), (19, 53)] 56⟩))))

def bytes_l128a63 : List UInt8 :=
  [0x80, 0x7F, 0x11, 0x00, 0x74, 0x2D]

theorem code_l128a63 : ∀ x ∈ codeRange 0x128a63 bytes_l128a63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a63 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a69 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a69 (testM8Imm8Effect 0x128a69 4 (.base 3 (.d8 0x12)) 0x80) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[3]
    (.letOp (n := 54) (.exec 0x128a69 (LoadPre 0x128a69 (fun s => AddrMode.addr (.base 3 (.d8 0x12)) s (0x128a69 + BitVec.ofNat 64 4)) 1) (testM8Imm8Effect 0x128a69 4 (.base 3 (.d8 0x12)) 0x80) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128a96, RegMap.args [(3, 3), (7, 7), (19, 53)] 56⟩ ⟨.l128a6f, RegMap.args [(3, 3), (7, 7), (19, 53)] 56⟩))))

def bytes_l128a69 : List UInt8 :=
  [0xF6, 0x43, 0x12, 0x80, 0x75, 0x27]

theorem code_l128a69 : ∀ x ∈ codeRange 0x128a69 bytes_l128a69, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a69 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a6f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a6f (movR64M64Effect 0x128a6f 0 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x128a6f (LoadPre 0x128a6f (fun s => AddrMode.addr (.base 3 .none) s (0x128a6f + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a6f 0 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x128a72 (LoadPre 0x128a72 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a72 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a72 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.exec 0x128a76 (fun s => s.RIP = 0x128a76) (leaR64Effect 0x128a76 6 (.rip 0xdb1b8)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x128a7d (fun s => s.RIP = 0x128a7d) (movR32Imm32Effect 0x128a7d 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.exec 0x128a82 (fun s => s.RIP = 0x128a82) (movR64R64Effect 0x128a82 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.exec 0x128a85 (fun s => s.RIP = 0x128a85) (movR64R64Effect 0x128a85 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (cutBlock 0x128a88)))))))

def bytes_l128a6f : List UInt8 :=
  [0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B, 0x08, 0x48, 0x8D, 0x35, 0xB8, 0xB1, 0x0D, 0x00, 0xBA, 0x01,
    0x00, 0x00, 0x00, 0x49, 0x89, 0xFE, 0x48, 0x89, 0xC7, 0xFF, 0x51, 0x18]

theorem code_l128a6f : ∀ x ∈ codeRange 0x128a6f bytes_l128a6f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a6f 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a8b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a8b (movR64R64Effect 0x128a8b 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x128a8b (fun s => s.RIP = 0x128a8b) (movR64R64Effect 0x128a8b 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x128a8e (movR32R32Effect 0x128a8e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 56) (.exec 0x128a8e (fun s => s.RIP = 0x128a8e) (movR32R32Effect 0x128a8e 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x128a90 (movR8Imm8Effect 0x128a90 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x128a90 (fun s => s.RIP = 0x128a90) (movR8Imm8Effect 0x128a90 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x128a92 (testR8R8Effect 0x128a92 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 60) (.exec 0x128a92 (fun s => s.RIP = 0x128a92) (testR8R8Effect 0x128a92 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l128ab5, RegMap.args [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l128a96, RegMap.args [(0, 57), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l128a8b : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x75, 0x1F]

theorem code_l128a8b : ∀ x ∈ codeRange 0x128a8b bytes_l128a8b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a8b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128a96 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128a96 (movR64M64Effect 0x128a96 0 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x128a96 (LoadPre 0x128a96 (fun s => AddrMode.addr (.base 3 .none) s (0x128a96 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128a96 0 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x128a99 (LoadPre 0x128a99 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x128a99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128a99 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 56) (.exec 0x128a9d (fun s => s.RIP = 0x128a9d) (leaR64Effect 0x128a9d 6 (.rip 0xdb190)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.exec 0x128aa4 (fun s => s.RIP = 0x128aa4) (movR32Imm32Effect 0x128aa4 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.exec 0x128aa9 (fun s => s.RIP = 0x128aa9) (movR64R64Effect 0x128aa9 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.exec 0x128aac (fun s => s.RIP = 0x128aac) (movR64R64Effect 0x128aac 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (cutBlock 0x128aaf)))))))

def bytes_l128a96 : List UInt8 :=
  [0x48, 0x8B, 0x03, 0x48, 0x8B, 0x4B, 0x08, 0x48, 0x8D, 0x35, 0x90, 0xB1, 0x0D, 0x00, 0xBA, 0x01,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xFB, 0x48, 0x89, 0xC7, 0xFF, 0x51, 0x18]

theorem code_l128a96 : ∀ x ∈ codeRange 0x128a96 bytes_l128a96, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a96 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128ab2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128ab2 (movR64R64Effect 0x128ab2 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x128ab2 (fun s => s.RIP = 0x128ab2) (movR64R64Effect 0x128ab2 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l128ab5, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128ab2 : List UInt8 :=
  [0x48, 0x89, 0xDF]

theorem code_l128ab2 : ∀ x ∈ codeRange 0x128ab2 bytes_l128ab2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28ab2 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128ab5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128ab5 (popR64Effect 0x128ab5 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x128ab5 (popR64Effect 0x128ab5 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x128ab5 (PopPre 0x128ab5) (popR64Effect 0x128ab5 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x128ab6 (popR64Effect 0x128ab6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[54]
    (.letOp (n := 57) (.out 0x128ab6 (popR64Effect 0x128ab6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x128ab6 (PopPre 0x128ab6) (popR64Effect 0x128ab6 2 14) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x128ab8 (popR64Effect 0x128ab8 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[57]
    (.letOp (n := 60) (.out 0x128ab8 (popR64Effect 0x128ab8 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x128ab8 (PopPre 0x128ab8) (popR64Effect 0x128ab8 1 5) (Reg.operands [.gpr 4] [])) #v[57]
    (.terminate (.br ⟨.l128ab9, RegMap.args [(0, 0), (2, 2), (3, 53), (4, 60), (5, 59), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 56), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l128ab5 : List UInt8 :=
  [0x5B, 0x41, 0x5E, 0x5D]

theorem code_l128ab5 : ∀ x ∈ codeRange 0x128ab5 bytes_l128ab5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28ab5 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128ab9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128ab9 (StorePre 0x128ab9 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128ab9 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x128ab9 3 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 54) (.out 0x128abc (movR32R32Effect 0x128abc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 55) (.exec 0x128abc (fun s => s.RIP = 0x128abc) (movR32R32Effect 0x128abc 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l128abe, RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128ab9 : List UInt8 :=
  [0x88, 0x47, 0x10, 0x89, 0xC1]

theorem code_l128ab9 : ∀ x ∈ codeRange 0x128ab9 bytes_l128ab9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28ab9 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128abe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128abe (movR32R32Effect 0x128abe 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x128abe (fun s => s.RIP = 0x128abe) (movR32R32Effect 0x128abe 2 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x128ac0 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 56) (.out 0x128ac0 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x128ac0 (RetPre 0x128ac0) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l128abe : List UInt8 :=
  [0x89, 0xC8, 0xC3]

theorem code_l128abe : ∀ x ∈ codeRange 0x128abe bytes_l128abe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28abe 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128ad0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128ad0 (pushR64Effect 0x128ad0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x128ad0 (PushPre 0x128ad0 1) (pushR64Effect 0x128ad0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x128ad1 (fun s => s.RIP = 0x128ad1) (movR64R64Effect 0x128ad1 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 56) (.out 0x128ad4 (pushR64Effect 0x128ad4 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 57) (.exec 0x128ad4 (PushPre 0x128ad4 2) (pushR64Effect 0x128ad4 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 58) (.out 0x128ad6 (pushR64Effect 0x128ad6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x128ad6 (PushPre 0x128ad6 2) (pushR64Effect 0x128ad6 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x128ad8 (pushR64Effect 0x128ad8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[58, 3]
    (.letOp (n := 61) (.exec 0x128ad8 (PushPre 0x128ad8 1) (pushR64Effect 0x128ad8 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[58, 3]
    (.letOp (n := 62) (.exec 0x128ad9 (PushPre 0x128ad9 1) (pushR64Effect 0x128ad9 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[60, 0]
    (.letOp (n := 63) (.exec 0x128ada (fun s => s.RIP = 0x128ada) (movR64R64Effect 0x128ada 3 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 64) (.exec 0x128add (fun s => s.RIP = 0x128add) (movR64R64Effect 0x128add 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x128ae0 (fun s => s.RIP = 0x128ae0) (movR64R64Effect 0x128ae0 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 66) (.exec 0x128ae3 (LoadPre 0x128ae3 (fun s => AddrMode.addr (.base 6 .none) s (0x128ae3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x128ae3 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.exec 0x128ae6 (LoadPre 0x128ae6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x128ae6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ae6 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 68) (.exec 0x128aea (fun s => s.RIP = 0x128aea) (movR64R64Effect 0x128aea 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.exec 0x128aed (fun s => s.RIP = 0x128aed) (movR64R64Effect 0x128aed 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (cutBlock 0x128af0)))))))))))))))))

def bytes_l128ad0 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x53, 0x50, 0x48, 0x89, 0xCB, 0x49, 0x89, 0xF6,
    0x49, 0x89, 0xFF, 0x48, 0x8B, 0x3E, 0x48, 0x8B, 0x46, 0x08, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xCA,
    0xFF, 0x50, 0x18]

theorem code_l128ad0 : ∀ x ∈ codeRange 0x128ad0 bytes_l128ad0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28ad0 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128af3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128af3 (testR64R64Effect 0x128af3 3 3) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 3] []) (.flag .ZF)) #v[3, 3]
    (.letOp (n := 54) (.exec 0x128af3 (fun s => s.RIP = 0x128af3) (testR64R64Effect 0x128af3 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.exec 0x128af6 (StorePre 0x128af6 4 (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x128af6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128af6 14 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 15] [])) #v[14, 15]
    (.letOp (n := 56) (.exec 0x128afa (StorePre 0x128afa 4 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x128afa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x128afa 4 0 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 15] [])) #v[0, 15]
    (.letOp (n := 57) (.exec 0x128afe (StorePre 0x128afe 7 (fun s => AddrMode.addr (.base 15 .none) s (0x128afe + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x128afe (.base 15 .none) 0x0) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 58) (.exec 0x128b05 (StorePre 0x128b05 5 (fun s => AddrMode.addr (.base 15 (.d8 0x11)) s (0x128b05 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x128b05 5 (.base 15 (.d8 0x11)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 15] [.ZF])) #v[15, 53]
    (.letOp (n := 59) (.out 0x128b0a (movR64R64Effect 0x128b0a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 60) (.exec 0x128b0a (fun s => s.RIP = 0x128b0a) (movR64R64Effect 0x128b0a 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 61) (.out 0x128b0d (addR64Imm8Effect 0x128b0d 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x128b0d (fun s => s.RIP = 0x128b0d) (addR64Imm8Effect 0x128b0d 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x128b11 (popR64Effect 0x128b11 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[61]
    (.letOp (n := 64) (.out 0x128b11 (popR64Effect 0x128b11 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x128b11 (PopPre 0x128b11) (popR64Effect 0x128b11 1 3) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x128b12 (popR64Effect 0x128b12 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x128b12 (popR64Effect 0x128b12 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x128b12 (PopPre 0x128b12) (popR64Effect 0x128b12 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x128b14 (popR64Effect 0x128b14 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x128b14 (popR64Effect 0x128b14 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x128b14 (PopPre 0x128b14) (popR64Effect 0x128b14 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x128b16 (popR64Effect 0x128b16 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x128b16 (popR64Effect 0x128b16 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x128b16 (PopPre 0x128b16) (popR64Effect 0x128b16 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x128b17 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x128b17 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x128b17 (RetPre 0x128b17) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 59), (1, 1), (2, 2), (3, 63), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l128af3 : List UInt8 :=
  [0x48, 0x85, 0xDB, 0x4D, 0x89, 0x77, 0x08, 0x41, 0x88, 0x47, 0x10, 0x49, 0xC7, 0x07, 0x00, 0x00,
    0x00, 0x00, 0x41, 0x0F, 0x94, 0x47, 0x11, 0x4C, 0x89, 0xF8, 0x48, 0x83, 0xC4, 0x08, 0x5B, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l128af3 : ∀ x ∈ codeRange 0x128af3 bytes_l128af3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28af3 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128b20_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x128b5a (testR32R32Effect 0x128b5a 2 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 93) (.exec 0x128b5a (fun s => s.RIP = 0x128b5a) (testR32R32Effect 0x128b5a 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 94) (.out 0x128b5c (movR32Imm32Effect 0x128b5c 5 6 0x2d) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 95) (.exec 0x128b5c (fun s => s.RIP = 0x128b5c) (movR32Imm32Effect 0x128b5c 5 6 0x2d) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x128b61 (atFlags (condHolds 5) (cmovR32R32Effect 0x128b61 3 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[94, 88, 92]
    (.letOp (n := 97) (.exec 0x128b61 (fun s => s.RIP = 0x128b61) (atFlags (condHolds 5) (cmovR32R32Effect 0x128b61 3 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[94, 88, 92]
    (.letOp (n := 98) (.exec 0x128b64 (StorePre 0x128b64 3 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128b64 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x128b64 6 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[96, 55]
    (.letOp (n := 99) (.out 0x128b67 (movR32Imm32Effect 0x128b67 6 9 0x1) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 100) (.exec 0x128b67 (fun s => s.RIP = 0x128b67) (movR32Imm32Effect 0x128b67 6 9 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x128b6d (atFlags (condHolds 5) (cmovR64R64Effect 0x128b6d 4 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[99, 90, 92]
    (.letOp (n := 102) (.exec 0x128b6d (fun s => s.RIP = 0x128b6d) (atFlags (condHolds 5) (cmovR64R64Effect 0x128b6d 4 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[99, 90, 92]
    (.letOp (n := 103) (.out 0x128b71 (addR64R64Effect 0x128b71 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[101, 69]
    (.letOp (n := 104) (.exec 0x128b71 (fun s => s.RIP = 0x128b71) (addR64R64Effect 0x128b71 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[101, 69]
    (.letOp (n := 105) (.out 0x128b74 (testR32Imm32Effect 0x128b74 7 15 0x800000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[76]
    (.letOp (n := 106) (.exec 0x128b74 (fun s => s.RIP = 0x128b74) (testR32Imm32Effect 0x128b74 7 15 0x800000) (Reg.operands [.gpr 15] [])) #v[76]
    (.letOp (n := 107) (.exec 0x128b7b (StorePre 0x128b7b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128b7b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128b7b 1 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 55]
    (.letOp (n := 108) (.pure (condOp 5)) #v[105]
    (.terminate (.condBr (Fin.last 108) ⟨.l128bdc, RegMap.args [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)] 109⟩ ⟨.l128b81, RegMap.args [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (10, 10), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)] 109⟩))))))))))))))))))

def bytes_l128b20_1 : List UInt8 :=
  [0x85, 0xF6, 0xBE, 0x2D, 0x00, 0x00, 0x00, 0x0F, 0x45, 0xF2, 0x89, 0x75, 0xD4, 0x41, 0xB9, 0x01,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0x45, 0xC8, 0x4D, 0x01, 0xE9, 0x41, 0xF7, 0xC7, 0x00, 0x00, 0x80,
    0x00, 0x48, 0x89, 0x4D, 0xB8, 0x75, 0x5B]

theorem code_l128b20_1 : ∀ x ∈ codeRange 0x128b5a bytes_l128b20_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28b5a 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128b20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128b20 (pushR64Effect 0x128b20 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x128b20 (PushPre 0x128b20 1) (pushR64Effect 0x128b20 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x128b21 (movR64R64Effect 0x128b21 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x128b21 (fun s => s.RIP = 0x128b21) (movR64R64Effect 0x128b21 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x128b24 (pushR64Effect 0x128b24 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 58) (.exec 0x128b24 (PushPre 0x128b24 2) (pushR64Effect 0x128b24 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 59) (.out 0x128b26 (pushR64Effect 0x128b26 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x128b26 (PushPre 0x128b26 2) (pushR64Effect 0x128b26 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x128b28 (pushR64Effect 0x128b28 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x128b28 (PushPre 0x128b28 2) (pushR64Effect 0x128b28 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x128b2a (pushR64Effect 0x128b2a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x128b2a (PushPre 0x128b2a 2) (pushR64Effect 0x128b2a 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x128b2c (pushR64Effect 0x128b2c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x128b2c (PushPre 0x128b2c 1) (pushR64Effect 0x128b2c 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x128b2d (subR64Imm8Effect 0x128b2d 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x128b2d (fun s => s.RIP = 0x128b2d) (subR64Imm8Effect 0x128b2d 4 0x48) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x128b31 (movR64R64Effect 0x128b31 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 70) (.exec 0x128b31 (fun s => s.RIP = 0x128b31) (movR64R64Effect 0x128b31 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 71) (.exec 0x128b34 (StorePre 0x128b34 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128b34 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128b34 8 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 8, .gpr 5] [])) #v[8, 55]
    (.letOp (n := 72) (.out 0x128b38 (movR64R64Effect 0x128b38 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 73) (.exec 0x128b38 (fun s => s.RIP = 0x128b38) (movR64R64Effect 0x128b38 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x128b3b (movR64R64Effect 0x128b3b 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 75) (.exec 0x128b3b (fun s => s.RIP = 0x128b3b) (movR64R64Effect 0x128b3b 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 76) (.out 0x128b3e (movR32M32Effect 0x128b3e 15 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 77) (.exec 0x128b3e (LoadPre 0x128b3e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x128b3e + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x128b3e 15 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x128b42 (movR32R32Effect 0x128b42 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 79) (.exec 0x128b42 (fun s => s.RIP = 0x128b42) (movR32R32Effect 0x128b42 3 0 15) (Reg.operands [.gpr 15] [])) #v[76]
    (.letOp (n := 80) (.out 0x128b45 (andEaxImm32Effect 0x128b45 0x200000) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[78]
    (.letOp (n := 81) (.exec 0x128b45 (fun s => s.RIP = 0x128b45) (andEaxImm32Effect 0x128b45 0x200000) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 82) (.out 0x128b4a (cmpR32Imm8Effect 0x128b4a 3 0 0x1) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[80]
    (.letOp (n := 83) (.exec 0x128b4a (fun s => s.RIP = 0x128b4a) (cmpR32Imm8Effect 0x128b4a 3 0 0x1) (Reg.operands [.gpr 0] [])) #v[80]
    (.letOp (n := 84) (.out 0x128b4d (movR32Imm32Effect 0x128b4d 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 85) (.exec 0x128b4d (fun s => s.RIP = 0x128b4d) (movR32Imm32Effect 0x128b4d 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x128b52 (atFlags StatusFlags.CF (sbbR32R32Effect 0x128b52 2 2 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[84, 84, 82]
    (.letOp (n := 87) (.exec 0x128b52 (fun s => s.RIP = 0x128b52) (atFlags StatusFlags.CF (sbbR32R32Effect 0x128b52 2 2 2)) (Reg.operands [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 84, 82]
    (.letOp (n := 88) (.out 0x128b54 (orR32Imm8Effect 0x128b54 3 2 0x2b) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[86]
    (.letOp (n := 89) (.exec 0x128b54 (fun s => s.RIP = 0x128b54) (orR32Imm8Effect 0x128b54 3 2 0x2b) (Reg.operands [.gpr 2] [])) #v[86]
    (.letOp (n := 90) (.out 0x128b57 (shrR32Effect 0x128b57 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[80]
    (.letOp (n := 91) (.exec 0x128b57 (fun s => s.RIP = 0x128b57) (shrR32Effect 0x128b57 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (b_l128b20_1)))))))))))))))))))))))))))))))))))))))

def bytes_l128b20 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC,
    0x48, 0x4D, 0x89, 0xCD, 0x4C, 0x89, 0x45, 0xC0, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xFC, 0x44, 0x8B,
    0x7F, 0x10, 0x44, 0x89, 0xF8, 0x25, 0x00, 0x00, 0x20, 0x00, 0x83, 0xF8, 0x01, 0xBA, 0x00, 0x00,
    0x00, 0x00, 0x19, 0xD2, 0x83, 0xCA, 0x2B, 0xC1, 0xE8, 0x15] ++ bytes_l128b20_1

theorem code_l128b20 : ∀ x ∈ codeRange 0x128b20 bytes_l128b20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x28b20 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l128b20_1

@[cfg_block] def b_l128b81 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128b81 (xorR32R32Effect 0x128b81 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x128b81 (fun s => s.RIP = 0x128b81) (xorR32R32Effect 0x128b81 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.out 0x128b84 (movzxR32M16Effect 0x128b84 6 3 (.sib 12 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 56) (.exec 0x128b84 (LoadPre 0x128b84 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x128b84 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x128b84 6 3 (.sib 12 none 0 (.d8 0x14))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x128b8a (cmpR64R64Effect 0x128b8a 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[9, 55]
    (.letOp (n := 58) (.exec 0x128b8a (fun s => s.RIP = 0x128b8a) (cmpR64R64Effect 0x128b8a 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 55]
    (.letOp (n := 59) (.pure (condOp 2)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128c97, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128b93, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128b81 : List UInt8 :=
  [0x45, 0x31, 0xF6, 0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14, 0x49, 0x39, 0xD9, 0x0F, 0x82, 0x04, 0x01,
    0x00, 0x00]

theorem code_l128b81 : ∀ x ∈ codeRange 0x128b81 bytes_l128b81, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28b81 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128b93 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128b93 (movR64M64Effect 0x128b93 15 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x128b93 (LoadPre 0x128b93 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x128b93 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128b93 15 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x128b97 (movR64M64Effect 0x128b97 12 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x128b97 (LoadPre 0x128b97 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x128b97 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128b97 12 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x128b9c (movR64R64Effect 0x128b9c 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x128b9c (fun s => s.RIP = 0x128b9c) (movR64R64Effect 0x128b9c 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x128b9f (movR64R64Effect 0x128b9f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 60) (.exec 0x128b9f (fun s => s.RIP = 0x128b9f) (movR64R64Effect 0x128b9f 6 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 61) (.out 0x128ba2 (movR32M32LowEffect 0x128ba2 2 (.base 5 (.d8 0xd4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 62) (.exec 0x128ba2 (LoadPre 0x128ba2 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128ba2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x128ba2 2 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x128ba5 (movR64R64Effect 0x128ba5 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 64) (.exec 0x128ba5 (fun s => s.RIP = 0x128ba5) (movR64R64Effect 0x128ba5 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x128ba8 (movR64M64Effect 0x128ba8 8 (.base 5 (.d8 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 66) (.exec 0x128ba8 (LoadPre 0x128ba8 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128ba8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ba8 8 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.out 0x128bac (callEffect (fun _ => 0x129c30) 0x128bb1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x128bac (PushPre 0x128bac 5) (callEffect (fun _ => 0x129c30) 0x128bb1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x128bb1⟩) #v[]
    (.terminate (.call ⟨.l129c30, RegMap.args [(0, 0), (1, 63), (2, 61), (3, 3), (4, 67), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l128bb1, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l128b93 : List UInt8 :=
  [0x4D, 0x8B, 0x3C, 0x24, 0x4D, 0x8B, 0x64, 0x24, 0x08, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0x8B,
    0x55, 0xD4, 0x4C, 0x89, 0xF1, 0x4C, 0x8B, 0x45, 0xB8, 0xE8, 0x7F, 0x10, 0x00, 0x00]

theorem code_l128b93 : ∀ x ∈ codeRange 0x128b93 bytes_l128b93, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28b93 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128bb1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128bb1 (movR32R32Effect 0x128bb1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x128bb1 (fun s => s.RIP = 0x128bb1) (movR32R32Effect 0x128bb1 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x128bb3 (movR8Imm8Effect 0x128bb3 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x128bb3 (fun s => s.RIP = 0x128bb3) (movR8Imm8Effect 0x128bb3 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x128bb5 (testR8R8Effect 0x128bb5 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x128bb5 (fun s => s.RIP = 0x128bb5) (testR8R8Effect 0x128bb5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128e28, RegMap.args [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128bbd, RegMap.args [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128bb1 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x0F, 0x85, 0x6B, 0x02, 0x00, 0x00]

theorem code_l128bb1 : ∀ x ∈ codeRange 0x128bb1 bytes_l128bb1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28bb1 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128bbd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128bbd (LoadPre 0x128bbd (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x128bbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128bbd 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.exec 0x128bc2 (fun s => s.RIP = 0x128bc2) (movR64R64Effect 0x128bc2 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x128bc5 (LoadPre 0x128bc5 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128bc5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128bc5 6 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.exec 0x128bc9 (fun s => s.RIP = 0x128bc9) (movR64R64Effect 0x128bc9 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x128bcc (addR64Imm8Effect 0x128bcc 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x128bcc (fun s => s.RIP = 0x128bcc) (addR64Imm8Effect 0x128bcc 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x128bd0 (popR64Effect 0x128bd0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x128bd0 (PopPre 0x128bd0) (popR64Effect 0x128bd0 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x128bd1 (popR64Effect 0x128bd1 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x128bd1 (PopPre 0x128bd1) (popR64Effect 0x128bd1 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x128bd3 (popR64Effect 0x128bd3 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x128bd3 (PopPre 0x128bd3) (popR64Effect 0x128bd3 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x128bd5 (popR64Effect 0x128bd5 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x128bd5 (PopPre 0x128bd5) (popR64Effect 0x128bd5 2 14) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x128bd7 (popR64Effect 0x128bd7 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x128bd7 (PopPre 0x128bd7) (popR64Effect 0x128bd7 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.exec 0x128bd9 (PopPre 0x128bd9) (popR64Effect 0x128bd9 1 5) (Reg.operands [.gpr 4] [])) #v[67]
    (cutBlock 0x128bda)))))))))))))))))

def bytes_l128bbd : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xFF, 0x48, 0x8B, 0x75, 0xC0, 0x4C, 0x89, 0xEA, 0x48,
    0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xFF, 0xE0]

theorem code_l128bbd : ∀ x ∈ codeRange 0x128bbd bytes_l128bbd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28bbd 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128bdc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128bdc (cmpR64Imm8Effect 0x128bdc 1 0x20) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 54) (.exec 0x128bdc (fun s => s.RIP = 0x128bdc) (cmpR64Imm8Effect 0x128bdc 1 0x20) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128bfa, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128be2, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128bdc : List UInt8 :=
  [0x48, 0x83, 0xF9, 0x20, 0x73, 0x18]

theorem code_l128bdc : ∀ x ∈ codeRange 0x128bdc bytes_l128bdc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28bdc 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128be2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128be2 (testR64R64Effect 0x128be2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x128be2 (fun s => s.RIP = 0x128be2) (testR64R64Effect 0x128be2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128c0e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128be7, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128be2 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x74, 0x27]

theorem code_l128be2 : ∀ x ∈ codeRange 0x128be2 bytes_l128be2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28be2 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128be7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128be7 (movR32R32Effect 0x128be7 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[1]
    (.letOp (n := 54) (.exec 0x128be7 (fun s => s.RIP = 0x128be7) (movR32R32Effect 0x128be7 3 10 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x128bea (andR32Imm8Effect 0x128bea 4 10 0x3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 56) (.exec 0x128bea (fun s => s.RIP = 0x128bea) (andR32Imm8Effect 0x128bea 4 10 0x3) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.out 0x128bee (cmpR64Imm8Effect 0x128bee 1 0x4) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 58) (.exec 0x128bee (fun s => s.RIP = 0x128bee) (cmpR64Imm8Effect 0x128bee 1 0x4) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128c12, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128bf4, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128be7 : List UInt8 :=
  [0x41, 0x89, 0xCA, 0x41, 0x83, 0xE2, 0x03, 0x48, 0x83, 0xF9, 0x04, 0x73, 0x1E]

theorem code_l128be7 : ∀ x ∈ codeRange 0x128be7 bytes_l128be7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28be7 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128bf4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128bf4 (xorR32R32Effect 0x128bf4 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x128bf4 (fun s => s.RIP = 0x128bf4) (xorR32R32Effect 0x128bf4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x128bf6 (xorR32R32Effect 0x128bf6 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x128bf6 (fun s => s.RIP = 0x128bf6) (xorR32R32Effect 0x128bf6 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l128c68, RegMap.args [(0, 55), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l128bf4 : List UInt8 :=
  [0x31, 0xD2, 0x31, 0xC0, 0xEB, 0x6E]

theorem code_l128bf4 : ∀ x ∈ codeRange 0x128bf4 bytes_l128bf4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28bf4 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128bfa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128bfa (movR64R64Effect 0x128bfa 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x128bfa (fun s => s.RIP = 0x128bfa) (movR64R64Effect 0x128bfa 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x128bfd (movR64R64Effect 0x128bfd 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 56) (.exec 0x128bfd (fun s => s.RIP = 0x128bfd) (movR64R64Effect 0x128bfd 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x128c00 (movR64R64Effect 0x128c00 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 58) (.exec 0x128c00 (fun s => s.RIP = 0x128c00) (movR64R64Effect 0x128c00 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x128c03 (callEffect (callMemPtr 0x128c03 (.rip 0xdb1e7)) (0x128c03 + BitVec.ofNat 64 (callMemLen (.rip 0xdb1e7)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x128c03 (GoesTo (CallMemPre 0x128c03 (.rip 0xdb1e7)) (callEffect (callMemPtr 0x128c03 (.rip 0xdb1e7)) (0x128c03 + BitVec.ofNat 64 (callMemLen (.rip 0xdb1e7)))) 0x1297a0) (callEffect (callMemPtr 0x128c03 (.rip 0xdb1e7)) (0x128c03 + BitVec.ofNat 64 (callMemLen (.rip 0xdb1e7)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x128c09⟩) #v[]
    (.terminate (.call ⟨.l1297a0, RegMap.args [(1, 1), (3, 57), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l128c09, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l128bfa : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x89, 0xCE, 0x4C, 0x89, 0xCB, 0xFF, 0x15, 0xE7, 0xB1, 0x0D, 0x00]

theorem code_l128bfa : ∀ x ∈ codeRange 0x128bfa bytes_l128bfa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28bfa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c09 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c09 (movR64R64Effect 0x128c09 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3]
    (.letOp (n := 54) (.exec 0x128c09 (fun s => s.RIP = 0x128c09) (movR64R64Effect 0x128c09 9 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l128c85, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128c09 : List UInt8 :=
  [0x49, 0x89, 0xD9, 0xEB, 0x77]

theorem code_l128c09 : ∀ x ∈ codeRange 0x128c09 bytes_l128c09, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c09 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c0e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c0e (xorR32R32Effect 0x128c0e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x128c0e (fun s => s.RIP = 0x128c0e) (xorR32R32Effect 0x128c0e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l128c85, RegMap.args [(0, 53), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128c0e : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x73]

theorem code_l128c0e : ∀ x ∈ codeRange 0x128c0e bytes_l128c0e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c0e 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c12 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c12 (movR32R32Effect 0x128c12 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 54) (.exec 0x128c12 (fun s => s.RIP = 0x128c12) (movR32R32Effect 0x128c12 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x128c14 (andR32Imm8Effect 0x128c14 3 6 0x1c) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x128c14 (fun s => s.RIP = 0x128c14) (andR32Imm8Effect 0x128c14 3 6 0x1c) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x128c17 (xorR32R32Effect 0x128c17 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x128c17 (fun s => s.RIP = 0x128c17) (xorR32R32Effect 0x128c17 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x128c19 (xorR32R32Effect 0x128c19 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 60) (.exec 0x128c19 (fun s => s.RIP = 0x128c19) (xorR32R32Effect 0x128c19 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 61) (.exec 0x128c1b (fun s => s.RIP = 0x128c1b) (fun _ => nopEffect 0x128c1b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128c20, RegMap.args [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l128c12 : List UInt8 :=
  [0x89, 0xCE, 0x83, 0xE6, 0x1C, 0x31, 0xD2, 0x31, 0xC0, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l128c12 : ∀ x ∈ codeRange 0x128c12 bytes_l128c12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c12 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c20 (xorR32R32Effect 0x128c20 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x128c20 (fun s => s.RIP = 0x128c20) (xorR32R32Effect 0x128c20 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x128c22 (cmpM8Imm8Effect 0x128c22 5 (.sib 14 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 56) (.out 0x128c22 (cmpM8Imm8Effect 0x128c22 5 (.sib 14 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 57) (.exec 0x128c22 (LoadPre 0x128c22 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x128c22 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x128c22 5 (.sib 14 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 58) (.out 0x128c27 (atFlags (condHolds 13) (setccR8Effect 0x128c27 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 7))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x128c27 (fun s => s.RIP = 0x128c27) (atFlags (condHolds 13) (setccR8Effect 0x128c27 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x128c2b (addR64R64Effect 0x128c2b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[58, 0]
    (.letOp (n := 61) (.exec 0x128c2b (fun s => s.RIP = 0x128c2b) (addR64R64Effect 0x128c2b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 62) (.out 0x128c2e (xorR32R32Effect 0x128c2e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 63) (.exec 0x128c2e (fun s => s.RIP = 0x128c2e) (xorR32R32Effect 0x128c2e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 64) (.out 0x128c30 (cmpM8Imm8Effect 0x128c30 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 65) (.out 0x128c30 (cmpM8Imm8Effect 0x128c30 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 66) (.exec 0x128c30 (LoadPre 0x128c30 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x128c30 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c30 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 67) (.out 0x128c36 (atFlags (condHolds 13) (setccR8Effect 0x128c36 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x128c36 (fun s => s.RIP = 0x128c36) (atFlags (condHolds 13) (setccR8Effect 0x128c36 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x128c39 (xorR32R32Effect 0x128c39 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 70) (.exec 0x128c39 (fun s => s.RIP = 0x128c39) (xorR32R32Effect 0x128c39 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 71) (.out 0x128c3c (cmpM8Imm8Effect 0x128c3c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 72) (.out 0x128c3c (cmpM8Imm8Effect 0x128c3c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 73) (.exec 0x128c3c (LoadPre 0x128c3c (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x128c3c + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c3c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 74) (.out 0x128c42 (atFlags (condHolds 13) (setccR8Effect 0x128c42 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x128c42 (fun s => s.RIP = 0x128c42) (atFlags (condHolds 13) (setccR8Effect 0x128c42 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x128c46 (addR64R64Effect 0x128c46 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x128c46 (fun s => s.RIP = 0x128c46) (addR64R64Effect 0x128c46 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x128c49 (addR64R64Effect 0x128c49 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x128c49 (fun s => s.RIP = 0x128c49) (addR64R64Effect 0x128c49 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x128c4c (xorR32R32Effect 0x128c4c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x128c4c (fun s => s.RIP = 0x128c4c) (xorR32R32Effect 0x128c4c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x128c4e (cmpM8Imm8Effect 0x128c4e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 83) (.out 0x128c4e (cmpM8Imm8Effect 0x128c4e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 84) (.exec 0x128c4e (LoadPre 0x128c4e (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x128c4e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x128c4e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 85) (.out 0x128c54 (atFlags (condHolds 13) (setccR8Effect 0x128c54 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x128c54 (fun s => s.RIP = 0x128c54) (atFlags (condHolds 13) (setccR8Effect 0x128c54 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x128c57 (addR64R64Effect 0x128c57 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x128c57 (fun s => s.RIP = 0x128c57) (addR64R64Effect 0x128c57 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x128c5a (addR64Imm8Effect 0x128c5a 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 90) (.exec 0x128c5a (fun s => s.RIP = 0x128c5a) (addR64Imm8Effect 0x128c5a 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 91) (.out 0x128c5e (cmpR64R64Effect 0x128c5e 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 89]
    (.letOp (n := 92) (.exec 0x128c5e (fun s => s.RIP = 0x128c5e) (cmpR64R64Effect 0x128c5e 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l128c20, RegMap.args [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l128c63, RegMap.args [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l128c20 : List UInt8 :=
  [0x31, 0xFF, 0x41, 0x80, 0x3C, 0x16, 0xC0, 0x40, 0x0F, 0x9D, 0xC7, 0x48, 0x01, 0xC7, 0x31, 0xC0,
    0x41, 0x80, 0x7C, 0x16, 0x01, 0xC0, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xC0, 0x41, 0x80, 0x7C, 0x16,
    0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x49, 0x01, 0xC0, 0x49, 0x01, 0xF8, 0x31, 0xC0, 0x41, 0x80,
    0x7C, 0x16, 0x03, 0xC0, 0x0F, 0x9D, 0xC0, 0x4C, 0x01, 0xC0, 0x48, 0x83, 0xC2, 0x04, 0x48, 0x39,
    0xD6, 0x75, 0xBD]

theorem code_l128c20 : ∀ x ∈ codeRange 0x128c20 bytes_l128c20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c20 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c63 (testR64R64Effect 0x128c63 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[10, 10]
    (.letOp (n := 54) (.exec 0x128c63 (fun s => s.RIP = 0x128c63) (testR64R64Effect 0x128c63 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128c85, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128c68, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128c63 : List UInt8 :=
  [0x4D, 0x85, 0xD2, 0x74, 0x1D]

theorem code_l128c63 : ∀ x ∈ codeRange 0x128c63 bytes_l128c63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c63 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c68 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c68 (addR64R64Effect 0x128c68 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[2, 14]
    (.letOp (n := 54) (.exec 0x128c68 (fun s => s.RIP = 0x128c68) (addR64R64Effect 0x128c68 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[2, 14]
    (.letOp (n := 55) (.out 0x128c6b (xorR32R32Effect 0x128c6b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x128c6b (fun s => s.RIP = 0x128c6b) (xorR32R32Effect 0x128c6b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.exec 0x128c6d (fun s => s.RIP = 0x128c6d) (fun _ => nopEffect 0x128c6d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128c70, RegMap.args [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128c68 : List UInt8 :=
  [0x4C, 0x01, 0xF2, 0x31, 0xF6, 0x0F, 0x1F, 0x00]

theorem code_l128c68 : ∀ x ∈ codeRange 0x128c68 bytes_l128c68, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c68 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c70 (xorR32R32Effect 0x128c70 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x128c70 (fun s => s.RIP = 0x128c70) (xorR32R32Effect 0x128c70 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x128c72 (cmpM8Imm8Effect 0x128c72 4 (.sib 2 (some 6) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 2, .gpr 6] []) (.flag .SF)) #v[2, 6]
    (.letOp (n := 56) (.out 0x128c72 (cmpM8Imm8Effect 0x128c72 4 (.sib 2 (some 6) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 2, .gpr 6] []) (.flag .OF)) #v[2, 6]
    (.letOp (n := 57) (.exec 0x128c72 (LoadPre 0x128c72 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x128c72 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x128c72 4 (.sib 2 (some 6) 0 .none) 0xc0) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 58) (.out 0x128c76 (atFlags (condHolds 13) (setccR8Effect 0x128c76 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 7))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x128c76 (fun s => s.RIP = 0x128c76) (atFlags (condHolds 13) (setccR8Effect 0x128c76 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x128c7a (addR64R64Effect 0x128c7a 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x128c7a (fun s => s.RIP = 0x128c7a) (addR64R64Effect 0x128c7a 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x128c7d (incR64Effect 0x128c7d 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 63) (.exec 0x128c7d (fun s => s.RIP = 0x128c7d) (incR64Effect 0x128c7d 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6]
    (.letOp (n := 64) (.out 0x128c80 (cmpR64R64Effect 0x128c80 10 6) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 6] []) (.flag .ZF)) #v[10, 62]
    (.letOp (n := 65) (.exec 0x128c80 (fun s => s.RIP = 0x128c80) (cmpR64R64Effect 0x128c80 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[10, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l128c70, RegMap.args [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l128c85, RegMap.args [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l128c70 : List UInt8 :=
  [0x31, 0xFF, 0x80, 0x3C, 0x32, 0xC0, 0x40, 0x0F, 0x9D, 0xC7, 0x48, 0x01, 0xF8, 0x48, 0xFF, 0xC6,
    0x49, 0x39, 0xF2, 0x75, 0xEB]

theorem code_l128c70 : ∀ x ∈ codeRange 0x128c70 bytes_l128c70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c70 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c85 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c85 (addR64R64Effect 0x128c85 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[9, 0]
    (.letOp (n := 54) (.exec 0x128c85 (fun s => s.RIP = 0x128c85) (addR64R64Effect 0x128c85 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 0]
    (.letOp (n := 55) (.out 0x128c88 (movzxR32M16Effect 0x128c88 6 3 (.sib 12 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 56) (.exec 0x128c88 (LoadPre 0x128c88 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x128c88 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x128c88 6 3 (.sib 12 none 0 (.d8 0x14))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x128c8e (cmpR64R64Effect 0x128c8e 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.exec 0x128c8e (fun s => s.RIP = 0x128c8e) (cmpR64R64Effect 0x128c8e 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128b93, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128c97, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128c85 : List UInt8 :=
  [0x49, 0x01, 0xC1, 0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14, 0x49, 0x39, 0xD9, 0x0F, 0x83, 0xFC, 0xFE,
    0xFF, 0xFF]

theorem code_l128c85 : ∀ x ∈ codeRange 0x128c85 bytes_l128c85, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c85 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128c97 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128c97 (testR32Imm32Effect 0x128c97 7 15 0x1000000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 54) (.exec 0x128c97 (fun s => s.RIP = 0x128c97) (testR32Imm32Effect 0x128c97 7 15 0x1000000) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x128c9e (StorePre 0x128c9e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128c9e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128c9e 13 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 56) (.exec 0x128ca2 (StorePre 0x128ca2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x128ca2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128ca2 9 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 9, .gpr 5] [])) #v[9, 5]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l128cd0, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128ca8, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128c97 : List UInt8 :=
  [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x01, 0x4C, 0x89, 0x6D, 0xA8, 0x4C, 0x89, 0x4D, 0xA0, 0x75,
    0x28]

theorem code_l128c97 : ∀ x ∈ codeRange 0x128c97 bytes_l128c97, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28c97 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128ca8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128ca8 (movR32R32Effect 0x128ca8 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 54) (.exec 0x128ca8 (fun s => s.RIP = 0x128ca8) (movR32R32Effect 0x128ca8 2 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x128caa (subR32R32Effect 0x128caa 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[53, 9]
    (.letOp (n := 56) (.exec 0x128caa (fun s => s.RIP = 0x128caa) (subR32R32Effect 0x128caa 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[53, 9]
    (.letOp (n := 57) (.out 0x128cad (movR32R32Effect 0x128cad 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 58) (.exec 0x128cad (fun s => s.RIP = 0x128cad) (movR32R32Effect 0x128cad 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x128cb0 (shrR32Effect 0x128cb0 3 0 29) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x128cb0 (fun s => s.RIP = 0x128cb0) (shrR32Effect 0x128cb0 3 0 29) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x128cb3 (andR32Imm8Effect 0x128cb3 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x128cb3 (fun s => s.RIP = 0x128cb3) (andR32Imm8Effect 0x128cb3 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 63) (.out 0x128cb6 (leaR64Effect 0x128cb6 1 (.rip 0xdae97)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 64) (.exec 0x128cb6 (fun s => s.RIP = 0x128cb6) (leaR64Effect 0x128cb6 1 (.rip 0xdae97)) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x128cbd (movsxdR64M32Effect 0x128cbd 4 0 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x128cbd (LoadPre 0x128cbd (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x128cbd + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x128cbd 4 0 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.exec 0x128cc1 (fun s => s.RIP = 0x128cc1) (addR64R64Effect 0x128cc1 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[65, 63]
    (.letOp (n := 68) (.exec 0x128cc4 (StorePre 0x128cc4 3 (fun s => AddrMode.addr (.base 5 (.d8 0xb4)) s (0x128cc4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x128cc4 2 (.base 5 (.d8 0xb4))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[55, 5]
    (cutBlock 0x128cc7))))))))))))))))

def bytes_l128ca8 : List UInt8 :=
  [0x89, 0xDA, 0x44, 0x29, 0xCA, 0x44, 0x89, 0xF8, 0xC1, 0xE8, 0x1D, 0x83, 0xE0, 0x03, 0x48, 0x8D,
    0x0D, 0x97, 0xAE, 0x0D, 0x00, 0x48, 0x63, 0x04, 0x81, 0x48, 0x01, 0xC8, 0x89, 0x55, 0xB4, 0xFF,
    0xE0]

theorem code_l128ca8 : ∀ x ∈ codeRange 0x128ca8 bytes_l128ca8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28ca8 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128cd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128cd0 (movR64M64Effect 0x128cd0 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x128cd0 (LoadPre 0x128cd0 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128cd0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128cd0 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.exec 0x128cd5 (StorePre 0x128cd5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128cd5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x128cd5 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 56) (.out 0x128cd9 (andEaxImm32Effect 0x128cd9 0x9fe00000) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x128cd9 (fun s => s.RIP = 0x128cd9) (andEaxImm32Effect 0x128cd9 0x9fe00000) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x128cde (orEaxImm32Effect 0x128cde 0x20000030) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x128cde (fun s => s.RIP = 0x128cde) (orEaxImm32Effect 0x128cde 0x20000030) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.exec 0x128ce3 (StorePre 0x128ce3 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128ce3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x128ce3 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 12] [])) #v[58, 12]
    (.letOp (n := 61) (.out 0x128ce8 (movR64M64Effect 0x128ce8 13 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 62) (.exec 0x128ce8 (LoadPre 0x128ce8 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x128ce8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128ce8 13 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 63) (.out 0x128cec (movR64M64Effect 0x128cec 15 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 64) (.exec 0x128cec (LoadPre 0x128cec (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x128cec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x128cec 15 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 65) (.out 0x128cf1 (movR64R64Effect 0x128cf1 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 66) (.exec 0x128cf1 (fun s => s.RIP = 0x128cf1) (movR64R64Effect 0x128cf1 7 13) (Reg.operands [.gpr 13] [])) #v[61]
    (.letOp (n := 67) (.out 0x128cf4 (movR64R64Effect 0x128cf4 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 68) (.exec 0x128cf4 (fun s => s.RIP = 0x128cf4) (movR64R64Effect 0x128cf4 6 15) (Reg.operands [.gpr 15] [])) #v[63]
    (.letOp (n := 69) (.out 0x128cf7 (movR32M32LowEffect 0x128cf7 2 (.base 5 (.d8 0xd4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 70) (.exec 0x128cf7 (LoadPre 0x128cf7 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x128cf7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x128cf7 2 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x128cfa (movR64R64Effect 0x128cfa 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 72) (.exec 0x128cfa (fun s => s.RIP = 0x128cfa) (movR64R64Effect 0x128cfa 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x128cfd (movR64M64Effect 0x128cfd 8 (.base 5 (.d8 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 74) (.exec 0x128cfd (LoadPre 0x128cfd (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x128cfd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128cfd 8 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 75) (.out 0x128d01 (callEffect (fun _ => 0x129c30) 0x128d06) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x128d01 (PushPre 0x128d01 5) (callEffect (fun _ => 0x129c30) 0x128d06) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x128d06⟩) #v[]
    (.terminate (.call ⟨.l129c30, RegMap.args [(0, 58), (1, 71), (2, 69), (3, 3), (4, 75), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (10, 10), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l128d06, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l128cd0 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x45, 0xC8, 0x25, 0x00, 0x00, 0xE0, 0x9F, 0x0D, 0x30,
    0x00, 0x00, 0x20, 0x41, 0x89, 0x44, 0x24, 0x10, 0x4D, 0x8B, 0x2C, 0x24, 0x4D, 0x8B, 0x7C, 0x24,
    0x08, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0x8B, 0x55, 0xD4, 0x4C, 0x89, 0xF1, 0x4C, 0x8B, 0x45,
    0xB8, 0xE8, 0x2A, 0x0F, 0x00, 0x00]

theorem code_l128cd0 : ∀ x ∈ codeRange 0x128cd0 bytes_l128cd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28cd0 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d06 (movR32R32Effect 0x128d06 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x128d06 (fun s => s.RIP = 0x128d06) (movR32R32Effect 0x128d06 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x128d08 (movR8Imm8Effect 0x128d08 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x128d08 (fun s => s.RIP = 0x128d08) (movR8Imm8Effect 0x128d08 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x128d0a (testR8R8Effect 0x128d0a 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x128d0a (fun s => s.RIP = 0x128d0a) (testR8R8Effect 0x128d0a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l128e28, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l128d12, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l128d06 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x0F, 0x85, 0x16, 0x01, 0x00, 0x00]

theorem code_l128d06 : ∀ x ∈ codeRange 0x128d06 bytes_l128d06, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d06 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d12 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d12 (subR32M32Effect 0x128d12 3 3 (.base 5 (.d8 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[3, 5]
    (.letOp (n := 54) (.exec 0x128d12 (LoadPre 0x128d12 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x128d12 + BitVec.ofNat 64 3)) 4) (subR32M32Effect 0x128d12 3 3 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 55) (.out 0x128d15 (incR32Effect 0x128d15 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.exec 0x128d15 (fun s => s.RIP = 0x128d15) (incR32Effect 0x128d15 2 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x128d17 (fun s => s.RIP = 0x128d17) (fun _ => nopEffect 0x128d17 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l128d20, RegMap.args [(3, 55), (5, 5), (13, 13)] 58⟩))))))

def bytes_l128d12 : List UInt8 :=
  [0x2B, 0x5D, 0xA0, 0xFF, 0xC3, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l128d12 : ∀ x ∈ codeRange 0x128d12 bytes_l128d12, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d12 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d20 (decR16Effect 0x128d20 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[3]
    (.letOp (n := 54) (.exec 0x128d20 (fun s => s.RIP = 0x128d20) (decR16Effect 0x128d20 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128d37, RegMap.args [(5, 5), (13, 13), (19, 53)] 56⟩ ⟨.l128d25, RegMap.args [(5, 5), (13, 13), (19, 53)] 56⟩))))

def bytes_l128d20 : List UInt8 :=
  [0x66, 0xFF, 0xCB, 0x74, 0x12]

theorem code_l128d20 : ∀ x ∈ codeRange 0x128d20 bytes_l128d20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d20 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d25 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128d25 (fun s => s.RIP = 0x128d25) (movR64R64Effect 0x128d25 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 54) (.exec 0x128d28 (fun s => s.RIP = 0x128d28) (movR32Imm32Effect 0x128d28 5 6 0x30) (Reg.operands [] [])) #v[]
    (cutBlock 0x128d2d))

def bytes_l128d25 : List UInt8 :=
  [0x4C, 0x89, 0xEF, 0xBE, 0x30, 0x00, 0x00, 0x00, 0x41, 0xFF, 0x57, 0x20]

theorem code_l128d25 : ∀ x ∈ codeRange 0x128d25 bytes_l128d25, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d25 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d31 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d31 (testR8R8Effect 0x128d31 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x128d31 (fun s => s.RIP = 0x128d31) (testR8R8Effect 0x128d31 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l128d20, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l128d35, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l128d31 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0xEB]

theorem code_l128d31 : ∀ x ∈ codeRange 0x128d31 bytes_l128d31, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d31 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d35 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l128da6, RegMap.args (entryMap (live .l128d35)) 53⟩)

def bytes_l128d35 : List UInt8 :=
  [0xEB, 0x6F]

theorem code_l128d35 : ∀ x ∈ codeRange 0x128d35 bytes_l128d35, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d35 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d37 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x128d37 (fun s => s.RIP = 0x128d37) (movR64R64Effect 0x128d37 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 54) (.exec 0x128d3a (LoadPre 0x128d3a (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x128d3a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d3a 6 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x128d3e (LoadPre 0x128d3e (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x128d3e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d3e 2 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 5] [])) #v[5]
    (cutBlock 0x128d42)))

def bytes_l128d37 : List UInt8 :=
  [0x4C, 0x89, 0xEF, 0x48, 0x8B, 0x75, 0xC0, 0x48, 0x8B, 0x55, 0xA8, 0x41, 0xFF, 0x57, 0x18]

theorem code_l128d37 : ∀ x ∈ codeRange 0x128d37 bytes_l128d37, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d37 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d46 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d46 (testR8R8Effect 0x128d46 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x128d46 (fun s => s.RIP = 0x128d46) (testR8R8Effect 0x128d46 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x128d48 (movR8Imm8Effect 0x128d48 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x128d48 (fun s => s.RIP = 0x128d48) (movR8Imm8Effect 0x128d48 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l128e28, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l128d50, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128d46 : List UInt8 :=
  [0x84, 0xC0, 0xB0, 0x01, 0x0F, 0x85, 0xD8, 0x00, 0x00, 0x00]

theorem code_l128d46 : ∀ x ∈ codeRange 0x128d46 bytes_l128d46, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d46 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128d50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128d50 (movR64M64Effect 0x128d50 0 (.base 5 (.d8 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x128d50 (LoadPre 0x128d50 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x128d50 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x128d50 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x128d54 (StorePre 0x128d54 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x128d54 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x128d54 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 12] [])) #v[53, 12]
    (.letOp (n := 56) (.out 0x128d59 (xorR32R32Effect 0x128d59 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 57) (.exec 0x128d59 (fun s => s.RIP = 0x128d59) (xorR32R32Effect 0x128d59 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l128e28, RegMap.args [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l128d50 : List UInt8 :=
  [0x48, 0x8B, 0x45, 0xC8, 0x49, 0x89, 0x44, 0x24, 0x10, 0x31, 0xC0, 0xE9, 0xC8, 0x00, 0x00, 0x00]

theorem code_l128d50 : ∀ x ∈ codeRange 0x128d50 bytes_l128d50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d50 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128da6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128da6 (movR8Imm8Effect 0x128da6 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x128da6 (fun s => s.RIP = 0x128da6) (movR8Imm8Effect 0x128da6 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l128e28, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l128da6 : List UInt8 :=
  [0xB0, 0x01, 0xEB, 0x7E]

theorem code_l128da6 : ∀ x ∈ codeRange 0x128da6 bytes_l128da6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28da6 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l128e28 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x128e28 (addR64Imm8Effect 0x128e28 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x128e28 (fun s => s.RIP = 0x128e28) (addR64Imm8Effect 0x128e28 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x128e2c (popR64Effect 0x128e2c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x128e2c (popR64Effect 0x128e2c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x128e2c (PopPre 0x128e2c) (popR64Effect 0x128e2c 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x128e2d (popR64Effect 0x128e2d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x128e2d (popR64Effect 0x128e2d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x128e2d (PopPre 0x128e2d) (popR64Effect 0x128e2d 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x128e2f (popR64Effect 0x128e2f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x128e2f (popR64Effect 0x128e2f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x128e2f (PopPre 0x128e2f) (popR64Effect 0x128e2f 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x128e31 (popR64Effect 0x128e31 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x128e31 (popR64Effect 0x128e31 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x128e31 (PopPre 0x128e31) (popR64Effect 0x128e31 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x128e33 (popR64Effect 0x128e33 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x128e33 (popR64Effect 0x128e33 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x128e33 (PopPre 0x128e33) (popR64Effect 0x128e33 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x128e35 (popR64Effect 0x128e35 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x128e35 (popR64Effect 0x128e35 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x128e35 (PopPre 0x128e35) (popR64Effect 0x128e35 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x128e36 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x128e36 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x128e36 (RetPre 0x128e36) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l128e28 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l128e28 : ∀ x ∈ codeRange 0x128e28 bytes_l128e28, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28e28 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129100 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129100 (pushR64Effect 0x129100 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129100 (PushPre 0x129100 1) (pushR64Effect 0x129100 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x129101 (movR64R64Effect 0x129101 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x129101 (fun s => s.RIP = 0x129101) (movR64R64Effect 0x129101 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129104 (pushR64Effect 0x129104 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 58) (.exec 0x129104 (PushPre 0x129104 2) (pushR64Effect 0x129104 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 59) (.out 0x129106 (pushR64Effect 0x129106 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x129106 (PushPre 0x129106 2) (pushR64Effect 0x129106 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x129108 (pushR64Effect 0x129108 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x129108 (PushPre 0x129108 2) (pushR64Effect 0x129108 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x12910a (pushR64Effect 0x12910a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x12910a (PushPre 0x12910a 2) (pushR64Effect 0x12910a 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x12910c (pushR64Effect 0x12910c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x12910c (PushPre 0x12910c 1) (pushR64Effect 0x12910c 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x12910d (subR64Imm8Effect 0x12910d 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x12910d (fun s => s.RIP = 0x12910d) (subR64Imm8Effect 0x12910d 4 0x28) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x129111 (movR64R64Effect 0x129111 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 70) (.exec 0x129111 (fun s => s.RIP = 0x129111) (movR64R64Effect 0x129111 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x129114 (movR64R64Effect 0x129114 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 72) (.exec 0x129114 (fun s => s.RIP = 0x129114) (movR64R64Effect 0x129114 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x129117 (movR32M32Effect 0x129117 15 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 74) (.exec 0x129117 (LoadPre 0x129117 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x129117 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x129117 15 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x12911b (testR32Imm32Effect 0x12911b 7 15 0x18000000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[73]
    (.letOp (n := 76) (.exec 0x12911b (fun s => s.RIP = 0x12911b) (testR32Imm32Effect 0x12911b 7 15 0x18000000) (Reg.operands [.gpr 15] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 4)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l1292ab, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 71), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l129128, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 69), (14, 71), (15, 73), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l129100 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC,
    0x28, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xF6, 0x44, 0x8B, 0x7F, 0x10, 0x41, 0xF7, 0xC7, 0x00, 0x00,
    0x00, 0x18, 0x0F, 0x84, 0x83, 0x01, 0x00, 0x00]

theorem code_l129100 : ∀ x ∈ codeRange 0x129100 bytes_l129100, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29100 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129128 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129128 (testR32Imm32Effect 0x129128 7 15 0x10000000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 54) (.exec 0x129128 (fun s => s.RIP = 0x129128) (testR32Imm32Effect 0x129128 7 15 0x10000000) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12915e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l129131, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129128 : List UInt8 :=
  [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x10, 0x75, 0x2D]

theorem code_l129128 : ∀ x ∈ codeRange 0x129128 bytes_l129128, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29128 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129131 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129131 (cmpR64Imm8Effect 0x129131 13 0x20) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 54) (.exec 0x129131 (fun s => s.RIP = 0x129131) (cmpR64Imm8Effect 0x129131 13 0x20) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1291bf, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12913b, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129131 : List UInt8 :=
  [0x49, 0x83, 0xFD, 0x20, 0x0F, 0x83, 0x84, 0x00, 0x00, 0x00]

theorem code_l129131 : ∀ x ∈ codeRange 0x129131 bytes_l129131, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29131 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12913b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12913b (testR64R64Effect 0x12913b 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 54) (.exec 0x12913b (fun s => s.RIP = 0x12913b) (testR64R64Effect 0x12913b 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1291ed, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l129144, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l12913b : List UInt8 :=
  [0x4D, 0x85, 0xED, 0x0F, 0x84, 0xA9, 0x00, 0x00, 0x00]

theorem code_l12913b : ∀ x ∈ codeRange 0x12913b bytes_l12913b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2913b 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129144 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129144 (movR32R32Effect 0x129144 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x129144 (fun s => s.RIP = 0x129144) (movR32R32Effect 0x129144 3 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x129147 (andR32Imm8Effect 0x129147 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x129147 (fun s => s.RIP = 0x129147) (andR32Imm8Effect 0x129147 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x12914a (cmpR64Imm8Effect 0x12914a 13 0x4) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[13]
    (.letOp (n := 58) (.exec 0x12914a (fun s => s.RIP = 0x12914a) (cmpR64Imm8Effect 0x12914a 13 0x4) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1291f5, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57)] 60⟩ ⟨.l129154, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57)] 60⟩))))))))

def bytes_l129144 : List UInt8 :=
  [0x44, 0x89, 0xE8, 0x83, 0xE0, 0x03, 0x49, 0x83, 0xFD, 0x04, 0x0F, 0x83, 0xA1, 0x00, 0x00, 0x00]

theorem code_l129144 : ∀ x ∈ codeRange 0x129144 bytes_l129144, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29144 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129154 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129154 (xorR32R32Effect 0x129154 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x129154 (fun s => s.RIP = 0x129154) (xorR32R32Effect 0x129154 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.out 0x129156 (xorR32R32Effect 0x129156 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 56) (.exec 0x129156 (fun s => s.RIP = 0x129156) (xorR32R32Effect 0x129156 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.terminate (.br ⟨.l12924c, RegMap.args [(0, 0), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 55), (13, 13), (14, 14), (15, 15)] 57⟩)))))

def bytes_l129154 : List UInt8 :=
  [0x31, 0xC9, 0x45, 0x31, 0xE4, 0xE9, 0xEE, 0x00, 0x00, 0x00]

theorem code_l129154 : ∀ x ∈ codeRange 0x129154 bytes_l129154, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29154 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12915e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12915e (movzxR32M16Effect 0x12915e 5 12 (.base 7 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 54) (.exec 0x12915e (LoadPre 0x12915e (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x12915e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12915e 5 12 (.base 7 (.d8 0x16))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x129163 (testR64R64Effect 0x129163 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x129163 (fun s => s.RIP = 0x129163) (testR64R64Effect 0x129163 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1291d9, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55)] 58⟩ ⟨.l129168, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15), (19, 55)] 58⟩))))))

def bytes_l12915e : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x67, 0x16, 0x4D, 0x85, 0xE4, 0x74, 0x71]

theorem code_l12915e : ∀ x ∈ codeRange 0x12915e bytes_l12915e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2915e 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129168 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129168 (addR64R64Effect 0x129168 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[13, 14]
    (.letOp (n := 54) (.exec 0x129168 (fun s => s.RIP = 0x129168) (addR64R64Effect 0x129168 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[13, 14]
    (.letOp (n := 55) (.out 0x12916b (xorR32R32Effect 0x12916b 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x12916b (fun s => s.RIP = 0x12916b) (xorR32R32Effect 0x12916b 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x12916d (movR64R64Effect 0x12916d 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 58) (.exec 0x12916d (fun s => s.RIP = 0x12916d) (movR64R64Effect 0x12916d 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x129170 (movR64R64Effect 0x129170 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 60) (.exec 0x129170 (fun s => s.RIP = 0x129170) (movR64R64Effect 0x129170 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l129195, RegMap.args [(0, 59), (1, 57), (2, 55), (4, 4), (5, 5), (7, 7), (12, 12), (13, 53), (14, 14), (15, 15)] 61⟩)))))))))

def bytes_l129168 : List UInt8 :=
  [0x4D, 0x01, 0xF5, 0x31, 0xD2, 0x4C, 0x89, 0xF1, 0x4C, 0x89, 0xE0, 0xEB, 0x20]

theorem code_l129168 : ∀ x ∈ codeRange 0x129168 bytes_l129168, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29168 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129180 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129180 (leaR64Effect 0x129180 8 (.base 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 54) (.exec 0x129180 (fun s => s.RIP = 0x129180) (leaR64Effect 0x129180 8 (.base 1 (.d8 0x1))) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l129184, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (12, 12), (13, 13), (14, 14), (15, 15)] 55⟩)))

def bytes_l129180 : List UInt8 :=
  [0x4C, 0x8D, 0x41, 0x01]

theorem code_l129180 : ∀ x ∈ codeRange 0x129180 bytes_l129180, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29180 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129184 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129184 (movR64R64Effect 0x129184 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 54) (.exec 0x129184 (fun s => s.RIP = 0x129184) (movR64R64Effect 0x129184 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 55) (.out 0x129187 (subR64R64Effect 0x129187 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[53, 1]
    (.letOp (n := 56) (.exec 0x129187 (fun s => s.RIP = 0x129187) (subR64R64Effect 0x129187 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[53, 1]
    (.letOp (n := 57) (.out 0x12918a (addR64R64Effect 0x12918a 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[55, 6]
    (.letOp (n := 58) (.exec 0x12918a (fun s => s.RIP = 0x12918a) (addR64R64Effect 0x12918a 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[55, 6]
    (.letOp (n := 59) (.out 0x12918d (movR64R64Effect 0x12918d 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 60) (.exec 0x12918d (fun s => s.RIP = 0x12918d) (movR64R64Effect 0x12918d 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 61) (.out 0x129190 (decR64Effect 0x129190 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 62) (.out 0x129190 (decR64Effect 0x129190 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[0]
    (.letOp (n := 63) (.exec 0x129190 (fun s => s.RIP = 0x129190) (decR64Effect 0x129190 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1291db, RegMap.args [(0, 61), (1, 59), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62)] 65⟩ ⟨.l129195, RegMap.args [(0, 61), (1, 59), (2, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (19, 62)] 65⟩)))))))))))))

def bytes_l129184 : List UInt8 :=
  [0x4C, 0x89, 0xC2, 0x48, 0x29, 0xCA, 0x48, 0x01, 0xF2, 0x4C, 0x89, 0xC1, 0x48, 0xFF, 0xC8, 0x74,
    0x46]

theorem code_l129184 : ∀ x ∈ codeRange 0x129184 bytes_l129184, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29184 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129195 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129195 (movR64R64Effect 0x129195 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 54) (.exec 0x129195 (fun s => s.RIP = 0x129195) (movR64R64Effect 0x129195 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x129198 (cmpR64R64Effect 0x129198 1 13) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 13] []) (.flag .ZF)) #v[1, 13]
    (.letOp (n := 56) (.exec 0x129198 (fun s => s.RIP = 0x129198) (cmpR64R64Effect 0x129198 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[1, 13]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1291df, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55)] 58⟩ ⟨.l12919d, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 53), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55)] 58⟩))))))

def bytes_l129195 : List UInt8 :=
  [0x48, 0x89, 0xD6, 0x4C, 0x39, 0xE9, 0x74, 0x42]

theorem code_l129195 : ∀ x ∈ codeRange 0x129195 bytes_l129195, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29195 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12919d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12919d (movzxR32M8Effect 0x12919d 3 2 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 54) (.exec 0x12919d (LoadPre 0x12919d (fun s => AddrMode.addr (.base 1 .none) s (0x12919d + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x12919d 3 2 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1291a0 (testR8R8Effect 0x1291a0 2 2 2) (EffectPart.reads (.flag .SF) [.gpr 2, .gpr 2] []) (.flag .SF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1291a0 (fun s => s.RIP = 0x1291a0) (testR8R8Effect 0x1291a0 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 9)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l129180, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55)] 58⟩ ⟨.l1291a4, RegMap.args [(0, 0), (1, 1), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (20, 55)] 58⟩))))))

def bytes_l12919d : List UInt8 :=
  [0x0F, 0xB6, 0x11, 0x84, 0xD2, 0x79, 0xDC]

theorem code_l12919d : ∀ x ∈ codeRange 0x12919d bytes_l12919d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2919d 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291a4 (cmpR8Imm8Effect 0x1291a4 3 2 0xe0) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.exec 0x1291a4 (fun s => s.RIP = 0x1291a4) (cmpR8Imm8Effect 0x1291a4 3 2 0xe0) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.pure (condOp 2)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1291b9, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53)] 56⟩ ⟨.l1291a9, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53)] 56⟩))))

def bytes_l1291a4 : List UInt8 :=
  [0x80, 0xFA, 0xE0, 0x72, 0x10]

theorem code_l1291a4 : ∀ x ∈ codeRange 0x1291a4 bytes_l1291a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291a4 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291a9 (cmpR8Imm8Effect 0x1291a9 3 2 0xf0) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.exec 0x1291a9 (fun s => s.RIP = 0x1291a9) (cmpR8Imm8Effect 0x1291a9 3 2 0xf0) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1291ac (movR64R64Effect 0x1291ac 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 56) (.exec 0x1291ac (fun s => s.RIP = 0x1291ac) (movR64R64Effect 0x1291ac 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1291af (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1291af 8 0xff)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x1291af (fun s => s.RIP = 0x1291af) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1291af 8 0xff)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 53]
    (.letOp (n := 59) (.out 0x1291b3 (addR64Imm8Effect 0x1291b3 8 0x3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x1291b3 (fun s => s.RIP = 0x1291b3) (addR64Imm8Effect 0x1291b3 8 0x3) (Reg.operands [.gpr 8] [])) #v[57]
    (.terminate (.br ⟨.l129184, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (12, 12), (13, 13), (14, 14), (15, 15)] 61⟩)))))))))

def bytes_l1291a9 : List UInt8 :=
  [0x80, 0xFA, 0xF0, 0x49, 0x89, 0xC8, 0x49, 0x83, 0xD8, 0xFF, 0x49, 0x83, 0xC0, 0x03, 0xEB, 0xCB]

theorem code_l1291a9 : ∀ x ∈ codeRange 0x1291a9 bytes_l1291a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291a9 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291b9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291b9 (leaR64Effect 0x1291b9 8 (.base 1 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 54) (.exec 0x1291b9 (fun s => s.RIP = 0x1291b9) (leaR64Effect 0x1291b9 8 (.base 1 (.d8 0x2))) (Reg.operands [.gpr 1] [])) #v[1]
    (.terminate (.br ⟨.l129184, RegMap.args [(0, 0), (1, 1), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (12, 12), (13, 13), (14, 14), (15, 15)] 55⟩)))

def bytes_l1291b9 : List UInt8 :=
  [0x4C, 0x8D, 0x41, 0x02, 0xEB, 0xC5]

theorem code_l1291b9 : ∀ x ∈ codeRange 0x1291b9 bytes_l1291b9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291b9 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291bf (movR64R64Effect 0x1291bf 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 54) (.exec 0x1291bf (fun s => s.RIP = 0x1291bf) (movR64R64Effect 0x1291bf 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1291c2 (movR64R64Effect 0x1291c2 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x1291c2 (fun s => s.RIP = 0x1291c2) (movR64R64Effect 0x1291c2 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1291c5 (movR64R64Effect 0x1291c5 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 58) (.exec 0x1291c5 (fun s => s.RIP = 0x1291c5) (movR64R64Effect 0x1291c5 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x1291c8 (callEffect (callMemPtr 0x1291c8 (.rip 0xdac22)) (0x1291c8 + BitVec.ofNat 64 (callMemLen (.rip 0xdac22)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1291c8 (GoesTo (CallMemPre 0x1291c8 (.rip 0xdac22)) (callEffect (callMemPtr 0x1291c8 (.rip 0xdac22)) (0x1291c8 + BitVec.ofNat 64 (callMemLen (.rip 0xdac22)))) 0x1297a0) (callEffect (callMemPtr 0x1291c8 (.rip 0xdac22)) (0x1291c8 + BitVec.ofNat 64 (callMemLen (.rip 0xdac22)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1291ce⟩) #v[]
    (.terminate (.call ⟨.l1297a0, RegMap.args [(1, 1), (3, 53), (4, 59), (5, 5), (6, 57), (7, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1291ce, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1291bf : List UInt8 :=
  [0x48, 0x89, 0xFB, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xEE, 0xFF, 0x15, 0x22, 0xAC, 0x0D, 0x00]

theorem code_l1291bf : ∀ x ∈ codeRange 0x1291bf bytes_l1291bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291bf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291ce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291ce (movR64R64Effect 0x1291ce 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x1291ce (fun s => s.RIP = 0x1291ce) (movR64R64Effect 0x1291ce 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1291d1 (movR64R64Effect 0x1291d1 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[0]
    (.letOp (n := 56) (.exec 0x1291d1 (fun s => s.RIP = 0x1291d1) (movR64R64Effect 0x1291d1 12 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l129275, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (7, 53), (12, 55), (13, 13), (14, 14), (15, 15)] 57⟩)))))

def bytes_l1291ce : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x49, 0x89, 0xC4, 0xE9, 0x9C, 0x00, 0x00, 0x00]

theorem code_l1291ce : ∀ x ∈ codeRange 0x1291ce bytes_l1291ce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291ce 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291d9 (xorR32R32Effect 0x1291d9 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1291d9 (fun s => s.RIP = 0x1291d9) (xorR32R32Effect 0x1291d9 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.terminate (.br ⟨.l1291db, RegMap.args [(0, 0), (2, 53), (4, 4), (5, 5), (7, 7), (12, 12), (14, 14), (15, 15)] 55⟩)))

def bytes_l1291d9 : List UInt8 :=
  [0x31, 0xD2]

theorem code_l1291d9 : ∀ x ∈ codeRange 0x1291d9 bytes_l1291d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291d9 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291db (xorR32R32Effect 0x1291db 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1291db (fun s => s.RIP = 0x1291db) (xorR32R32Effect 0x1291db 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1291e2, RegMap.args [(0, 53), (2, 2), (4, 4), (5, 5), (7, 7), (12, 12), (14, 14), (15, 15)] 55⟩)))

def bytes_l1291db : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x03]

theorem code_l1291db : ∀ x ∈ codeRange 0x1291db bytes_l1291db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291db 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291df (movR64R64Effect 0x1291df 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 54) (.exec 0x1291df (fun s => s.RIP = 0x1291df) (movR64R64Effect 0x1291df 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.terminate (.br ⟨.l1291e2, RegMap.args [(0, 0), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (14, 14), (15, 15)] 55⟩)))

def bytes_l1291df : List UInt8 :=
  [0x48, 0x89, 0xF2]

theorem code_l1291df : ∀ x ∈ codeRange 0x1291df bytes_l1291df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291df 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291e2 (subR64R64Effect 0x1291e2 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 0]
    (.letOp (n := 54) (.exec 0x1291e2 (fun s => s.RIP = 0x1291e2) (subR64R64Effect 0x1291e2 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 0]
    (.letOp (n := 55) (.out 0x1291e5 (movR64R64Effect 0x1291e5 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 56) (.exec 0x1291e5 (fun s => s.RIP = 0x1291e5) (movR64R64Effect 0x1291e5 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l129275, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (7, 7), (12, 53), (13, 55), (14, 14), (15, 15)] 57⟩)))))

def bytes_l1291e2 : List UInt8 :=
  [0x49, 0x29, 0xC4, 0x49, 0x89, 0xD5, 0xE9, 0x88, 0x00, 0x00, 0x00]

theorem code_l1291e2 : ∀ x ∈ codeRange 0x1291e2 bytes_l1291e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291e2 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291ed (xorR32R32Effect 0x1291ed 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 54) (.exec 0x1291ed (fun s => s.RIP = 0x1291ed) (xorR32R32Effect 0x1291ed 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.terminate (.br ⟨.l129275, RegMap.args [(4, 4), (5, 5), (7, 7), (12, 53), (13, 13), (14, 14), (15, 15)] 55⟩)))

def bytes_l1291ed : List UInt8 :=
  [0x45, 0x31, 0xE4, 0xE9, 0x80, 0x00, 0x00, 0x00]

theorem code_l1291ed : ∀ x ∈ codeRange 0x1291ed bytes_l1291ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291ed 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1291f5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1291f5 (movR32R32Effect 0x1291f5 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 54) (.exec 0x1291f5 (fun s => s.RIP = 0x1291f5) (movR32R32Effect 0x1291f5 3 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1291f8 (andR32Imm8Effect 0x1291f8 3 2 0x1c) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x1291f8 (fun s => s.RIP = 0x1291f8) (andR32Imm8Effect 0x1291f8 3 2 0x1c) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x1291fb (xorR32R32Effect 0x1291fb 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 58) (.exec 0x1291fb (fun s => s.RIP = 0x1291fb) (xorR32R32Effect 0x1291fb 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 59) (.out 0x1291fd (xorR32R32Effect 0x1291fd 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 60) (.exec 0x1291fd (fun s => s.RIP = 0x1291fd) (xorR32R32Effect 0x1291fd 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.terminate (.br ⟨.l129200, RegMap.args [(0, 0), (1, 57), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 59), (13, 13), (14, 14), (15, 15)] 61⟩)))))))))

def bytes_l1291f5 : List UInt8 :=
  [0x44, 0x89, 0xEA, 0x83, 0xE2, 0x1C, 0x31, 0xC9, 0x45, 0x31, 0xE4]

theorem code_l1291f5 : ∀ x ∈ codeRange 0x1291f5 bytes_l1291f5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x291f5 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129200 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129200 (xorR32R32Effect 0x129200 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x129200 (fun s => s.RIP = 0x129200) (xorR32R32Effect 0x129200 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x129202 (cmpM8Imm8Effect 0x129202 5 (.sib 14 (some 1) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 1] []) (.flag .SF)) #v[14, 1]
    (.letOp (n := 56) (.out 0x129202 (cmpM8Imm8Effect 0x129202 5 (.sib 14 (some 1) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 1] []) (.flag .OF)) #v[14, 1]
    (.letOp (n := 57) (.exec 0x129202 (LoadPre 0x129202 (fun s => AddrMode.addr (.sib 14 (some 1) 0 .none) s (0x129202 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129202 5 (.sib 14 (some 1) 0 .none) 0xc0) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 1]
    (.letOp (n := 58) (.out 0x129207 (atFlags (condHolds 13) (setccR8Effect 0x129207 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129207 (fun s => s.RIP = 0x129207) (atFlags (condHolds 13) (setccR8Effect 0x129207 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12920b (addR64R64Effect 0x12920b 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[58, 12]
    (.letOp (n := 61) (.exec 0x12920b (fun s => s.RIP = 0x12920b) (addR64R64Effect 0x12920b 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[58, 12]
    (.letOp (n := 62) (.out 0x12920e (xorR32R32Effect 0x12920e 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 63) (.exec 0x12920e (fun s => s.RIP = 0x12920e) (xorR32R32Effect 0x12920e 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 64) (.out 0x129211 (cmpM8Imm8Effect 0x129211 6 (.sib 14 (some 1) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 1] []) (.flag .SF)) #v[14, 1]
    (.letOp (n := 65) (.out 0x129211 (cmpM8Imm8Effect 0x129211 6 (.sib 14 (some 1) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 1] []) (.flag .OF)) #v[14, 1]
    (.letOp (n := 66) (.exec 0x129211 (LoadPre 0x129211 (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x1)) s (0x129211 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x129211 6 (.sib 14 (some 1) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 1]
    (.letOp (n := 67) (.out 0x129217 (atFlags (condHolds 13) (setccR8Effect 0x129217 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x129217 (fun s => s.RIP = 0x129217) (atFlags (condHolds 13) (setccR8Effect 0x129217 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x12921b (xorR32R32Effect 0x12921b 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 70) (.exec 0x12921b (fun s => s.RIP = 0x12921b) (xorR32R32Effect 0x12921b 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 71) (.out 0x12921e (cmpM8Imm8Effect 0x12921e 6 (.sib 14 (some 1) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 1] []) (.flag .SF)) #v[14, 1]
    (.letOp (n := 72) (.out 0x12921e (cmpM8Imm8Effect 0x12921e 6 (.sib 14 (some 1) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 1] []) (.flag .OF)) #v[14, 1]
    (.letOp (n := 73) (.exec 0x12921e (LoadPre 0x12921e (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x2)) s (0x12921e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x12921e 6 (.sib 14 (some 1) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 1]
    (.letOp (n := 74) (.out 0x129224 (atFlags (condHolds 13) (setccR8Effect 0x129224 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x129224 (fun s => s.RIP = 0x129224) (atFlags (condHolds 13) (setccR8Effect 0x129224 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x129228 (addR64R64Effect 0x129228 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x129228 (fun s => s.RIP = 0x129228) (addR64R64Effect 0x129228 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x12922b (addR64R64Effect 0x12922b 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x12922b (fun s => s.RIP = 0x12922b) (addR64R64Effect 0x12922b 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x12922e (xorR32R32Effect 0x12922e 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 81) (.exec 0x12922e (fun s => s.RIP = 0x12922e) (xorR32R32Effect 0x12922e 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 82) (.out 0x129231 (cmpM8Imm8Effect 0x129231 6 (.sib 14 (some 1) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 1] []) (.flag .SF)) #v[14, 1]
    (.letOp (n := 83) (.out 0x129231 (cmpM8Imm8Effect 0x129231 6 (.sib 14 (some 1) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 1] []) (.flag .OF)) #v[14, 1]
    (.letOp (n := 84) (.exec 0x129231 (LoadPre 0x129231 (fun s => AddrMode.addr (.sib 14 (some 1) 0 (.d8 0x3)) s (0x129231 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x129231 6 (.sib 14 (some 1) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 14, .gpr 1] [])) #v[14, 1]
    (.letOp (n := 85) (.out 0x129237 (atFlags (condHolds 13) (setccR8Effect 0x129237 4 12)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 12))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x129237 (fun s => s.RIP = 0x129237) (atFlags (condHolds 13) (setccR8Effect 0x129237 4 12)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x12923b (addR64R64Effect 0x12923b 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x12923b (fun s => s.RIP = 0x12923b) (addR64R64Effect 0x12923b 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x12923e (addR64Imm8Effect 0x12923e 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 90) (.exec 0x12923e (fun s => s.RIP = 0x12923e) (addR64Imm8Effect 0x12923e 1 0x4) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 91) (.out 0x129242 (cmpR64R64Effect 0x129242 2 1) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[2, 89]
    (.letOp (n := 92) (.exec 0x129242 (fun s => s.RIP = 0x129242) (cmpR64R64Effect 0x129242 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l129200, RegMap.args [(0, 0), (1, 89), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 87), (13, 13), (14, 14), (15, 15), (19, 91)] 94⟩ ⟨.l129247, RegMap.args [(0, 0), (1, 89), (2, 2), (4, 4), (5, 5), (6, 60), (7, 7), (8, 67), (9, 78), (12, 87), (13, 13), (14, 14), (15, 15), (19, 91)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l129200 : List UInt8 :=
  [0x31, 0xF6, 0x41, 0x80, 0x3C, 0x0E, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x4C, 0x01, 0xE6, 0x45, 0x31,
    0xC0, 0x41, 0x80, 0x7C, 0x0E, 0x01, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xC9, 0x41, 0x80,
    0x7C, 0x0E, 0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4D, 0x01, 0xC1, 0x49, 0x01, 0xF1, 0x45, 0x31,
    0xE4, 0x41, 0x80, 0x7C, 0x0E, 0x03, 0xC0, 0x41, 0x0F, 0x9D, 0xC4, 0x4D, 0x01, 0xCC, 0x48, 0x83,
    0xC1, 0x04, 0x48, 0x39, 0xCA, 0x75, 0xB9]

theorem code_l129200 : ∀ x ∈ codeRange 0x129200 bytes_l129200, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29200 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129247 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129247 (testR64R64Effect 0x129247 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x129247 (fun s => s.RIP = 0x129247) (testR64R64Effect 0x129247 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129275, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l12924c, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l129247 : List UInt8 :=
  [0x48, 0x85, 0xC0, 0x74, 0x29]

theorem code_l129247 : ∀ x ∈ codeRange 0x129247 bytes_l129247, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29247 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12924c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12924c (addR64R64Effect 0x12924c 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[1, 14]
    (.letOp (n := 54) (.exec 0x12924c (fun s => s.RIP = 0x12924c) (addR64R64Effect 0x12924c 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[1, 14]
    (.letOp (n := 55) (.out 0x12924f (xorR32R32Effect 0x12924f 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x12924f (fun s => s.RIP = 0x12924f) (xorR32R32Effect 0x12924f 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.exec 0x129251 (fun s => s.RIP = 0x129251) (fun _ => nopEffect 0x129251 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129260, RegMap.args [(0, 0), (1, 53), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15)] 58⟩))))))

def bytes_l12924c : List UInt8 :=
  [0x4C, 0x01, 0xF1, 0x31, 0xD2, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00,
    0x00, 0x00, 0x00, 0x00]

theorem code_l12924c : ∀ x ∈ codeRange 0x12924c bytes_l12924c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2924c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129260 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129260 (xorR32R32Effect 0x129260 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x129260 (fun s => s.RIP = 0x129260) (xorR32R32Effect 0x129260 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x129262 (cmpM8Imm8Effect 0x129262 4 (.sib 1 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 1, .gpr 2] []) (.flag .SF)) #v[1, 2]
    (.letOp (n := 56) (.out 0x129262 (cmpM8Imm8Effect 0x129262 4 (.sib 1 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 1, .gpr 2] []) (.flag .OF)) #v[1, 2]
    (.letOp (n := 57) (.exec 0x129262 (LoadPre 0x129262 (fun s => AddrMode.addr (.sib 1 (some 2) 0 .none) s (0x129262 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129262 4 (.sib 1 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 2]
    (.letOp (n := 58) (.out 0x129266 (atFlags (condHolds 13) (setccR8Effect 0x129266 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129266 (fun s => s.RIP = 0x129266) (atFlags (condHolds 13) (setccR8Effect 0x129266 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12926a (addR64R64Effect 0x12926a 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[12, 58]
    (.letOp (n := 61) (.exec 0x12926a (fun s => s.RIP = 0x12926a) (addR64R64Effect 0x12926a 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[12, 58]
    (.letOp (n := 62) (.out 0x12926d (incR64Effect 0x12926d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 63) (.exec 0x12926d (fun s => s.RIP = 0x12926d) (incR64Effect 0x12926d 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 64) (.out 0x129270 (cmpR64R64Effect 0x129270 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[0, 62]
    (.letOp (n := 65) (.exec 0x129270 (fun s => s.RIP = 0x129270) (cmpR64R64Effect 0x129270 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[0, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l129260, RegMap.args [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 58), (7, 7), (12, 60), (13, 13), (14, 14), (15, 15), (19, 64)] 67⟩ ⟨.l129275, RegMap.args [(0, 0), (1, 1), (2, 62), (4, 4), (5, 5), (6, 58), (7, 7), (12, 60), (13, 13), (14, 14), (15, 15), (19, 64)] 67⟩)))))))))))))))

def bytes_l129260 : List UInt8 :=
  [0x31, 0xF6, 0x80, 0x3C, 0x11, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x49, 0x01, 0xF4, 0x48, 0xFF, 0xC2,
    0x48, 0x39, 0xD0, 0x75, 0xEB]

theorem code_l129260 : ∀ x ∈ codeRange 0x129260 bytes_l129260, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29260 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129275 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129275 (movzxR32M16Effect 0x129275 4 0 (.base 7 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x129275 (LoadPre 0x129275 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x129275 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x129275 4 0 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x129279 (cmpR64R64Effect 0x129279 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[12, 53]
    (.letOp (n := 56) (.exec 0x129279 (fun s => s.RIP = 0x129279) (cmpR64R64Effect 0x129279 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 53]
    (.letOp (n := 57) (.pure (condOp 3)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1292ab, RegMap.args [(0, 53), (4, 4), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55)] 58⟩ ⟨.l12927e, RegMap.args [(0, 53), (4, 4), (5, 5), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 55)] 58⟩))))))

def bytes_l129275 : List UInt8 :=
  [0x0F, 0xB7, 0x47, 0x14, 0x49, 0x39, 0xC4, 0x73, 0x2D]

theorem code_l129275 : ∀ x ∈ codeRange 0x129275 bytes_l129275, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29275 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12927e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12927e (StorePre 0x12927e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x12927e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12927e 0 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 54) (.out 0x129282 (movR32R32Effect 0x129282 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[0]
    (.letOp (n := 55) (.exec 0x129282 (fun s => s.RIP = 0x129282) (movR32R32Effect 0x129282 2 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.out 0x129284 (subR32R32Effect 0x129284 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[54, 12]
    (.letOp (n := 57) (.exec 0x129284 (fun s => s.RIP = 0x129284) (subR32R32Effect 0x129284 3 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[54, 12]
    (.letOp (n := 58) (.out 0x129287 (movR32R32Effect 0x129287 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 59) (.exec 0x129287 (fun s => s.RIP = 0x129287) (movR32R32Effect 0x129287 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 60) (.out 0x12928a (shrR32Effect 0x12928a 3 0 29) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[58]
    (.letOp (n := 61) (.exec 0x12928a (fun s => s.RIP = 0x12928a) (shrR32Effect 0x12928a 3 0 29) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x12928d (andR32Imm8Effect 0x12928d 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 63) (.exec 0x12928d (fun s => s.RIP = 0x12928d) (andR32Imm8Effect 0x12928d 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 64) (.out 0x129290 (leaR64Effect 0x129290 1 (.rip 0xda8cd)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 65) (.exec 0x129290 (fun s => s.RIP = 0x129290) (leaR64Effect 0x129290 1 (.rip 0xda8cd)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x129297 (movsxdR64M32Effect 0x129297 4 0 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x129297 (LoadPre 0x129297 (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x129297 + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x129297 4 0 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[64, 62]
    (.letOp (n := 68) (.exec 0x12929b (fun s => s.RIP = 0x12929b) (addR64R64Effect 0x12929b 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[66, 64]
    (.letOp (n := 69) (.exec 0x12929e (StorePre 0x12929e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x12929e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12929e 13 (.base 5 (.d8 0xb0))) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 70) (.exec 0x1292a2 (StorePre 0x1292a2 3 (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x1292a2 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1292a2 2 (.base 5 (.d8 0xcc))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[56, 5]
    (cutBlock 0x1292a5))))))))))))))))))

def bytes_l12927e : List UInt8 :=
  [0x48, 0x89, 0x45, 0xC0, 0x89, 0xC2, 0x44, 0x29, 0xE2, 0x44, 0x89, 0xF8, 0xC1, 0xE8, 0x1D, 0x83,
    0xE0, 0x03, 0x48, 0x8D, 0x0D, 0xCD, 0xA8, 0x0D, 0x00, 0x48, 0x63, 0x04, 0x81, 0x48, 0x01, 0xC8,
    0x4C, 0x89, 0x6D, 0xB0, 0x89, 0x55, 0xCC, 0xFF, 0xE0]

theorem code_l12927e : ∀ x ∈ codeRange 0x12927e bytes_l12927e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2927e 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1292ab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1292ab (movR64M64Effect 0x1292ab 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1292ab (LoadPre 0x1292ab (fun s => AddrMode.addr (.base 7 .none) s (0x1292ab + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1292ab 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1292ae (movR64M64Effect 0x1292ae 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 56) (.exec 0x1292ae (LoadPre 0x1292ae (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1292ae + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1292ae 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x1292b2 (LoadPre 0x1292b2 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x1292b2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1292b2 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 58) (.exec 0x1292b6 (fun s => s.RIP = 0x1292b6) (movR64R64Effect 0x1292b6 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.exec 0x1292b9 (fun s => s.RIP = 0x1292b9) (movR64R64Effect 0x1292b9 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 60) (.exec 0x1292bc (fun s => s.RIP = 0x1292bc) (movR64R64Effect 0x1292bc 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x1292bf (addR64Imm8Effect 0x1292bf 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1292bf (fun s => s.RIP = 0x1292bf) (addR64Imm8Effect 0x1292bf 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1292c3 (popR64Effect 0x1292c3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x1292c3 (PopPre 0x1292c3) (popR64Effect 0x1292c3 1 3) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x1292c4 (popR64Effect 0x1292c4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1292c4 (PopPre 0x1292c4) (popR64Effect 0x1292c4 2 12) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1292c6 (popR64Effect 0x1292c6 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x1292c6 (PopPre 0x1292c6) (popR64Effect 0x1292c6 2 13) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x1292c8 (popR64Effect 0x1292c8 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 70) (.exec 0x1292c8 (PopPre 0x1292c8) (popR64Effect 0x1292c8 2 14) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 71) (.out 0x1292ca (popR64Effect 0x1292ca 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 72) (.exec 0x1292ca (PopPre 0x1292ca) (popR64Effect 0x1292ca 2 15) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 73) (.exec 0x1292cc (PopPre 0x1292cc) (popR64Effect 0x1292cc 1 5) (Reg.operands [.gpr 4] [])) #v[71]
    (cutBlock 0x1292cd)))))))))))))))))))))

def bytes_l1292ab : List UInt8 :=
  [0x48, 0x8B, 0x07, 0x48, 0x8B, 0x4F, 0x08, 0x48, 0x8B, 0x49, 0x18, 0x48, 0x89, 0xC7, 0x4C, 0x89,
    0xF6, 0x4C, 0x89, 0xEA, 0x48, 0x83, 0xC4, 0x28, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41,
    0x5F, 0x5D, 0xFF, 0xE1]

theorem code_l1292ab : ∀ x ∈ codeRange 0x1292ab bytes_l1292ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x292ab 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1293a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1293a0 (pushR64Effect 0x1293a0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1293a0 (PushPre 0x1293a0 1) (pushR64Effect 0x1293a0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1293a1 (movR64R64Effect 0x1293a1 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x1293a1 (fun s => s.RIP = 0x1293a1) (movR64R64Effect 0x1293a1 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x1293a4 (pushR64Effect 0x1293a4 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 58) (.exec 0x1293a4 (PushPre 0x1293a4 2) (pushR64Effect 0x1293a4 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 59) (.out 0x1293a6 (pushR64Effect 0x1293a6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x1293a6 (PushPre 0x1293a6 2) (pushR64Effect 0x1293a6 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x1293a8 (pushR64Effect 0x1293a8 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x1293a8 (PushPre 0x1293a8 2) (pushR64Effect 0x1293a8 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x1293aa (pushR64Effect 0x1293aa 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x1293aa (PushPre 0x1293aa 2) (pushR64Effect 0x1293aa 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x1293ac (pushR64Effect 0x1293ac 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x1293ac (PushPre 0x1293ac 1) (pushR64Effect 0x1293ac 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x1293ad (subR64Imm8Effect 0x1293ad 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x1293ad (fun s => s.RIP = 0x1293ad) (subR64Imm8Effect 0x1293ad 4 0x38) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x1293b1 (movR64R64Effect 0x1293b1 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 70) (.exec 0x1293b1 (fun s => s.RIP = 0x1293b1) (movR64R64Effect 0x1293b1 3 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x1293b4 (movR64R64Effect 0x1293b4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 72) (.exec 0x1293b4 (fun s => s.RIP = 0x1293b4) (movR64R64Effect 0x1293b4 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x1293b7 (movR64R64Effect 0x1293b7 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 74) (.exec 0x1293b7 (fun s => s.RIP = 0x1293b7) (movR64R64Effect 0x1293b7 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x1293ba (testR8Imm8LowEffect 0x1293ba 3 0x1) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[69]
    (.letOp (n := 76) (.exec 0x1293ba (fun s => s.RIP = 0x1293ba) (testR8Imm8LowEffect 0x1293ba 3 0x1) (Reg.operands [.gpr 3] [])) #v[69]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l12952b, RegMap.args [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 73), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l1293c3, RegMap.args [(1, 1), (2, 2), (3, 69), (4, 67), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 71), (14, 73), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l1293a0 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC,
    0x38, 0x48, 0x89, 0xCB, 0x49, 0x89, 0xD5, 0x49, 0x89, 0xFE, 0xF6, 0xC3, 0x01, 0x0F, 0x85, 0x68,
    0x01, 0x00, 0x00]

theorem code_l1293a0 : ∀ x ∈ codeRange 0x1293a0 bytes_l1293a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x293a0 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1293c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1293c3 (movzxR32M8Effect 0x1293c3 5 0 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x1293c3 (LoadPre 0x1293c3 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1293c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1293c3 5 0 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x1293c8 (testR8R8Effect 0x1293c8 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1293c8 (fun s => s.RIP = 0x1293c8) (testR8R8Effect 0x1293c8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l12954b, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1293d0, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1293c3 : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0x45, 0x00, 0x84, 0xC0, 0x0F, 0x84, 0x7B, 0x01, 0x00, 0x00]

theorem code_l1293c3 : ∀ x ∈ codeRange 0x1293c3 bytes_l1293c3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x293c3 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1293d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1293d0 (StorePre 0x1293d0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1293d0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1293d0 6 (.base 5 (.d8 0xb0))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 5]
    (.letOp (n := 54) (.out 0x1293d4 (movR64M64Effect 0x1293d4 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 55) (.exec 0x1293d4 (LoadPre 0x1293d4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1293d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1293d4 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.exec 0x1293d8 (StorePre 0x1293d8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x1293d8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1293d8 1 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[54, 5]
    (.letOp (n := 57) (.exec 0x1293dc (StorePre 0x1293dc 8 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1293dc + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1293dc (.base 5 (.d8 0xd0)) 0x0) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l129400, RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (5, 5), (6, 6), (13, 13), (14, 14)] 58⟩))))))

def bytes_l1293d0 : List UInt8 :=
  [0x48, 0x89, 0x75, 0xB0, 0x48, 0x8B, 0x4E, 0x18, 0x48, 0x89, 0x4D, 0xA8, 0x48, 0xC7, 0x45, 0xD0,
    0x00, 0x00, 0x00, 0x00, 0xEB, 0x1A]

theorem code_l1293d0 : ∀ x ∈ codeRange 0x1293d0 bytes_l1293d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x293d0 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1293f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1293f0 (movzxR32M8Effect 0x1293f0 5 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x1293f0 (LoadPre 0x1293f0 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1293f0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1293f0 5 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1293f5 (movR64R64Effect 0x1293f5 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 56) (.exec 0x1293f5 (fun s => s.RIP = 0x1293f5) (movR64R64Effect 0x1293f5 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1293f8 (testR8R8Effect 0x1293f8 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x1293f8 (fun s => s.RIP = 0x1293f8) (testR8R8Effect 0x1293f8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l12954b, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l129400, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1293f0 : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0x04, 0x24, 0x4D, 0x89, 0xE5, 0x84, 0xC0, 0x0F, 0x84, 0x4B, 0x01, 0x00, 0x00]

theorem code_l1293f0 : ∀ x ∈ codeRange 0x1293f0 bytes_l1293f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x293f0 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129400 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129400 (leaR64Effect 0x129400 12 (.base 13 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[13]
    (.letOp (n := 54) (.exec 0x129400 (fun s => s.RIP = 0x129400) (leaR64Effect 0x129400 12 (.base 13 (.d8 0x1))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x129404 (movzxR32R8Effect 0x129404 4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 56) (.exec 0x129404 (fun s => s.RIP = 0x129404) (movzxR32R8Effect 0x129404 4 15 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x129408 (testR8R8Effect 0x129408 2 0 0) (EffectPart.reads (.flag .SF) [.gpr 0, .gpr 0] []) (.flag .SF)) #v[0, 0]
    (.letOp (n := 58) (.exec 0x129408 (fun s => s.RIP = 0x129408) (testR8R8Effect 0x129408 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 59) (.pure (condOp 8)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l129430, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 53), (13, 13), (14, 14), (15, 55), (20, 57)] 60⟩ ⟨.l12940c, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 53), (13, 13), (14, 14), (15, 55), (20, 57)] 60⟩))))))))

def bytes_l129400 : List UInt8 :=
  [0x4D, 0x8D, 0x65, 0x01, 0x44, 0x0F, 0xB6, 0xF8, 0x84, 0xC0, 0x78, 0x24]

theorem code_l129400 : ∀ x ∈ codeRange 0x129400 bytes_l129400, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29400 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12940c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12940c (fun s => s.RIP = 0x12940c) (movR64R64Effect 0x12940c 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.exec 0x12940f (fun s => s.RIP = 0x12940f) (movR64R64Effect 0x12940f 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.exec 0x129412 (fun s => s.RIP = 0x129412) (movR64R64Effect 0x129412 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (cutBlock 0x129415)))

def bytes_l12940c : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xFA, 0xFF, 0x55, 0xA8]

theorem code_l12940c : ∀ x ∈ codeRange 0x12940c bytes_l12940c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2940c 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129418 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129418 (testR8R8Effect 0x129418 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x129418 (fun s => s.RIP = 0x129418) (testR8R8Effect 0x129418 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12954f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l129420, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129418 : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x85, 0x2F, 0x01, 0x00, 0x00]

theorem code_l129418 : ∀ x ∈ codeRange 0x129418 bytes_l129418, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29418 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129420 (addR64R64Effect 0x129420 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[12, 15]
    (.letOp (n := 54) (.exec 0x129420 (fun s => s.RIP = 0x129420) (addR64R64Effect 0x129420 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[12, 15]
    (.terminate (.br ⟨.l1293f0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l129420 : List UInt8 :=
  [0x4D, 0x01, 0xFC, 0xEB, 0xCB]

theorem code_l129420 : ∀ x ∈ codeRange 0x129420 bytes_l129420, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29420 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129430 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129430 (cmpAlImm8Effect 0x129430 0x80) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x129430 (fun s => s.RIP = 0x129430) (cmpAlImm8Effect 0x129430 0x80) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129455, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l129434, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l129430 : List UInt8 :=
  [0x3C, 0x80, 0x74, 0x21]

theorem code_l129430 : ∀ x ∈ codeRange 0x129430 bytes_l129430, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29430 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129434 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129434 (cmpR32Imm32Effect 0x129434 7 15 0xc0) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 54) (.exec 0x129434 (fun s => s.RIP = 0x129434) (cmpR32Imm32Effect 0x129434 7 15 0xc0) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12947c, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l12943d, RegMap.args [(0, 0), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l129434 : List UInt8 :=
  [0x41, 0x81, 0xFF, 0xC0, 0x00, 0x00, 0x00, 0x75, 0x3F]

theorem code_l129434 : ∀ x ∈ codeRange 0x129434 bytes_l129434, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29434 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12943d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12943d (movR64M64Effect 0x12943d 15 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 54) (.exec 0x12943d (LoadPre 0x12943d (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12943d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12943d 15 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x129441 (movR64R64Effect 0x129441 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x129441 (fun s => s.RIP = 0x129441) (movR64R64Effect 0x129441 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x129444 (shlR64Effect 0x129444 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x129444 (fun s => s.RIP = 0x129444) (shlR64Effect 0x129444 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.exec 0x129448 (StorePre 0x129448 8 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x129448 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x129448 (.base 5 (.d8 0xc8)) 0x60000020) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l1294f2, RegMap.args [(0, 57), (3, 3), (5, 5), (14, 14), (15, 53)] 60⟩))))))))

def bytes_l12943d : List UInt8 :=
  [0x4C, 0x8B, 0x7D, 0xD0, 0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0xC7, 0x45, 0xC8, 0x20,
    0x00, 0x00, 0x60, 0xE9, 0x9D, 0x00, 0x00, 0x00]

theorem code_l12943d : ∀ x ∈ codeRange 0x12943d bytes_l12943d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2943d 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129455 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129455 (movzxR32M16Effect 0x129455 5 15 (.base 13 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[13]
    (.letOp (n := 54) (.exec 0x129455 (LoadPre 0x129455 (fun s => AddrMode.addr (.base 13 (.d8 0x1)) s (0x129455 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x129455 5 15 (.base 13 (.d8 0x1))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.exec 0x12945a (fun s => s.RIP = 0x12945a) (leaR64Effect 0x12945a 6 (.base 13 (.d8 0x3))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 56) (.exec 0x12945e (fun s => s.RIP = 0x12945e) (movR64R64Effect 0x12945e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.exec 0x129461 (fun s => s.RIP = 0x129461) (movR64R64Effect 0x129461 2 15) (Reg.operands [.gpr 15] [])) #v[53]
    (cutBlock 0x129464)))))

def bytes_l129455 : List UInt8 :=
  [0x45, 0x0F, 0xB7, 0x7D, 0x01, 0x49, 0x8D, 0x75, 0x03, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0xFF,
    0x55, 0xA8]

theorem code_l129455 : ∀ x ∈ codeRange 0x129455 bytes_l129455, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29455 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129467 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129467 (testR8R8Effect 0x129467 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x129467 (fun s => s.RIP = 0x129467) (testR8R8Effect 0x129467 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12954f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12946f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129467 : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x85, 0xE0, 0x00, 0x00, 0x00]

theorem code_l129467 : ∀ x ∈ codeRange 0x129467 bytes_l129467, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29467 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12946f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12946f (leaR64Effect 0x12946f 12 (.sib 15 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15, .gpr 13] []) (.reg (.gpr 12))) #v[15, 13]
    (.letOp (n := 54) (.exec 0x12946f (fun s => s.RIP = 0x12946f) (leaR64Effect 0x12946f 12 (.sib 15 (some 13) 0 .none)) (Reg.operands [.gpr 15, .gpr 13] [])) #v[15, 13]
    (.letOp (n := 55) (.out 0x129473 (addR64Imm8Effect 0x129473 12 0x3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.exec 0x129473 (fun s => s.RIP = 0x129473) (addR64Imm8Effect 0x129473 12 0x3) (Reg.operands [.gpr 12] [])) #v[53]
    (.terminate (.br ⟨.l1293f0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l12946f : List UInt8 :=
  [0x4F, 0x8D, 0x24, 0x2F, 0x49, 0x83, 0xC4, 0x03, 0xE9, 0x74, 0xFF, 0xFF, 0xFF]

theorem code_l12946f : ∀ x ∈ codeRange 0x12946f bytes_l12946f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2946f 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12947c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12947c (movR32Imm32Effect 0x12947c 5 1 0x60000020) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x12947c (fun s => s.RIP = 0x12947c) (movR32Imm32Effect 0x12947c 5 1 0x60000020) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x129481 (testAlImm8Effect 0x129481 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 56) (.exec 0x129481 (fun s => s.RIP = 0x129481) (testAlImm8Effect 0x129481 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l129490, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (19, 55)] 58⟩ ⟨.l129485, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (13, 13), (14, 14), (19, 55)] 58⟩))))))

def bytes_l12947c : List UInt8 :=
  [0xB9, 0x20, 0x00, 0x00, 0x60, 0xA8, 0x01, 0x74, 0x0B]

theorem code_l12947c : ∀ x ∈ codeRange 0x12947c bytes_l12947c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2947c 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129485 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129485 (movR32M32Effect 0x129485 1 (.base 13 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 54) (.exec 0x129485 (LoadPre 0x129485 (fun s => AddrMode.addr (.base 13 (.d8 0x1)) s (0x129485 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x129485 1 (.base 13 (.d8 0x1))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x129489 (addR64Imm8Effect 0x129489 13 0x5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 56) (.exec 0x129489 (fun s => s.RIP = 0x129489) (addR64Imm8Effect 0x129489 13 0x5) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x12948d (movR64R64Effect 0x12948d 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 58) (.exec 0x12948d (fun s => s.RIP = 0x12948d) (movR64R64Effect 0x12948d 12 13) (Reg.operands [.gpr 13] [])) #v[55]
    (.terminate (.br ⟨.l129490, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (5, 5), (6, 6), (12, 57), (13, 55), (14, 14)] 59⟩)))))))

def bytes_l129485 : List UInt8 :=
  [0x41, 0x8B, 0x4D, 0x01, 0x49, 0x83, 0xC5, 0x05, 0x4D, 0x89, 0xEC]

theorem code_l129485 : ∀ x ∈ codeRange 0x129485 bytes_l129485, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29485 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129490 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129490 (testAlImm8Effect 0x129490 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x129490 (fun s => s.RIP = 0x129490) (testAlImm8Effect 0x129490 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1294ad, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (19, 53)] 56⟩ ⟨.l129494, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (19, 53)] 56⟩))))

def bytes_l129490 : List UInt8 :=
  [0xA8, 0x02, 0x75, 0x19]

theorem code_l129490 : ∀ x ∈ codeRange 0x129490 bytes_l129490, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29490 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129494 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129494 (xorR32R32Effect 0x129494 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x129494 (fun s => s.RIP = 0x129494) (xorR32R32Effect 0x129494 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x129496 (movR64M64Effect 0x129496 15 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 56) (.exec 0x129496 (LoadPre 0x129496 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129496 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129496 15 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x12949a (testAlImm8Effect 0x12949a 0x4) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 58) (.exec 0x12949a (fun s => s.RIP = 0x12949a) (testAlImm8Effect 0x12949a 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1294be, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (15, 55), (19, 57)] 60⟩ ⟨.l12949e, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 12), (14, 14), (15, 55), (19, 57)] 60⟩))))))))

def bytes_l129494 : List UInt8 :=
  [0x31, 0xD2, 0x4C, 0x8B, 0x7D, 0xD0, 0xA8, 0x04, 0x74, 0x20]

theorem code_l129494 : ∀ x ∈ codeRange 0x129494 bytes_l129494, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29494 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12949e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12949e (movzxR32M16Effect 0x12949e 5 6 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 54) (.exec 0x12949e (LoadPre 0x12949e (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x12949e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x12949e 5 6 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1294a3 (addR64Imm8Effect 0x1294a3 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x1294a3 (fun s => s.RIP = 0x1294a3) (addR64Imm8Effect 0x1294a3 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1294a7 (testAlImm8Effect 0x1294a7 0x8) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 58) (.exec 0x1294a7 (fun s => s.RIP = 0x1294a7) (testAlImm8Effect 0x1294a7 0x8) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1294c4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 55), (14, 14), (15, 15), (19, 57)] 60⟩ ⟨.l1294ab, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 55), (14, 14), (15, 15), (19, 57)] 60⟩))))))))

def bytes_l12949e : List UInt8 :=
  [0x41, 0x0F, 0xB7, 0x34, 0x24, 0x49, 0x83, 0xC4, 0x02, 0xA8, 0x08, 0x75, 0x19]

theorem code_l12949e : ∀ x ∈ codeRange 0x12949e bytes_l12949e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2949e 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294ab : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1294cd, RegMap.args (entryMap (live .l1294ab)) 53⟩)

def bytes_l1294ab : List UInt8 :=
  [0xEB, 0x20]

theorem code_l1294ab : ∀ x ∈ codeRange 0x1294ab bytes_l1294ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294ab 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294ad : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294ad (movzxR32M16Effect 0x1294ad 5 2 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 54) (.exec 0x1294ad (LoadPre 0x1294ad (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1294ad + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294ad 5 2 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1294b2 (addR64Imm8Effect 0x1294b2 12 0x2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x1294b2 (fun s => s.RIP = 0x1294b2) (addR64Imm8Effect 0x1294b2 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1294b6 (movR64M64Effect 0x1294b6 15 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[5]
    (.letOp (n := 58) (.exec 0x1294b6 (LoadPre 0x1294b6 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1294b6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294b6 15 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 59) (.out 0x1294ba (testAlImm8Effect 0x1294ba 0x4) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 60) (.exec 0x1294ba (fun s => s.RIP = 0x1294ba) (testAlImm8Effect 0x1294ba 0x4) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l12949e, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 55), (14, 14), (15, 57), (19, 59)] 62⟩ ⟨.l1294be, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (5, 5), (6, 6), (12, 55), (14, 14), (15, 57), (19, 59)] 62⟩))))))))))

def bytes_l1294ad : List UInt8 :=
  [0x41, 0x0F, 0xB7, 0x14, 0x24, 0x49, 0x83, 0xC4, 0x02, 0x4C, 0x8B, 0x7D, 0xD0, 0xA8, 0x04, 0x75,
    0xE0]

theorem code_l1294ad : ∀ x ∈ codeRange 0x1294ad bytes_l1294ad, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294ad 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294be (xorR32R32Effect 0x1294be 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x1294be (fun s => s.RIP = 0x1294be) (xorR32R32Effect 0x1294be 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x1294c0 (testAlImm8Effect 0x1294c0 0x8) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 56) (.exec 0x1294c0 (fun s => s.RIP = 0x1294c0) (testAlImm8Effect 0x1294c0 0x8) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1294cd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 12), (14, 14), (15, 15), (19, 55)] 58⟩ ⟨.l1294c4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 53), (12, 12), (14, 14), (15, 15), (19, 55)] 58⟩))))))

def bytes_l1294be : List UInt8 :=
  [0x31, 0xF6, 0xA8, 0x08, 0x74, 0x09]

theorem code_l1294be : ∀ x ∈ codeRange 0x1294be bytes_l1294be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294be 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294c4 (movzxR32M16Effect 0x1294c4 5 15 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x1294c4 (LoadPre 0x1294c4 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1294c4 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294c4 5 15 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.exec 0x1294c9 (fun s => s.RIP = 0x1294c9) (addR64Imm8Effect 0x1294c9 12 0x2) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l1294cd, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 53)] 56⟩))))

def bytes_l1294c4 : List UInt8 :=
  [0x45, 0x0F, 0xB7, 0x3C, 0x24, 0x49, 0x83, 0xC4, 0x02]

theorem code_l1294c4 : ∀ x ∈ codeRange 0x1294c4 bytes_l1294c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294c4 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294cd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294cd (testAlImm8Effect 0x1294cd 0x10) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1294cd (fun s => s.RIP = 0x1294cd) (testAlImm8Effect 0x1294cd 0x10) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12951a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l1294d1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l1294cd : List UInt8 :=
  [0xA8, 0x10, 0x75, 0x49]

theorem code_l1294cd : ∀ x ∈ codeRange 0x1294cd bytes_l1294cd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294cd 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294d1 (testAlImm8Effect 0x1294d1 0x20) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1294d1 (fun s => s.RIP = 0x1294d1) (testAlImm8Effect 0x1294d1 0x20) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1294e0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩ ⟨.l1294d5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 53)] 56⟩))))

def bytes_l1294d1 : List UInt8 :=
  [0xA8, 0x20, 0x74, 0x0B]

theorem code_l1294d1 : ∀ x ∈ codeRange 0x1294d1 bytes_l1294d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294d1 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294d5 (movzxR32R16Effect 0x1294d5 3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1294d5 (fun s => s.RIP = 0x1294d5) (movzxR32R16Effect 0x1294d5 3 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1294d8 (shlR32Effect 0x1294d8 3 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1294d8 (fun s => s.RIP = 0x1294d8) (shlR32Effect 0x1294d8 3 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x1294db (movzxR32M16Effect 0x1294db 5 6 (.sib 3 (some 0) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3, .gpr 0] []) (.reg (.gpr 6))) #v[3, 55]
    (.letOp (n := 58) (.exec 0x1294db (LoadPre 0x1294db (fun s => AddrMode.addr (.sib 3 (some 0) 0 (.d8 0x8)) s (0x1294db + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1294db 5 6 (.sib 3 (some 0) 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3, 55]
    (.terminate (.br ⟨.l1294e0, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 57), (14, 14), (15, 15)] 59⟩)))))))

def bytes_l1294d5 : List UInt8 :=
  [0x0F, 0xB7, 0xC6, 0xC1, 0xE0, 0x04, 0x0F, 0xB7, 0x74, 0x03, 0x08]

theorem code_l1294d5 : ∀ x ∈ codeRange 0x1294d5 bytes_l1294d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294d5 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1294e0 (movR64R64Effect 0x1294e0 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x1294e0 (fun s => s.RIP = 0x1294e0) (movR64R64Effect 0x1294e0 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x1294e3 (shlR64Effect 0x1294e3 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1294e3 (fun s => s.RIP = 0x1294e3) (shlR64Effect 0x1294e3 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1294e7 (StorePre 0x1294e7 3 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1294e7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1294e7 1 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 5]
    (.letOp (n := 58) (.exec 0x1294ea (StorePre 0x1294ea 4 (fun s => AddrMode.addr (.base 5 (.d8 0xcc)) s (0x1294ea + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1294ea 4 2 (.base 5 (.d8 0xcc))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 5]
    (.letOp (n := 59) (.exec 0x1294ee (StorePre 0x1294ee 4 (fun s => AddrMode.addr (.base 5 (.d8 0xce)) s (0x1294ee + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x1294ee 4 6 (.base 5 (.d8 0xce))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 5]
    (.terminate (.br ⟨.l1294f2, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15)] 60⟩))))))))

def bytes_l1294e0 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE0, 0x04, 0x89, 0x4D, 0xC8, 0x66, 0x89, 0x55, 0xCC, 0x66, 0x89,
    0x75, 0xCE]

theorem code_l1294e0 : ∀ x ∈ codeRange 0x1294e0 bytes_l1294e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294e0 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1294f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1294f2 (StorePre 0x1294f2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1294f2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1294f2 14 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 14, .gpr 5] [])) #v[14, 5]
    (.letOp (n := 54) (.out 0x1294f6 (movR64M64Effect 0x1294f6 1 (.base 5 (.d8 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 55) (.exec 0x1294f6 (LoadPre 0x1294f6 (fun s => AddrMode.addr (.base 5 (.d8 0xb0)) s (0x1294f6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294f6 1 (.base 5 (.d8 0xb0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.exec 0x1294fa (StorePre 0x1294fa 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1294fa + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1294fa 1 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[54, 5]
    (.letOp (n := 57) (.exec 0x1294fe (LoadPre 0x1294fe (fun s => AddrMode.addr (.sib 3 (some 0) 0 .none) s (0x1294fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1294fe 7 (.sib 3 (some 0) 0 .none)) (Reg.operands [.gpr 3, .gpr 0] [])) #v[3, 0]
    (.letOp (n := 58) (.exec 0x129502 (fun s => s.RIP = 0x129502) (leaR64Effect 0x129502 6 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (cutBlock 0x129506))))))

def bytes_l1294f2 : List UInt8 :=
  [0x4C, 0x89, 0x75, 0xB8, 0x48, 0x8B, 0x4D, 0xB0, 0x48, 0x89, 0x4D, 0xC0, 0x48, 0x8B, 0x3C, 0x03,
    0x48, 0x8D, 0x75, 0xB8, 0xFF, 0x54, 0x03, 0x08]

theorem code_l1294f2 : ∀ x ∈ codeRange 0x1294f2 bytes_l1294f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294f2 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12950a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12950a (testR8R8Effect 0x12950a 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x12950a (fun s => s.RIP = 0x12950a) (testR8R8Effect 0x12950a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12954f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12950e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12950a : List UInt8 :=
  [0x84, 0xC0, 0x75, 0x41]

theorem code_l12950a : ∀ x ∈ codeRange 0x12950a bytes_l12950a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2950a 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12950e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12950e (incR64Effect 0x12950e 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 54) (.exec 0x12950e (fun s => s.RIP = 0x12950e) (incR64Effect 0x12950e 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 55) (.exec 0x129511 (StorePre 0x129511 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129511 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129511 15 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 15, .gpr 5] [])) #v[53, 5]
    (.terminate (.br ⟨.l1293f0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12950e : List UInt8 :=
  [0x49, 0xFF, 0xC7, 0x4C, 0x89, 0x7D, 0xD0, 0xE9, 0xD6, 0xFE, 0xFF, 0xFF]

theorem code_l12950e : ∀ x ∈ codeRange 0x12950e bytes_l12950e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2950e 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12951a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12951a (movzxR32R16Effect 0x12951a 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x12951a (fun s => s.RIP = 0x12951a) (movzxR32R16Effect 0x12951a 3 2 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x12951d (shlR32Effect 0x12951d 3 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x12951d (fun s => s.RIP = 0x12951d) (shlR32Effect 0x12951d 3 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x129520 (movzxR32M16Effect 0x129520 5 2 (.sib 3 (some 2) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 2] []) (.reg (.gpr 2))) #v[3, 55]
    (.letOp (n := 58) (.exec 0x129520 (LoadPre 0x129520 (fun s => AddrMode.addr (.sib 3 (some 2) 0 (.d8 0x8)) s (0x129520 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x129520 5 2 (.sib 3 (some 2) 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 2] [])) #v[3, 55]
    (.letOp (n := 59) (.out 0x129525 (testAlImm8Effect 0x129525 0x20) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 60) (.exec 0x129525 (fun s => s.RIP = 0x129525) (testAlImm8Effect 0x129525 0x20) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l1294d5, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 59)] 62⟩ ⟨.l129529, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (5, 5), (6, 6), (14, 14), (15, 15), (19, 59)] 62⟩))))))))))

def bytes_l12951a : List UInt8 :=
  [0x0F, 0xB7, 0xD2, 0xC1, 0xE2, 0x04, 0x0F, 0xB7, 0x54, 0x13, 0x08, 0xA8, 0x20, 0x75, 0xAC]

theorem code_l12951a : ∀ x ∈ codeRange 0x12951a bytes_l12951a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2951a 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129529 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1294e0, RegMap.args (entryMap (live .l129529)) 53⟩)

def bytes_l129529 : List UInt8 :=
  [0xEB, 0xB5]

theorem code_l129529 : ∀ x ∈ codeRange 0x129529 bytes_l129529, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29529 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12952b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12952b (shrR64Effect 0x12952b 3 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 54) (.exec 0x12952b (fun s => s.RIP = 0x12952b) (shrR64Effect 0x12952b 3 3 1) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 55) (.exec 0x12952e (LoadPre 0x12952e (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12952e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12952e 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.exec 0x129532 (fun s => s.RIP = 0x129532) (movR64R64Effect 0x129532 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.exec 0x129535 (fun s => s.RIP = 0x129535) (movR64R64Effect 0x129535 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 58) (.exec 0x129538 (fun s => s.RIP = 0x129538) (movR64R64Effect 0x129538 2 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x12953b (addR64Imm8Effect 0x12953b 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x12953b (fun s => s.RIP = 0x12953b) (addR64Imm8Effect 0x12953b 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x12953f (popR64Effect 0x12953f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x12953f (PopPre 0x12953f) (popR64Effect 0x12953f 1 3) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x129540 (popR64Effect 0x129540 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x129540 (PopPre 0x129540) (popR64Effect 0x129540 2 12) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x129542 (popR64Effect 0x129542 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x129542 (PopPre 0x129542) (popR64Effect 0x129542 2 13) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x129544 (popR64Effect 0x129544 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x129544 (PopPre 0x129544) (popR64Effect 0x129544 2 14) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x129546 (popR64Effect 0x129546 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 70) (.exec 0x129546 (PopPre 0x129546) (popR64Effect 0x129546 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 71) (.exec 0x129548 (PopPre 0x129548) (popR64Effect 0x129548 1 5) (Reg.operands [.gpr 4] [])) #v[69]
    (cutBlock 0x129549)))))))))))))))))))

def bytes_l12952b : List UInt8 :=
  [0x48, 0xD1, 0xEB, 0x48, 0x8B, 0x46, 0x18, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xEE, 0x48, 0x89, 0xDA,
    0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xFF, 0xE0]

theorem code_l12952b : ∀ x ∈ codeRange 0x12952b bytes_l12952b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2952b 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Sec1.LIR
