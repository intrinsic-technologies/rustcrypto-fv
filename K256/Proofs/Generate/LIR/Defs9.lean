import K256.Proofs.Generate.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Generate.LIR.Generated.Footprints

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR

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

@[cfg_block] def b_l127f50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f50 (cmpR64R64Effect 0x127f50 6 1) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 1] []) (.flag .ZF)) #v[6, 1]
    (.letOp (n := 54) (.exec 0x127f50 (fun s => s.RIP = 0x127f50) (cmpR64R64Effect 0x127f50 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l127f9a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l127f55, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127f50 : List UInt8 :=
  [0x48, 0x39, 0xCE, 0x75, 0x45]

theorem code_l127f50 : ∀ x ∈ codeRange 0x127f50 bytes_l127f50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f50 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127f55 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f55 (testR64R64Effect 0x127f55 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 54) (.exec 0x127f55 (fun s => s.RIP = 0x127f55) (testR64R64Effect 0x127f55 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l127fa9, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l127f5a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l127f55 : List UInt8 :=
  [0x48, 0x85, 0xF6, 0x74, 0x4F]

theorem code_l127f55 : ∀ x ∈ codeRange 0x127f55 bytes_l127f55, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f55 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127f5a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f5a (movR16Imm16Effect 0x127f5a 4 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x127f5a (fun s => s.RIP = 0x127f5a) (movR16Imm16Effect 0x127f5a 4 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x127f5e (xorR32R32Effect 0x127f5e 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x127f5e (fun s => s.RIP = 0x127f5e) (xorR32R32Effect 0x127f5e 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 57) (.out 0x127f61 (xorR32R32Effect 0x127f61 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 58) (.exec 0x127f61 (fun s => s.RIP = 0x127f61) (xorR32R32Effect 0x127f61 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 59) (.exec 0x127f63 (fun s => s.RIP = 0x127f63) (fun _ => nopEffect 0x127f63 13) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l127f70, RegMap.args [(0, 53), (1, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l127f5a : List UInt8 :=
  [0x66, 0xB8, 0x01, 0x00, 0x45, 0x31, 0xC0, 0x31, 0xC9, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F,
    0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l127f5a : ∀ x ∈ codeRange 0x127f5a bytes_l127f5a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f5a 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127f70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f70 (movR64M64Effect 0x127f70 9 (.sib 7 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7, .gpr 8] []) (.reg (.gpr 9))) #v[7, 8]
    (.letOp (n := 54) (.exec 0x127f70 (LoadPre 0x127f70 (fun s => AddrMode.addr (.sib 7 (some 8) 3 .none) s (0x127f70 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f70 9 (.sib 7 (some 8) 3 .none)) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 8]
    (.letOp (n := 55) (.out 0x127f74 (movR64M64Effect 0x127f74 10 (.sib 2 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2, .gpr 8] []) (.reg (.gpr 10))) #v[2, 8]
    (.letOp (n := 56) (.exec 0x127f74 (LoadPre 0x127f74 (fun s => AddrMode.addr (.sib 2 (some 8) 3 .none) s (0x127f74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x127f74 10 (.sib 2 (some 8) 3 .none)) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 8]
    (.letOp (n := 57) (.out 0x127f78 (incR64Effect 0x127f78 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 58) (.exec 0x127f78 (fun s => s.RIP = 0x127f78) (incR64Effect 0x127f78 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 59) (.out 0x127f7b (movzxR32R8Effect 0x127f7b 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x127f7b (fun s => s.RIP = 0x127f7b) (movzxR32R8Effect 0x127f7b 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x127f7e (xorR64R64Effect 0x127f7e 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[53, 55]
    (.letOp (n := 62) (.out 0x127f7e (xorR64R64Effect 0x127f7e 9 10) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 10] []) (.flag .ZF)) #v[53, 55]
    (.letOp (n := 63) (.exec 0x127f7e (fun s => s.RIP = 0x127f7e) (xorR64R64Effect 0x127f7e 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[53, 55]
    (.letOp (n := 64) (.out 0x127f81 (atFlags (condHolds 5) (cmovR64R64Effect 0x127f81 4 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[59, 1, 62]
    (.letOp (n := 65) (.exec 0x127f81 (fun s => s.RIP = 0x127f81) (atFlags (condHolds 5) (cmovR64R64Effect 0x127f81 4 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 1, 62]
    (.letOp (n := 66) (.out 0x127f85 (cmpR64R64Effect 0x127f85 6 8) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 8] []) (.flag .ZF)) #v[6, 57]
    (.letOp (n := 67) (.exec 0x127f85 (fun s => s.RIP = 0x127f85) (cmpR64R64Effect 0x127f85 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 57]
    (.letOp (n := 68) (.pure (condOp 5)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l127f70, RegMap.args [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l127f8a, RegMap.args [(0, 64), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 57), (9, 61), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l127f70 : List UInt8 :=
  [0x4E, 0x8B, 0x0C, 0xC7, 0x4E, 0x8B, 0x14, 0xC2, 0x49, 0xFF, 0xC0, 0x0F, 0xB6, 0xC0, 0x4D, 0x31,
    0xD1, 0x48, 0x0F, 0x45, 0xC1, 0x4C, 0x39, 0xC6, 0x75, 0xE6]

theorem code_l127f70 : ∀ x ∈ codeRange 0x127f70 bytes_l127f70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f70 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127f8a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f8a (movzxR32R8Effect 0x127f8a 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x127f8a (fun s => s.RIP = 0x127f8a) (movzxR32R8Effect 0x127f8a 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x127f8d (xorR32R32Effect 0x127f8d 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x127f8d (fun s => s.RIP = 0x127f8d) (xorR32R32Effect 0x127f8d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 57) (.out 0x127f8f (movR16Imm16Effect 0x127f8f 4 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 58) (.exec 0x127f8f (fun s => s.RIP = 0x127f8f) (movR16Imm16Effect 0x127f8f 4 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x127f93 (xorR16R16Effect 0x127f93 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 57]
    (.letOp (n := 60) (.out 0x127f93 (xorR16R16Effect 0x127f93 3 1 2) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 2] []) (.flag .ZF)) #v[53, 57]
    (.letOp (n := 61) (.exec 0x127f93 (fun s => s.RIP = 0x127f93) (xorR16R16Effect 0x127f93 3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 57]
    (.letOp (n := 62) (.out 0x127f96 (atFlags (condHolds 4) (cmovR32R32Effect 0x127f96 3 0 2)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[55, 57, 60]
    (.letOp (n := 63) (.exec 0x127f96 (fun s => s.RIP = 0x127f96) (atFlags (condHolds 4) (cmovR32R32Effect 0x127f96 3 0 2)) (Reg.operands [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[55, 57, 60]
    (.letOp (n := 64) (.out 0x127f99 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 65) (.out 0x127f99 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x127f99 (RetPre 0x127f99) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l127f8a : List UInt8 :=
  [0x0F, 0xB6, 0xC8, 0x31, 0xC0, 0x66, 0xBA, 0x01, 0x00, 0x66, 0x31, 0xD1, 0x0F, 0x44, 0xC2, 0xC3]

theorem code_l127f8a : ∀ x ∈ codeRange 0x127f8a bytes_l127f8a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f8a 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127f9a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127f9a (xorR32R32Effect 0x127f9a 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 54) (.exec 0x127f9a (fun s => s.RIP = 0x127f9a) (xorR32R32Effect 0x127f9a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.out 0x127f9c (xorR32R32Effect 0x127f9c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x127f9c (fun s => s.RIP = 0x127f9c) (xorR32R32Effect 0x127f9c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 57) (.out 0x127f9e (movR16Imm16Effect 0x127f9e 4 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 58) (.exec 0x127f9e (fun s => s.RIP = 0x127f9e) (movR16Imm16Effect 0x127f9e 4 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x127fa2 (xorR16R16Effect 0x127fa2 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 57]
    (.letOp (n := 60) (.out 0x127fa2 (xorR16R16Effect 0x127fa2 3 1 2) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 2] []) (.flag .ZF)) #v[53, 57]
    (.letOp (n := 61) (.exec 0x127fa2 (fun s => s.RIP = 0x127fa2) (xorR16R16Effect 0x127fa2 3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 57]
    (.letOp (n := 62) (.out 0x127fa5 (atFlags (condHolds 4) (cmovR32R32Effect 0x127fa5 3 0 2)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[55, 57, 60]
    (.letOp (n := 63) (.exec 0x127fa5 (fun s => s.RIP = 0x127fa5) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fa5 3 0 2)) (Reg.operands [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[55, 57, 60]
    (.letOp (n := 64) (.out 0x127fa8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 65) (.out 0x127fa8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x127fa8 (RetPre 0x127fa8) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l127f9a : List UInt8 :=
  [0x31, 0xC9, 0x31, 0xC0, 0x66, 0xBA, 0x01, 0x00, 0x66, 0x31, 0xD1, 0x0F, 0x44, 0xC2, 0xC3]

theorem code_l127f9a : ∀ x ∈ codeRange 0x127f9a bytes_l127f9a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27f9a 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l127fa9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x127fa9 (movR16Imm16Effect 0x127fa9 4 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x127fa9 (fun s => s.RIP = 0x127fa9) (movR16Imm16Effect 0x127fa9 4 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x127fad (xorR32R32Effect 0x127fad 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x127fad (fun s => s.RIP = 0x127fad) (xorR32R32Effect 0x127fad 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 57) (.out 0x127faf (movR16Imm16Effect 0x127faf 4 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 58) (.exec 0x127faf (fun s => s.RIP = 0x127faf) (movR16Imm16Effect 0x127faf 4 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x127fb3 (xorR16R16Effect 0x127fb3 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[53, 57]
    (.letOp (n := 60) (.out 0x127fb3 (xorR16R16Effect 0x127fb3 3 1 2) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 2] []) (.flag .ZF)) #v[53, 57]
    (.letOp (n := 61) (.exec 0x127fb3 (fun s => s.RIP = 0x127fb3) (xorR16R16Effect 0x127fb3 3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[53, 57]
    (.letOp (n := 62) (.out 0x127fb6 (atFlags (condHolds 4) (cmovR32R32Effect 0x127fb6 3 0 2)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[55, 57, 60]
    (.letOp (n := 63) (.exec 0x127fb6 (fun s => s.RIP = 0x127fb6) (atFlags (condHolds 4) (cmovR32R32Effect 0x127fb6 3 0 2)) (Reg.operands [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[55, 57, 60]
    (.letOp (n := 64) (.out 0x127fb9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 65) (.out 0x127fb9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x127fb9 (RetPre 0x127fb9) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 62), (1, 59), (2, 57), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 67) (some ⟨64, by decide⟩))))))))))))))))

def bytes_l127fa9 : List UInt8 :=
  [0x66, 0xB9, 0x01, 0x00, 0x31, 0xC0, 0x66, 0xBA, 0x01, 0x00, 0x66, 0x31, 0xD1, 0x0F, 0x44, 0xC2,
    0xC3]

theorem code_l127fa9 : ∀ x ∈ codeRange 0x127fa9 bytes_l127fa9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27fa9 17 (by decide +kernel)
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

@[cfg_block] def b_l12954b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12954b (xorR32R32Effect 0x12954b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x12954b (fun s => s.RIP = 0x12954b) (xorR32R32Effect 0x12954b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l129551, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12954b : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x02]

theorem code_l12954b : ∀ x ∈ codeRange 0x12954b bytes_l12954b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2954b 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12954f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12954f (movR8Imm8Effect 0x12954f 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x12954f (fun s => s.RIP = 0x12954f) (movR8Imm8Effect 0x12954f 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l129551, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l12954f : List UInt8 :=
  [0xB0, 0x01]

theorem code_l12954f : ∀ x ∈ codeRange 0x12954f bytes_l12954f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2954f 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129551 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129551 (addR64Imm8Effect 0x129551 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x129551 (fun s => s.RIP = 0x129551) (addR64Imm8Effect 0x129551 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x129555 (popR64Effect 0x129555 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x129555 (popR64Effect 0x129555 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x129555 (PopPre 0x129555) (popR64Effect 0x129555 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x129556 (popR64Effect 0x129556 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x129556 (popR64Effect 0x129556 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x129556 (PopPre 0x129556) (popR64Effect 0x129556 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x129558 (popR64Effect 0x129558 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x129558 (popR64Effect 0x129558 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x129558 (PopPre 0x129558) (popR64Effect 0x129558 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x12955a (popR64Effect 0x12955a 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x12955a (popR64Effect 0x12955a 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x12955a (PopPre 0x12955a) (popR64Effect 0x12955a 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x12955c (popR64Effect 0x12955c 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x12955c (popR64Effect 0x12955c 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x12955c (PopPre 0x12955c) (popR64Effect 0x12955c 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x12955e (popR64Effect 0x12955e 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x12955e (popR64Effect 0x12955e 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x12955e (PopPre 0x12955e) (popR64Effect 0x12955e 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x12955f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x12955f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x12955f (RetPre 0x12955f) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l129551 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l129551 : ∀ x ∈ codeRange 0x129551 bytes_l129551, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29551 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129560 (pushR64Effect 0x129560 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129560 (PushPre 0x129560 1) (pushR64Effect 0x129560 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x129561 (movR64R64Effect 0x129561 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x129561 (fun s => s.RIP = 0x129561) (movR64R64Effect 0x129561 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129564 (subR64Imm8Effect 0x129564 4 0x20) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x129564 (fun s => s.RIP = 0x129564) (subR64Imm8Effect 0x129564 4 0x20) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x129568 (StorePre 0x129568 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129568 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129568 7 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 55]
    (.letOp (n := 60) (.exec 0x12956c (StorePre 0x12956c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12956c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12956c 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 61) (.out 0x129570 (leaR64Effect 0x129570 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 62) (.exec 0x129570 (fun s => s.RIP = 0x129570) (leaR64Effect 0x129570 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 63) (.exec 0x129574 (StorePre 0x129574 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129574 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129574 0 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 55]
    (.letOp (n := 64) (.out 0x129578 (leaR64Effect 0x129578 0 (.rip 0xaf1)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x129578 (fun s => s.RIP = 0x129578) (leaR64Effect 0x129578 0 (.rip 0xaf1)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x12957f (StorePre 0x12957f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12957f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12957f 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[64, 55]
    (.letOp (n := 67) (.out 0x129583 (leaR64Effect 0x129583 7 (.rip 0xd8481)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 68) (.exec 0x129583 (fun s => s.RIP = 0x129583) (leaR64Effect 0x129583 7 (.rip 0xd8481)) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x12958a (leaR64Effect 0x12958a 6 (.base 5 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 70) (.exec 0x12958a (fun s => s.RIP = 0x12958a) (leaR64Effect 0x12958a 6 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 71) (.out 0x12958e (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 72) (.exec 0x12958e (GoesTo (CallMemPre 0x12958e (.rip 0xda84c)) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c)))) 0x129770) (callEffect (callMemPtr 0x12958e (.rip 0xda84c)) (0x12958e + BitVec.ofNat 64 (callMemLen (.rip 0xda84c)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 73) (.const ⟨64, 0x129594⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 64), (2, 2), (4, 71), (5, 55), (6, 69), (7, 67)] 74⟩ { target := .l129594, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l129560 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x20, 0x48, 0x89, 0x7D, 0xF0, 0x48, 0x89, 0x75, 0xF8,
    0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x45, 0xE0, 0x48, 0x8D, 0x05, 0xF1, 0x0A, 0x00, 0x00, 0x48,
    0x89, 0x45, 0xE8, 0x48, 0x8D, 0x3D, 0x81, 0x84, 0x0D, 0x00, 0x48, 0x8D, 0x75, 0xE0, 0xFF, 0x15,
    0x4C, 0xA8, 0x0D, 0x00]

theorem code_l129560 : ∀ x ∈ codeRange 0x129560 bytes_l129560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29560 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129594 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x129594 (fun s => s.RIP = 0x129594) (fun _ => nopEffect 0x129594 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x12959e (fun s => s.RIP = 0x12959e) (fun _ => nopEffect 0x12959e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1295a0, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)] 55⟩)))

def bytes_l129594 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l129594 : ∀ x ∈ codeRange 0x129594 bytes_l129594, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29594 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1295a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1295a0 (pushR64Effect 0x1295a0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1295a0 (PushPre 0x1295a0 1) (pushR64Effect 0x1295a0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1295a1 (movR64R64Effect 0x1295a1 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x1295a1 (fun s => s.RIP = 0x1295a1) (movR64R64Effect 0x1295a1 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x1295a4 (subR64Imm8Effect 0x1295a4 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x1295a4 (fun s => s.RIP = 0x1295a4) (subR64Imm8Effect 0x1295a4 4 0x40) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x1295a8 (StorePre 0x1295a8 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x1295a8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295a8 7 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 55]
    (.letOp (n := 60) (.exec 0x1295ac (StorePre 0x1295ac 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x1295ac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295ac 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 61) (.exec 0x1295b0 (StorePre 0x1295b0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x1295b0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295b0 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 55]
    (.letOp (n := 62) (.exec 0x1295b4 (StorePre 0x1295b4 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x1295b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295b4 1 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 55]
    (.letOp (n := 63) (.out 0x1295b8 (leaR64Effect 0x1295b8 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 64) (.exec 0x1295b8 (fun s => s.RIP = 0x1295b8) (leaR64Effect 0x1295b8 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 65) (.exec 0x1295bc (StorePre 0x1295bc 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1295bc + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295bc 0 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[63, 55]
    (.letOp (n := 66) (.out 0x1295c0 (leaR64Effect 0x1295c0 0 (.rip 0xaa9)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 67) (.exec 0x1295c0 (fun s => s.RIP = 0x1295c0) (leaR64Effect 0x1295c0 0 (.rip 0xaa9)) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.exec 0x1295c7 (StorePre 0x1295c7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1295c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295c7 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[66, 55]
    (.letOp (n := 69) (.out 0x1295cb (leaR64Effect 0x1295cb 0 (.base 5 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 70) (.exec 0x1295cb (fun s => s.RIP = 0x1295cb) (leaR64Effect 0x1295cb 0 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 71) (.exec 0x1295cf (StorePre 0x1295cf 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x1295cf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295cf 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[69, 55]
    (.letOp (n := 72) (.out 0x1295d3 (leaR64Effect 0x1295d3 0 (.rip 0xa76)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 73) (.exec 0x1295d3 (fun s => s.RIP = 0x1295d3) (leaR64Effect 0x1295d3 0 (.rip 0xa76)) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.exec 0x1295da (StorePre 0x1295da 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x1295da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1295da 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[72, 55]
    (.letOp (n := 75) (.out 0x1295de (leaR64Effect 0x1295de 7 (.rip 0xd8422)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 76) (.exec 0x1295de (fun s => s.RIP = 0x1295de) (leaR64Effect 0x1295de 7 (.rip 0xd8422)) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x1295e5 (leaR64Effect 0x1295e5 6 (.base 5 (.d8 0xc0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 78) (.exec 0x1295e5 (fun s => s.RIP = 0x1295e5) (leaR64Effect 0x1295e5 6 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 79) (.out 0x1295e9 (movR64R64Effect 0x1295e9 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 80) (.exec 0x1295e9 (fun s => s.RIP = 0x1295e9) (movR64R64Effect 0x1295e9 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 81) (.out 0x1295ec (callEffect (callMemPtr 0x1295ec (.rip 0xda7ee)) (0x1295ec + BitVec.ofNat 64 (callMemLen (.rip 0xda7ee)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 82) (.exec 0x1295ec (GoesTo (CallMemPre 0x1295ec (.rip 0xda7ee)) (callEffect (callMemPtr 0x1295ec (.rip 0xda7ee)) (0x1295ec + BitVec.ofNat 64 (callMemLen (.rip 0xda7ee)))) 0x129770) (callEffect (callMemPtr 0x1295ec (.rip 0xda7ee)) (0x1295ec + BitVec.ofNat 64 (callMemLen (.rip 0xda7ee)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 83) (.const ⟨64, 0x1295f2⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 72), (1, 1), (2, 79), (4, 81), (5, 55), (6, 77), (7, 75), (8, 8)] 84⟩ { target := .l1295f2, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l1295a0 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x40, 0x48, 0x89, 0x7D, 0xF0, 0x48, 0x89, 0x75, 0xF8,
    0x48, 0x89, 0x55, 0xE0, 0x48, 0x89, 0x4D, 0xE8, 0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x45, 0xC0,
    0x48, 0x8D, 0x05, 0xA9, 0x0A, 0x00, 0x00, 0x48, 0x89, 0x45, 0xC8, 0x48, 0x8D, 0x45, 0xE0, 0x48,
    0x89, 0x45, 0xD0, 0x48, 0x8D, 0x05, 0x76, 0x0A, 0x00, 0x00, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x8D,
    0x3D, 0x22, 0x84, 0x0D, 0x00, 0x48, 0x8D, 0x75, 0xC0, 0x4C, 0x89, 0xC2, 0xFF, 0x15, 0xEE, 0xA7,
    0x0D, 0x00]

theorem code_l1295a0 : ∀ x ∈ codeRange 0x1295a0 bytes_l1295a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x295a0 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1295f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1295f2 (pushR64Effect 0x1295f2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1295f2 (PushPre 0x1295f2 1) (pushR64Effect 0x1295f2 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1295f3 (movR64R64Effect 0x1295f3 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x1295f3 (fun s => s.RIP = 0x1295f3) (movR64R64Effect 0x1295f3 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x1295f6 (subR64Imm8Effect 0x1295f6 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x1295f6 (fun s => s.RIP = 0x1295f6) (subR64Imm8Effect 0x1295f6 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x1295fa (leaR64Effect 0x1295fa 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 60) (.exec 0x1295fa (fun s => s.RIP = 0x1295fa) (leaR64Effect 0x1295fa 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 61) (.exec 0x1295fe (StorePre 0x1295fe 3 (fun s => AddrMode.addr (.base 0 .none) s (0x1295fe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1295fe 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 59]
    (.letOp (n := 62) (.out 0x129601 (leaR64Effect 0x129601 1 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 63) (.exec 0x129601 (fun s => s.RIP = 0x129601) (leaR64Effect 0x129601 1 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 64) (.exec 0x129605 (StorePre 0x129605 3 (fun s => AddrMode.addr (.base 1 .none) s (0x129605 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129605 6 (.base 1 .none)) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6, 62]
    (.letOp (n := 65) (.out 0x129608 (leaR64Effect 0x129608 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 66) (.exec 0x129608 (fun s => s.RIP = 0x129608) (leaR64Effect 0x129608 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 67) (.exec 0x12960c (StorePre 0x12960c 3 (fun s => AddrMode.addr (.base 6 .none) s (0x12960c + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x12960c 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[62, 65]
    (.letOp (n := 68) (.out 0x12960f (leaR64Effect 0x12960f 1 (.rip 0xe1a)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 69) (.exec 0x12960f (fun s => s.RIP = 0x12960f) (leaR64Effect 0x12960f 1 (.rip 0xe1a)) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.exec 0x129616 (StorePre 0x129616 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x129616 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129616 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[68, 65]
    (.letOp (n := 71) (.exec 0x12961a (StorePre 0x12961a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x12961a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961a 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[59, 65]
    (.letOp (n := 72) (.exec 0x12961e (StorePre 0x12961e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12961e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12961e 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[68, 65]
    (.letOp (n := 73) (.out 0x129622 (leaR64Effect 0x129622 7 (.rip 0xd8432)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 74) (.exec 0x129622 (fun s => s.RIP = 0x129622) (leaR64Effect 0x129622 7 (.rip 0xd8432)) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x129629 (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 76) (.exec 0x129629 (GoesTo (CallMemPre 0x129629 (.rip 0xda7b1)) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1)))) 0x129770) (callEffect (callMemPtr 0x129629 (.rip 0xda7b1)) (0x129629 + BitVec.ofNat 64 (callMemLen (.rip 0xda7b1)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 77) (.const ⟨64, 0x12962f⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 59), (1, 68), (2, 2), (4, 75), (5, 55), (6, 65), (7, 73)] 78⟩ { target := .l12962f, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l1295f2 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x38, 0x48,
    0x8D, 0x4D, 0xF0, 0x48, 0x89, 0x31, 0x48, 0x8D, 0x75, 0xD0, 0x48, 0x89, 0x0E, 0x48, 0x8D, 0x0D,
    0x1A, 0x0E, 0x00, 0x00, 0x48, 0x89, 0x4E, 0x08, 0x48, 0x89, 0x46, 0x10, 0x48, 0x89, 0x4E, 0x18,
    0x48, 0x8D, 0x3D, 0x32, 0x84, 0x0D, 0x00, 0xFF, 0x15, 0xB1, 0xA7, 0x0D, 0x00]

theorem code_l1295f2 : ∀ x ∈ codeRange 0x1295f2 bytes_l1295f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x295f2 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12962f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12962f (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x129630 (pushR64Effect 0x129630 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x129630 (PushPre 0x129630 1) (pushR64Effect 0x129630 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x129631 (movR64R64Effect 0x129631 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[54]
    (.letOp (n := 57) (.exec 0x129631 (fun s => s.RIP = 0x129631) (movR64R64Effect 0x129631 5 4) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 58) (.out 0x129634 (subR64Imm8Effect 0x129634 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 59) (.exec 0x129634 (fun s => s.RIP = 0x129634) (subR64Imm8Effect 0x129634 4 0x30) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 60) (.exec 0x129638 (StorePre 0x129638 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129638 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129638 7 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 56]
    (.letOp (n := 61) (.exec 0x12963c (StorePre 0x12963c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x12963c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12963c 6 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 56]
    (.letOp (n := 62) (.out 0x129640 (leaR64Effect 0x129640 0 (.base 5 (.d8 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 63) (.exec 0x129640 (fun s => s.RIP = 0x129640) (leaR64Effect 0x129640 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 5] [])) #v[56]
    (.letOp (n := 64) (.exec 0x129644 (StorePre 0x129644 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129644 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129644 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[62, 56]
    (.letOp (n := 65) (.exec 0x129648 (StorePre 0x129648 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129648 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129648 1 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 56]
    (.letOp (n := 66) (.exec 0x12964c (StorePre 0x12964c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12964c + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x12964c (.base 5 (.d8 0xf8)) 0x0) (Reg.operands [.gpr 5] [])) #v[56]
    (.letOp (n := 67) (.exec 0x129650 (StorePre 0x129650 3 (fun s => AddrMode.addr (.base 5 (.d8 0xf9)) s (0x129650 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x129650 3 2 (.base 5 (.d8 0xf9))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 56]
    (.letOp (n := 68) (.exec 0x129653 (fun s => s.RIP = 0x129653) (leaR64Effect 0x129653 7 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 5] [])) #v[56]
    (.letOp (n := 69) (.exec 0x129657 (GoesTo (CallMemPre 0x129657 (.rip 0xda7c3)) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3)))) 0x100a20) (callEffect (callMemPtr 0x129657 (.rip 0xda7c3)) (0x129657 + BitVec.ofNat 64 (callMemLen (.rip 0xda7c3)))) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 70) (.const ⟨64, 0x12965d⟩) #v[]
    (.terminate (.call ⟨.l100a20, RegMap.args [(0, 62), (1, 1), (2, 2), (5, 56), (6, 6)] 71⟩ { target := .l12965d, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l12962f : List UInt8 :=
  [0x90, 0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0x7D, 0xD8, 0x48, 0x89, 0x75,
    0xE0, 0x48, 0x8D, 0x45, 0xD8, 0x48, 0x89, 0x45, 0xE8, 0x48, 0x89, 0x4D, 0xF0, 0xC6, 0x45, 0xF8,
    0x00, 0x88, 0x55, 0xF9, 0x48, 0x8D, 0x7D, 0xE8, 0xFF, 0x15, 0xC3, 0xA7, 0x0D, 0x00]

theorem code_l12962f : ∀ x ∈ codeRange 0x12962f bytes_l12962f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2962f 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12965d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12965d (pushR64Effect 0x12965d 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x12965d (PushPre 0x12965d 1) (pushR64Effect 0x12965d 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x12965e (movR64R64Effect 0x12965e 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x12965e (fun s => s.RIP = 0x12965e) (movR64R64Effect 0x12965e 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129661 (subR64Imm32Effect 0x129661 4 0x80) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x129661 (fun s => s.RIP = 0x129661) (subR64Imm32Effect 0x129661 4 0x80) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x129668 (movR64R64Effect 0x129668 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 60) (.exec 0x129668 (fun s => s.RIP = 0x129668) (movR64R64Effect 0x129668 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x12966b (movR64M64Effect 0x12966b 2 (.base 5 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 62) (.exec 0x12966b (LoadPre 0x12966b (fun s => AddrMode.addr (.base 5 (.d8 0x18)) s (0x12966b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12966b 2 (.base 5 (.d8 0x18))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 63) (.exec 0x12966f (StorePre 0x12966f 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x12966f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12966f 6 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 64) (.exec 0x129673 (StorePre 0x129673 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129673 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129673 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[59, 55]
    (.letOp (n := 65) (.exec 0x129677 (StorePre 0x129677 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129677 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129677 1 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 55]
    (.letOp (n := 66) (.exec 0x12967b (StorePre 0x12967b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12967b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12967b 8 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 8, .gpr 5] [])) #v[8, 55]
    (.letOp (n := 67) (.out 0x12967f (leaR64Effect 0x12967f 0 (.rip 0xda68a)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 68) (.exec 0x12967f (fun s => s.RIP = 0x12967f) (leaR64Effect 0x12967f 0 (.rip 0xda68a)) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x129686 (movzxR32R8Effect 0x129686 4 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 70) (.exec 0x129686 (fun s => s.RIP = 0x129686) (movzxR32R8Effect 0x129686 4 1 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x12968a (movsxdR64M32Effect 0x12968a 4 6 (.sib 0 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0, .gpr 1] []) (.reg (.gpr 6))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x12968a (LoadPre 0x12968a (fun s => AddrMode.addr (.sib 0 (some 1) 2 .none) s (0x12968a + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x12968a 4 6 (.sib 0 (some 1) 2 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[67, 69]
    (.letOp (n := 73) (.out 0x12968e (addR64R64Effect 0x12968e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x12968e (fun s => s.RIP = 0x12968e) (addR64R64Effect 0x12968e 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x129691 (leaR64Effect 0x129691 0 (.rip 0xda688)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 76) (.exec 0x129691 (fun s => s.RIP = 0x129691) (leaR64Effect 0x129691 0 (.rip 0xda688)) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x129698 (movR64M64Effect 0x129698 0 (.sib 0 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[75, 69]
    (.letOp (n := 78) (.exec 0x129698 (LoadPre 0x129698 (fun s => AddrMode.addr (.sib 0 (some 1) 3 .none) s (0x129698 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129698 0 (.sib 0 (some 1) 3 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[75, 69]
    (.letOp (n := 79) (.exec 0x12969c (StorePre 0x12969c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x12969c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12969c 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[73, 55]
    (.letOp (n := 80) (.exec 0x1296a0 (StorePre 0x1296a0 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x1296a0 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296a0 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[77, 55]
    (.letOp (n := 81) (.out 0x1296a4 (testR64R64Effect 0x1296a4 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[9, 9]
    (.letOp (n := 82) (.exec 0x1296a4 (fun s => s.RIP = 0x1296a4) (testR64R64Effect 0x1296a4 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 83) (.pure (condOp 5)) #v[81]
    (.terminate (.condBr (Fin.last 83) ⟨.l1296eb, RegMap.args [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9), (19, 81)] 84⟩ ⟨.l1296a9, RegMap.args [(0, 77), (1, 69), (2, 61), (4, 57), (5, 55), (6, 73), (7, 7), (8, 8), (9, 9), (19, 81)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l12965d : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x81, 0xEC, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xD0, 0x48, 0x8B,
    0x55, 0x18, 0x48, 0x89, 0x75, 0xF0, 0x48, 0x89, 0x45, 0xF8, 0x48, 0x89, 0x4D, 0xE0, 0x4C, 0x89,
    0x45, 0xE8, 0x48, 0x8D, 0x05, 0x8A, 0xA6, 0x0D, 0x00, 0x40, 0x0F, 0xB6, 0xCF, 0x48, 0x63, 0x34,
    0x88, 0x48, 0x01, 0xC6, 0x48, 0x8D, 0x05, 0x88, 0xA6, 0x0D, 0x00, 0x48, 0x8B, 0x04, 0xC8, 0x48,
    0x89, 0x75, 0xD0, 0x48, 0x89, 0x45, 0xD8, 0x4D, 0x85, 0xC9, 0x75, 0x42]

theorem code_l12965d : ∀ x ∈ codeRange 0x12965d bytes_l12965d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2965d 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1296a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1296a9 (leaR64Effect 0x1296a9 0 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x1296a9 (fun s => s.RIP = 0x1296a9) (leaR64Effect 0x1296a9 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1296ad (leaR64Effect 0x1296ad 6 (.base 5 (.d8 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 56) (.exec 0x1296ad (fun s => s.RIP = 0x1296ad) (leaR64Effect 0x1296ad 6 (.base 5 (.d8 0x80))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x1296b1 (StorePre 0x1296b1 3 (fun s => AddrMode.addr (.base 6 .none) s (0x1296b1 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296b1 0 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[53, 55]
    (.letOp (n := 58) (.out 0x1296b4 (leaR64Effect 0x1296b4 0 (.rip 0x9b5)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 59) (.exec 0x1296b4 (fun s => s.RIP = 0x1296b4) (leaR64Effect 0x1296b4 0 (.rip 0x9b5)) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x1296bb (StorePre 0x1296bb 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1296bb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296bb 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[58, 55]
    (.letOp (n := 61) (.out 0x1296bf (leaR64Effect 0x1296bf 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 62) (.exec 0x1296bf (fun s => s.RIP = 0x1296bf) (leaR64Effect 0x1296bf 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.exec 0x1296c3 (StorePre 0x1296c3 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1296c3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296c3 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[61, 55]
    (.letOp (n := 64) (.out 0x1296c7 (leaR64Effect 0x1296c7 0 (.rip 0x982)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x1296c7 (fun s => s.RIP = 0x1296c7) (leaR64Effect 0x1296c7 0 (.rip 0x982)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x1296ce (StorePre 0x1296ce 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1296ce + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296ce 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[64, 55]
    (.letOp (n := 67) (.out 0x1296d2 (leaR64Effect 0x1296d2 1 (.base 5 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 68) (.exec 0x1296d2 (fun s => s.RIP = 0x1296d2) (leaR64Effect 0x1296d2 1 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 69) (.exec 0x1296d6 (StorePre 0x1296d6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1296d6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296d6 1 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[67, 55]
    (.letOp (n := 70) (.exec 0x1296da (StorePre 0x1296da 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x1296da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296da 0 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[64, 55]
    (.letOp (n := 71) (.out 0x1296de (leaR64Effect 0x1296de 7 (.rip 0xd83ad)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 72) (.exec 0x1296de (fun s => s.RIP = 0x1296de) (leaR64Effect 0x1296de 7 (.rip 0xd83ad)) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x1296e5 (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x1296e5 (GoesTo (CallMemPre 0x1296e5 (.rip 0xda6f5)) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5)))) 0x129770) (callEffect (callMemPtr 0x1296e5 (.rip 0xda6f5)) (0x1296e5 + BitVec.ofNat 64 (callMemLen (.rip 0xda6f5)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x1296eb⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 64), (1, 67), (2, 2), (4, 73), (5, 5), (6, 55), (7, 71)] 76⟩ { target := .l1296eb, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l1296a9 : List UInt8 :=
  [0x48, 0x8D, 0x45, 0xD0, 0x48, 0x8D, 0x75, 0x80, 0x48, 0x89, 0x06, 0x48, 0x8D, 0x05, 0xB5, 0x09,
    0x00, 0x00, 0x48, 0x89, 0x46, 0x08, 0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x46, 0x10, 0x48, 0x8D,
    0x05, 0x82, 0x09, 0x00, 0x00, 0x48, 0x89, 0x46, 0x18, 0x48, 0x8D, 0x4D, 0xE0, 0x48, 0x89, 0x4E,
    0x20, 0x48, 0x89, 0x46, 0x28, 0x48, 0x8D, 0x3D, 0xAD, 0x83, 0x0D, 0x00, 0xFF, 0x15, 0xF5, 0xA6,
    0x0D, 0x00]

theorem code_l1296a9 : ∀ x ∈ codeRange 0x1296a9 bytes_l1296a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x296a9 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1296eb_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x129745 (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x129745 (GoesTo (CallMemPre 0x129745 (.rip 0xda695)) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695)))) 0x129770) (callEffect (callMemPtr 0x129745 (.rip 0xda695)) (0x129745 + BitVec.ofNat 64 (callMemLen (.rip 0xda695)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x12974b⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 74), (1, 77), (2, 2), (4, 83), (5, 5), (6, 61), (7, 81), (9, 9)] 86⟩ { target := .l12974b, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))

def bytes_l1296eb_1 : List UInt8 :=
  [0xFF, 0x15, 0x95, 0xA6, 0x0D, 0x00]

theorem code_l1296eb_1 : ∀ x ∈ codeRange 0x129745 bytes_l1296eb_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29745 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1296eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1296eb (movR64M64Effect 0x1296eb 0 (.base 5 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x1296eb (LoadPre 0x1296eb (fun s => AddrMode.addr (.base 5 (.d8 0x10)) s (0x1296eb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1296eb 0 (.base 5 (.d8 0x10))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1296ef (leaR64Effect 0x1296ef 1 (.base 5 (.d8 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 56) (.exec 0x1296ef (fun s => s.RIP = 0x1296ef) (leaR64Effect 0x1296ef 1 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x1296f3 (StorePre 0x1296f3 3 (fun s => AddrMode.addr (.base 1 .none) s (0x1296f3 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1296f3 9 (.base 1 .none)) (Reg.operands [.gpr 9, .gpr 1] [])) #v[9, 55]
    (.letOp (n := 58) (.exec 0x1296f6 (StorePre 0x1296f6 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x1296f6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1296f6 0 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x1296fa (leaR64Effect 0x1296fa 0 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 60) (.exec 0x1296fa (fun s => s.RIP = 0x1296fa) (leaR64Effect 0x1296fa 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 61) (.out 0x1296fe (leaR64Effect 0x1296fe 6 (.base 5 (.d8 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[5]
    (.letOp (n := 62) (.exec 0x1296fe (fun s => s.RIP = 0x1296fe) (leaR64Effect 0x1296fe 6 (.base 5 (.d8 0x80))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.exec 0x129702 (StorePre 0x129702 3 (fun s => AddrMode.addr (.base 6 .none) s (0x129702 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x129702 0 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[59, 61]
    (.letOp (n := 64) (.out 0x129705 (leaR64Effect 0x129705 0 (.rip 0x964)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x129705 (fun s => s.RIP = 0x129705) (leaR64Effect 0x129705 0 (.rip 0x964)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x12970c (StorePre 0x12970c 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12970c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12970c 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[64, 61]
    (.letOp (n := 67) (.exec 0x129710 (StorePre 0x129710 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x129710 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129710 1 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[55, 61]
    (.letOp (n := 68) (.out 0x129714 (leaR64Effect 0x129714 0 (.rip 0x9e5)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 69) (.exec 0x129714 (fun s => s.RIP = 0x129714) (leaR64Effect 0x129714 0 (.rip 0x9e5)) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.exec 0x12971b (StorePre 0x12971b 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x12971b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12971b 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[68, 61]
    (.letOp (n := 71) (.out 0x12971f (leaR64Effect 0x12971f 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 72) (.exec 0x12971f (fun s => s.RIP = 0x12971f) (leaR64Effect 0x12971f 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 73) (.exec 0x129723 (StorePre 0x129723 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x129723 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129723 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[71, 61]
    (.letOp (n := 74) (.out 0x129727 (leaR64Effect 0x129727 0 (.rip 0x922)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 75) (.exec 0x129727 (fun s => s.RIP = 0x129727) (leaR64Effect 0x129727 0 (.rip 0x922)) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.exec 0x12972e (StorePre 0x12972e 4 (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x12972e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12972e 0 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[74, 61]
    (.letOp (n := 77) (.out 0x129732 (leaR64Effect 0x129732 1 (.base 5 (.d8 0xe0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 78) (.exec 0x129732 (fun s => s.RIP = 0x129732) (leaR64Effect 0x129732 1 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 79) (.exec 0x129736 (StorePre 0x129736 4 (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x129736 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129736 1 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[77, 61]
    (.letOp (n := 80) (.exec 0x12973a (StorePre 0x12973a 4 (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x12973a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12973a 0 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[74, 61]
    (.letOp (n := 81) (.out 0x12973e (leaR64Effect 0x12973e 7 (.rip 0xd8384)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 82) (.exec 0x12973e (fun s => s.RIP = 0x12973e) (leaR64Effect 0x12973e 7 (.rip 0xd8384)) (Reg.operands [] [])) #v[]
    (b_l1296eb_1))))))))))))))))))))))))))))))

def bytes_l1296eb : List UInt8 :=
  [0x48, 0x8B, 0x45, 0x10, 0x48, 0x8D, 0x4D, 0xC0, 0x4C, 0x89, 0x09, 0x48, 0x89, 0x41, 0x08, 0x48,
    0x8D, 0x45, 0xD0, 0x48, 0x8D, 0x75, 0x80, 0x48, 0x89, 0x06, 0x48, 0x8D, 0x05, 0x64, 0x09, 0x00,
    0x00, 0x48, 0x89, 0x46, 0x08, 0x48, 0x89, 0x4E, 0x10, 0x48, 0x8D, 0x05, 0xE5, 0x09, 0x00, 0x00,
    0x48, 0x89, 0x46, 0x18, 0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x46, 0x20, 0x48, 0x8D, 0x05, 0x22,
    0x09, 0x00, 0x00, 0x48, 0x89, 0x46, 0x28, 0x48, 0x8D, 0x4D, 0xE0, 0x48, 0x89, 0x4E, 0x30, 0x48,
    0x89, 0x46, 0x38, 0x48, 0x8D, 0x3D, 0x84, 0x83, 0x0D, 0x00] ++ bytes_l1296eb_1

theorem code_l1296eb : ∀ x ∈ codeRange 0x1296eb bytes_l1296eb, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x296eb 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1296eb_1

@[cfg_block] def b_l12974b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12974b (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x129750 (pushR64Effect 0x129750 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x129750 (PushPre 0x129750 1) (pushR64Effect 0x129750 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x129751 (movR64R64Effect 0x129751 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[54]
    (.letOp (n := 57) (.exec 0x129751 (fun s => s.RIP = 0x129751) (movR64R64Effect 0x129751 5 4) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 58) (.out 0x129754 (leaR64Effect 0x129754 6 (.abs (some 6) 1 0x1)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 59) (.exec 0x129754 (fun s => s.RIP = 0x129754) (leaR64Effect 0x129754 6 (.abs (some 6) 1 0x1)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x12975c (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 61) (.exec 0x12975c (GoesTo (CallMemPre 0x12975c (.rip 0xda67e)) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) 0x129770) (callEffect (callMemPtr 0x12975c (.rip 0xda67e)) (0x12975c + BitVec.ofNat 64 (callMemLen (.rip 0xda67e)))) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 62) (.const ⟨64, 0x129762⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(2, 2), (4, 60), (5, 56), (6, 58), (7, 7)] 63⟩ { target := .l129762, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l12974b : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00, 0x55, 0x48, 0x89, 0xE5, 0x48, 0x8D, 0x34, 0x75, 0x01, 0x00, 0x00,
    0x00, 0xFF, 0x15, 0x7E, 0xA6, 0x0D, 0x00]

theorem code_l12974b : ∀ x ∈ codeRange 0x12974b bytes_l12974b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2974b 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129762 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x129762 (fun s => s.RIP = 0x129762) (fun _ => nopEffect 0x129762 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x12976c (fun s => s.RIP = 0x12976c) (fun _ => nopEffect 0x12976c 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129770, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 55⟩)))

def bytes_l129762 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x40, 0x00]

theorem code_l129762 : ∀ x ∈ codeRange 0x129762 bytes_l129762, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29762 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129770 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129770 (pushR64Effect 0x129770 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129770 (PushPre 0x129770 1) (pushR64Effect 0x129770 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x129771 (movR64R64Effect 0x129771 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x129771 (fun s => s.RIP = 0x129771) (movR64R64Effect 0x129771 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129774 (subR64Imm8Effect 0x129774 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x129774 (fun s => s.RIP = 0x129774) (subR64Imm8Effect 0x129774 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x129778 (StorePre 0x129778 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129778 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129778 7 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 55]
    (.letOp (n := 60) (.exec 0x12977c (StorePre 0x12977c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x12977c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x12977c 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 61) (.out 0x129780 (leaR64Effect 0x129780 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 62) (.exec 0x129780 (fun s => s.RIP = 0x129780) (leaR64Effect 0x129780 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 63) (.exec 0x129784 (StorePre 0x129784 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129784 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129784 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 55]
    (.letOp (n := 64) (.exec 0x129788 (StorePre 0x129788 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129788 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129788 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 55]
    (.letOp (n := 65) (.exec 0x12978c (StorePre 0x12978c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x12978c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x12978c (.base 5 (.d8 0xe8)) 0x1) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 66) (.exec 0x129792 (fun s => s.RIP = 0x129792) (leaR64Effect 0x129792 7 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 67) (.exec 0x129796 (GoesTo (CallMemPre 0x129796 (.rip 0xda684)) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684)))) 0x100a20) (callEffect (callMemPtr 0x129796 (.rip 0xda684)) (0x129796 + BitVec.ofNat 64 (callMemLen (.rip 0xda684)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 68) (.const ⟨64, 0x12979c⟩) #v[]
    (.terminate (.call ⟨.l100a20, RegMap.args [(0, 61), (2, 2), (5, 55), (6, 6)] 69⟩ { target := .l12979c, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l129770 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0x7D, 0xF0, 0x48, 0x89, 0x75, 0xF8,
    0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x89, 0x55, 0xE0, 0x66, 0xC7, 0x45, 0xE8,
    0x01, 0x00, 0x48, 0x8D, 0x7D, 0xD8, 0xFF, 0x15, 0x84, 0xA6, 0x0D, 0x00]

theorem code_l129770 : ∀ x ∈ codeRange 0x129770 bytes_l129770, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29770 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12979c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x12979c (fun s => s.RIP = 0x12979c) (fun _ => nopEffect 0x12979c 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1297a0, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l12979c : List UInt8 :=
  [0x0F, 0x1F, 0x40, 0x00]

theorem code_l12979c : ∀ x ∈ codeRange 0x12979c bytes_l12979c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2979c 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297a0 (leaR64Effect 0x1297a0 8 (.base 7 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 54) (.exec 0x1297a0 (fun s => s.RIP = 0x1297a0) (leaR64Effect 0x1297a0 8 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1297a4 (andR64Imm8Effect 0x1297a4 8 0xf8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x1297a4 (fun s => s.RIP = 0x1297a4) (andR64Imm8Effect 0x1297a4 8 0xf8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 57) (.out 0x1297a8 (movR64R64Effect 0x1297a8 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x1297a8 (fun s => s.RIP = 0x1297a8) (movR64R64Effect 0x1297a8 0 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x1297ab (subR64R64Effect 0x1297ab 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[57, 7]
    (.letOp (n := 60) (.exec 0x1297ab (fun s => s.RIP = 0x1297ab) (subR64R64Effect 0x1297ab 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 61) (.out 0x1297ae (movR64R64Effect 0x1297ae 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 62) (.exec 0x1297ae (fun s => s.RIP = 0x1297ae) (movR64R64Effect 0x1297ae 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1297b1 (subR64R64Effect 0x1297b1 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[61, 59]
    (.letOp (n := 64) (.out 0x1297b1 (subR64R64Effect 0x1297b1 2 0) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 0] []) (.flag .CF)) #v[61, 59]
    (.letOp (n := 65) (.exec 0x1297b1 (fun s => s.RIP = 0x1297b1) (subR64R64Effect 0x1297b1 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[61, 59]
    (.letOp (n := 66) (.pure (condOp 3)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l1297cf, RegMap.args [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l1297b6, RegMap.args [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1297a0 : List UInt8 :=
  [0x4C, 0x8D, 0x47, 0x07, 0x49, 0x83, 0xE0, 0xF8, 0x4C, 0x89, 0xC0, 0x48, 0x29, 0xF8, 0x48, 0x89,
    0xF2, 0x48, 0x29, 0xC2, 0x73, 0x19]

theorem code_l1297a0 : ∀ x ∈ codeRange 0x1297a0 bytes_l1297a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297a0 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297b6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297b6 (testR64R64Effect 0x1297b6 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 54) (.exec 0x1297b6 (fun s => s.RIP = 0x1297b6) (testR64R64Effect 0x1297b6 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129815, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1297bb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1297b6 : List UInt8 :=
  [0x48, 0x85, 0xF6, 0x74, 0x5A]

theorem code_l1297b6 : ∀ x ∈ codeRange 0x1297b6 bytes_l1297b6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297b6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297bb (movR32R32Effect 0x1297bb 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x1297bb (fun s => s.RIP = 0x1297bb) (movR32R32Effect 0x1297bb 2 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1297bd (andR32Imm8Effect 0x1297bd 3 1 0x3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x1297bd (fun s => s.RIP = 0x1297bd) (andR32Imm8Effect 0x1297bd 3 1 0x3) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1297c0 (cmpR64Imm8Effect 0x1297c0 6 0x4) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 58) (.exec 0x1297c0 (fun s => s.RIP = 0x1297c0) (cmpR64Imm8Effect 0x1297c0 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l129818, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1297c6, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1297bb : List UInt8 :=
  [0x89, 0xF1, 0x83, 0xE1, 0x03, 0x48, 0x83, 0xFE, 0x04, 0x73, 0x52]

theorem code_l1297bb : ∀ x ∈ codeRange 0x1297bb bytes_l1297bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297bb 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297c6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297c6 (xorR32R32Effect 0x1297c6 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1297c6 (fun s => s.RIP = 0x1297c6) (xorR32R32Effect 0x1297c6 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x1297c8 (xorR32R32Effect 0x1297c8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x1297c8 (fun s => s.RIP = 0x1297c8) (xorR32R32Effect 0x1297c8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l129865, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1297c6 : List UInt8 :=
  [0x31, 0xD2, 0x31, 0xC0, 0xE9, 0x96, 0x00, 0x00, 0x00]

theorem code_l1297c6 : ∀ x ∈ codeRange 0x1297c6 bytes_l1297c6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297c6 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297cf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297cf (movR64R64Effect 0x1297cf 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x1297cf (fun s => s.RIP = 0x1297cf) (movR64R64Effect 0x1297cf 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1297d2 (shrR64Effect 0x1297d2 4 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.out 0x1297d2 (shrR64Effect 0x1297d2 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x1297d2 (fun s => s.RIP = 0x1297d2) (shrR64Effect 0x1297d2 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1297b6, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1297d8, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1297cf : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x03, 0x74, 0xDE]

theorem code_l1297cf : ∀ x ∈ codeRange 0x1297cf bytes_l1297cf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297cf 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297d8 (pushR64Effect 0x1297d8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x1297d8 (PushPre 0x1297d8 2) (pushR64Effect 0x1297d8 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x1297da (pushR64Effect 0x1297da 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1297da (PushPre 0x1297da 2) (pushR64Effect 0x1297da 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1297dc (pushR64Effect 0x1297dc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x1297dc (PushPre 0x1297dc 2) (pushR64Effect 0x1297dc 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x1297de (pushR64Effect 0x1297de 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1297de (PushPre 0x1297de 2) (pushR64Effect 0x1297de 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1297e0 (pushR64Effect 0x1297e0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x1297e0 (PushPre 0x1297e0 1) (pushR64Effect 0x1297e0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x1297e1 (movR32R32Effect 0x1297e1 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 64) (.exec 0x1297e1 (fun s => s.RIP = 0x1297e1) (movR32R32Effect 0x1297e1 2 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 65) (.out 0x1297e3 (andR32Imm8Effect 0x1297e3 3 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 66) (.exec 0x1297e3 (fun s => s.RIP = 0x1297e3) (andR32Imm8Effect 0x1297e3 3 6 0x7) (Reg.operands [.gpr 6] [])) #v[63]
    (.letOp (n := 67) (.out 0x1297e6 (cmpR64R64Effect 0x1297e6 8 7) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 7] []) (.flag .ZF)) #v[8, 7]
    (.letOp (n := 68) (.exec 0x1297e6 (fun s => s.RIP = 0x1297e6) (cmpR64R64Effect 0x1297e6 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 7]
    (.letOp (n := 69) (.pure (condOp 5)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l1297f3, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1297eb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1297d8 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x89, 0xD6, 0x83, 0xE6, 0x07, 0x49, 0x39,
    0xF8, 0x75, 0x08]

theorem code_l1297d8 : ∀ x ∈ codeRange 0x1297d8 bytes_l1297d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297d8 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297eb (xorR32R32Effect 0x1297eb 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x1297eb (fun s => s.RIP = 0x1297eb) (xorR32R32Effect 0x1297eb 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l129915, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1297eb : List UInt8 :=
  [0x45, 0x31, 0xC0, 0xE9, 0x22, 0x01, 0x00, 0x00]

theorem code_l1297eb : ∀ x ∈ codeRange 0x1297eb bytes_l1297eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297eb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1297f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1297f3 (movR32R32Effect 0x1297f3 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 54) (.exec 0x1297f3 (fun s => s.RIP = 0x1297f3) (movR32R32Effect 0x1297f3 3 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1297f6 (andR32Imm8Effect 0x1297f6 4 9 0x3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x1297f6 (fun s => s.RIP = 0x1297f6) (andR32Imm8Effect 0x1297f6 4 9 0x3) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 57) (.out 0x1297fa (movR64R64Effect 0x1297fa 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 58) (.exec 0x1297fa (fun s => s.RIP = 0x1297fa) (movR64R64Effect 0x1297fa 10 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x1297fd (subR64R64Effect 0x1297fd 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[57, 8]
    (.letOp (n := 60) (.exec 0x1297fd (fun s => s.RIP = 0x1297fd) (subR64R64Effect 0x1297fd 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[57, 8]
    (.letOp (n := 61) (.out 0x129800 (cmpR64Imm8Effect 0x129800 10 0xfc) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x129800 (cmpR64Imm8Effect 0x129800 10 0xfc) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x129800 (fun s => s.RIP = 0x129800) (cmpR64Imm8Effect 0x129800 10 0xfc) (Reg.operands [.gpr 10] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l129886, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l12980a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l1297f3 : List UInt8 :=
  [0x41, 0x89, 0xC1, 0x41, 0x83, 0xE1, 0x03, 0x49, 0x89, 0xFA, 0x4D, 0x29, 0xC2, 0x49, 0x83, 0xFA,
    0xFC, 0x0F, 0x86, 0x7C, 0x00, 0x00, 0x00]

theorem code_l1297f3 : ∀ x ∈ codeRange 0x1297f3 bytes_l1297f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x297f3 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12980a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12980a (xorR32R32Effect 0x12980a 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 54) (.exec 0x12980a (fun s => s.RIP = 0x12980a) (xorR32R32Effect 0x12980a 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 55) (.out 0x12980d (xorR32R32Effect 0x12980d 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x12980d (fun s => s.RIP = 0x12980d) (xorR32R32Effect 0x12980d 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l1298eb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l12980a : List UInt8 :=
  [0x45, 0x31, 0xD2, 0x45, 0x31, 0xC0, 0xE9, 0xD6, 0x00, 0x00, 0x00]

theorem code_l12980a : ∀ x ∈ codeRange 0x12980a bytes_l12980a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2980a 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129815 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129815 (xorR32R32Effect 0x129815 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x129815 (fun s => s.RIP = 0x129815) (xorR32R32Effect 0x129815 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x129817 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 56) (.out 0x129817 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x129817 (RetPre 0x129817) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l129815 : List UInt8 :=
  [0x31, 0xC0, 0xC3]

theorem code_l129815 : ∀ x ∈ codeRange 0x129815 bytes_l129815, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29815 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129818 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129818 (andR64Imm8Effect 0x129818 6 0xfc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x129818 (fun s => s.RIP = 0x129818) (andR64Imm8Effect 0x129818 6 0xfc) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12981c (xorR32R32Effect 0x12981c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x12981c (fun s => s.RIP = 0x12981c) (xorR32R32Effect 0x12981c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x12981e (xorR32R32Effect 0x12981e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 58) (.exec 0x12981e (fun s => s.RIP = 0x12981e) (xorR32R32Effect 0x12981e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l129820, RegMap.args [(0, 57), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l129818 : List UInt8 :=
  [0x48, 0x83, 0xE6, 0xFC, 0x31, 0xD2, 0x31, 0xC0]

theorem code_l129818 : ∀ x ∈ codeRange 0x129818 bytes_l129818, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29818 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129820 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129820 (xorR32R32Effect 0x129820 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x129820 (fun s => s.RIP = 0x129820) (xorR32R32Effect 0x129820 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.out 0x129823 (cmpM8Imm8Effect 0x129823 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x129823 (cmpM8Imm8Effect 0x129823 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x129823 (LoadPre 0x129823 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129823 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129823 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129827 (atFlags (condHolds 13) (setccR8Effect 0x129827 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129827 (fun s => s.RIP = 0x129827) (atFlags (condHolds 13) (setccR8Effect 0x129827 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12982b (addR64R64Effect 0x12982b 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[58, 0]
    (.letOp (n := 61) (.exec 0x12982b (fun s => s.RIP = 0x12982b) (addR64R64Effect 0x12982b 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 62) (.out 0x12982e (xorR32R32Effect 0x12982e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 63) (.exec 0x12982e (fun s => s.RIP = 0x12982e) (xorR32R32Effect 0x12982e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 64) (.out 0x129830 (cmpM8Imm8Effect 0x129830 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 65) (.out 0x129830 (cmpM8Imm8Effect 0x129830 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 66) (.exec 0x129830 (LoadPre 0x129830 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x129830 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129830 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 67) (.out 0x129835 (atFlags (condHolds 13) (setccR8Effect 0x129835 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x129835 (fun s => s.RIP = 0x129835) (atFlags (condHolds 13) (setccR8Effect 0x129835 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x129838 (xorR32R32Effect 0x129838 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 70) (.exec 0x129838 (fun s => s.RIP = 0x129838) (xorR32R32Effect 0x129838 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 71) (.out 0x12983b (cmpM8Imm8Effect 0x12983b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 72) (.out 0x12983b (cmpM8Imm8Effect 0x12983b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 73) (.exec 0x12983b (LoadPre 0x12983b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x12983b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12983b 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 74) (.out 0x129840 (atFlags (condHolds 13) (setccR8Effect 0x129840 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x129840 (fun s => s.RIP = 0x129840) (atFlags (condHolds 13) (setccR8Effect 0x129840 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x129844 (addR64R64Effect 0x129844 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x129844 (fun s => s.RIP = 0x129844) (addR64R64Effect 0x129844 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x129847 (addR64R64Effect 0x129847 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x129847 (fun s => s.RIP = 0x129847) (addR64R64Effect 0x129847 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x12984a (xorR32R32Effect 0x12984a 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x12984a (fun s => s.RIP = 0x12984a) (xorR32R32Effect 0x12984a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x12984c (cmpM8Imm8Effect 0x12984c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 83) (.out 0x12984c (cmpM8Imm8Effect 0x12984c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 84) (.exec 0x12984c (LoadPre 0x12984c (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x12984c + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12984c 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 85) (.out 0x129851 (atFlags (condHolds 13) (setccR8Effect 0x129851 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x129851 (fun s => s.RIP = 0x129851) (atFlags (condHolds 13) (setccR8Effect 0x129851 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x129854 (addR64R64Effect 0x129854 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x129854 (fun s => s.RIP = 0x129854) (addR64R64Effect 0x129854 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x129857 (addR64Imm8Effect 0x129857 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 90) (.exec 0x129857 (fun s => s.RIP = 0x129857) (addR64Imm8Effect 0x129857 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 91) (.out 0x12985b (cmpR64R64Effect 0x12985b 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 89]
    (.letOp (n := 92) (.exec 0x12985b (fun s => s.RIP = 0x12985b) (cmpR64R64Effect 0x12985b 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l129820, RegMap.args [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l129860, RegMap.args [(0, 87), (1, 1), (2, 89), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 78), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l129820 : List UInt8 :=
  [0x45, 0x31, 0xC0, 0x80, 0x3C, 0x17, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x49, 0x01, 0xC0, 0x31, 0xC0,
    0x80, 0x7C, 0x17, 0x01, 0xC0, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x02, 0xC0,
    0x41, 0x0F, 0x9D, 0xC1, 0x49, 0x01, 0xC1, 0x4D, 0x01, 0xC1, 0x31, 0xC0, 0x80, 0x7C, 0x17, 0x03,
    0xC0, 0x0F, 0x9D, 0xC0, 0x4C, 0x01, 0xC8, 0x48, 0x83, 0xC2, 0x04, 0x48, 0x39, 0xD6, 0x75, 0xC0]

theorem code_l129820 : ∀ x ∈ codeRange 0x129820 bytes_l129820, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29820 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129860 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129860 (testR64R64Effect 0x129860 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x129860 (fun s => s.RIP = 0x129860) (testR64R64Effect 0x129860 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129885, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l129865, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129860 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x74, 0x20]

theorem code_l129860 : ∀ x ∈ codeRange 0x129860 bytes_l129860, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29860 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129865 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129865 (addR64R64Effect 0x129865 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x129865 (fun s => s.RIP = 0x129865) (addR64R64Effect 0x129865 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.out 0x129868 (xorR32R32Effect 0x129868 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x129868 (fun s => s.RIP = 0x129868) (xorR32R32Effect 0x129868 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.exec 0x12986a (fun s => s.RIP = 0x12986a) (fun _ => nopEffect 0x12986a 6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129870, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l129865 : List UInt8 :=
  [0x48, 0x01, 0xD7, 0x31, 0xD2, 0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l129865 : ∀ x ∈ codeRange 0x129865 bytes_l129865, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29865 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129870 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129870 (xorR32R32Effect 0x129870 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x129870 (fun s => s.RIP = 0x129870) (xorR32R32Effect 0x129870 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x129872 (cmpM8Imm8Effect 0x129872 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x129872 (cmpM8Imm8Effect 0x129872 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x129872 (LoadPre 0x129872 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129872 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129872 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129876 (atFlags (condHolds 13) (setccR8Effect 0x129876 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129876 (fun s => s.RIP = 0x129876) (atFlags (condHolds 13) (setccR8Effect 0x129876 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12987a (addR64R64Effect 0x12987a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x12987a (fun s => s.RIP = 0x12987a) (addR64R64Effect 0x12987a 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x12987d (incR64Effect 0x12987d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 63) (.exec 0x12987d (fun s => s.RIP = 0x12987d) (incR64Effect 0x12987d 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 64) (.out 0x129880 (cmpR64R64Effect 0x129880 1 2) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 2] []) (.flag .ZF)) #v[1, 62]
    (.letOp (n := 65) (.exec 0x129880 (fun s => s.RIP = 0x129880) (cmpR64R64Effect 0x129880 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l129870, RegMap.args [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l129885, RegMap.args [(0, 60), (1, 1), (2, 62), (3, 3), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l129870 : List UInt8 :=
  [0x31, 0xF6, 0x80, 0x3C, 0x17, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x48, 0x01, 0xF0, 0x48, 0xFF, 0xC2,
    0x48, 0x39, 0xD1, 0x75, 0xEB]

theorem code_l129870 : ∀ x ∈ codeRange 0x129870 bytes_l129870, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29870 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129885 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129885 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x129885 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x129885 (RetPre 0x129885) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l129885 : List UInt8 :=
  [0xC3]

theorem code_l129885 : ∀ x ∈ codeRange 0x129885 bytes_l129885, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29885 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129886 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129886 (movR32R32Effect 0x129886 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[0]
    (.letOp (n := 54) (.exec 0x129886 (fun s => s.RIP = 0x129886) (movR32R32Effect 0x129886 3 11 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x129889 (andR32Imm8Effect 0x129889 4 11 0x4) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 56) (.exec 0x129889 (fun s => s.RIP = 0x129889) (andR32Imm8Effect 0x129889 4 11 0x4) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 57) (.out 0x12988d (xorR32R32Effect 0x12988d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 58) (.exec 0x12988d (fun s => s.RIP = 0x12988d) (xorR32R32Effect 0x12988d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 59) (.out 0x129890 (xorR32R32Effect 0x129890 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 60) (.exec 0x129890 (fun s => s.RIP = 0x129890) (xorR32R32Effect 0x129890 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 61) (.exec 0x129893 (fun s => s.RIP = 0x129893) (fun _ => nopEffect 0x129893 13) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1298a0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 59), (9, 9), (10, 57), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l129886 : List UInt8 :=
  [0x41, 0x89, 0xC3, 0x41, 0x83, 0xE3, 0x04, 0x45, 0x31, 0xD2, 0x45, 0x31, 0xC0, 0x66, 0x66, 0x66,
    0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l129886 : ∀ x ∈ codeRange 0x129886 bytes_l129886, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29886 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1298a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1298a0 (xorR32R32Effect 0x1298a0 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 54) (.exec 0x1298a0 (fun s => s.RIP = 0x1298a0) (xorR32R32Effect 0x1298a0 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.out 0x1298a2 (cmpM8Imm8Effect 0x1298a2 5 (.sib 7 (some 10) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 56) (.out 0x1298a2 (cmpM8Imm8Effect 0x1298a2 5 (.sib 7 (some 10) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 57) (.exec 0x1298a2 (LoadPre 0x1298a2 (fun s => AddrMode.addr (.sib 7 (some 10) 0 .none) s (0x1298a2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1298a2 5 (.sib 7 (some 10) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 58) (.out 0x1298a7 (atFlags (condHolds 13) (setccR8Effect 0x1298a7 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 3))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x1298a7 (fun s => s.RIP = 0x1298a7) (atFlags (condHolds 13) (setccR8Effect 0x1298a7 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x1298aa (addR64R64Effect 0x1298aa 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[58, 8]
    (.letOp (n := 61) (.exec 0x1298aa (fun s => s.RIP = 0x1298aa) (addR64R64Effect 0x1298aa 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[58, 8]
    (.letOp (n := 62) (.out 0x1298ad (xorR32R32Effect 0x1298ad 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 63) (.exec 0x1298ad (fun s => s.RIP = 0x1298ad) (xorR32R32Effect 0x1298ad 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 64) (.out 0x1298b0 (cmpM8Imm8Effect 0x1298b0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 65) (.out 0x1298b0 (cmpM8Imm8Effect 0x1298b0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 66) (.exec 0x1298b0 (LoadPre 0x1298b0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x1)) s (0x1298b0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298b0 6 (.sib 7 (some 10) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 67) (.out 0x1298b6 (atFlags (condHolds 13) (setccR8Effect 0x1298b6 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x1298b6 (fun s => s.RIP = 0x1298b6) (atFlags (condHolds 13) (setccR8Effect 0x1298b6 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x1298ba (xorR32R32Effect 0x1298ba 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 70) (.exec 0x1298ba (fun s => s.RIP = 0x1298ba) (xorR32R32Effect 0x1298ba 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 71) (.out 0x1298bd (cmpM8Imm8Effect 0x1298bd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 72) (.out 0x1298bd (cmpM8Imm8Effect 0x1298bd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 73) (.exec 0x1298bd (LoadPre 0x1298bd (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x2)) s (0x1298bd + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298bd 6 (.sib 7 (some 10) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 74) (.out 0x1298c3 (atFlags (condHolds 13) (setccR8Effect 0x1298c3 4 14)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 14))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x1298c3 (fun s => s.RIP = 0x1298c3) (atFlags (condHolds 13) (setccR8Effect 0x1298c3 4 14)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x1298c7 (addR64R64Effect 0x1298c7 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x1298c7 (fun s => s.RIP = 0x1298c7) (addR64R64Effect 0x1298c7 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x1298ca (addR64R64Effect 0x1298ca 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x1298ca (fun s => s.RIP = 0x1298ca) (addR64R64Effect 0x1298ca 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x1298cd (xorR32R32Effect 0x1298cd 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x1298cd (fun s => s.RIP = 0x1298cd) (xorR32R32Effect 0x1298cd 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x1298d0 (cmpM8Imm8Effect 0x1298d0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 10] []) (.flag .SF)) #v[7, 10]
    (.letOp (n := 83) (.out 0x1298d0 (cmpM8Imm8Effect 0x1298d0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 10] []) (.flag .OF)) #v[7, 10]
    (.letOp (n := 84) (.exec 0x1298d0 (LoadPre 0x1298d0 (fun s => AddrMode.addr (.sib 7 (some 10) 0 (.d8 0x3)) s (0x1298d0 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x1298d0 6 (.sib 7 (some 10) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 10] [])) #v[7, 10]
    (.letOp (n := 85) (.out 0x1298d6 (atFlags (condHolds 13) (setccR8Effect 0x1298d6 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x1298d6 (fun s => s.RIP = 0x1298d6) (atFlags (condHolds 13) (setccR8Effect 0x1298d6 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x1298da (addR64R64Effect 0x1298da 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x1298da (fun s => s.RIP = 0x1298da) (addR64R64Effect 0x1298da 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x1298dd (addR64Imm8Effect 0x1298dd 10 0x4) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 90) (.exec 0x1298dd (fun s => s.RIP = 0x1298dd) (addR64Imm8Effect 0x1298dd 10 0x4) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 91) (.out 0x1298e1 (cmpR64R64Effect 0x1298e1 11 10) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 10] []) (.flag .ZF)) #v[11, 89]
    (.letOp (n := 92) (.exec 0x1298e1 (fun s => s.RIP = 0x1298e1) (cmpR64R64Effect 0x1298e1 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[11, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l1298a0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l1298e6, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 60), (4, 4), (5, 5), (6, 6), (7, 7), (8, 87), (9, 9), (10, 89), (11, 11), (14, 78), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l1298a0 : List UInt8 :=
  [0x31, 0xDB, 0x42, 0x80, 0x3C, 0x17, 0xC0, 0x0F, 0x9D, 0xC3, 0x4C, 0x01, 0xC3, 0x45, 0x31, 0xC0,
    0x42, 0x80, 0x7C, 0x17, 0x01, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xF6, 0x42, 0x80, 0x7C,
    0x17, 0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC6, 0x4D, 0x01, 0xC6, 0x49, 0x01, 0xDE, 0x45, 0x31, 0xC0,
    0x42, 0x80, 0x7C, 0x17, 0x03, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x4D, 0x01, 0xF0, 0x49, 0x83, 0xC2,
    0x04, 0x4D, 0x39, 0xD3, 0x75, 0xBA]

theorem code_l1298a0 : ∀ x ∈ codeRange 0x1298a0 bytes_l1298a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x298a0 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1298e6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1298e6 (testR64R64Effect 0x1298e6 9 9) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 9] []) (.flag .ZF)) #v[9, 9]
    (.letOp (n := 54) (.exec 0x1298e6 (fun s => s.RIP = 0x1298e6) (testR64R64Effect 0x1298e6 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129915, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1298eb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1298e6 : List UInt8 :=
  [0x4D, 0x85, 0xC9, 0x74, 0x2A]

theorem code_l1298e6 : ∀ x ∈ codeRange 0x1298e6 bytes_l1298e6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x298e6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1298eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1298eb (addR64R64Effect 0x1298eb 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[10, 7]
    (.letOp (n := 54) (.exec 0x1298eb (fun s => s.RIP = 0x1298eb) (addR64R64Effect 0x1298eb 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[10, 7]
    (.letOp (n := 55) (.out 0x1298ee (xorR32R32Effect 0x1298ee 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[11, 11]
    (.letOp (n := 56) (.exec 0x1298ee (fun s => s.RIP = 0x1298ee) (xorR32R32Effect 0x1298ee 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[11, 11]
    (.letOp (n := 57) (.exec 0x1298f1 (fun s => s.RIP = 0x1298f1) (fun _ => nopEffect 0x1298f1 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129900, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 55), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1298eb : List UInt8 :=
  [0x49, 0x01, 0xFA, 0x45, 0x31, 0xDB, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84,
    0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l1298eb : ∀ x ∈ codeRange 0x1298eb bytes_l1298eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x298eb 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129900 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129900 (xorR32R32Effect 0x129900 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 54) (.exec 0x129900 (fun s => s.RIP = 0x129900) (xorR32R32Effect 0x129900 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 55) (.out 0x129902 (cmpM8Imm8Effect 0x129902 5 (.sib 10 (some 11) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 10, .gpr 11] []) (.flag .SF)) #v[10, 11]
    (.letOp (n := 56) (.out 0x129902 (cmpM8Imm8Effect 0x129902 5 (.sib 10 (some 11) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 10, .gpr 11] []) (.flag .OF)) #v[10, 11]
    (.letOp (n := 57) (.exec 0x129902 (LoadPre 0x129902 (fun s => AddrMode.addr (.sib 10 (some 11) 0 .none) s (0x129902 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129902 5 (.sib 10 (some 11) 0 .none) 0xc0) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 11]
    (.letOp (n := 58) (.out 0x129907 (atFlags (condHolds 13) (setccR8Effect 0x129907 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 3))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129907 (fun s => s.RIP = 0x129907) (atFlags (condHolds 13) (setccR8Effect 0x129907 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12990a (addR64R64Effect 0x12990a 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[8, 58]
    (.letOp (n := 61) (.exec 0x12990a (fun s => s.RIP = 0x12990a) (addR64R64Effect 0x12990a 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[8, 58]
    (.letOp (n := 62) (.out 0x12990d (incR64Effect 0x12990d 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 63) (.exec 0x12990d (fun s => s.RIP = 0x12990d) (incR64Effect 0x12990d 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[11]
    (.letOp (n := 64) (.out 0x129910 (cmpR64R64Effect 0x129910 9 11) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 11] []) (.flag .ZF)) #v[9, 62]
    (.letOp (n := 65) (.exec 0x129910 (fun s => s.RIP = 0x129910) (cmpR64R64Effect 0x129910 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[9, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l129900, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l129915, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 58), (4, 4), (5, 5), (6, 6), (7, 7), (8, 60), (9, 9), (10, 10), (11, 62), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l129900 : List UInt8 :=
  [0x31, 0xDB, 0x43, 0x80, 0x3C, 0x1A, 0xC0, 0x0F, 0x9D, 0xC3, 0x49, 0x01, 0xD8, 0x49, 0xFF, 0xC3,
    0x4D, 0x39, 0xD9, 0x75, 0xEB]

theorem code_l129900 : ∀ x ∈ codeRange 0x129900 bytes_l129900, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29900 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129915 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129915 (addR64R64Effect 0x129915 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[7, 0]
    (.letOp (n := 54) (.exec 0x129915 (fun s => s.RIP = 0x129915) (addR64R64Effect 0x129915 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 0]
    (.letOp (n := 55) (.out 0x129918 (testR64R64Effect 0x129918 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 56) (.exec 0x129918 (fun s => s.RIP = 0x129918) (testR64R64Effect 0x129918 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1299b0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l129921, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l129915 : List UInt8 :=
  [0x48, 0x01, 0xC7, 0x48, 0x85, 0xF6, 0x0F, 0x84, 0x8F, 0x00, 0x00, 0x00]

theorem code_l129915 : ∀ x ∈ codeRange 0x129915 bytes_l129915, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29915 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129921 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129921 (movR64Imm64Effect 0x129921 0 0x7ffffffffffffff8) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x129921 (fun s => s.RIP = 0x129921) (movR64Imm64Effect 0x129921 0 0x7ffffffffffffff8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12992b (andR64R64Effect 0x12992b 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x12992b (fun s => s.RIP = 0x12992b) (andR64R64Effect 0x12992b 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x12992e (xorR32R32Effect 0x12992e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 58) (.exec 0x12992e (fun s => s.RIP = 0x12992e) (xorR32R32Effect 0x12992e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 59) (.out 0x129930 (cmpM8Imm8Effect 0x129930 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 55]
    (.letOp (n := 60) (.out 0x129930 (cmpM8Imm8Effect 0x129930 4 (.sib 7 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 55]
    (.letOp (n := 61) (.exec 0x129930 (LoadPre 0x129930 (fun s => AddrMode.addr (.sib 7 (some 2) 0 .none) s (0x129930 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x129930 4 (.sib 7 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 55]
    (.letOp (n := 62) (.out 0x129934 (atFlags (condHolds 13) (setccR8Effect 0x129934 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[57, 59, 60]
    (.letOp (n := 63) (.exec 0x129934 (fun s => s.RIP = 0x129934) (atFlags (condHolds 13) (setccR8Effect 0x129934 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[57, 59, 60]
    (.letOp (n := 64) (.out 0x129937 (cmpR32Imm8Effect 0x129937 3 6 0x1) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 65) (.exec 0x129937 (fun s => s.RIP = 0x129937) (cmpR32Imm8Effect 0x129937 3 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 66) (.pure (condOp 4)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l1299b2, RegMap.args [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l12993c, RegMap.args [(0, 62), (1, 1), (2, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l129921 : List UInt8 :=
  [0x48, 0xB8, 0xF8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x21, 0xC2, 0x31, 0xC0, 0x80,
    0x3C, 0x17, 0xC0, 0x0F, 0x9D, 0xC0, 0x83, 0xFE, 0x01, 0x74, 0x76]

theorem code_l129921 : ∀ x ∈ codeRange 0x129921 bytes_l129921, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29921 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12993c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12993c (xorR32R32Effect 0x12993c 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x12993c (fun s => s.RIP = 0x12993c) (xorR32R32Effect 0x12993c 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x12993f (cmpM8Imm8Effect 0x12993f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x12993f (cmpM8Imm8Effect 0x12993f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x12993f (LoadPre 0x12993f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x1)) s (0x12993f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12993f 5 (.sib 7 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129944 (atFlags (condHolds 13) (setccR8Effect 0x129944 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129944 (fun s => s.RIP = 0x129944) (atFlags (condHolds 13) (setccR8Effect 0x129944 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x129948 (addR64R64Effect 0x129948 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x129948 (fun s => s.RIP = 0x129948) (addR64R64Effect 0x129948 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x12994b (cmpR32Imm8Effect 0x12994b 3 6 0x2) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x12994b (fun s => s.RIP = 0x12994b) (cmpR32Imm8Effect 0x12994b 3 6 0x2) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l129950, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12993c : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x01, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x02, 0x74, 0x62]

theorem code_l12993c : ∀ x ∈ codeRange 0x12993c bytes_l12993c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2993c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129950 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129950 (xorR32R32Effect 0x129950 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x129950 (fun s => s.RIP = 0x129950) (xorR32R32Effect 0x129950 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x129953 (cmpM8Imm8Effect 0x129953 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x129953 (cmpM8Imm8Effect 0x129953 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x129953 (LoadPre 0x129953 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x2)) s (0x129953 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129953 5 (.sib 7 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129958 (atFlags (condHolds 13) (setccR8Effect 0x129958 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129958 (fun s => s.RIP = 0x129958) (atFlags (condHolds 13) (setccR8Effect 0x129958 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x12995c (addR64R64Effect 0x12995c 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x12995c (fun s => s.RIP = 0x12995c) (addR64R64Effect 0x12995c 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x12995f (cmpR32Imm8Effect 0x12995f 3 6 0x3) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x12995f (fun s => s.RIP = 0x12995f) (cmpR32Imm8Effect 0x12995f 3 6 0x3) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l129964, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l129950 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x03, 0x74, 0x4E]

theorem code_l129950 : ∀ x ∈ codeRange 0x129950 bytes_l129950, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29950 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129964 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129964 (xorR32R32Effect 0x129964 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x129964 (fun s => s.RIP = 0x129964) (xorR32R32Effect 0x129964 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x129967 (cmpM8Imm8Effect 0x129967 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x129967 (cmpM8Imm8Effect 0x129967 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x129967 (LoadPre 0x129967 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x3)) s (0x129967 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x129967 5 (.sib 7 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x12996c (atFlags (condHolds 13) (setccR8Effect 0x12996c 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x12996c (fun s => s.RIP = 0x12996c) (atFlags (condHolds 13) (setccR8Effect 0x12996c 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x129970 (addR64R64Effect 0x129970 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x129970 (fun s => s.RIP = 0x129970) (addR64R64Effect 0x129970 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x129973 (cmpR32Imm8Effect 0x129973 3 6 0x4) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x129973 (fun s => s.RIP = 0x129973) (cmpR32Imm8Effect 0x129973 3 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l129978, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l129964 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x03, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x04, 0x74, 0x3A]

theorem code_l129964 : ∀ x ∈ codeRange 0x129964 bytes_l129964, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29964 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129978 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129978 (xorR32R32Effect 0x129978 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x129978 (fun s => s.RIP = 0x129978) (xorR32R32Effect 0x129978 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x12997b (cmpM8Imm8Effect 0x12997b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x12997b (cmpM8Imm8Effect 0x12997b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x12997b (LoadPre 0x12997b (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x4)) s (0x12997b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12997b 5 (.sib 7 (some 2) 0 (.d8 0x4)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129980 (atFlags (condHolds 13) (setccR8Effect 0x129980 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129980 (fun s => s.RIP = 0x129980) (atFlags (condHolds 13) (setccR8Effect 0x129980 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x129984 (addR64R64Effect 0x129984 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x129984 (fun s => s.RIP = 0x129984) (addR64R64Effect 0x129984 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x129987 (cmpR32Imm8Effect 0x129987 3 6 0x5) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x129987 (fun s => s.RIP = 0x129987) (cmpR32Imm8Effect 0x129987 3 6 0x5) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l12998c, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l129978 : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x04, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x05, 0x74, 0x26]

theorem code_l129978 : ∀ x ∈ codeRange 0x129978 bytes_l129978, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29978 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12998c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12998c (xorR32R32Effect 0x12998c 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 54) (.exec 0x12998c (fun s => s.RIP = 0x12998c) (xorR32R32Effect 0x12998c 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 55) (.out 0x12998f (cmpM8Imm8Effect 0x12998f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x12998f (cmpM8Imm8Effect 0x12998f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x12998f (LoadPre 0x12998f (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x5)) s (0x12998f + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x12998f 5 (.sib 7 (some 2) 0 (.d8 0x5)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x129994 (atFlags (condHolds 13) (setccR8Effect 0x129994 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 9))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x129994 (fun s => s.RIP = 0x129994) (atFlags (condHolds 13) (setccR8Effect 0x129994 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x129998 (addR64R64Effect 0x129998 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x129998 (fun s => s.RIP = 0x129998) (addR64R64Effect 0x129998 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x12999b (cmpR32Imm8Effect 0x12999b 3 6 0x6) (EffectPart.reads (.flag .ZF) [.gpr 6] []) (.flag .ZF)) #v[6]
    (.letOp (n := 63) (.exec 0x12999b (fun s => s.RIP = 0x12999b) (cmpR32Imm8Effect 0x12999b 3 6 0x6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.pure (condOp 4)) #v[62]
    (.terminate (.condBr (Fin.last 64) ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l1299a0, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 58), (10, 10), (11, 11), (14, 14), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l12998c : List UInt8 :=
  [0x45, 0x31, 0xC9, 0x80, 0x7C, 0x17, 0x05, 0xC0, 0x41, 0x0F, 0x9D, 0xC1, 0x4C, 0x01, 0xC8, 0x83,
    0xFE, 0x06, 0x74, 0x12]

theorem code_l12998c : ∀ x ∈ codeRange 0x12998c bytes_l12998c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2998c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1299a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1299a0 (xorR32R32Effect 0x1299a0 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x1299a0 (fun s => s.RIP = 0x1299a0) (xorR32R32Effect 0x1299a0 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x1299a2 (cmpM8Imm8Effect 0x1299a2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 7, .gpr 2] []) (.flag .SF)) #v[7, 2]
    (.letOp (n := 56) (.out 0x1299a2 (cmpM8Imm8Effect 0x1299a2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 7, .gpr 2] []) (.flag .OF)) #v[7, 2]
    (.letOp (n := 57) (.exec 0x1299a2 (LoadPre 0x1299a2 (fun s => AddrMode.addr (.sib 7 (some 2) 0 (.d8 0x6)) s (0x1299a2 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1299a2 5 (.sib 7 (some 2) 0 (.d8 0x6)) 0xc0) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 58) (.out 0x1299a7 (atFlags (condHolds 13) (setccR8Effect 0x1299a7 4 6)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 6))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x1299a7 (fun s => s.RIP = 0x1299a7) (atFlags (condHolds 13) (setccR8Effect 0x1299a7 4 6)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x1299ab (addR64R64Effect 0x1299ab 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x1299ab (fun s => s.RIP = 0x1299ab) (addR64R64Effect 0x1299ab 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 58]
    (.terminate (.br ⟨.l1299b2, RegMap.args [(0, 60), (1, 1), (2, 2), (4, 4), (5, 5), (6, 58), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1299a0 : List UInt8 :=
  [0x31, 0xF6, 0x80, 0x7C, 0x17, 0x06, 0xC0, 0x40, 0x0F, 0x9D, 0xC6, 0x48, 0x01, 0xF0, 0xEB, 0x02]

theorem code_l1299a0 : ∀ x ∈ codeRange 0x1299a0 bytes_l1299a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x299a0 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1299b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1299b0 (xorR32R32Effect 0x1299b0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1299b0 (fun s => s.RIP = 0x1299b0) (xorR32R32Effect 0x1299b0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1299b2, RegMap.args [(0, 53), (1, 1), (4, 4), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1299b0 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l1299b0 : ∀ x ∈ codeRange 0x1299b0 bytes_l1299b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x299b0 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1299b2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1299b2 (addR64R64Effect 0x1299b2 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[0, 8]
    (.letOp (n := 54) (.exec 0x1299b2 (fun s => s.RIP = 0x1299b2) (addR64R64Effect 0x1299b2 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[0, 8]
    (.letOp (n := 55) (.out 0x1299b5 (movR64Imm64Effect 0x1299b5 8 0x101010101010101) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x1299b5 (fun s => s.RIP = 0x1299b5) (movR64Imm64Effect 0x1299b5 8 0x101010101010101) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1299bf (movR64Imm64Effect 0x1299bf 6 0xff00ff00ff00ff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x1299bf (fun s => s.RIP = 0x1299bf) (movR64Imm64Effect 0x1299bf 6 0xff00ff00ff00ff) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1299c9 (movR64Imm64Effect 0x1299c9 2 0x1000100010001) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x1299c9 (fun s => s.RIP = 0x1299c9) (movR64Imm64Effect 0x1299c9 2 0x1000100010001) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129a14, RegMap.args [(0, 53), (1, 1), (2, 59), (4, 4), (5, 5), (6, 57), (7, 7), (8, 55), (9, 9), (10, 10), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l1299b2 : List UInt8 :=
  [0x4C, 0x01, 0xC0, 0x49, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0xBE, 0xFF,
    0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0x48, 0xBA, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01,
    0x00, 0xEB, 0x3F]

theorem code_l1299b2 : ∀ x ∈ codeRange 0x1299b2 bytes_l1299b2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x299b2 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1299e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1299e0 (xorR32R32Effect 0x1299e0 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x1299e0 (fun s => s.RIP = 0x1299e0) (xorR32R32Effect 0x1299e0 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.terminate (.br ⟨.l1299e3, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1299e0 : List UInt8 :=
  [0x45, 0x31, 0xF6]

theorem code_l1299e0 : ∀ x ∈ codeRange 0x1299e0 bytes_l1299e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x299e0 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1299e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1299e3 (addR64R64Effect 0x1299e3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[7, 9]
    (.letOp (n := 54) (.exec 0x1299e3 (fun s => s.RIP = 0x1299e3) (addR64R64Effect 0x1299e3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[7, 9]
    (.letOp (n := 55) (.out 0x1299e6 (subR64R64Effect 0x1299e6 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1, 10]
    (.letOp (n := 56) (.exec 0x1299e6 (fun s => s.RIP = 0x1299e6) (subR64R64Effect 0x1299e6 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1, 10]
    (.letOp (n := 57) (.out 0x1299e9 (movR32R32Effect 0x1299e9 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 58) (.exec 0x1299e9 (fun s => s.RIP = 0x1299e9) (movR32R32Effect 0x1299e9 3 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 59) (.out 0x1299ec (andR32Imm8Effect 0x1299ec 4 11 0x3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x1299ec (fun s => s.RIP = 0x1299ec) (andR32Imm8Effect 0x1299ec 4 11 0x3) (Reg.operands [.gpr 11] [])) #v[57]
    (.letOp (n := 61) (.out 0x1299f0 (movR64R64Effect 0x1299f0 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[14]
    (.letOp (n := 62) (.exec 0x1299f0 (fun s => s.RIP = 0x1299f0) (movR64R64Effect 0x1299f0 3 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x1299f3 (andR64R64Effect 0x1299f3 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[61, 6]
    (.letOp (n := 64) (.exec 0x1299f3 (fun s => s.RIP = 0x1299f3) (andR64R64Effect 0x1299f3 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[61, 6]
    (.letOp (n := 65) (.out 0x1299f6 (shrR64Effect 0x1299f6 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x1299f6 (fun s => s.RIP = 0x1299f6) (shrR64Effect 0x1299f6 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[14]
    (.letOp (n := 67) (.out 0x1299fa (andR64R64Effect 0x1299fa 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[65, 6]
    (.letOp (n := 68) (.exec 0x1299fa (fun s => s.RIP = 0x1299fa) (andR64R64Effect 0x1299fa 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[65, 6]
    (.letOp (n := 69) (.out 0x1299fd (addR64R64Effect 0x1299fd 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[67, 63]
    (.letOp (n := 70) (.exec 0x1299fd (fun s => s.RIP = 0x1299fd) (addR64R64Effect 0x1299fd 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[67, 63]
    (.letOp (n := 71) (.out 0x129a00 (imulR64R64Effect 0x129a00 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[69, 2]
    (.letOp (n := 72) (.exec 0x129a00 (fun s => s.RIP = 0x129a00) (imulR64R64Effect 0x129a00 4 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[69, 2]
    (.letOp (n := 73) (.out 0x129a04 (shrR64Effect 0x129a04 4 14 48) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.exec 0x129a04 (fun s => s.RIP = 0x129a04) (shrR64Effect 0x129a04 4 14 48) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.out 0x129a08 (addR64R64Effect 0x129a08 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[0, 73]
    (.letOp (n := 76) (.exec 0x129a08 (fun s => s.RIP = 0x129a08) (addR64R64Effect 0x129a08 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 73]
    (.letOp (n := 77) (.out 0x129a0b (testR64R64Effect 0x129a0b 11 11) (EffectPart.reads (.flag .ZF) [.gpr 11, .gpr 11] []) (.flag .ZF)) #v[59, 59]
    (.letOp (n := 78) (.exec 0x129a0b (fun s => s.RIP = 0x129a0b) (testR64R64Effect 0x129a0b 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[59, 59]
    (.letOp (n := 79) (.pure (condOp 5)) #v[77]
    (.terminate (.condBr (Fin.last 79) ⟨.l129ac9, RegMap.args [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ ⟨.l129a14, RegMap.args [(0, 75), (1, 55), (2, 2), (3, 63), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 59), (14, 73), (19, 77), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l1299e3 : List UInt8 :=
  [0x4C, 0x01, 0xCF, 0x4C, 0x29, 0xD1, 0x45, 0x89, 0xD3, 0x41, 0x83, 0xE3, 0x03, 0x4C, 0x89, 0xF3,
    0x48, 0x21, 0xF3, 0x49, 0xC1, 0xEE, 0x08, 0x49, 0x21, 0xF6, 0x49, 0x01, 0xDE, 0x4C, 0x0F, 0xAF,
    0xF2, 0x49, 0xC1, 0xEE, 0x30, 0x4C, 0x01, 0xF0, 0x4D, 0x85, 0xDB, 0x0F, 0x85, 0xB5, 0x00, 0x00,
    0x00]

theorem code_l1299e3 : ∀ x ∈ codeRange 0x1299e3 bytes_l1299e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x299e3 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129a14 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129a14 (testR64R64Effect 0x129a14 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x129a14 (fun s => s.RIP = 0x129a14) (testR64R64Effect 0x129a14 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129b4a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l129a1d, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129a14 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x0F, 0x84, 0x2D, 0x01, 0x00, 0x00]

theorem code_l129a14 : ∀ x ∈ codeRange 0x129a14 bytes_l129a14, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29a14 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129a1d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129a1d (movR64R64Effect 0x129a1d 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 54) (.exec 0x129a1d (fun s => s.RIP = 0x129a1d) (movR64R64Effect 0x129a1d 9 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x129a20 (cmpR64Imm32Effect 0x129a20 1 0xc0) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 56) (.exec 0x129a20 (fun s => s.RIP = 0x129a20) (cmpR64Imm32Effect 0x129a20 1 0xc0) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x129a27 (movR32Imm32Effect 0x129a27 6 10 0xc0) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 58) (.exec 0x129a27 (fun s => s.RIP = 0x129a27) (movR32Imm32Effect 0x129a27 6 10 0xc0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x129a2d (atFlags (condHolds 2) (cmovR64R64Effect 0x129a2d 4 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[57, 1, 55]
    (.letOp (n := 60) (.exec 0x129a2d (fun s => s.RIP = 0x129a2d) (atFlags (condHolds 2) (cmovR64R64Effect 0x129a2d 4 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 1, 55]
    (.letOp (n := 61) (.out 0x129a31 (leaR32Effect 0x129a31 8 7 (.abs (some 10) 3 0x0)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x129a31 (fun s => s.RIP = 0x129a31) (leaR32Effect 0x129a31 8 7 (.abs (some 10) 3 0x0)) (Reg.operands [.gpr 10] [])) #v[59]
    (.letOp (n := 63) (.out 0x129a39 (movR32R32Effect 0x129a39 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 64) (.exec 0x129a39 (fun s => s.RIP = 0x129a39) (movR32R32Effect 0x129a39 3 11 7) (Reg.operands [.gpr 7] [])) #v[61]
    (.letOp (n := 65) (.out 0x129a3c (andR32Imm32Effect 0x129a3c 7 11 0x7e0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[63]
    (.letOp (n := 66) (.out 0x129a3c (andR32Imm32Effect 0x129a3c 7 11 0x7e0) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[63]
    (.letOp (n := 67) (.exec 0x129a3c (fun s => s.RIP = 0x129a3c) (andR32Imm32Effect 0x129a3c 7 11 0x7e0) (Reg.operands [.gpr 11] [])) #v[63]
    (.letOp (n := 68) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l1299e0, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l129a45, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 61), (8, 8), (9, 53), (10, 59), (11, 65), (14, 14), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l129a1d : List UInt8 :=
  [0x49, 0x89, 0xF9, 0x48, 0x81, 0xF9, 0xC0, 0x00, 0x00, 0x00, 0x41, 0xBA, 0xC0, 0x00, 0x00, 0x00,
    0x4C, 0x0F, 0x42, 0xD1, 0x42, 0x8D, 0x3C, 0xD5, 0x00, 0x00, 0x00, 0x00, 0x41, 0x89, 0xFB, 0x41,
    0x81, 0xE3, 0xE0, 0x07, 0x00, 0x00, 0x74, 0x9B]

theorem code_l129a1d : ∀ x ∈ codeRange 0x129a1d bytes_l129a1d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29a1d 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129a45 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129a45 (addR64R64Effect 0x129a45 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[11, 9]
    (.letOp (n := 54) (.exec 0x129a45 (fun s => s.RIP = 0x129a45) (addR64R64Effect 0x129a45 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[11, 9]
    (.letOp (n := 55) (.out 0x129a48 (xorR32R32Effect 0x129a48 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 56) (.exec 0x129a48 (fun s => s.RIP = 0x129a48) (xorR32R32Effect 0x129a48 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.out 0x129a4b (movR64R64Effect 0x129a4b 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 58) (.exec 0x129a4b (fun s => s.RIP = 0x129a4b) (movR64R64Effect 0x129a4b 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.exec 0x129a4e (fun s => s.RIP = 0x129a4e) (fun _ => nopEffect 0x129a4e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129a50, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 57), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 53), (14, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l129a45 : List UInt8 :=
  [0x4D, 0x01, 0xCB, 0x45, 0x31, 0xF6, 0x4C, 0x89, 0xCB, 0x66, 0x90]

theorem code_l129a45 : ∀ x ∈ codeRange 0x129a45 bytes_l129a45, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29a45 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129a50_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x129a94 (orR64R64Effect 0x129a94 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[91, 89]
    (.letOp (n := 94) (.exec 0x129a94 (fun s => s.RIP = 0x129a94) (orR64R64Effect 0x129a94 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[91, 89]
    (.letOp (n := 95) (.out 0x129a97 (andR64R64Effect 0x129a97 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[93, 8]
    (.letOp (n := 96) (.exec 0x129a97 (fun s => s.RIP = 0x129a97) (andR64R64Effect 0x129a97 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[93, 8]
    (.letOp (n := 97) (.out 0x129a9a (addR64R64Effect 0x129a9a 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[95, 81]
    (.letOp (n := 98) (.exec 0x129a9a (fun s => s.RIP = 0x129a9a) (addR64R64Effect 0x129a9a 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[95, 81]
    (.letOp (n := 99) (.out 0x129a9d (addR64R64Effect 0x129a9d 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[97, 69]
    (.letOp (n := 100) (.exec 0x129a9d (fun s => s.RIP = 0x129a9d) (addR64R64Effect 0x129a9d 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[97, 69]
    (.letOp (n := 101) (.out 0x129aa0 (movR64M64Effect 0x129aa0 14 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[3]
    (.letOp (n := 102) (.exec 0x129aa0 (LoadPre 0x129aa0 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x129aa0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129aa0 14 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 103) (.out 0x129aa4 (movR64R64Effect 0x129aa4 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[101]
    (.letOp (n := 104) (.exec 0x129aa4 (fun s => s.RIP = 0x129aa4) (movR64R64Effect 0x129aa4 15 14) (Reg.operands [.gpr 14] [])) #v[101]
    (.letOp (n := 105) (.out 0x129aa7 (notR64Effect 0x129aa7 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[103]
    (.letOp (n := 106) (.exec 0x129aa7 (fun s => s.RIP = 0x129aa7) (notR64Effect 0x129aa7 15) (Reg.operands [.gpr 15] [])) #v[103]
    (.letOp (n := 107) (.out 0x129aaa (shrR64Effect 0x129aaa 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[105]
    (.letOp (n := 108) (.exec 0x129aaa (fun s => s.RIP = 0x129aaa) (shrR64Effect 0x129aaa 4 15 7) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105]
    (.letOp (n := 109) (.out 0x129aae (shrR64Effect 0x129aae 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[101]
    (.letOp (n := 110) (.exec 0x129aae (fun s => s.RIP = 0x129aae) (shrR64Effect 0x129aae 4 14 6) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 111) (.out 0x129ab2 (orR64R64Effect 0x129ab2 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x129ab2 (fun s => s.RIP = 0x129ab2) (orR64R64Effect 0x129ab2 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x129ab5 (andR64R64Effect 0x129ab5 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[111, 8]
    (.letOp (n := 114) (.exec 0x129ab5 (fun s => s.RIP = 0x129ab5) (andR64R64Effect 0x129ab5 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[111, 8]
    (.letOp (n := 115) (.out 0x129ab8 (addR64R64Effect 0x129ab8 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[113, 99]
    (.letOp (n := 116) (.exec 0x129ab8 (fun s => s.RIP = 0x129ab8) (addR64R64Effect 0x129ab8 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[113, 99]
    (.letOp (n := 117) (.out 0x129abb (addR64Imm8Effect 0x129abb 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 118) (.exec 0x129abb (fun s => s.RIP = 0x129abb) (addR64Imm8Effect 0x129abb 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 119) (.out 0x129abf (cmpR64R64Effect 0x129abf 3 11) (EffectPart.reads (.flag .ZF) [.gpr 3, .gpr 11] []) (.flag .ZF)) #v[117, 11]
    (.letOp (n := 120) (.exec 0x129abf (fun s => s.RIP = 0x129abf) (cmpR64R64Effect 0x129abf 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[117, 11]
    (.letOp (n := 121) (.pure (condOp 5)) #v[119]
    (.terminate (.condBr (Fin.last 121) ⟨.l129a50, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)] 122⟩ ⟨.l129ac4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 117), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 81), (13, 99), (14, 115), (15, 107), (19, 119), (22, 22), (39, 39), (50, 50), (51, 51)] 122⟩))))))))))))))))))))))))))))))

def bytes_l129a50_1 : List UInt8 :=
  [0x4D, 0x09, 0xF5, 0x4D, 0x21, 0xC5, 0x4D, 0x01, 0xE5, 0x4D, 0x01, 0xFD, 0x4C, 0x8B, 0x73, 0x18,
    0x4D, 0x89, 0xF7, 0x49, 0xF7, 0xD7, 0x49, 0xC1, 0xEF, 0x07, 0x49, 0xC1, 0xEE, 0x06, 0x4D, 0x09,
    0xFE, 0x4D, 0x21, 0xC6, 0x4D, 0x01, 0xEE, 0x48, 0x83, 0xC3, 0x20, 0x4C, 0x39, 0xDB, 0x75, 0x8C]

theorem code_l129a50_1 : ∀ x ∈ codeRange 0x129a94 bytes_l129a50_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29a94 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129a50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129a50 (movR64M64Effect 0x129a50 15 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 54) (.exec 0x129a50 (LoadPre 0x129a50 (fun s => AddrMode.addr (.base 3 .none) s (0x129a50 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x129a50 15 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x129a53 (movR64M64Effect 0x129a53 12 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[3]
    (.letOp (n := 56) (.exec 0x129a53 (LoadPre 0x129a53 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x129a53 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129a53 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x129a57 (movR64R64Effect 0x129a57 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 58) (.exec 0x129a57 (fun s => s.RIP = 0x129a57) (movR64R64Effect 0x129a57 13 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x129a5a (notR64Effect 0x129a5a 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x129a5a (fun s => s.RIP = 0x129a5a) (notR64Effect 0x129a5a 13) (Reg.operands [.gpr 13] [])) #v[57]
    (.letOp (n := 61) (.out 0x129a5d (shrR64Effect 0x129a5d 4 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.exec 0x129a5d (fun s => s.RIP = 0x129a5d) (shrR64Effect 0x129a5d 4 13 7) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x129a61 (shrR64Effect 0x129a61 4 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 64) (.exec 0x129a61 (fun s => s.RIP = 0x129a61) (shrR64Effect 0x129a61 4 15 6) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 65) (.out 0x129a65 (orR64R64Effect 0x129a65 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x129a65 (fun s => s.RIP = 0x129a65) (orR64R64Effect 0x129a65 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x129a68 (andR64R64Effect 0x129a68 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[65, 8]
    (.letOp (n := 68) (.exec 0x129a68 (fun s => s.RIP = 0x129a68) (andR64R64Effect 0x129a68 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[65, 8]
    (.letOp (n := 69) (.out 0x129a6b (addR64R64Effect 0x129a6b 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[67, 14]
    (.letOp (n := 70) (.exec 0x129a6b (fun s => s.RIP = 0x129a6b) (addR64R64Effect 0x129a6b 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[67, 14]
    (.letOp (n := 71) (.out 0x129a6e (movR64R64Effect 0x129a6e 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 72) (.exec 0x129a6e (fun s => s.RIP = 0x129a6e) (movR64R64Effect 0x129a6e 14 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 73) (.out 0x129a71 (notR64Effect 0x129a71 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.exec 0x129a71 (fun s => s.RIP = 0x129a71) (notR64Effect 0x129a71 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 75) (.out 0x129a74 (shrR64Effect 0x129a74 4 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[73]
    (.letOp (n := 76) (.exec 0x129a74 (fun s => s.RIP = 0x129a74) (shrR64Effect 0x129a74 4 14 7) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x129a78 (shrR64Effect 0x129a78 4 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 78) (.exec 0x129a78 (fun s => s.RIP = 0x129a78) (shrR64Effect 0x129a78 4 12 6) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 79) (.out 0x129a7c (orR64R64Effect 0x129a7c 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x129a7c (fun s => s.RIP = 0x129a7c) (orR64R64Effect 0x129a7c 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x129a7f (andR64R64Effect 0x129a7f 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[79, 8]
    (.letOp (n := 82) (.exec 0x129a7f (fun s => s.RIP = 0x129a7f) (andR64R64Effect 0x129a7f 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[79, 8]
    (.letOp (n := 83) (.out 0x129a82 (movR64M64Effect 0x129a82 13 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 84) (.exec 0x129a82 (LoadPre 0x129a82 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x129a82 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129a82 13 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 85) (.out 0x129a86 (movR64R64Effect 0x129a86 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[83]
    (.letOp (n := 86) (.exec 0x129a86 (fun s => s.RIP = 0x129a86) (movR64R64Effect 0x129a86 14 13) (Reg.operands [.gpr 13] [])) #v[83]
    (.letOp (n := 87) (.out 0x129a89 (notR64Effect 0x129a89 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[85]
    (.letOp (n := 88) (.exec 0x129a89 (fun s => s.RIP = 0x129a89) (notR64Effect 0x129a89 14) (Reg.operands [.gpr 14] [])) #v[85]
    (.letOp (n := 89) (.out 0x129a8c (shrR64Effect 0x129a8c 4 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[87]
    (.letOp (n := 90) (.exec 0x129a8c (fun s => s.RIP = 0x129a8c) (shrR64Effect 0x129a8c 4 14 7) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x129a90 (shrR64Effect 0x129a90 4 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[83]
    (.letOp (n := 92) (.exec 0x129a90 (fun s => s.RIP = 0x129a90) (shrR64Effect 0x129a90 4 13 6) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (b_l129a50_1))))))))))))))))))))))))))))))))))))))))

def bytes_l129a50 : List UInt8 :=
  [0x4C, 0x8B, 0x3B, 0x4C, 0x8B, 0x63, 0x08, 0x4D, 0x89, 0xFD, 0x49, 0xF7, 0xD5, 0x49, 0xC1, 0xED,
    0x07, 0x49, 0xC1, 0xEF, 0x06, 0x4D, 0x09, 0xEF, 0x4D, 0x21, 0xC7, 0x4D, 0x01, 0xF7, 0x4D, 0x89,
    0xE6, 0x49, 0xF7, 0xD6, 0x49, 0xC1, 0xEE, 0x07, 0x49, 0xC1, 0xEC, 0x06, 0x4D, 0x09, 0xF4, 0x4D,
    0x21, 0xC4, 0x4C, 0x8B, 0x6B, 0x10, 0x4D, 0x89, 0xEE, 0x49, 0xF7, 0xD6, 0x49, 0xC1, 0xEE, 0x07,
    0x49, 0xC1, 0xED, 0x06] ++ bytes_l129a50_1

theorem code_l129a50 : ∀ x ∈ codeRange 0x129a50 bytes_l129a50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x29a50 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l129a50_1

@[cfg_block] def b_l129ac4 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1299e3, RegMap.args (entryMap (live .l129ac4)) 53⟩)

def bytes_l129ac4 : List UInt8 :=
  [0xE9, 0x1A, 0xFF, 0xFF, 0xFF]

theorem code_l129ac4 : ∀ x ∈ codeRange 0x129ac4 bytes_l129ac4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29ac4 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129ac9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129ac9 (andR32Imm32Effect 0x129ac9 7 10 0xfc) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x129ac9 (fun s => s.RIP = 0x129ac9) (andR32Imm32Effect 0x129ac9 7 10 0xfc) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x129ad0 (movR32R32Effect 0x129ad0 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 10] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x129ad0 (fun s => s.RIP = 0x129ad0) (movR32R32Effect 0x129ad0 3 1 10) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.out 0x129ad3 (movR64M64Effect 0x129ad3 1 (.sib 9 (some 1) 3 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9, .gpr 1] []) (.reg (.gpr 1))) #v[9, 55]
    (.letOp (n := 58) (.exec 0x129ad3 (LoadPre 0x129ad3 (fun s => AddrMode.addr (.sib 9 (some 1) 3 .none) s (0x129ad3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x129ad3 1 (.sib 9 (some 1) 3 .none)) (Reg.operands [.gpr 9, .gpr 1] [])) #v[9, 55]
    (.letOp (n := 59) (.out 0x129ad7 (movR64R64Effect 0x129ad7 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x129ad7 (fun s => s.RIP = 0x129ad7) (movR64R64Effect 0x129ad7 7 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x129ada (notR64Effect 0x129ada 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x129ada (fun s => s.RIP = 0x129ada) (notR64Effect 0x129ada 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x129add (shrR64Effect 0x129add 4 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x129add (fun s => s.RIP = 0x129add) (shrR64Effect 0x129add 4 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x129ae1 (shrR64Effect 0x129ae1 4 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 66) (.exec 0x129ae1 (fun s => s.RIP = 0x129ae1) (shrR64Effect 0x129ae1 4 1 6) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x129ae5 (orR64R64Effect 0x129ae5 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x129ae5 (fun s => s.RIP = 0x129ae5) (orR64R64Effect 0x129ae5 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x129ae8 (andR64R64Effect 0x129ae8 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[67, 8]
    (.letOp (n := 70) (.exec 0x129ae8 (fun s => s.RIP = 0x129ae8) (andR64R64Effect 0x129ae8 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[67, 8]
    (.letOp (n := 71) (.out 0x129aeb (cmpR32Imm8Effect 0x129aeb 4 11 0x1) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 72) (.exec 0x129aeb (fun s => s.RIP = 0x129aeb) (cmpR32Imm8Effect 0x129aeb 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 73) (.pure (condOp 4)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l129b2f, RegMap.args [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l129af1, RegMap.args [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 63), (8, 8), (9, 9), (10, 53), (11, 11), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l129ac9 : List UInt8 :=
  [0x41, 0x81, 0xE2, 0xFC, 0x00, 0x00, 0x00, 0x44, 0x89, 0xD1, 0x49, 0x8B, 0x0C, 0xC9, 0x48, 0x89,
    0xCF, 0x48, 0xF7, 0xD7, 0x48, 0xC1, 0xEF, 0x07, 0x48, 0xC1, 0xE9, 0x06, 0x48, 0x09, 0xF9, 0x4C,
    0x21, 0xC1, 0x41, 0x83, 0xFB, 0x01, 0x74, 0x3E]

theorem code_l129ac9 : ∀ x ∈ codeRange 0x129ac9 bytes_l129ac9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29ac9 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129af1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129af1 (movR64M64Effect 0x129af1 7 (.sib 9 (some 10) 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 10] []) (.reg (.gpr 7))) #v[9, 10]
    (.letOp (n := 54) (.exec 0x129af1 (LoadPre 0x129af1 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x8)) s (0x129af1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129af1 7 (.sib 9 (some 10) 3 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 55) (.out 0x129af6 (movR64R64Effect 0x129af6 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.exec 0x129af6 (fun s => s.RIP = 0x129af6) (movR64R64Effect 0x129af6 3 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x129af9 (notR64Effect 0x129af9 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.exec 0x129af9 (fun s => s.RIP = 0x129af9) (notR64Effect 0x129af9 3) (Reg.operands [.gpr 3] [])) #v[55]
    (.letOp (n := 59) (.out 0x129afc (shrR64Effect 0x129afc 4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.exec 0x129afc (fun s => s.RIP = 0x129afc) (shrR64Effect 0x129afc 4 3 7) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x129b00 (shrR64Effect 0x129b00 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 62) (.exec 0x129b00 (fun s => s.RIP = 0x129b00) (shrR64Effect 0x129b00 4 7 6) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 63) (.out 0x129b04 (orR64R64Effect 0x129b04 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x129b04 (fun s => s.RIP = 0x129b04) (orR64R64Effect 0x129b04 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x129b07 (andR64R64Effect 0x129b07 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[63, 8]
    (.letOp (n := 66) (.exec 0x129b07 (fun s => s.RIP = 0x129b07) (andR64R64Effect 0x129b07 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[63, 8]
    (.letOp (n := 67) (.out 0x129b0a (addR64R64Effect 0x129b0a 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 65]
    (.letOp (n := 68) (.exec 0x129b0a (fun s => s.RIP = 0x129b0a) (addR64R64Effect 0x129b0a 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 65]
    (.letOp (n := 69) (.out 0x129b0d (cmpR32Imm8Effect 0x129b0d 4 11 0x2) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[11]
    (.letOp (n := 70) (.exec 0x129b0d (fun s => s.RIP = 0x129b0d) (cmpR32Imm8Effect 0x129b0d 4 11 0x2) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 71) (.pure (condOp 4)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l129b2f, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l129b13, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 59), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l129af1 : List UInt8 :=
  [0x4B, 0x8B, 0x7C, 0xD1, 0x08, 0x48, 0x89, 0xFB, 0x48, 0xF7, 0xD3, 0x48, 0xC1, 0xEB, 0x07, 0x48,
    0xC1, 0xEF, 0x06, 0x48, 0x09, 0xDF, 0x4C, 0x21, 0xC7, 0x48, 0x01, 0xF9, 0x41, 0x83, 0xFB, 0x02,
    0x74, 0x1C]

theorem code_l129af1 : ∀ x ∈ codeRange 0x129af1 bytes_l129af1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29af1 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129b13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129b13 (movR64M64Effect 0x129b13 7 (.sib 9 (some 10) 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 10] []) (.reg (.gpr 7))) #v[9, 10]
    (.letOp (n := 54) (.exec 0x129b13 (LoadPre 0x129b13 (fun s => AddrMode.addr (.sib 9 (some 10) 3 (.d8 0x10)) s (0x129b13 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129b13 7 (.sib 9 (some 10) 3 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 10]
    (.letOp (n := 55) (.out 0x129b18 (movR64R64Effect 0x129b18 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x129b18 (fun s => s.RIP = 0x129b18) (movR64R64Effect 0x129b18 9 7) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x129b1b (notR64Effect 0x129b1b 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x129b1b (fun s => s.RIP = 0x129b1b) (notR64Effect 0x129b1b 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 59) (.out 0x129b1e (shrR64Effect 0x129b1e 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 60) (.exec 0x129b1e (fun s => s.RIP = 0x129b1e) (shrR64Effect 0x129b1e 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x129b22 (shrR64Effect 0x129b22 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 62) (.exec 0x129b22 (fun s => s.RIP = 0x129b22) (shrR64Effect 0x129b22 4 7 6) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 63) (.out 0x129b26 (orR64R64Effect 0x129b26 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x129b26 (fun s => s.RIP = 0x129b26) (orR64R64Effect 0x129b26 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x129b29 (andR64R64Effect 0x129b29 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[63, 8]
    (.letOp (n := 66) (.exec 0x129b29 (fun s => s.RIP = 0x129b29) (andR64R64Effect 0x129b29 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[63, 8]
    (.letOp (n := 67) (.out 0x129b2c (addR64R64Effect 0x129b2c 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 65]
    (.letOp (n := 68) (.exec 0x129b2c (fun s => s.RIP = 0x129b2c) (addR64R64Effect 0x129b2c 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 65]
    (.terminate (.br ⟨.l129b2f, RegMap.args [(0, 0), (1, 67), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 8), (9, 59), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l129b13 : List UInt8 :=
  [0x4B, 0x8B, 0x7C, 0xD1, 0x10, 0x49, 0x89, 0xF9, 0x49, 0xF7, 0xD1, 0x49, 0xC1, 0xE9, 0x07, 0x48,
    0xC1, 0xEF, 0x06, 0x4C, 0x09, 0xCF, 0x4C, 0x21, 0xC7, 0x48, 0x01, 0xF9]

theorem code_l129b13 : ∀ x ∈ codeRange 0x129b13 bytes_l129b13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29b13 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129b2f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129b2f (movR64R64Effect 0x129b2f 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 54) (.exec 0x129b2f (fun s => s.RIP = 0x129b2f) (movR64R64Effect 0x129b2f 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x129b32 (andR64R64Effect 0x129b32 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 6]
    (.letOp (n := 56) (.exec 0x129b32 (fun s => s.RIP = 0x129b32) (andR64R64Effect 0x129b32 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 6]
    (.letOp (n := 57) (.out 0x129b35 (shrR64Effect 0x129b35 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 58) (.exec 0x129b35 (fun s => s.RIP = 0x129b35) (shrR64Effect 0x129b35 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 59) (.out 0x129b39 (andR64R64Effect 0x129b39 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[57, 6]
    (.letOp (n := 60) (.exec 0x129b39 (fun s => s.RIP = 0x129b39) (andR64R64Effect 0x129b39 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[57, 6]
    (.letOp (n := 61) (.out 0x129b3c (addR64R64Effect 0x129b3c 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x129b3c (fun s => s.RIP = 0x129b3c) (addR64R64Effect 0x129b3c 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x129b3f (imulR64R64Effect 0x129b3f 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[61, 2]
    (.letOp (n := 64) (.exec 0x129b3f (fun s => s.RIP = 0x129b3f) (imulR64R64Effect 0x129b3f 4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[61, 2]
    (.letOp (n := 65) (.out 0x129b43 (shrR64Effect 0x129b43 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x129b43 (fun s => s.RIP = 0x129b43) (shrR64Effect 0x129b43 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x129b47 (addR64R64Effect 0x129b47 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[0, 65]
    (.letOp (n := 68) (.exec 0x129b47 (fun s => s.RIP = 0x129b47) (addR64R64Effect 0x129b47 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 65]
    (.terminate (.br ⟨.l129b4a, RegMap.args [(0, 67), (1, 65), (2, 2), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l129b2f : List UInt8 :=
  [0x48, 0x89, 0xCF, 0x48, 0x21, 0xF7, 0x48, 0xC1, 0xE9, 0x08, 0x48, 0x21, 0xF1, 0x48, 0x01, 0xF9,
    0x48, 0x0F, 0xAF, 0xCA, 0x48, 0xC1, 0xE9, 0x30, 0x48, 0x01, 0xC8]

theorem code_l129b2f : ∀ x ∈ codeRange 0x129b2f bytes_l129b2f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29b2f 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129b4a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129b4a (popR64Effect 0x129b4a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x129b4a (popR64Effect 0x129b4a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x129b4a (PopPre 0x129b4a) (popR64Effect 0x129b4a 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x129b4b (popR64Effect 0x129b4b 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 57) (.out 0x129b4b (popR64Effect 0x129b4b 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x129b4b (PopPre 0x129b4b) (popR64Effect 0x129b4b 2 12) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x129b4d (popR64Effect 0x129b4d 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.out 0x129b4d (popR64Effect 0x129b4d 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x129b4d (PopPre 0x129b4d) (popR64Effect 0x129b4d 2 13) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x129b4f (popR64Effect 0x129b4f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[60]
    (.letOp (n := 63) (.out 0x129b4f (popR64Effect 0x129b4f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x129b4f (PopPre 0x129b4f) (popR64Effect 0x129b4f 2 14) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x129b51 (popR64Effect 0x129b51 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[63]
    (.letOp (n := 66) (.out 0x129b51 (popR64Effect 0x129b51 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x129b51 (PopPre 0x129b51) (popR64Effect 0x129b51 2 15) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x129b53 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x129b53 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x129b53 (RetPre 0x129b53) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 59), (14, 62), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l129b4a : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l129b4a : ∀ x ∈ codeRange 0x129b4a bytes_l129b4a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29b4a 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c30 (pushR64Effect 0x129c30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129c30 (PushPre 0x129c30 1) (pushR64Effect 0x129c30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.exec 0x129c31 (fun s => s.RIP = 0x129c31) (movR64R64Effect 0x129c31 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 56) (.out 0x129c34 (pushR64Effect 0x129c34 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 57) (.exec 0x129c34 (PushPre 0x129c34 2) (pushR64Effect 0x129c34 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 58) (.out 0x129c36 (pushR64Effect 0x129c36 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x129c36 (PushPre 0x129c36 2) (pushR64Effect 0x129c36 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x129c38 (pushR64Effect 0x129c38 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[58, 12]
    (.letOp (n := 61) (.exec 0x129c38 (PushPre 0x129c38 2) (pushR64Effect 0x129c38 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[58, 12]
    (.letOp (n := 62) (.out 0x129c3a (pushR64Effect 0x129c3a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[60, 3]
    (.letOp (n := 63) (.exec 0x129c3a (PushPre 0x129c3a 1) (pushR64Effect 0x129c3a 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 64) (.out 0x129c3b (movR64R64Effect 0x129c3b 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 65) (.exec 0x129c3b (fun s => s.RIP = 0x129c3b) (movR64R64Effect 0x129c3b 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 66) (.out 0x129c3e (movR64R64Effect 0x129c3e 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 67) (.exec 0x129c3e (fun s => s.RIP = 0x129c3e) (movR64R64Effect 0x129c3e 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 68) (.out 0x129c41 (movR64R64Effect 0x129c41 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 69) (.exec 0x129c41 (fun s => s.RIP = 0x129c41) (movR64R64Effect 0x129c41 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x129c44 (movR64R64Effect 0x129c44 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 71) (.exec 0x129c44 (fun s => s.RIP = 0x129c44) (movR64R64Effect 0x129c44 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 72) (.out 0x129c47 (cmpR32Imm8Effect 0x129c47 3 2 0xff) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 73) (.exec 0x129c47 (fun s => s.RIP = 0x129c47) (cmpR32Imm8Effect 0x129c47 3 2 0xff) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.pure (condOp 4)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l129c5e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l129c4c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 64), (4, 62), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 68), (13, 13), (14, 66), (15, 70), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l129c30 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x4C, 0x89, 0xC3, 0x49, 0x89,
    0xCE, 0x49, 0x89, 0xF4, 0x49, 0x89, 0xFF, 0x83, 0xFA, 0xFF, 0x74, 0x12]

theorem code_l129c30 : ∀ x ∈ codeRange 0x129c30 bytes_l129c30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c30 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x129c4c (fun s => s.RIP = 0x129c4c) (movR64R64Effect 0x129c4c 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 54) (.exec 0x129c4f (fun s => s.RIP = 0x129c4f) (movR32R32Effect 0x129c4f 2 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (cutBlock 0x129c51))

def bytes_l129c4c : List UInt8 :=
  [0x4C, 0x89, 0xFF, 0x89, 0xD6, 0x41, 0xFF, 0x54, 0x24, 0x20]

theorem code_l129c4c : ∀ x ∈ codeRange 0x129c4c bytes_l129c4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c4c 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c56 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c56 (movR32R32Effect 0x129c56 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x129c56 (fun s => s.RIP = 0x129c56) (movR32R32Effect 0x129c56 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x129c58 (movR8Imm8Effect 0x129c58 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x129c58 (fun s => s.RIP = 0x129c58) (movR8Imm8Effect 0x129c58 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x129c5a (testR8R8Effect 0x129c5a 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x129c5a (fun s => s.RIP = 0x129c5a) (testR8R8Effect 0x129c5a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l129c7d, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l129c5e, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l129c56 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x75, 0x1F]

theorem code_l129c56 : ∀ x ∈ codeRange 0x129c56 bytes_l129c56, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c56 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c5e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c5e (testR64R64Effect 0x129c5e 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 54) (.exec 0x129c5e (fun s => s.RIP = 0x129c5e) (testR64R64Effect 0x129c5e 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l129c7b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l129c63, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l129c5e : List UInt8 :=
  [0x4D, 0x85, 0xF6, 0x74, 0x18]

theorem code_l129c5e : ∀ x ∈ codeRange 0x129c5e bytes_l129c5e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c5e 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x129c63 (LoadPre 0x129c63 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x129c63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x129c63 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.exec 0x129c68 (fun s => s.RIP = 0x129c68) (movR64R64Effect 0x129c68 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x129c6b (fun s => s.RIP = 0x129c6b) (movR64R64Effect 0x129c6b 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x129c6e (fun s => s.RIP = 0x129c6e) (movR64R64Effect 0x129c6e 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x129c71 (popR64Effect 0x129c71 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x129c71 (PopPre 0x129c71) (popR64Effect 0x129c71 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x129c72 (popR64Effect 0x129c72 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x129c72 (PopPre 0x129c72) (popR64Effect 0x129c72 2 12) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x129c74 (popR64Effect 0x129c74 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x129c74 (PopPre 0x129c74) (popR64Effect 0x129c74 2 14) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x129c76 (popR64Effect 0x129c76 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x129c76 (PopPre 0x129c76) (popR64Effect 0x129c76 2 15) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.exec 0x129c78 (PopPre 0x129c78) (popR64Effect 0x129c78 1 5) (Reg.operands [.gpr 4] [])) #v[63]
    (cutBlock 0x129c79)))))))))))))

def bytes_l129c63 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xF6, 0x48, 0x89, 0xDA, 0x5B, 0x41,
    0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xFF, 0xE0]

theorem code_l129c63 : ∀ x ∈ codeRange 0x129c63 bytes_l129c63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c63 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c7b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c7b (xorR32R32Effect 0x129c7b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x129c7b (fun s => s.RIP = 0x129c7b) (xorR32R32Effect 0x129c7b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l129c7d, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l129c7b : List UInt8 :=
  [0x31, 0xC0]

theorem code_l129c7b : ∀ x ∈ codeRange 0x129c7b bytes_l129c7b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c7b 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c7d (popR64Effect 0x129c7d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.out 0x129c7d (popR64Effect 0x129c7d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x129c7d (PopPre 0x129c7d) (popR64Effect 0x129c7d 1 3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x129c7e (popR64Effect 0x129c7e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 57) (.out 0x129c7e (popR64Effect 0x129c7e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x129c7e (PopPre 0x129c7e) (popR64Effect 0x129c7e 2 12) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x129c80 (popR64Effect 0x129c80 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[57]
    (.letOp (n := 60) (.out 0x129c80 (popR64Effect 0x129c80 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x129c80 (PopPre 0x129c80) (popR64Effect 0x129c80 2 14) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x129c82 (popR64Effect 0x129c82 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[60]
    (.letOp (n := 63) (.out 0x129c82 (popR64Effect 0x129c82 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x129c82 (PopPre 0x129c82) (popR64Effect 0x129c82 2 15) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x129c84 (popR64Effect 0x129c84 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[63]
    (.letOp (n := 66) (.out 0x129c84 (popR64Effect 0x129c84 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x129c84 (PopPre 0x129c84) (popR64Effect 0x129c84 1 5) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x129c85 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[66]
    (.letOp (n := 69) (.out 0x129c85 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x129c85 (RetPre 0x129c85) (retEffect) (Reg.operands [.gpr 4] [])) #v[66]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 69), (5, 65), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 56), (13, 13), (14, 59), (15, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 71) (some ⟨68, by decide⟩))))))))))))))))))))

def bytes_l129c7d : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l129c7d : ∀ x ∈ codeRange 0x129c7d bytes_l129c7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c7d 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129c90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129c90 (pushR64Effect 0x129c90 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129c90 (PushPre 0x129c90 1) (pushR64Effect 0x129c90 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x129c91 (movR64R64Effect 0x129c91 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x129c91 (fun s => s.RIP = 0x129c91) (movR64R64Effect 0x129c91 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129c94 (subR64Imm8Effect 0x129c94 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x129c94 (fun s => s.RIP = 0x129c94) (subR64Imm8Effect 0x129c94 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x129c98 (StorePre 0x129c98 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x129c98 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c98 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 60) (.exec 0x129c9c (StorePre 0x129c9c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x129c9c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129c9c 7 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 55]
    (.letOp (n := 61) (.out 0x129ca0 (leaR64Effect 0x129ca0 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 62) (.exec 0x129ca0 (fun s => s.RIP = 0x129ca0) (leaR64Effect 0x129ca0 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 63) (.exec 0x129ca4 (StorePre 0x129ca4 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd0)) s (0x129ca4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129ca4 0 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 55]
    (.letOp (n := 64) (.out 0x129ca8 (leaR64Effect 0x129ca8 0 (.rip 0x781)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 65) (.exec 0x129ca8 (fun s => s.RIP = 0x129ca8) (leaR64Effect 0x129ca8 0 (.rip 0x781)) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.exec 0x129caf (StorePre 0x129caf 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x129caf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129caf 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[64, 55]
    (.letOp (n := 67) (.out 0x129cb3 (leaR64Effect 0x129cb3 1 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 68) (.exec 0x129cb3 (fun s => s.RIP = 0x129cb3) (leaR64Effect 0x129cb3 1 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 69) (.exec 0x129cb7 (StorePre 0x129cb7 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x129cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cb7 1 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[67, 55]
    (.letOp (n := 70) (.exec 0x129cbb (StorePre 0x129cbb 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x129cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x129cbb 0 (.base 5 (.d8 0xe8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[64, 55]
    (.letOp (n := 71) (.out 0x129cbf (leaR64Effect 0x129cbf 7 (.rip 0xd809c)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 72) (.exec 0x129cbf (fun s => s.RIP = 0x129cbf) (leaR64Effect 0x129cbf 7 (.rip 0xd809c)) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x129cc6 (leaR64Effect 0x129cc6 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 74) (.exec 0x129cc6 (fun s => s.RIP = 0x129cc6) (leaR64Effect 0x129cc6 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 75) (.out 0x129cca (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 76) (.exec 0x129cca (GoesTo (CallMemPre 0x129cca (.rip 0xda110)) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110)))) 0x129770) (callEffect (callMemPtr 0x129cca (.rip 0xda110)) (0x129cca + BitVec.ofNat 64 (callMemLen (.rip 0xda110)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 77) (.const ⟨64, 0x129cd0⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 64), (1, 67), (2, 2), (4, 75), (5, 55), (6, 73), (7, 71)] 78⟩ { target := .l129cd0, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l129c90 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0x75, 0xF8, 0x48, 0x89, 0x7D, 0xF0,
    0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x45, 0xD0, 0x48, 0x8D, 0x05, 0x81, 0x07, 0x00, 0x00, 0x48,
    0x89, 0x45, 0xD8, 0x48, 0x8D, 0x4D, 0xF0, 0x48, 0x89, 0x4D, 0xE0, 0x48, 0x89, 0x45, 0xE8, 0x48,
    0x8D, 0x3D, 0x9C, 0x80, 0x0D, 0x00, 0x48, 0x8D, 0x75, 0xD0, 0xFF, 0x15, 0x10, 0xA1, 0x0D, 0x00]

theorem code_l129c90 : ∀ x ∈ codeRange 0x129c90 bytes_l129c90, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c90 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129cd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129cd0 (pushR64Effect 0x129cd0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x129cd0 (PushPre 0x129cd0 1) (pushR64Effect 0x129cd0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x129cd1 (movR64R64Effect 0x129cd1 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x129cd1 (fun s => s.RIP = 0x129cd1) (movR64R64Effect 0x129cd1 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x129cd4 (subR64Imm8Effect 0x129cd4 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x129cd4 (fun s => s.RIP = 0x129cd4) (subR64Imm8Effect 0x129cd4 4 0x10) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x129cd8 (movzxR32M8Effect 0x129cd8 3 1 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 60) (.exec 0x129cd8 (LoadPre 0x129cd8 (fun s => AddrMode.addr (.base 7 .none) s (0x129cd8 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x129cd8 3 1 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x129cdb (movR32Imm32Effect 0x129cdb 5 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x129cdb (fun s => s.RIP = 0x129cdb) (movR32Imm32Effect 0x129cdb 5 0 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x129ce0 (movR32R32Effect 0x129ce0 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 64) (.exec 0x129ce0 (fun s => s.RIP = 0x129ce0) (movR32R32Effect 0x129ce0 2 2 1) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 65) (.out 0x129ce2 (cmpR8Imm8Effect 0x129ce2 3 1 0xa) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[59]
    (.letOp (n := 66) (.exec 0x129ce2 (fun s => s.RIP = 0x129ce2) (cmpR8Imm8Effect 0x129ce2 3 1 0xa) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 67) (.pure (condOp 2)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l129d13, RegMap.args [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l129ce7, RegMap.args [(0, 61), (1, 59), (2, 63), (3, 3), (4, 57), (5, 55), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l129cd0 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x10, 0x0F, 0xB6, 0x0F, 0xB8, 0x03, 0x00, 0x00, 0x00,
    0x89, 0xCA, 0x80, 0xF9, 0x0A, 0x72, 0x2C]

theorem code_l129cd0 : ∀ x ∈ codeRange 0x129cd0 bytes_l129cd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29cd0 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129ce7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129ce7 (movzxR32R8Effect 0x129ce7 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 54) (.exec 0x129ce7 (fun s => s.RIP = 0x129ce7) (movzxR32R8Effect 0x129ce7 3 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x129cea (leaR32Effect 0x129cea 3 2 (.sib 0 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 0] []) (.reg (.gpr 2))) #v[53, 53]
    (.letOp (n := 56) (.exec 0x129cea (fun s => s.RIP = 0x129cea) (leaR32Effect 0x129cea 3 2 (.sib 0 (some 0) 2 .none)) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.letOp (n := 57) (.out 0x129ced (leaR32Effect 0x129ced 3 2 (.sib 0 (some 2) 3 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 2] []) (.reg (.gpr 2))) #v[53, 55]
    (.letOp (n := 58) (.exec 0x129ced (fun s => s.RIP = 0x129ced) (leaR32Effect 0x129ced 3 2 (.sib 0 (some 2) 3 .none)) (Reg.operands [.gpr 0, .gpr 2] [])) #v[53, 55]
    (.letOp (n := 59) (.out 0x129cf0 (shrR32Effect 0x129cf0 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x129cf0 (fun s => s.RIP = 0x129cf0) (shrR32Effect 0x129cf0 3 2 12) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x129cf3 (imulR32R32Imm8Effect 0x129cf3 3 0 2 0x64) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x129cf3 (fun s => s.RIP = 0x129cf3) (imulR32R32Imm8Effect 0x129cf3 3 0 2 0x64) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 63) (.out 0x129cf6 (movR32R32Effect 0x129cf6 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 64) (.exec 0x129cf6 (fun s => s.RIP = 0x129cf6) (movR32R32Effect 0x129cf6 2 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x129cf8 (subR8R8Effect 0x129cf8 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x129cf8 (fun s => s.RIP = 0x129cf8) (subR8R8Effect 0x129cf8 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x129cfb (movzxR32R8Effect 0x129cfb 4 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x129cfb (fun s => s.RIP = 0x129cfb) (movzxR32R8Effect 0x129cfb 4 0 7) (Reg.operands [.gpr 7] [])) #v[65]
    (.letOp (n := 69) (.out 0x129cff (leaR64Effect 0x129cff 7 (.rip 0xd9f3d)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 70) (.exec 0x129cff (fun s => s.RIP = 0x129cff) (leaR64Effect 0x129cff 7 (.rip 0xd9f3d)) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x129d06 (movzxR32M16Effect 0x129d06 4 0 (.sib 7 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[69, 67]
    (.letOp (n := 72) (.exec 0x129d06 (LoadPre 0x129d06 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x129d06 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x129d06 4 0 (.sib 7 (some 0) 1 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[69, 67]
    (.letOp (n := 73) (.exec 0x129d0a (StorePre 0x129d0a 4 (fun s => AddrMode.addr (.base 5 (.d8 0xfe)) s (0x129d0a + BitVec.ofNat 64 4)) 2) (movM16R16Effect 0x129d0a 4 0 (.base 5 (.d8 0xfe))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[71, 5]
    (.letOp (n := 74) (.out 0x129d0e (movR32Imm32Effect 0x129d0e 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 75) (.exec 0x129d0e (fun s => s.RIP = 0x129d0e) (movR32Imm32Effect 0x129d0e 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129d13, RegMap.args [(0, 74), (1, 1), (2, 59), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l129ce7 : List UInt8 :=
  [0x0F, 0xB6, 0xC1, 0x8D, 0x14, 0x80, 0x8D, 0x14, 0xD0, 0xC1, 0xEA, 0x0C, 0x6B, 0xC2, 0x64, 0x89,
    0xCF, 0x40, 0x28, 0xC7, 0x40, 0x0F, 0xB6, 0xC7, 0x48, 0x8D, 0x3D, 0x3D, 0x9F, 0x0D, 0x00, 0x0F,
    0xB7, 0x04, 0x47, 0x66, 0x89, 0x45, 0xFE, 0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l129ce7 : ∀ x ∈ codeRange 0x129ce7 bytes_l129ce7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29ce7 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129d13 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129d13 (testR8R8Effect 0x129d13 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x129d13 (fun s => s.RIP = 0x129d13) (testR8R8Effect 0x129d13 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x129d15 (atFlags (condHolds 4) (setccR8Effect 0x129d15 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 53]
    (.letOp (n := 56) (.exec 0x129d15 (fun s => s.RIP = 0x129d15) (atFlags (condHolds 4) (setccR8Effect 0x129d15 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 53]
    (.letOp (n := 57) (.out 0x129d19 (testR8R8Effect 0x129d19 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 58) (.exec 0x129d19 (fun s => s.RIP = 0x129d19) (testR8R8Effect 0x129d19 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 59) (.out 0x129d1b (atFlags (condHolds 5) (setccR8Effect 0x129d1b 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[1, 57]
    (.letOp (n := 60) (.exec 0x129d1b (fun s => s.RIP = 0x129d1b) (atFlags (condHolds 5) (setccR8Effect 0x129d1b 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[1, 57]
    (.letOp (n := 61) (.out 0x129d1e (testR8R8Effect 0x129d1e 3 1 7) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 7] []) (.flag .ZF)) #v[59, 55]
    (.letOp (n := 62) (.exec 0x129d1e (fun s => s.RIP = 0x129d1e) (testR8R8Effect 0x129d1e 3 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[59, 55]
    (.letOp (n := 63) (.pure (condOp 5)) #v[61]
    (.terminate (.condBr (Fin.last 63) ⟨.l129d39, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ ⟨.l129d23, RegMap.args [(0, 0), (1, 59), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l129d13 : List UInt8 :=
  [0x84, 0xD2, 0x40, 0x0F, 0x94, 0xC7, 0x84, 0xC9, 0x0F, 0x95, 0xC1, 0x40, 0x84, 0xF9, 0x75, 0x16]

theorem code_l129d13 : ∀ x ∈ codeRange 0x129d13 bytes_l129d13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29d13 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129d23 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129d23 (movzxR32R8Effect 0x129d23 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x129d23 (fun s => s.RIP = 0x129d23) (movzxR32R8Effect 0x129d23 3 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x129d26 (leaR64Effect 0x129d26 2 (.rip 0xd9f16)) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x129d26 (fun s => s.RIP = 0x129d26) (leaR64Effect 0x129d26 2 (.rip 0xd9f16)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x129d2d (movzxR32M8Effect 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 1] []) (.reg (.gpr 1))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x129d2d (LoadPre 0x129d2d (fun s => AddrMode.addr (.sib 2 (some 1) 1 (.d8 0x1)) s (0x129d2d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x129d2d 5 1 (.sib 2 (some 1) 1 (.d8 0x1))) (Reg.operands [.gpr 2, .gpr 1] [])) #v[55, 53]
    (.letOp (n := 59) (.exec 0x129d32 (StorePre 0x129d32 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xfc)) s (0x129d32 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x129d32 4 1 (.sib 5 (some 0) 0 (.d8 0xfc))) (Reg.operands [.gpr 1, .gpr 5, .gpr 0] [])) #v[57, 5, 0]
    (.letOp (n := 60) (.out 0x129d36 (decR64Effect 0x129d36 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 61) (.exec 0x129d36 (fun s => s.RIP = 0x129d36) (decR64Effect 0x129d36 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.terminate (.br ⟨.l129d39, RegMap.args [(0, 60), (1, 57), (2, 55), (3, 3), (4, 4), (5, 5), (6, 6), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l129d23 : List UInt8 :=
  [0x0F, 0xB6, 0xCA, 0x48, 0x8D, 0x15, 0x16, 0x9F, 0x0D, 0x00, 0x0F, 0xB6, 0x4C, 0x4A, 0x01, 0x88,
    0x4C, 0x05, 0xFC, 0x48, 0xFF, 0xC8]

theorem code_l129d23 : ∀ x ∈ codeRange 0x129d23 bytes_l129d23, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29d23 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129d39 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129d39 (movR32Imm32Effect 0x129d39 6 9 0x3) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x129d39 (fun s => s.RIP = 0x129d39) (movR32Imm32Effect 0x129d39 6 9 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x129d3f (subR64R64Effect 0x129d3f 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x129d3f (fun s => s.RIP = 0x129d3f) (subR64R64Effect 0x129d3f 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x129d42 (leaR64Effect 0x129d42 8 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[0, 5]
    (.letOp (n := 58) (.exec 0x129d42 (fun s => s.RIP = 0x129d42) (leaR64Effect 0x129d42 8 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 59) (.out 0x129d46 (addR64Imm8Effect 0x129d46 8 0xfd) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x129d46 (fun s => s.RIP = 0x129d46) (addR64Imm8Effect 0x129d46 8 0xfd) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x129d4a (movR32Imm32Effect 0x129d4a 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x129d4a (fun s => s.RIP = 0x129d4a) (movR32Imm32Effect 0x129d4a 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x129d4f (movR64R64Effect 0x129d4f 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x129d4f (fun s => s.RIP = 0x129d4f) (movR64R64Effect 0x129d4f 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x129d52 (movR32Imm32Effect 0x129d52 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 66) (.exec 0x129d52 (fun s => s.RIP = 0x129d52) (movR32Imm32Effect 0x129d52 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x129d57 (xorR32R32Effect 0x129d57 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 68) (.exec 0x129d57 (fun s => s.RIP = 0x129d57) (xorR32R32Effect 0x129d57 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 69) (.out 0x129d59 (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x129d59 (GoesTo (CallMemPre 0x129d59 (.rip 0xda089)) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089)))) 0x128b20) (callEffect (callMemPtr 0x129d59 (.rip 0xda089)) (0x129d59 + BitVec.ofNat 64 (callMemLen (.rip 0xda089)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x129d5f⟩) #v[]
    (.terminate (.call ⟨.l128b20, RegMap.args [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l129d5f, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l129d39 : List UInt8 :=
  [0x41, 0xB9, 0x03, 0x00, 0x00, 0x00, 0x49, 0x29, 0xC1, 0x4C, 0x8D, 0x04, 0x28, 0x49, 0x83, 0xC0,
    0xFD, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF7, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x31, 0xC9,
    0xFF, 0x15, 0x89, 0xA0, 0x0D, 0x00]

theorem code_l129d39 : ∀ x ∈ codeRange 0x129d39 bytes_l129d39, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29d39 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l129d5f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x129d5f (addR64Imm8Effect 0x129d5f 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x129d5f (fun s => s.RIP = 0x129d5f) (addR64Imm8Effect 0x129d5f 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x129d63 (popR64Effect 0x129d63 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.out 0x129d63 (popR64Effect 0x129d63 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x129d63 (PopPre 0x129d63) (popR64Effect 0x129d63 1 5) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x129d64 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[56]
    (.letOp (n := 59) (.out 0x129d64 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x129d64 (RetPre 0x129d64) (retEffect) (Reg.operands [.gpr 4] [])) #v[56]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 59), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61) (some ⟨58, by decide⟩))))))))))

def bytes_l129d5f : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x5D, 0xC3]

theorem code_l129d5f : ∀ x ∈ codeRange 0x129d5f bytes_l129d5f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29d5f 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a050 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a050 (movR64M64Effect 0x12a050 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x12a050 (LoadPre 0x12a050 (fun s => AddrMode.addr (.base 7 .none) s (0x12a050 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a050 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x12a053 (movR64M64Effect 0x12a053 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 56) (.exec 0x12a053 (LoadPre 0x12a053 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a053 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a053 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x12a057 (LoadPre 0x12a057 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x12a057 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a057 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 58) (.exec 0x12a05b (fun s => s.RIP = 0x12a05b) (movR64R64Effect 0x12a05b 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (cutBlock 0x12a05e))))))

def bytes_l12a050 : List UInt8 :=
  [0x48, 0x8B, 0x07, 0x48, 0x8B, 0x4F, 0x08, 0x48, 0x8B, 0x49, 0x18, 0x48, 0x89, 0xC7, 0xFF, 0xE1]

theorem code_l12a050 : ∀ x ∈ codeRange 0x12a050 bytes_l12a050, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a050 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a070 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a070 (movR64R64Effect 0x12a070 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x12a070 (fun s => s.RIP = 0x12a070) (movR64R64Effect 0x12a070 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12a073 (movR64M64Effect 0x12a073 6 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 56) (.exec 0x12a073 (LoadPre 0x12a073 (fun s => AddrMode.addr (.base 7 .none) s (0x12a073 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a073 6 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x12a076 (movR64M64Effect 0x12a076 2 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 58) (.exec 0x12a076 (LoadPre 0x12a076 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a076 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a076 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x12a07a (movR64R64Effect 0x12a07a 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x12a07a (fun s => s.RIP = 0x12a07a) (movR64R64Effect 0x12a07a 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.exec 0x12a07d (GoesTo (JmpMemPre 0x12a07d 6 (.rip 0xd9d85)) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85)) 0x129100) (jmpM64Effect 0x12a07d 6 (.rip 0xd9d85)) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l129100, RegMap.args [(0, 53), (1, 1), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l12a070 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x48, 0x8B, 0x37, 0x48, 0x8B, 0x57, 0x08, 0x48, 0x89, 0xC7, 0xFF, 0x25, 0x85,
    0x9D, 0x0D, 0x00]

theorem code_l12a070 : ∀ x ∈ codeRange 0x12a070 bytes_l12a070, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a070 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a100 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a100 (movR64M64Effect 0x12a100 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x12a100 (LoadPre 0x12a100 (fun s => AddrMode.addr (.base 6 .none) s (0x12a100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a100 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x12a103 (movR64M64Effect 0x12a103 6 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 56) (.exec 0x12a103 (LoadPre 0x12a103 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x12a103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a103 6 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x12a107 (movR64M64Effect 0x12a107 2 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 58) (.exec 0x12a107 (LoadPre 0x12a107 (fun s => AddrMode.addr (.base 7 .none) s (0x12a107 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a107 2 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x12a10a (movR64M64Effect 0x12a10a 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 60) (.exec 0x12a10a (LoadPre 0x12a10a (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x12a10a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x12a10a 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x12a10e (movR64R64Effect 0x12a10e 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 62) (.exec 0x12a10e (fun s => s.RIP = 0x12a10e) (movR64R64Effect 0x12a10e 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.exec 0x12a111 (GoesTo (JmpMemPre 0x12a111 6 (.rip 0xd9d11)) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11)) 0x1293a0) (jmpM64Effect 0x12a111 6 (.rip 0xd9d11)) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1293a0, RegMap.args [(0, 53), (1, 59), (2, 57), (3, 3), (4, 4), (5, 5), (6, 55), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l12a100 : List UInt8 :=
  [0x48, 0x8B, 0x06, 0x48, 0x8B, 0x76, 0x08, 0x48, 0x8B, 0x17, 0x48, 0x8B, 0x4F, 0x08, 0x48, 0x89,
    0xC7, 0xFF, 0x25, 0x11, 0x9D, 0x0D, 0x00]

theorem code_l12a100 : ∀ x ∈ codeRange 0x12a100 bytes_l12a100, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a100 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a430 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a430 (pushR64Effect 0x12a430 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x12a430 (PushPre 0x12a430 1) (pushR64Effect 0x12a430 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x12a431 (movR64R64Effect 0x12a431 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x12a431 (fun s => s.RIP = 0x12a431) (movR64R64Effect 0x12a431 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x12a434 (pushR64Effect 0x12a434 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 58) (.exec 0x12a434 (PushPre 0x12a434 1) (pushR64Effect 0x12a434 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 59) (.out 0x12a435 (subR64Imm8Effect 0x12a435 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x12a435 (fun s => s.RIP = 0x12a435) (subR64Imm8Effect 0x12a435 4 0x18) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x12a439 (movR64M64Effect 0x12a439 8 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 62) (.exec 0x12a439 (LoadPre 0x12a439 (fun s => AddrMode.addr (.base 7 .none) s (0x12a439 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x12a439 8 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x12a43c (movR32Imm32Effect 0x12a43c 5 0 0x14) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 64) (.exec 0x12a43c (fun s => s.RIP = 0x12a43c) (movR32Imm32Effect 0x12a43c 5 0 0x14) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x12a441 (leaR64Effect 0x12a441 7 (.rip 0xd97fb)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 66) (.exec 0x12a441 (fun s => s.RIP = 0x12a441) (leaR64Effect 0x12a441 7 (.rip 0xd97fb)) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x12a448 (movR64R64Effect 0x12a448 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 68) (.exec 0x12a448 (fun s => s.RIP = 0x12a448) (movR64R64Effect 0x12a448 2 8) (Reg.operands [.gpr 8] [])) #v[61]
    (.letOp (n := 69) (.out 0x12a44b (cmpR64Imm32Effect 0x12a44b 8 0x3e8) (EffectPart.reads (.flag .CF) [.gpr 8] []) (.flag .CF)) #v[61]
    (.letOp (n := 70) (.exec 0x12a44b (fun s => s.RIP = 0x12a44b) (cmpR64Imm32Effect 0x12a44b 8 0x3e8) (Reg.operands [.gpr 8] [])) #v[61]
    (.letOp (n := 71) (.pure (condOp 2)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l12a4c1, RegMap.args [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l12a454, RegMap.args [(0, 63), (1, 1), (2, 67), (3, 3), (4, 59), (5, 55), (6, 6), (7, 65), (8, 61), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l12a430 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x4C, 0x8B, 0x07, 0xB8, 0x14, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x3D, 0xFB, 0x97, 0x0D, 0x00, 0x4C, 0x89, 0xC2, 0x49, 0x81, 0xF8, 0xE8, 0x03,
    0x00, 0x00, 0x72, 0x6D]

theorem code_l12a430 : ∀ x ∈ codeRange 0x12a430 bytes_l12a430, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a430 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a454 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a454 (movR64Imm64Effect 0x12a454 9 0x346dc5d63886594b) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x12a454 (fun s => s.RIP = 0x12a454) (movR64Imm64Effect 0x12a454 9 0x346dc5d63886594b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12a45e (movR64R64Effect 0x12a45e 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 56) (.exec 0x12a45e (fun s => s.RIP = 0x12a45e) (movR64R64Effect 0x12a45e 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.exec 0x12a461 (fun s => s.RIP = 0x12a461) (fun _ => nopEffect 0x12a461 15) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l12a470, RegMap.args [(0, 0), (1, 55), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12a454 : List UInt8 :=
  [0x49, 0xB9, 0x4B, 0x59, 0x86, 0x38, 0xD6, 0xC5, 0x6D, 0x34, 0x4C, 0x89, 0xC1, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l12a454 : ∀ x ∈ codeRange 0x12a454 bytes_l12a454, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a454 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a470 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a470 (movR64R64Effect 0x12a470 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[0]
    (.letOp (n := 54) (.exec 0x12a470 (fun s => s.RIP = 0x12a470) (movR64R64Effect 0x12a470 10 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x12a473 (movR64R64Effect 0x12a473 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 56) (.exec 0x12a473 (fun s => s.RIP = 0x12a473) (movR64R64Effect 0x12a473 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x12a476 (mulR64Effect 0x12a476 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 55]
    (.letOp (n := 58) (.exec 0x12a476 (fun s => s.RIP = 0x12a476) (mulR64Effect 0x12a476 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 55]
    (.letOp (n := 59) (.out 0x12a479 (shrR64Effect 0x12a479 4 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x12a479 (fun s => s.RIP = 0x12a479) (shrR64Effect 0x12a479 4 2 11) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x12a47d (imulR32R32Imm32Effect 0x12a47d 6 0 2 0x2710) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x12a47d (fun s => s.RIP = 0x12a47d) (imulR32R32Imm32Effect 0x12a47d 6 0 2 0x2710) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 63) (.out 0x12a483 (movR32R32Effect 0x12a483 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[1]
    (.letOp (n := 64) (.exec 0x12a483 (fun s => s.RIP = 0x12a483) (movR32R32Effect 0x12a483 3 11 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x12a486 (subR32R32Effect 0x12a486 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x12a486 (fun s => s.RIP = 0x12a486) (subR32R32Effect 0x12a486 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x12a489 (imulR32R32Imm32Effect 0x12a489 7 0 11 0x147b) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 68) (.exec 0x12a489 (fun s => s.RIP = 0x12a489) (imulR32R32Imm32Effect 0x12a489 7 0 11 0x147b) (Reg.operands [.gpr 11] [])) #v[65]
    (.letOp (n := 69) (.out 0x12a490 (shrR32Effect 0x12a490 3 0 19) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x12a490 (fun s => s.RIP = 0x12a490) (shrR32Effect 0x12a490 3 0 19) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x12a493 (imulR32R32Imm8Effect 0x12a493 3 3 0 0x64) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.exec 0x12a493 (fun s => s.RIP = 0x12a493) (imulR32R32Imm8Effect 0x12a493 3 3 0 0x64) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x12a496 (subR32R32Effect 0x12a496 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[65, 71]
    (.letOp (n := 74) (.exec 0x12a496 (fun s => s.RIP = 0x12a496) (subR32R32Effect 0x12a496 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[65, 71]
    (.letOp (n := 75) (.out 0x12a499 (movzxR32M16Effect 0x12a499 4 0 (.sib 7 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[7, 69]
    (.letOp (n := 76) (.exec 0x12a499 (LoadPre 0x12a499 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a499 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a499 4 0 (.sib 7 (some 0) 1 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 69]
    (.letOp (n := 77) (.exec 0x12a49d (StorePre 0x12a49d 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe0)) s (0x12a49d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a49d 6 0 (.sib 5 (some 10) 0 (.d8 0xe0))) (Reg.operands [.gpr 0, .gpr 5, .gpr 10] [])) #v[75, 5, 53]
    (.letOp (n := 78) (.out 0x12a4a3 (movzxR32R16Effect 0x12a4a3 4 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 79) (.exec 0x12a4a3 (fun s => s.RIP = 0x12a4a3) (movzxR32R16Effect 0x12a4a3 4 0 11) (Reg.operands [.gpr 11] [])) #v[73]
    (.letOp (n := 80) (.out 0x12a4a7 (movzxR32M16Effect 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7, .gpr 0] []) (.reg (.gpr 0))) #v[7, 78]
    (.letOp (n := 81) (.exec 0x12a4a7 (LoadPre 0x12a4a7 (fun s => AddrMode.addr (.sib 7 (some 0) 1 .none) s (0x12a4a7 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4a7 4 0 (.sib 7 (some 0) 1 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 78]
    (.letOp (n := 82) (.exec 0x12a4ab (StorePre 0x12a4ab 6 (fun s => AddrMode.addr (.sib 5 (some 10) 0 (.d8 0xe2)) s (0x12a4ab + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x12a4ab 6 0 (.sib 5 (some 10) 0 (.d8 0xe2))) (Reg.operands [.gpr 0, .gpr 5, .gpr 10] [])) #v[80, 5, 53]
    (.letOp (n := 83) (.out 0x12a4b1 (leaR64Effect 0x12a4b1 0 (.base 10 (.d8 0xfc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 84) (.exec 0x12a4b1 (fun s => s.RIP = 0x12a4b1) (leaR64Effect 0x12a4b1 0 (.base 10 (.d8 0xfc))) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 85) (.out 0x12a4b5 (cmpR64Imm32Effect 0x12a4b5 1 0x98967f) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 86) (.out 0x12a4b5 (cmpR64Imm32Effect 0x12a4b5 1 0x98967f) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 87) (.exec 0x12a4b5 (fun s => s.RIP = 0x12a4b5) (cmpR64Imm32Effect 0x12a4b5 1 0x98967f) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 88) (.out 0x12a4bc (movR64R64Effect 0x12a4bc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 89) (.exec 0x12a4bc (fun s => s.RIP = 0x12a4bc) (movR64R64Effect 0x12a4bc 1 2) (Reg.operands [.gpr 2] [])) #v[59]
    (.letOp (n := 90) (.pure (condOp 7)) #v[85, 86]
    (.terminate (.condBr (Fin.last 90) ⟨.l12a470, RegMap.args [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l12a4c1, RegMap.args [(0, 83), (1, 88), (2, 59), (3, 71), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 53), (11, 73), (12, 12), (13, 13), (14, 14), (15, 15), (16, 85), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l12a470 : List UInt8 :=
  [0x49, 0x89, 0xC2, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE1, 0x48, 0xC1, 0xEA, 0x0B, 0x69, 0xC2, 0x10,
    0x27, 0x00, 0x00, 0x41, 0x89, 0xCB, 0x41, 0x29, 0xC3, 0x41, 0x69, 0xC3, 0x7B, 0x14, 0x00, 0x00,
    0xC1, 0xE8, 0x13, 0x6B, 0xD8, 0x64, 0x41, 0x29, 0xDB, 0x0F, 0xB7, 0x04, 0x47, 0x66, 0x42, 0x89,
    0x44, 0x15, 0xE0, 0x41, 0x0F, 0xB7, 0xC3, 0x0F, 0xB7, 0x04, 0x47, 0x66, 0x42, 0x89, 0x44, 0x15,
    0xE2, 0x49, 0x8D, 0x42, 0xFC, 0x48, 0x81, 0xF9, 0x7F, 0x96, 0x98, 0x00, 0x48, 0x89, 0xD1, 0x77,
    0xAF]

theorem code_l12a470 : ∀ x ∈ codeRange 0x12a470 bytes_l12a470, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a470 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a4c1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a4c1 (cmpR64Imm8Effect 0x12a4c1 2 0x9) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 54) (.out 0x12a4c1 (cmpR64Imm8Effect 0x12a4c1 2 0x9) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 55) (.exec 0x12a4c1 (fun s => s.RIP = 0x12a4c1) (cmpR64Imm8Effect 0x12a4c1 2 0x9) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 56) (.pure (condOp 6)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l12a4f2, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l12a4c7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l12a4c1 : List UInt8 :=
  [0x48, 0x83, 0xFA, 0x09, 0x76, 0x2B]

theorem code_l12a4c1 : ∀ x ∈ codeRange 0x12a4c1 bytes_l12a4c1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a4c1 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a4c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a4c7 (movR32R32Effect 0x12a4c7 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x12a4c7 (fun s => s.RIP = 0x12a4c7) (movR32R32Effect 0x12a4c7 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x12a4c9 (shrR32Effect 0x12a4c9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x12a4c9 (fun s => s.RIP = 0x12a4c9) (shrR32Effect 0x12a4c9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x12a4cc (movzxR32R16Effect 0x12a4cc 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x12a4cc (fun s => s.RIP = 0x12a4cc) (movzxR32R16Effect 0x12a4cc 3 1 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x12a4cf (imulR32R32Imm32Effect 0x12a4cf 6 1 1 0x147b) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x12a4cf (fun s => s.RIP = 0x12a4cf) (imulR32R32Imm32Effect 0x12a4cf 6 1 1 0x147b) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x12a4d5 (shrR32Effect 0x12a4d5 3 1 17) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x12a4d5 (fun s => s.RIP = 0x12a4d5) (shrR32Effect 0x12a4d5 3 1 17) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x12a4d8 (imulR32R32Imm8Effect 0x12a4d8 4 9 1 0x64) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 64) (.exec 0x12a4d8 (fun s => s.RIP = 0x12a4d8) (imulR32R32Imm8Effect 0x12a4d8 4 9 1 0x64) (Reg.operands [.gpr 1] [])) #v[61]
    (.letOp (n := 65) (.out 0x12a4dc (subR32R32Effect 0x12a4dc 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 66) (.exec 0x12a4dc (fun s => s.RIP = 0x12a4dc) (subR32R32Effect 0x12a4dc 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[2, 63]
    (.letOp (n := 67) (.out 0x12a4df (movzxR32R16Effect 0x12a4df 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 68) (.exec 0x12a4df (fun s => s.RIP = 0x12a4df) (movzxR32R16Effect 0x12a4df 3 2 2) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.out 0x12a4e2 (movzxR32M16Effect 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7, .gpr 2] []) (.reg (.gpr 2))) #v[7, 67]
    (.letOp (n := 70) (.exec 0x12a4e2 (LoadPre 0x12a4e2 (fun s => AddrMode.addr (.sib 7 (some 2) 1 .none) s (0x12a4e2 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x12a4e2 4 2 (.sib 7 (some 2) 1 .none)) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 67]
    (.letOp (n := 71) (.exec 0x12a4e6 (StorePre 0x12a4e6 5 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe2)) s (0x12a4e6 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x12a4e6 5 2 (.sib 5 (some 0) 0 (.d8 0xe2))) (Reg.operands [.gpr 2, .gpr 5, .gpr 0] [])) #v[69, 5, 0]
    (.letOp (n := 72) (.out 0x12a4eb (addR64Imm8Effect 0x12a4eb 0 0xfe) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 73) (.exec 0x12a4eb (fun s => s.RIP = 0x12a4eb) (addR64Imm8Effect 0x12a4eb 0 0xfe) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 74) (.out 0x12a4ef (movR64R64Effect 0x12a4ef 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 75) (.exec 0x12a4ef (fun s => s.RIP = 0x12a4ef) (movR64R64Effect 0x12a4ef 2 1) (Reg.operands [.gpr 1] [])) #v[61]
    (.terminate (.br ⟨.l12a4f2, RegMap.args [(0, 72), (1, 61), (2, 74), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 63), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l12a4c7 : List UInt8 :=
  [0x89, 0xD1, 0xC1, 0xE9, 0x02, 0x0F, 0xB7, 0xC9, 0x69, 0xC9, 0x7B, 0x14, 0x00, 0x00, 0xC1, 0xE9,
    0x11, 0x44, 0x6B, 0xC9, 0x64, 0x44, 0x29, 0xCA, 0x0F, 0xB7, 0xD2, 0x0F, 0xB7, 0x14, 0x57, 0x66,
    0x89, 0x54, 0x05, 0xE2, 0x48, 0x83, 0xC0, 0xFE, 0x48, 0x89, 0xCA]

theorem code_l12a4c7 : ∀ x ∈ codeRange 0x12a4c7 bytes_l12a4c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a4c7 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a4f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a4f2 (testR64R64Effect 0x12a4f2 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[8, 8]
    (.letOp (n := 54) (.exec 0x12a4f2 (fun s => s.RIP = 0x12a4f2) (testR64R64Effect 0x12a4f2 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12a4fc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12a4f7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12a4f2 : List UInt8 :=
  [0x4D, 0x85, 0xC0, 0x74, 0x05]

theorem code_l12a4f2 : ∀ x ∈ codeRange 0x12a4f2 bytes_l12a4f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a4f2 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a4f7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a4f7 (testR64R64Effect 0x12a4f7 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x12a4f7 (fun s => s.RIP = 0x12a4f7) (testR64R64Effect 0x12a4f7 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l12a508, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l12a4fc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l12a4f7 : List UInt8 :=
  [0x48, 0x85, 0xD2, 0x74, 0x0C]

theorem code_l12a4f7 : ∀ x ∈ codeRange 0x12a4f7 bytes_l12a4f7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a4f7 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a4fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a4fc (movzxR32M8Effect 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7, .gpr 2] []) (.reg (.gpr 1))) #v[7, 2]
    (.letOp (n := 54) (.exec 0x12a4fc (LoadPre 0x12a4fc (fun s => AddrMode.addr (.sib 7 (some 2) 1 (.d8 0x1)) s (0x12a4fc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x12a4fc 5 1 (.sib 7 (some 2) 1 (.d8 0x1))) (Reg.operands [.gpr 7, .gpr 2] [])) #v[7, 2]
    (.letOp (n := 55) (.exec 0x12a501 (StorePre 0x12a501 4 (fun s => AddrMode.addr (.sib 5 (some 0) 0 (.d8 0xe3)) s (0x12a501 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x12a501 4 1 (.sib 5 (some 0) 0 (.d8 0xe3))) (Reg.operands [.gpr 1, .gpr 5, .gpr 0] [])) #v[53, 5, 0]
    (.letOp (n := 56) (.out 0x12a505 (decR64Effect 0x12a505 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 57) (.exec 0x12a505 (fun s => s.RIP = 0x12a505) (decR64Effect 0x12a505 0) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[0]
    (.terminate (.br ⟨.l12a508, RegMap.args [(0, 56), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l12a4fc : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x57, 0x01, 0x88, 0x4C, 0x05, 0xE3, 0x48, 0xFF, 0xC8]

theorem code_l12a4fc : ∀ x ∈ codeRange 0x12a4fc bytes_l12a4fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a4fc 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a508 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a508 (movR32Imm32Effect 0x12a508 6 9 0x14) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 54) (.exec 0x12a508 (fun s => s.RIP = 0x12a508) (movR32Imm32Effect 0x12a508 6 9 0x14) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x12a50e (subR64R64Effect 0x12a50e 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x12a50e (fun s => s.RIP = 0x12a50e) (subR64R64Effect 0x12a50e 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.out 0x12a511 (leaR64Effect 0x12a511 8 (.sib 0 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 5] []) (.reg (.gpr 8))) #v[0, 5]
    (.letOp (n := 58) (.exec 0x12a511 (fun s => s.RIP = 0x12a511) (leaR64Effect 0x12a511 8 (.sib 0 (some 5) 0 .none)) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 59) (.out 0x12a515 (addR64Imm8Effect 0x12a515 8 0xe4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x12a515 (fun s => s.RIP = 0x12a515) (addR64Imm8Effect 0x12a515 8 0xe4) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x12a519 (movR32Imm32Effect 0x12a519 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 62) (.exec 0x12a519 (fun s => s.RIP = 0x12a519) (movR32Imm32Effect 0x12a519 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x12a51e (movR64R64Effect 0x12a51e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x12a51e (fun s => s.RIP = 0x12a51e) (movR64R64Effect 0x12a51e 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x12a521 (movR32Imm32Effect 0x12a521 5 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 66) (.exec 0x12a521 (fun s => s.RIP = 0x12a521) (movR32Imm32Effect 0x12a521 5 6 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x12a526 (xorR32R32Effect 0x12a526 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 68) (.exec 0x12a526 (fun s => s.RIP = 0x12a526) (xorR32R32Effect 0x12a526 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 69) (.out 0x12a528 (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x12a528 (GoesTo (CallMemPre 0x12a528 (.rip 0xd98ba)) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) 0x128b20) (callEffect (callMemPtr 0x12a528 (.rip 0xd98ba)) (0x12a528 + BitVec.ofNat 64 (callMemLen (.rip 0xd98ba)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x12a52e⟩) #v[]
    (.terminate (.call ⟨.l128b20, RegMap.args [(0, 0), (1, 67), (2, 61), (3, 3), (4, 69), (5, 5), (6, 65), (7, 63), (8, 59), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l12a52e, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l12a508 : List UInt8 :=
  [0x41, 0xB9, 0x14, 0x00, 0x00, 0x00, 0x49, 0x29, 0xC1, 0x4C, 0x8D, 0x04, 0x28, 0x49, 0x83, 0xC0,
    0xE4, 0xBA, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF7, 0xBE, 0x01, 0x00, 0x00, 0x00, 0x31, 0xC9,
    0xFF, 0x15, 0xBA, 0x98, 0x0D, 0x00]

theorem code_l12a508 : ∀ x ∈ codeRange 0x12a508 bytes_l12a508, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a508 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a52e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a52e (addR64Imm8Effect 0x12a52e 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x12a52e (fun s => s.RIP = 0x12a52e) (addR64Imm8Effect 0x12a52e 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x12a532 (popR64Effect 0x12a532 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x12a532 (popR64Effect 0x12a532 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x12a532 (PopPre 0x12a532) (popR64Effect 0x12a532 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x12a533 (popR64Effect 0x12a533 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 59) (.out 0x12a533 (popR64Effect 0x12a533 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x12a533 (PopPre 0x12a533) (popR64Effect 0x12a533 1 5) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x12a534 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[59]
    (.letOp (n := 62) (.out 0x12a534 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x12a534 (RetPre 0x12a534) (retEffect) (Reg.operands [.gpr 4] [])) #v[59]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 62), (5, 58), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l12a52e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x18, 0x5B, 0x5D, 0xC3]

theorem code_l12a52e : ∀ x ∈ codeRange 0x12a52e bytes_l12a52e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a52e 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l12a820 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x12a820 (movR64R64Effect 0x12a820 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x12a820 (fun s => s.RIP = 0x12a820) (movR64R64Effect 0x12a820 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x12a823 (movR32R32Effect 0x12a823 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x12a823 (fun s => s.RIP = 0x12a823) (movR32R32Effect 0x12a823 3 8 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x12a826 (negR32Effect 0x12a826 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x12a826 (fun s => s.RIP = 0x12a826) (negR32Effect 0x12a826 3 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x12a829 (andR32Imm8Effect 0x12a829 4 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x12a829 (fun s => s.RIP = 0x12a829) (andR32Imm8Effect 0x12a829 4 8 0x7) (Reg.operands [.gpr 8] [])) #v[57]
    (.letOp (n := 61) (.out 0x12a82d (cmpR64R64Effect 0x12a82d 2 8) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 8] []) (.flag .CF)) #v[2, 59]
    (.letOp (n := 62) (.exec 0x12a82d (fun s => s.RIP = 0x12a82d) (cmpR64R64Effect 0x12a82d 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 59]
    (.letOp (n := 63) (.out 0x12a830 (atFlags (condHolds 2) (cmovR64R64Effect 0x12a830 4 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[59, 2, 61]
    (.letOp (n := 64) (.exec 0x12a830 (fun s => s.RIP = 0x12a830) (atFlags (condHolds 2) (cmovR64R64Effect 0x12a830 4 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[59, 2, 61]
    (.letOp (n := 65) (.out 0x12a834 (movR64R64Effect 0x12a834 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x12a834 (fun s => s.RIP = 0x12a834) (movR64R64Effect 0x12a834 1 8) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.out 0x12a837 (repMovsbEffect 0x12a837) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[6, 7, 65, 22]
    (.letOp (n := 68) (.out 0x12a837 (repMovsbEffect 0x12a837) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[6, 7, 65, 22]
    (.letOp (n := 69) (.exec 0x12a837 (RepPre 0x12a837 (RepMovsbPre 0x12a837)) (repMovsbEffect 0x12a837) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[6, 7, 65, 22]
    (.letOp (n := 70) (.out 0x12a839 (subR64R64Effect 0x12a839 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 63]
    (.letOp (n := 71) (.exec 0x12a839 (fun s => s.RIP = 0x12a839) (subR64R64Effect 0x12a839 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 63]
    (.letOp (n := 72) (.out 0x12a83c (movR64R64Effect 0x12a83c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[70]
    (.letOp (n := 73) (.exec 0x12a83c (fun s => s.RIP = 0x12a83c) (movR64R64Effect 0x12a83c 1 2) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 74) (.out 0x12a83f (shrR64Effect 0x12a83f 4 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[72]
    (.letOp (n := 75) (.exec 0x12a83f (fun s => s.RIP = 0x12a83f) (shrR64Effect 0x12a83f 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[72]
    (.letOp (n := 76) (.out 0x12a843 (repMovsqEffect 0x12a843) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[67, 68, 74, 22]
    (.letOp (n := 77) (.out 0x12a843 (repMovsqEffect 0x12a843) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[67, 68, 74, 22]
    (.letOp (n := 78) (.exec 0x12a843 (RepPre 0x12a843 (RepMovsqPre 0x12a843)) (repMovsqEffect 0x12a843) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[67, 68, 74, 22]
    (.letOp (n := 79) (.out 0x12a846 (andR32Imm8Effect 0x12a846 3 2 0x7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[70]
    (.letOp (n := 80) (.exec 0x12a846 (fun s => s.RIP = 0x12a846) (andR32Imm8Effect 0x12a846 3 2 0x7) (Reg.operands [.gpr 2] [])) #v[70]
    (.letOp (n := 81) (.out 0x12a849 (movR64R64Effect 0x12a849 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x12a849 (fun s => s.RIP = 0x12a849) (movR64R64Effect 0x12a849 1 2) (Reg.operands [.gpr 2] [])) #v[79]
    (.letOp (n := 83) (.out 0x12a84c (repMovsbEffect 0x12a84c) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[76, 77, 81, 22]
    (.letOp (n := 84) (.out 0x12a84c (repMovsbEffect 0x12a84c) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 7))) #v[76, 77, 81, 22]
    (.letOp (n := 85) (.out 0x12a84c (repMovsbEffect 0x12a84c) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[76, 77, 81, 22]
    (.letOp (n := 86) (.exec 0x12a84c (RepPre 0x12a84c (RepMovsbPre 0x12a84c)) (repMovsbEffect 0x12a84c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[76, 77, 81, 22]
    (.letOp (n := 87) (.out 0x12a84e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 88) (.out 0x12a84e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x12a84e (RetPre 0x12a84e) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 85), (2, 79), (3, 3), (4, 88), (5, 5), (6, 83), (7, 84), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90) (some ⟨87, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l12a820 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x41, 0x89, 0xC0, 0x41, 0xF7, 0xD8, 0x41, 0x83, 0xE0, 0x07, 0x4C, 0x39, 0xC2,
    0x4C, 0x0F, 0x42, 0xC2, 0x4C, 0x89, 0xC1, 0xF3, 0xA4, 0x4C, 0x29, 0xC2, 0x48, 0x89, 0xD1, 0x48,
    0xC1, 0xE9, 0x03, 0xF3, 0x48, 0xA5, 0x83, 0xE2, 0x07, 0x48, 0x89, 0xD1, 0xF3, 0xA4, 0xC3]

theorem code_l12a820 : ∀ x ∈ codeRange 0x12a820 bytes_l12a820, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a820 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Generate.LIR
