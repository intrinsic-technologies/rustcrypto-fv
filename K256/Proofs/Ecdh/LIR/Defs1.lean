import K256.Proofs.Ecdh.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Ecdh.LIR.Generated.Footprints

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

@[cfg_block] def b_l100a20 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l100a20, RegMap.args (entryMap (live .l100a20)) 53⟩)

def bytes_l100a20 : List UInt8 :=
  [0xEB, 0xFE]

theorem code_l100a20 : ∀ x ∈ codeRange 0x100a20 bytes_l100a20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa20 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100a30 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l100a30, RegMap.args (entryMap (live .l100a30)) 53⟩)

def bytes_l100a30 : List UInt8 :=
  [0xEB, 0xFE]

theorem code_l100a30 : ∀ x ∈ codeRange 0x100a30 bytes_l100a30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa30 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101660_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x1016b1 (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[68]
    (.letOp (n := 89) (.exec 0x1016b1 (fun s => s.RIP = 0x1016b1) (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 90) (.out 0x1016b6 (movR64R64Effect 0x1016b6 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[86]
    (.letOp (n := 91) (.exec 0x1016b6 (fun s => s.RIP = 0x1016b6) (movR64R64Effect 0x1016b6 7 15) (Reg.operands [.gpr 15] [])) #v[86]
    (.letOp (n := 92) (.out 0x1016b9 (callEffect (fun _ => 0x109e60) 0x1016be) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 93) (.exec 0x1016b9 (PushPre 0x1016b9 5) (callEffect (fun _ => 0x109e60) 0x1016be) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 94) (.const ⟨64, 0x1016be⟩) #v[]
    (.terminate (.call ⟨.l109e60, RegMap.args [(0, 80), (1, 82), (2, 2), (3, 72), (4, 92), (5, 5), (6, 88), (7, 90), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 70), (15, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 95⟩ { target := .l1016be, kept := #v[], arity := rfl, guard := some (Fin.last 94) }))))))))

def bytes_l101660_1 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x58, 0x4C, 0x89, 0xFF, 0xE8, 0xA2, 0x87, 0x00, 0x00]

theorem code_l101660_1 : ∀ x ∈ codeRange 0x1016b1 bytes_l101660_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16b1 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101660 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101660 (pushR64Effect 0x101660 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101660 (PushPre 0x101660 1) (pushR64Effect 0x101660 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101661 (pushR64Effect 0x101661 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101661 (PushPre 0x101661 2) (pushR64Effect 0x101661 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101663 (pushR64Effect 0x101663 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101663 (PushPre 0x101663 2) (pushR64Effect 0x101663 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101665 (pushR64Effect 0x101665 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101665 (PushPre 0x101665 2) (pushR64Effect 0x101665 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101667 (pushR64Effect 0x101667 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101667 (PushPre 0x101667 2) (pushR64Effect 0x101667 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101669 (pushR64Effect 0x101669 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101669 (PushPre 0x101669 1) (pushR64Effect 0x101669 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10166a (subR64Imm32Effect 0x10166a 4 0x1000) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10166a (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x1000) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x101671 (StorePre 0x101671 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101671 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101671 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 68) (.out 0x101679 (subR64Imm32Effect 0x101679 4 0x7d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x101679 (fun s => s.RIP = 0x101679) (subR64Imm32Effect 0x101679 4 0x7d8) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x101680 (movR64R64Effect 0x101680 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 71) (.exec 0x101680 (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 72) (.out 0x101683 (movR64R64Effect 0x101683 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 73) (.exec 0x101683 (fun s => s.RIP = 0x101683) (movR64R64Effect 0x101683 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 74) (.out 0x101686 (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 75) (.exec 0x101686 (LoadPre 0x101686 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101686 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.exec 0x10168a (StorePre 0x10168a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10168a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10168a 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 68]
    (.letOp (n := 77) (.out 0x10168f (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 78) (.exec 0x10168f (LoadPre 0x10168f (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10168f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.exec 0x101693 (StorePre 0x101693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101693 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 68]
    (.letOp (n := 80) (.out 0x101698 (movR64M64Effect 0x101698 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 81) (.exec 0x101698 (LoadPre 0x101698 (fun s => AddrMode.addr (.base 6 .none) s (0x101698 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101698 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.out 0x10169b (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 83) (.exec 0x10169b (LoadPre 0x10169b (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10169b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 84) (.exec 0x10169f (StorePre 0x10169f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10169f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10169f 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[82, 68]
    (.letOp (n := 85) (.exec 0x1016a4 (StorePre 0x1016a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1016a4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016a4 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 68]
    (.letOp (n := 86) (.out 0x1016a9 (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[68]
    (.letOp (n := 87) (.exec 0x1016a9 (fun s => s.RIP = 0x1016a9) (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[68]
    (b_l101660_1)))))))))))))))))))))))))))))))))))

def bytes_l101660 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x00, 0x10, 0x00,
    0x00, 0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xEC, 0xD8, 0x07, 0x00, 0x00,
    0x49, 0x89, 0xD6, 0x48, 0x89, 0xFB, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x70, 0x48,
    0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48,
    0x89, 0x4C, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x58, 0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00,
    0x00] ++ bytes_l101660_1

theorem code_l101660 : ∀ x ∈ codeRange 0x101660 bytes_l101660, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1660 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101660_1

@[cfg_block] def b_l1016be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1016be (StorePre 0x1016be 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8f0)) s (0x1016be + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016be (.sib 4 none 0 (.d32 0x8f0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1016ca (StorePre 0x1016ca 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e8)) s (0x1016ca + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016ca (.sib 4 none 0 (.d32 0x8e8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1016d6 (StorePre 0x1016d6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e0)) s (0x1016d6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016d6 (.sib 4 none 0 (.d32 0x8e0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1016e2 (StorePre 0x1016e2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8d8)) s (0x1016e2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1016e2 (.sib 4 none 0 (.d32 0x8d8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1016ee (movR32M32LowEffect 0x1016ee 5 (.sib 4 none 0 (.d32 0x178))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x1016ee (LoadPre 0x1016ee (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x178)) s (0x1016ee + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1016ee 5 (.sib 4 none 0 (.d32 0x178))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1016f5 (leaR64Effect 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 60) (.exec 0x1016f5 (fun s => s.RIP = 0x1016f5) (leaR64Effect 0x1016f5 12 (.sib 4 none 0 (.d32 0xc98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1016fd (leaR64Effect 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1016fd (fun s => s.RIP = 0x1016fd) (leaR64Effect 0x1016fd 6 (.sib 4 none 0 (.d32 0x8d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x101705 (movR64R64Effect 0x101705 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 64) (.exec 0x101705 (fun s => s.RIP = 0x101705) (movR64R64Effect 0x101705 7 12) (Reg.operands [.gpr 12] [])) #v[59]
    (.letOp (n := 65) (.out 0x101708 (movR64R64Effect 0x101708 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 66) (.exec 0x101708 (fun s => s.RIP = 0x101708) (movR64R64Effect 0x101708 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 67) (.out 0x10170b (movR32R32Effect 0x10170b 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 68) (.exec 0x10170b (fun s => s.RIP = 0x10170b) (movR32R32Effect 0x10170b 2 1 5) (Reg.operands [.gpr 5] [])) #v[57]
    (.letOp (n := 69) (.out 0x10170d (callEffect (fun _ => 0x10a220) 0x101712) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x10170d (PushPre 0x10170d 5) (callEffect (fun _ => 0x10a220) 0x101712) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101712⟩) #v[]
    (.terminate (.call ⟨.l10a220, RegMap.args [(1, 67), (2, 65), (3, 3), (4, 69), (5, 57), (6, 61), (7, 63), (12, 59), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101712, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1016be : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xF0, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xE8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0, 0x08, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x8B, 0xAC, 0x24, 0x78, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xA4, 0x24, 0x98, 0x0C, 0x00, 0x00, 0x48,
    0x8D, 0xB4, 0x24, 0xD8, 0x08, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xFA, 0x89, 0xE9, 0xE8,
    0x0E, 0x8B, 0x00, 0x00]

theorem code_l1016be : ∀ x ∈ codeRange 0x1016be bytes_l1016be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16be 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101712 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101712 (StorePre 0x101712 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1070)) s (0x101712 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101712 (.sib 4 none 0 (.d32 0x1070)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10171e (StorePre 0x10171e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1068)) s (0x10171e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10171e (.sib 4 none 0 (.d32 0x1068)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10172a (StorePre 0x10172a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1060)) s (0x10172a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10172a (.sib 4 none 0 (.d32 0x1060)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x101736 (StorePre 0x101736 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1058)) s (0x101736 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101736 (.sib 4 none 0 (.d32 0x1058)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101742 (leaR64Effect 0x101742 6 (.sib 4 none 0 (.d32 0x1058))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x101742 (fun s => s.RIP = 0x101742) (leaR64Effect 0x101742 6 (.sib 4 none 0 (.d32 0x1058))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10174a (movR64R64Effect 0x10174a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 60) (.exec 0x10174a (fun s => s.RIP = 0x10174a) (movR64R64Effect 0x10174a 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x10174d (callEffect (fun _ => 0x10a280) 0x101752) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10174d (PushPre 0x10174d 5) (callEffect (fun _ => 0x10a280) 0x101752) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x101752⟩) #v[]
    (.terminate (.call ⟨.l10a280, RegMap.args [(0, 0), (3, 3), (4, 61), (5, 5), (6, 57), (7, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l101752, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l101712 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0x70, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0x68, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x60, 0x10, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0xE8, 0x2E, 0x8B, 0x00, 0x00]

theorem code_l101712 : ∀ x ∈ codeRange 0x101712 bytes_l101712, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1712 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101752 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101752 (notR8Effect 0x101752 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x101752 (fun s => s.RIP = 0x101752) (notR8Effect 0x101752 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x101754 (andAlImm8Effect 0x101754 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x101754 (fun s => s.RIP = 0x101754) (andAlImm8Effect 0x101754 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x101756 (movzxR32R8Effect 0x101756 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x101756 (fun s => s.RIP = 0x101756) (movzxR32R8Effect 0x101756 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x101759 (callEffect (fun _ => 0x127d50) 0x10175e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101759 (PushPre 0x101759 5) (callEffect (fun _ => 0x127d50) 0x10175e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10175e⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10175e, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101752 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xF2, 0x65, 0x02, 0x00]

theorem code_l101752 : ∀ x ∈ codeRange 0x101752 bytes_l101752, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1752 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10175e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10175e (movR64M64Effect 0x10175e 1 (.sib 4 none 0 (.d32 0xc98))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x10175e (LoadPre 0x10175e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc98)) s (0x10175e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10175e 1 (.sib 4 none 0 (.d32 0xc98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101766 (movR64M64Effect 0x101766 2 (.sib 4 none 0 (.d32 0xca0))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x101766 (LoadPre 0x101766 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca0)) s (0x101766 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101766 2 (.sib 4 none 0 (.d32 0xca0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10176e (StorePre 0x10176e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10176e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10176e 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x101776 (StorePre 0x101776 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x101776 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101776 2 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x10177e (movR64M64Effect 0x10177e 1 (.sib 4 none 0 (.d32 0xca8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x10177e (LoadPre 0x10177e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca8)) s (0x10177e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10177e 1 (.sib 4 none 0 (.d32 0xca8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101786 (StorePre 0x101786 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x101786 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101786 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10178e (movR64M64Effect 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x10178e (LoadPre 0x10178e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb0)) s (0x10178e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10178e 1 (.sib 4 none 0 (.d32 0xcb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x101796 (StorePre 0x101796 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x101796 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101796 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x10179e (andR8R8Effect 0x10179e 3 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[0, 5]
    (.letOp (n := 66) (.exec 0x10179e (fun s => s.RIP = 0x10179e) (andR8R8Effect 0x10179e 3 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 67) (.out 0x1017a1 (movzxR32R8Effect 0x1017a1 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 68) (.exec 0x1017a1 (fun s => s.RIP = 0x1017a1) (movzxR32R8Effect 0x1017a1 3 7 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 69) (.out 0x1017a4 (callEffect (fun _ => 0x127d50) 0x1017a9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x1017a4 (PushPre 0x1017a4 5) (callEffect (fun _ => 0x127d50) 0x1017a9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x1017a9⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 65), (1, 62), (2, 55), (3, 3), (4, 69), (5, 5), (6, 6), (7, 67), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l1017a9, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l10175e : List UInt8 :=
  [0x48, 0x8B, 0x8C, 0x24, 0x98, 0x0C, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0xA0, 0x0C, 0x00, 0x00,
    0x48, 0x89, 0x8C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xA8, 0x0C, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x0C, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00,
    0x40, 0x20, 0xE8, 0x0F, 0xB6, 0xF8, 0xE8, 0xA7, 0x65, 0x02, 0x00]

theorem code_l10175e : ∀ x ∈ codeRange 0x10175e bytes_l10175e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x175e 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1017a9 (cmpAlImm8Effect 0x1017a9 0x1) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x1017a9 (fun s => s.RIP = 0x1017a9) (cmpAlImm8Effect 0x1017a9 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101c5e, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1017b1, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1017a9 : List UInt8 :=
  [0x3C, 0x01, 0x0F, 0x85, 0xAD, 0x04, 0x00, 0x00]

theorem code_l1017a9 : ∀ x ∈ codeRange 0x1017a9 bytes_l1017a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x17a9 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017b1_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x10181e (callEffect (fun _ => 0x120f30) 0x101823) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 85) (.exec 0x10181e (PushPre 0x10181e 5) (callEffect (fun _ => 0x120f30) 0x101823) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.const ⟨64, 0x101823⟩) #v[]
    (.terminate (.call ⟨.l120f30, RegMap.args [(0, 74), (1, 76), (3, 3), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩ { target := .l101823, kept := #v[], arity := rfl, guard := some (Fin.last 86) }))))

def bytes_l1017b1_1 : List UInt8 :=
  [0xE8, 0x0D, 0xF7, 0x01, 0x00]

theorem code_l1017b1_1 : ∀ x ∈ codeRange 0x10181e bytes_l1017b1_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x181e 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1017b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1017b1 (movR64M64Effect 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1017b1 (LoadPre 0x1017b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1017b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017b1 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1017b9 (StorePre 0x1017b9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1017b9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017b9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1017be (movR64M64Effect 0x1017be 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1017be (LoadPre 0x1017be (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1017be + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017be 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1017c6 (StorePre 0x1017c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1017c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017c6 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1017cb (movR64M64Effect 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1017cb (LoadPre 0x1017cb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1017cb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017cb 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1017d3 (movR64M64Effect 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x1017d3 (LoadPre 0x1017d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1017d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1017d3 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1017db (StorePre 0x1017db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1017db + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017db 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x1017e0 (StorePre 0x1017e0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1017e0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017e0 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x1017e5 (movzxR32M8Effect 0x1017e5 5 0 (.base 14 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 66) (.exec 0x1017e5 (LoadPre 0x1017e5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1017e5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1017e5 5 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.exec 0x1017ea (StorePre 0x1017ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1017ea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1017ea 4 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1017ee (movR64M64Effect 0x1017ee 0 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 69) (.exec 0x1017ee (LoadPre 0x1017ee (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x1017ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017ee 0 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 70) (.exec 0x1017f2 (StorePre 0x1017f2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1017f2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017f2 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1017f7 (movR64M64Effect 0x1017f7 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 72) (.exec 0x1017f7 (LoadPre 0x1017f7 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x1017f7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1017f7 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.exec 0x1017fb (StorePre 0x1017fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1017fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1017fb 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x101800 (movR64M64Effect 0x101800 0 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 75) (.exec 0x101800 (LoadPre 0x101800 (fun s => AddrMode.addr (.base 14 .none) s (0x101800 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101800 0 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 76) (.out 0x101803 (movR64M64Effect 0x101803 1 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 77) (.exec 0x101803 (LoadPre 0x101803 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101803 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101803 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 78) (.exec 0x101807 (StorePre 0x101807 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101807 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101807 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.exec 0x10180c (StorePre 0x10180c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10180c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10180c 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 80) (.out 0x101811 (leaR64Effect 0x101811 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 81) (.exec 0x101811 (fun s => s.RIP = 0x101811) (leaR64Effect 0x101811 7 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x101819 (leaR64Effect 0x101819 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 83) (.exec 0x101819 (fun s => s.RIP = 0x101819) (leaR64Effect 0x101819 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1017b1_1)))))))))))))))))))))))))))))))

def bytes_l1017b1 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xC0, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x41, 0x0F, 0xB6, 0x46, 0x20, 0x88, 0x44, 0x24, 0x50, 0x49, 0x8B, 0x46,
    0x18, 0x48, 0x89, 0x44, 0x24, 0x48, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x40, 0x49,
    0x8B, 0x06, 0x49, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x30,
    0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x30] ++ bytes_l1017b1_1

theorem code_l1017b1 : ∀ x ∈ codeRange 0x1017b1 bytes_l1017b1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x17b1 109 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1017b1_1

@[cfg_block] def b_l101823 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101823 (cmpM8Imm8Effect 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101823 (LoadPre 0x101823 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1b0)) s (0x101823 + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x101823 8 (.sib 4 none 0 (.d32 0x1b0)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101c5e, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101831, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101823 : List UInt8 :=
  [0x80, 0xBC, 0x24, 0xB0, 0x01, 0x00, 0x00, 0x01, 0x0F, 0x85, 0x2D, 0x04, 0x00, 0x00]

theorem code_l101823 : ∀ x ∈ codeRange 0x101823 bytes_l101823, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1823 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101831 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101831 (leaR64Effect 0x101831 0 (.sib 4 none 0 (.d32 0x1058))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101831 (fun s => s.RIP = 0x101831) (leaR64Effect 0x101831 0 (.sib 4 none 0 (.d32 0x1058))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101839 (leaR64Effect 0x101839 6 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x101839 (fun s => s.RIP = 0x101839) (leaR64Effect 0x101839 6 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101841 (movR32Imm32Effect 0x101841 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x101841 (fun s => s.RIP = 0x101841) (movR32Imm32Effect 0x101841 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x101846 (movR64R64Effect 0x101846 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x101846 (fun s => s.RIP = 0x101846) (movR64R64Effect 0x101846 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.out 0x101849 (repMovsqEffect 0x101849) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[55, 59, 57, 22]
    (.letOp (n := 62) (.exec 0x101849 (RepPre 0x101849 (RepMovsqPre 0x101849)) (repMovsqEffect 0x101849) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 59, 57, 22]
    (.letOp (n := 63) (.out 0x10184c (leaR64Effect 0x10184c 15 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 64) (.exec 0x10184c (fun s => s.RIP = 0x10184c) (leaR64Effect 0x10184c 15 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x101854 (movR64R64Effect 0x101854 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x101854 (fun s => s.RIP = 0x101854) (movR64R64Effect 0x101854 7 15) (Reg.operands [.gpr 15] [])) #v[63]
    (.letOp (n := 67) (.out 0x101857 (movR64R64Effect 0x101857 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 68) (.exec 0x101857 (fun s => s.RIP = 0x101857) (movR64R64Effect 0x101857 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 69) (.out 0x10185a (callEffect (fun _ => 0x10fa10) 0x10185f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x10185a (PushPre 0x10185a 5) (callEffect (fun _ => 0x10fa10) 0x10185f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x10185f⟩) #v[]
    (.terminate (.call ⟨.l10fa10, RegMap.args [(0, 53), (1, 61), (2, 2), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10185f, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101831 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0x58, 0x10, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x58, 0x01, 0x00, 0x00,
    0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0xBC, 0x24, 0x58,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0x89, 0xC6, 0xE8, 0xB1, 0xE1, 0x00, 0x00]

theorem code_l101831 : ∀ x ∈ codeRange 0x101831 bytes_l101831, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1831 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10185f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10185f (movR64M64Effect 0x10185f 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10185f (LoadPre 0x10185f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10185f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10185f 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101864 (movR64M64Effect 0x101864 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101864 (LoadPre 0x101864 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101864 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101864 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101869 (StorePre 0x101869 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d0)) s (0x101869 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101869 0 (.sib 4 none 0 (.d32 0x1d0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x101871 (StorePre 0x101871 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1d8)) s (0x101871 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101871 1 (.sib 4 none 0 (.d32 0x1d8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x101879 (movR64M64Effect 0x101879 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101879 (LoadPre 0x101879 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101879 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101879 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10187e (StorePre 0x10187e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e0)) s (0x10187e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10187e 0 (.sib 4 none 0 (.d32 0x1e0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x101886 (movR64M64Effect 0x101886 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x101886 (LoadPre 0x101886 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101886 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101886 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10188b (StorePre 0x10188b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x1e8)) s (0x10188b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10188b 0 (.sib 4 none 0 (.d32 0x1e8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x101893 (leaR64Effect 0x101893 14 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 66) (.exec 0x101893 (fun s => s.RIP = 0x101893) (leaR64Effect 0x101893 14 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10189b (leaR64Effect 0x10189b 13 (.rip 0x28f7e)) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 68) (.exec 0x10189b (fun s => s.RIP = 0x10189b) (leaR64Effect 0x10189b 13 (.rip 0x28f7e)) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x1018a2 (movR32Imm32Effect 0x1018a2 5 2 0x98) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 70) (.exec 0x1018a2 (fun s => s.RIP = 0x1018a2) (movR32Imm32Effect 0x1018a2 5 2 0x98) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x1018a7 (movR64R64Effect 0x1018a7 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x1018a7 (fun s => s.RIP = 0x1018a7) (movR64R64Effect 0x1018a7 7 14) (Reg.operands [.gpr 14] [])) #v[65]
    (.letOp (n := 73) (.out 0x1018aa (movR64R64Effect 0x1018aa 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 74) (.exec 0x1018aa (fun s => s.RIP = 0x1018aa) (movR64R64Effect 0x1018aa 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 75) (.out 0x1018ad (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 67]
    (.letOp (n := 76) (.exec 0x1018ad (GoesTo (CallPre 0x1018ad 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x1018b0) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 67]
    (.letOp (n := 77) (.const ⟨64, 0x1018b0⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 62), (1, 55), (2, 69), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l1018b0, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10185f : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xD8, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48,
    0x89, 0x84, 0x24, 0xE0, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
    0xE8, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x2D, 0x7E,
    0x8F, 0x02, 0x00, 0xBA, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFE, 0x41, 0xFF,
    0xD5]

theorem code_l10185f : ∀ x ∈ codeRange 0x10185f bytes_l10185f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x185f 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1018b0_3 : Block Op Label signature Reg.count 159 :=
  .letOp (n := 159) (.out 0x101a05 (movR64Imm32Effect 0x101a05 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 160) (.exec 0x101a05 (fun s => s.RIP = 0x101a05) (movR64Imm32Effect 0x101a05 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 161) (.exec 0x101a0c (RepPre 0x101a0c (RepMovsqPre 0x101a0c)) (repMovsqEffect 0x101a0c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[159, 155, 157, 22]
    (.letOp (n := 162) (.out 0x101a0f (leaR64Effect 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 163) (.exec 0x101a0f (fun s => s.RIP = 0x101a0f) (leaR64Effect 0x101a0f 7 (.sib 4 none 0 (.d32 0xfe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x101a17 (movR32Imm32Effect 0x101a17 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 165) (.exec 0x101a17 (fun s => s.RIP = 0x101a17) (movR32Imm32Effect 0x101a17 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 166) (.out 0x101a1c (movR64Imm32Effect 0x101a1c 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 167) (.exec 0x101a1c (fun s => s.RIP = 0x101a1c) (movR64Imm32Effect 0x101a1c 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 168) (.exec 0x101a23 (RepPre 0x101a23 (RepMovsqPre 0x101a23)) (repMovsqEffect 0x101a23) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[166, 162, 164, 22]
    (.letOp (n := 169) (.out 0x101a26 (leaR64Effect 0x101a26 12 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 170) (.exec 0x101a26 (fun s => s.RIP = 0x101a26) (leaR64Effect 0x101a26 12 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 171) (.out 0x101a2e (movR32Imm32Effect 0x101a2e 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 172) (.exec 0x101a2e (fun s => s.RIP = 0x101a2e) (movR32Imm32Effect 0x101a2e 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 173) (.out 0x101a33 (movR64R64Effect 0x101a33 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[169]
    (.letOp (n := 174) (.exec 0x101a33 (fun s => s.RIP = 0x101a33) (movR64R64Effect 0x101a33 7 12) (Reg.operands [.gpr 12] [])) #v[169]
    (.letOp (n := 175) (.out 0x101a36 (movR64R64Effect 0x101a36 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 176) (.exec 0x101a36 (fun s => s.RIP = 0x101a36) (movR64R64Effect 0x101a36 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 177) (.out 0x101a39 (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 178) (.exec 0x101a39 (GoesTo (CallPre 0x101a39 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a3c) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 179) (.const ⟨64, 0x101a3c⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 53), (2, 171), (3, 3), (4, 177), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)] 180⟩ { target := .l101a3c, kept := #v[], arity := rfl, guard := some (Fin.last 179) }))))))))))))))))))))))

def bytes_l1018b0_3 : List UInt8 :=
  [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x0F,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x4C, 0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89,
    0xE7, 0x48, 0x89, 0xC6, 0x41, 0xFF, 0xD5]

theorem code_l1018b0_3 : ∀ x ∈ codeRange 0x101a05 bytes_l1018b0_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a05 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1018b0_2 : Block Op Label signature Reg.count 124 :=
  .letOp (n := 124) (.out 0x101992 (movR64Imm32Effect 0x101992 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 125) (.exec 0x101992 (fun s => s.RIP = 0x101992) (movR64Imm32Effect 0x101992 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 126) (.exec 0x101999 (RepPre 0x101999 (RepMovsqPre 0x101999)) (repMovsqEffect 0x101999) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[124, 120, 122, 22]
    (.letOp (n := 127) (.out 0x10199c (leaR64Effect 0x10199c 7 (.sib 4 none 0 (.d32 0xd88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 128) (.exec 0x10199c (fun s => s.RIP = 0x10199c) (leaR64Effect 0x10199c 7 (.sib 4 none 0 (.d32 0xd88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 129) (.out 0x1019a4 (movR32Imm32Effect 0x1019a4 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 130) (.exec 0x1019a4 (fun s => s.RIP = 0x1019a4) (movR32Imm32Effect 0x1019a4 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 131) (.out 0x1019a9 (movR64Imm32Effect 0x1019a9 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 132) (.exec 0x1019a9 (fun s => s.RIP = 0x1019a9) (movR64Imm32Effect 0x1019a9 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 133) (.exec 0x1019b0 (RepPre 0x1019b0 (RepMovsqPre 0x1019b0)) (repMovsqEffect 0x1019b0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[131, 127, 129, 22]
    (.letOp (n := 134) (.out 0x1019b3 (leaR64Effect 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 135) (.exec 0x1019b3 (fun s => s.RIP = 0x1019b3) (leaR64Effect 0x1019b3 7 (.sib 4 none 0 (.d32 0xe00))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 136) (.out 0x1019bb (movR32Imm32Effect 0x1019bb 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 137) (.exec 0x1019bb (fun s => s.RIP = 0x1019bb) (movR32Imm32Effect 0x1019bb 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 138) (.out 0x1019c0 (movR64Imm32Effect 0x1019c0 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 139) (.exec 0x1019c0 (fun s => s.RIP = 0x1019c0) (movR64Imm32Effect 0x1019c0 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.exec 0x1019c7 (RepPre 0x1019c7 (RepMovsqPre 0x1019c7)) (repMovsqEffect 0x1019c7) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[138, 134, 136, 22]
    (.letOp (n := 141) (.out 0x1019ca (leaR64Effect 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 142) (.exec 0x1019ca (fun s => s.RIP = 0x1019ca) (leaR64Effect 0x1019ca 7 (.sib 4 none 0 (.d32 0xe78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.out 0x1019d2 (movR32Imm32Effect 0x1019d2 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 144) (.exec 0x1019d2 (fun s => s.RIP = 0x1019d2) (movR32Imm32Effect 0x1019d2 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 145) (.out 0x1019d7 (movR64Imm32Effect 0x1019d7 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 146) (.exec 0x1019d7 (fun s => s.RIP = 0x1019d7) (movR64Imm32Effect 0x1019d7 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 147) (.exec 0x1019de (RepPre 0x1019de (RepMovsqPre 0x1019de)) (repMovsqEffect 0x1019de) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[145, 141, 143, 22]
    (.letOp (n := 148) (.out 0x1019e1 (leaR64Effect 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 149) (.exec 0x1019e1 (fun s => s.RIP = 0x1019e1) (leaR64Effect 0x1019e1 7 (.sib 4 none 0 (.d32 0xef0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 150) (.out 0x1019e9 (movR32Imm32Effect 0x1019e9 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 151) (.exec 0x1019e9 (fun s => s.RIP = 0x1019e9) (movR32Imm32Effect 0x1019e9 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 152) (.out 0x1019ee (movR64Imm32Effect 0x1019ee 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 153) (.exec 0x1019ee (fun s => s.RIP = 0x1019ee) (movR64Imm32Effect 0x1019ee 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 154) (.exec 0x1019f5 (RepPre 0x1019f5 (RepMovsqPre 0x1019f5)) (repMovsqEffect 0x1019f5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[152, 148, 150, 22]
    (.letOp (n := 155) (.out 0x1019f8 (leaR64Effect 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 156) (.exec 0x1019f8 (fun s => s.RIP = 0x1019f8) (leaR64Effect 0x1019f8 7 (.sib 4 none 0 (.d32 0xf68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 157) (.out 0x101a00 (movR32Imm32Effect 0x101a00 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 158) (.exec 0x101a00 (fun s => s.RIP = 0x101a00) (movR32Imm32Effect 0x101a00 5 1 0xf) (Reg.operands [] [])) #v[]
    (b_l1018b0_3)))))))))))))))))))))))))))))))))))

def bytes_l1018b0_2 : List UInt8 :=
  [0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x88, 0x0D,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x00, 0x0E, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x78, 0x0E, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48,
    0x8D, 0xBC, 0x24, 0xF0, 0x0E, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20,
    0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x68, 0x0F, 0x00, 0x00, 0xB9, 0x0F,
    0x00, 0x00, 0x00] ++ bytes_l1018b0_3

theorem code_l1018b0_2 : ∀ x ∈ codeRange 0x101992 bytes_l1018b0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1992 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1018b0_3

@[cfg_block] def b_l1018b0_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x101923 (RepPre 0x101923 (RepMovsqPre 0x101923)) (repMovsqEffect 0x101923) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[87, 83, 85, 22]
    (.letOp (n := 90) (.out 0x101926 (leaR64Effect 0x101926 7 (.sib 4 none 0 (.d32 0xb30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 91) (.exec 0x101926 (fun s => s.RIP = 0x101926) (leaR64Effect 0x101926 7 (.sib 4 none 0 (.d32 0xb30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x10192e (movR32Imm32Effect 0x10192e 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 93) (.exec 0x10192e (fun s => s.RIP = 0x10192e) (movR32Imm32Effect 0x10192e 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 94) (.out 0x101933 (movR64Imm32Effect 0x101933 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 95) (.exec 0x101933 (fun s => s.RIP = 0x101933) (movR64Imm32Effect 0x101933 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.exec 0x10193a (RepPre 0x10193a (RepMovsqPre 0x10193a)) (repMovsqEffect 0x10193a) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[94, 90, 92, 22]
    (.letOp (n := 97) (.out 0x10193d (leaR64Effect 0x10193d 7 (.sib 4 none 0 (.d32 0xba8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 98) (.exec 0x10193d (fun s => s.RIP = 0x10193d) (leaR64Effect 0x10193d 7 (.sib 4 none 0 (.d32 0xba8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x101945 (movR32Imm32Effect 0x101945 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 100) (.exec 0x101945 (fun s => s.RIP = 0x101945) (movR32Imm32Effect 0x101945 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x10194a (movR64Imm32Effect 0x10194a 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 102) (.exec 0x10194a (fun s => s.RIP = 0x10194a) (movR64Imm32Effect 0x10194a 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 103) (.exec 0x101951 (RepPre 0x101951 (RepMovsqPre 0x101951)) (repMovsqEffect 0x101951) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[101, 97, 99, 22]
    (.letOp (n := 104) (.out 0x101954 (leaR64Effect 0x101954 7 (.sib 4 none 0 (.d32 0xc20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 105) (.exec 0x101954 (fun s => s.RIP = 0x101954) (leaR64Effect 0x101954 7 (.sib 4 none 0 (.d32 0xc20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x10195c (movR32Imm32Effect 0x10195c 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 107) (.exec 0x10195c (fun s => s.RIP = 0x10195c) (movR32Imm32Effect 0x10195c 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 108) (.out 0x101961 (movR64Imm32Effect 0x101961 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 109) (.exec 0x101961 (fun s => s.RIP = 0x101961) (movR64Imm32Effect 0x101961 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 110) (.exec 0x101968 (RepPre 0x101968 (RepMovsqPre 0x101968)) (repMovsqEffect 0x101968) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[108, 104, 106, 22]
    (.letOp (n := 111) (.out 0x10196b (leaR64Effect 0x10196b 15 (.sib 4 none 0 (.d32 0xc98))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 112) (.exec 0x10196b (fun s => s.RIP = 0x10196b) (leaR64Effect 0x10196b 15 (.sib 4 none 0 (.d32 0xc98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x101973 (movR32Imm32Effect 0x101973 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 114) (.exec 0x101973 (fun s => s.RIP = 0x101973) (movR32Imm32Effect 0x101973 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 115) (.out 0x101978 (movR64R64Effect 0x101978 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[111]
    (.letOp (n := 116) (.exec 0x101978 (fun s => s.RIP = 0x101978) (movR64R64Effect 0x101978 7 15) (Reg.operands [.gpr 15] [])) #v[111]
    (.letOp (n := 117) (.out 0x10197b (movR64Imm32Effect 0x10197b 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 118) (.exec 0x10197b (fun s => s.RIP = 0x10197b) (movR64Imm32Effect 0x10197b 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 119) (.exec 0x101982 (RepPre 0x101982 (RepMovsqPre 0x101982)) (repMovsqEffect 0x101982) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[117, 115, 113, 22]
    (.letOp (n := 120) (.out 0x101985 (leaR64Effect 0x101985 7 (.sib 4 none 0 (.d32 0xd10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 121) (.exec 0x101985 (fun s => s.RIP = 0x101985) (leaR64Effect 0x101985 7 (.sib 4 none 0 (.d32 0xd10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.out 0x10198d (movR32Imm32Effect 0x10198d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 123) (.exec 0x10198d (fun s => s.RIP = 0x10198d) (movR32Imm32Effect 0x10198d 5 1 0xf) (Reg.operands [] [])) #v[]
    (b_l1018b0_2)))))))))))))))))))))))))))))))))))

def bytes_l1018b0_1 : List UInt8 :=
  [0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x30, 0x0B, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xA8, 0x0B,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x20, 0x0C, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0xBC, 0x24, 0x98, 0x0C, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3,
    0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x10, 0x0D, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00] ++ bytes_l1018b0_2

theorem code_l1018b0_1 : ∀ x ∈ codeRange 0x101923 bytes_l1018b0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1923 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1018b0_2

@[cfg_block] def b_l1018b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1018b0 (leaR64Effect 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1018b0 (fun s => s.RIP = 0x1018b0) (leaR64Effect 0x1018b0 0 (.sib 4 none 0 (.d32 0x8d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1018b8 (movR32Imm32Effect 0x1018b8 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1018b8 (fun s => s.RIP = 0x1018b8) (movR32Imm32Effect 0x1018b8 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1018bd (movR64R64Effect 0x1018bd 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x1018bd (fun s => s.RIP = 0x1018bd) (movR64R64Effect 0x1018bd 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x1018c0 (movR64Imm32Effect 0x1018c0 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x1018c0 (fun s => s.RIP = 0x1018c0) (movR64Imm32Effect 0x1018c0 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.exec 0x1018c7 (RepPre 0x1018c7 (RepMovsqPre 0x1018c7)) (repMovsqEffect 0x1018c7) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 55, 22]
    (.letOp (n := 62) (.out 0x1018ca (leaR64Effect 0x1018ca 7 (.sib 4 none 0 (.d32 0x950))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1018ca (fun s => s.RIP = 0x1018ca) (leaR64Effect 0x1018ca 7 (.sib 4 none 0 (.d32 0x950))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1018d2 (movR32Imm32Effect 0x1018d2 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 65) (.exec 0x1018d2 (fun s => s.RIP = 0x1018d2) (movR32Imm32Effect 0x1018d2 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x1018d7 (movR64Imm32Effect 0x1018d7 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 67) (.exec 0x1018d7 (fun s => s.RIP = 0x1018d7) (movR64Imm32Effect 0x1018d7 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.exec 0x1018de (RepPre 0x1018de (RepMovsqPre 0x1018de)) (repMovsqEffect 0x1018de) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 62, 64, 22]
    (.letOp (n := 69) (.out 0x1018e1 (leaR64Effect 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1018e1 (fun s => s.RIP = 0x1018e1) (leaR64Effect 0x1018e1 7 (.sib 4 none 0 (.d32 0x9c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1018e9 (movR32Imm32Effect 0x1018e9 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 72) (.exec 0x1018e9 (fun s => s.RIP = 0x1018e9) (movR32Imm32Effect 0x1018e9 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x1018ee (movR64Imm32Effect 0x1018ee 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 74) (.exec 0x1018ee (fun s => s.RIP = 0x1018ee) (movR64Imm32Effect 0x1018ee 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.exec 0x1018f5 (RepPre 0x1018f5 (RepMovsqPre 0x1018f5)) (repMovsqEffect 0x1018f5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 69, 71, 22]
    (.letOp (n := 76) (.out 0x1018f8 (leaR64Effect 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 77) (.exec 0x1018f8 (fun s => s.RIP = 0x1018f8) (leaR64Effect 0x1018f8 7 (.sib 4 none 0 (.d32 0xa40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x101900 (movR32Imm32Effect 0x101900 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x101900 (fun s => s.RIP = 0x101900) (movR32Imm32Effect 0x101900 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x101905 (movR64Imm32Effect 0x101905 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 81) (.exec 0x101905 (fun s => s.RIP = 0x101905) (movR64Imm32Effect 0x101905 6 0x202420) (Reg.operands [] [])) #v[]
    (.letOp (n := 82) (.exec 0x10190c (RepPre 0x10190c (RepMovsqPre 0x10190c)) (repMovsqEffect 0x10190c) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 76, 78, 22]
    (.letOp (n := 83) (.out 0x10190f (leaR64Effect 0x10190f 7 (.sib 4 none 0 (.d32 0xab8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 84) (.exec 0x10190f (fun s => s.RIP = 0x10190f) (leaR64Effect 0x10190f 7 (.sib 4 none 0 (.d32 0xab8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x101917 (movR32Imm32Effect 0x101917 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 86) (.exec 0x101917 (fun s => s.RIP = 0x101917) (movR32Imm32Effect 0x101917 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x10191c (movR64Imm32Effect 0x10191c 6 0x202420) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 88) (.exec 0x10191c (fun s => s.RIP = 0x10191c) (movR64Imm32Effect 0x10191c 6 0x202420) (Reg.operands [] [])) #v[]
    (b_l1018b0_1))))))))))))))))))))))))))))))))))))

def bytes_l1018b0 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0xD8, 0x08, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7,
    0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x50, 0x09,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x09, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x40, 0x0A, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20, 0x24, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48,
    0x8D, 0xBC, 0x24, 0xB8, 0x0A, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x20,
    0x24, 0x20, 0x00] ++ bytes_l1018b0_1

theorem code_l1018b0 : ∀ x ∈ codeRange 0x1018b0 bytes_l1018b0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x18b0 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1018b0_1

@[cfg_block] def b_l101a3c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101a3c (leaR64Effect 0x101a3c 7 (.sib 4 none 0 (.d32 0x518))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101a3c (fun s => s.RIP = 0x101a3c) (leaR64Effect 0x101a3c 7 (.sib 4 none 0 (.d32 0x518))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101a44 (movR32Imm32Effect 0x101a44 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x101a44 (fun s => s.RIP = 0x101a44) (movR32Imm32Effect 0x101a44 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101a49 (movR64R64Effect 0x101a49 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x101a49 (fun s => s.RIP = 0x101a49) (movR64R64Effect 0x101a49 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x101a4c (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 60) (.exec 0x101a4c (GoesTo (CallPre 0x101a4c 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a4f) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 61) (.const ⟨64, 0x101a4f⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101a4f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101a3c : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x18, 0x05, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xFE,
    0x41, 0xFF, 0xD5]

theorem code_l101a3c : ∀ x ∈ codeRange 0x101a3c bytes_l101a3c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a3c 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101a4f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101a4f (leaR64Effect 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x101a4f (fun s => s.RIP = 0x101a4f) (leaR64Effect 0x101a4f 15 (.sib 4 none 0 (.d32 0x1058))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101a57 (movR32Imm32Effect 0x101a57 5 2 0x780) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x101a57 (fun s => s.RIP = 0x101a57) (movR32Imm32Effect 0x101a57 5 2 0x780) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101a5c (movR64R64Effect 0x101a5c 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x101a5c (fun s => s.RIP = 0x101a5c) (movR64R64Effect 0x101a5c 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x101a5f (movR64R64Effect 0x101a5f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 60) (.exec 0x101a5f (fun s => s.RIP = 0x101a5f) (movR64R64Effect 0x101a5f 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x101a62 (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 62) (.exec 0x101a62 (GoesTo (CallPre 0x101a62 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x101a65) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 63) (.const ⟨64, 0x101a65⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l101a65, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l101a4f : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x10, 0x00, 0x00, 0xBA, 0x80, 0x07, 0x00, 0x00, 0x4C, 0x89, 0xFF,
    0x4C, 0x89, 0xE6, 0x41, 0xFF, 0xD5]

theorem code_l101a4f : ∀ x ∈ codeRange 0x101a4f bytes_l101a4f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a4f 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101a65 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101a65 (StorePre 0x101a65 10 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x101a65 + BitVec.ofNat 64 10)) 2) (movM16Imm16Effect 0x101a65 (.sib 4 none 0 (.d32 0xb8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x101a6f (StorePre 0x101a6f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x101a6f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a6f (.sib 4 none 0 (.d32 0xb0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x101a7b (StorePre 0x101a7b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x101a7b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a7b (.sib 4 none 0 (.d32 0xa8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x101a87 (StorePre 0x101a87 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101a87 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a87 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101a93 (StorePre 0x101a93 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101a93 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a93 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101a9f (StorePre 0x101a9f 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101a9f + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101a9f (.sib 4 none 0 (.d32 0x90)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x101aab (StorePre 0x101aab 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101aab + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101aab (.sib 4 none 0 (.d32 0x88)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x101ab7 (StorePre 0x101ab7 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101ab7 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x101ab7 (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101ac3 (StorePre 0x101ac3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101ac3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101ac3 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x101acc (StorePre 0x101acc 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101acc + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101acc (.sib 4 none 0 .none) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x101ad4 (leaR64Effect 0x101ad4 12 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x101ad4 (fun s => s.RIP = 0x101ad4) (leaR64Effect 0x101ad4 12 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x101adc (leaR64Effect 0x101adc 9 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 66) (.exec 0x101adc (fun s => s.RIP = 0x101adc) (leaR64Effect 0x101adc 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x101ae1 (movR32Imm32Effect 0x101ae1 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 68) (.exec 0x101ae1 (fun s => s.RIP = 0x101ae1) (movR32Imm32Effect 0x101ae1 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x101ae6 (movR32Imm32Effect 0x101ae6 6 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 70) (.exec 0x101ae6 (fun s => s.RIP = 0x101ae6) (movR32Imm32Effect 0x101ae6 6 8 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x101aec (movR64R64Effect 0x101aec 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 72) (.exec 0x101aec (fun s => s.RIP = 0x101aec) (movR64R64Effect 0x101aec 7 12) (Reg.operands [.gpr 12] [])) #v[63]
    (.letOp (n := 73) (.out 0x101aef (movR64R64Effect 0x101aef 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 74) (.exec 0x101aef (fun s => s.RIP = 0x101aef) (movR64R64Effect 0x101aef 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 75) (.out 0x101af2 (movR64R64Effect 0x101af2 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 76) (.exec 0x101af2 (fun s => s.RIP = 0x101af2) (movR64R64Effect 0x101af2 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 77) (.out 0x101af5 (callEffect (fun _ => 0x11c880) 0x101afa) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 78) (.exec 0x101af5 (PushPre 0x101af5 5) (callEffect (fun _ => 0x11c880) 0x101afa) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.const ⟨64, 0x101afa⟩) #v[]
    (.terminate (.call ⟨.l11c880, RegMap.args [(1, 75), (2, 67), (3, 3), (4, 77), (5, 5), (6, 73), (7, 71), (8, 69), (9, 65), (12, 63), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩ { target := .l101afa, kept := #v[], arity := rfl, guard := some (Fin.last 79) }))))))))))))))))))))))))))))

def bytes_l101a65 : List UInt8 :=
  [0x66, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x04, 0x24, 0x01, 0x00, 0x00, 0x00, 0x4C,
    0x8D, 0xA4, 0x24, 0x58, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0x4C, 0x24, 0x78, 0xBA, 0x01, 0x00, 0x00,
    0x00, 0x41, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xF9,
    0xE8, 0x86, 0xAD, 0x01, 0x00]

theorem code_l101a65 : ∀ x ∈ codeRange 0x101a65 bytes_l101a65, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a65 149 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101afa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101afa (leaR64Effect 0x101afa 14 (.sib 4 none 0 (.d32 0x1058))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x101afa (fun s => s.RIP = 0x101afa) (leaR64Effect 0x101afa 14 (.sib 4 none 0 (.d32 0x1058))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101b02 (movR64R64Effect 0x101b02 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x101b02 (fun s => s.RIP = 0x101b02) (movR64R64Effect 0x101b02 7 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 57) (.out 0x101b05 (movR64R64Effect 0x101b05 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 58) (.exec 0x101b05 (fun s => s.RIP = 0x101b05) (movR64R64Effect 0x101b05 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x101b08 (callEffect (fun _ => 0x10fe50) 0x101b0d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101b08 (PushPre 0x101b08 5) (callEffect (fun _ => 0x10fe50) 0x101b0d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101b0d⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101b0d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101afa : List UInt8 :=
  [0x4C, 0x8D, 0xB4, 0x24, 0x58, 0x10, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0xE8, 0x43,
    0xE3, 0x00, 0x00]

theorem code_l101afa : ∀ x ∈ codeRange 0x101afa bytes_l101afa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1afa 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b0d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101b0d (leaR64Effect 0x101b0d 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101b0d (fun s => s.RIP = 0x101b0d) (leaR64Effect 0x101b0d 7 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101b15 (movR64R64Effect 0x101b15 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x101b15 (fun s => s.RIP = 0x101b15) (movR64R64Effect 0x101b15 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x101b18 (callEffect (fun _ => 0x120350) 0x101b1d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x101b18 (PushPre 0x101b18 5) (callEffect (fun _ => 0x120350) 0x101b1d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x101b1d⟩) #v[]
    (.terminate (.call ⟨.l120350, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l101b1d, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l101b0d : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xE8, 0x33, 0xE8, 0x01, 0x00]

theorem code_l101b0d : ∀ x ∈ codeRange 0x101b0d bytes_l101b0d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b0d 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b1d_2 : Block Op Label signature Reg.count 97 :=
  .letOp (n := 97) (.out 0x101c4c (addR64Imm32Effect 0x101c4c 4 0x17d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 98) (.exec 0x101c4c (fun s => s.RIP = 0x101c4c) (addR64Imm32Effect 0x101c4c 4 0x17d8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x101c53 (popR64Effect 0x101c53 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[97]
    (.letOp (n := 100) (.out 0x101c53 (popR64Effect 0x101c53 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x101c53 (PopPre 0x101c53) (popR64Effect 0x101c53 1 3) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x101c54 (popR64Effect 0x101c54 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[100]
    (.letOp (n := 103) (.out 0x101c54 (popR64Effect 0x101c54 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x101c54 (PopPre 0x101c54) (popR64Effect 0x101c54 2 12) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x101c56 (popR64Effect 0x101c56 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[103]
    (.letOp (n := 106) (.out 0x101c56 (popR64Effect 0x101c56 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x101c56 (PopPre 0x101c56) (popR64Effect 0x101c56 2 13) (Reg.operands [.gpr 4] [])) #v[103]
    (.letOp (n := 108) (.out 0x101c58 (popR64Effect 0x101c58 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[106]
    (.letOp (n := 109) (.out 0x101c58 (popR64Effect 0x101c58 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[106]
    (.letOp (n := 110) (.exec 0x101c58 (PopPre 0x101c58) (popR64Effect 0x101c58 2 14) (Reg.operands [.gpr 4] [])) #v[106]
    (.letOp (n := 111) (.out 0x101c5a (popR64Effect 0x101c5a 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[109]
    (.letOp (n := 112) (.out 0x101c5a (popR64Effect 0x101c5a 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[109]
    (.letOp (n := 113) (.exec 0x101c5a (PopPre 0x101c5a) (popR64Effect 0x101c5a 2 15) (Reg.operands [.gpr 4] [])) #v[109]
    (.letOp (n := 114) (.out 0x101c5c (popR64Effect 0x101c5c 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[112]
    (.letOp (n := 115) (.out 0x101c5c (popR64Effect 0x101c5c 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[112]
    (.letOp (n := 116) (.exec 0x101c5c (PopPre 0x101c5c) (popR64Effect 0x101c5c 1 5) (Reg.operands [.gpr 4] [])) #v[112]
    (.letOp (n := 117) (.out 0x101c5d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[115]
    (.letOp (n := 118) (.out 0x101c5d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[115]
    (.letOp (n := 119) (.exec 0x101c5d (RetPre 0x101c5d) (retEffect) (Reg.operands [.gpr 4] [])) #v[115]
    (.terminate (.ret (RegMap.args [(0, 59), (1, 61), (2, 2), (3, 99), (4, 118), (5, 114), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 102), (13, 105), (14, 108), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)] 120) (some ⟨117, by decide⟩)))))))))))))))))))))))))

def bytes_l101b1d_2 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xD8, 0x17, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l101b1d_2 : ∀ x ∈ codeRange 0x101c4c bytes_l101b1d_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c4c 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101b1d_1 : Block Op Label signature Reg.count 77 :=
  .letOp (n := 77) (.exec 0x101bac (StorePre 0x101bac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x164)) s (0x101bac + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bac (.sib 4 none 0 (.d32 0x164)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x101bb4 (StorePre 0x101bb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x165)) s (0x101bb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bb4 (.sib 4 none 0 (.d32 0x165)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x101bbc (StorePre 0x101bbc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x166)) s (0x101bbc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bbc (.sib 4 none 0 (.d32 0x166)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x101bc4 (StorePre 0x101bc4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x167)) s (0x101bc4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bc4 (.sib 4 none 0 (.d32 0x167)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x101bcc (StorePre 0x101bcc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101bcc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bcc (.sib 4 none 0 (.d32 0x168)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x101bd4 (StorePre 0x101bd4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x169)) s (0x101bd4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bd4 (.sib 4 none 0 (.d32 0x169)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.exec 0x101bdc (StorePre 0x101bdc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16a)) s (0x101bdc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bdc (.sib 4 none 0 (.d32 0x16a)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x101be4 (StorePre 0x101be4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16b)) s (0x101be4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101be4 (.sib 4 none 0 (.d32 0x16b)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x101bec (StorePre 0x101bec 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16c)) s (0x101bec + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bec (.sib 4 none 0 (.d32 0x16c)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 86) (.exec 0x101bf4 (StorePre 0x101bf4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16d)) s (0x101bf4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bf4 (.sib 4 none 0 (.d32 0x16d)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x101bfc (StorePre 0x101bfc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16e)) s (0x101bfc + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101bfc (.sib 4 none 0 (.d32 0x16e)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 88) (.exec 0x101c04 (StorePre 0x101c04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x16f)) s (0x101c04 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c04 (.sib 4 none 0 (.d32 0x16f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x101c0c (StorePre 0x101c0c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101c0c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c0c (.sib 4 none 0 (.d32 0x170)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.exec 0x101c14 (StorePre 0x101c14 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x171)) s (0x101c14 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c14 (.sib 4 none 0 (.d32 0x171)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x101c1c (StorePre 0x101c1c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x172)) s (0x101c1c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c1c (.sib 4 none 0 (.d32 0x172)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x101c24 (StorePre 0x101c24 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x173)) s (0x101c24 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c24 (.sib 4 none 0 (.d32 0x173)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x101c2c (StorePre 0x101c2c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x174)) s (0x101c2c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c2c (.sib 4 none 0 (.d32 0x174)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x101c34 (StorePre 0x101c34 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x175)) s (0x101c34 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c34 (.sib 4 none 0 (.d32 0x175)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.exec 0x101c3c (StorePre 0x101c3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x176)) s (0x101c3c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c3c (.sib 4 none 0 (.d32 0x176)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.exec 0x101c44 (StorePre 0x101c44 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x177)) s (0x101c44 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101c44 (.sib 4 none 0 (.d32 0x177)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101b1d_2))))))))))))))))))))

def bytes_l101b1d_1 : List UInt8 :=
  [0xC6, 0x84, 0x24, 0x64, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x65, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x66, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x67, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x68, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x69, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x6A, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x6B, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x6C, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x6D, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x6E, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x6F, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x71, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x72, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x73, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x74, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x75, 0x01, 0x00, 0x00, 0x00,
    0xC6, 0x84, 0x24, 0x76, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x77, 0x01, 0x00, 0x00, 0x00] ++ bytes_l101b1d_2

theorem code_l101b1d_1 : ∀ x ∈ codeRange 0x101bac bytes_l101b1d_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1bac 160 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101b1d_2

@[cfg_block] def b_l101b1d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101b1d (movR64M64Effect 0x101b1d 0 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101b1d (LoadPre 0x101b1d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x170)) s (0x101b1d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b1d 0 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x101b25 (StorePre 0x101b25 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101b25 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b25 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x101b29 (movR64M64Effect 0x101b29 0 (.sib 4 none 0 (.d32 0x168))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x101b29 (LoadPre 0x101b29 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x101b29 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b29 0 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101b31 (StorePre 0x101b31 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101b31 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b31 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x101b35 (movR64M64Effect 0x101b35 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101b35 (LoadPre 0x101b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b35 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b35 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x101b3d (movR64M64Effect 0x101b3d 1 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x101b3d (LoadPre 0x101b3d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b3d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101b3d 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x101b45 (StorePre 0x101b45 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101b45 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101b45 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101b49 (StorePre 0x101b49 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101b49 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101b49 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 65) (.exec 0x101b4c (StorePre 0x101b4c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x101b4c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b4c (.sib 4 none 0 (.d32 0x158)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x101b54 (StorePre 0x101b54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x159)) s (0x101b54 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b54 (.sib 4 none 0 (.d32 0x159)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x101b5c (StorePre 0x101b5c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15a)) s (0x101b5c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b5c (.sib 4 none 0 (.d32 0x15a)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x101b64 (StorePre 0x101b64 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15b)) s (0x101b64 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b64 (.sib 4 none 0 (.d32 0x15b)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x101b6c (StorePre 0x101b6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15c)) s (0x101b6c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b6c (.sib 4 none 0 (.d32 0x15c)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x101b74 (StorePre 0x101b74 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15d)) s (0x101b74 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b74 (.sib 4 none 0 (.d32 0x15d)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x101b7c (StorePre 0x101b7c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15e)) s (0x101b7c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b7c (.sib 4 none 0 (.d32 0x15e)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x101b84 (StorePre 0x101b84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x15f)) s (0x101b84 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b84 (.sib 4 none 0 (.d32 0x15f)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x101b8c (StorePre 0x101b8c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x101b8c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b8c (.sib 4 none 0 (.d32 0x160)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x101b94 (StorePre 0x101b94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x161)) s (0x101b94 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b94 (.sib 4 none 0 (.d32 0x161)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x101b9c (StorePre 0x101b9c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x162)) s (0x101b9c + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101b9c (.sib 4 none 0 (.d32 0x162)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x101ba4 (StorePre 0x101ba4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x163)) s (0x101ba4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x101ba4 (.sib 4 none 0 (.d32 0x163)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101b1d_1))))))))))))))))))))))))

def bytes_l101b1d : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8B, 0x84, 0x24,
    0x68, 0x01, 0x00, 0x00, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x03, 0xC6,
    0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x59, 0x01, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0x5A, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x5B, 0x01, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0x5C, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x5D, 0x01, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0x5E, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x5F, 0x01, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0x60, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x61, 0x01, 0x00, 0x00, 0x00, 0xC6,
    0x84, 0x24, 0x62, 0x01, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x63, 0x01, 0x00, 0x00, 0x00] ++ bytes_l101b1d_1

theorem code_l101b1d : ∀ x ∈ codeRange 0x101b1d bytes_l101b1d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b1d 143 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101b1d_1

@[cfg_block] def b_l101c5e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101c5e (PushPre 0x101c5e 5) (callEffect (fun _ => 0x100a30) 0x101c63) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x101c63⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l101c63, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l101c5e : List UInt8 :=
  [0xE8, 0xCD, 0xED, 0xFF, 0xFF]

theorem code_l101c5e : ∀ x ∈ codeRange 0x101c5e bytes_l101c5e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c5e 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101c63 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101c63 (fun s => s.RIP = 0x101c63) (fun _ => nopEffect 0x101c63 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x101c6d (fun s => s.RIP = 0x101c6d) (fun _ => nopEffect 0x101c6d 3) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101c70 (pushR64Effect 0x101c70 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 56) (.exec 0x101c70 (PushPre 0x101c70 2) (pushR64Effect 0x101c70 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 57) (.out 0x101c72 (pushR64Effect 0x101c72 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x101c72 (PushPre 0x101c72 1) (pushR64Effect 0x101c72 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x101c73 (subR64Imm32Effect 0x101c73 4 0x1e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x101c73 (fun s => s.RIP = 0x101c73) (subR64Imm32Effect 0x101c73 4 0x1e8) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x101c7a (movR64R64Effect 0x101c7a 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 62) (.exec 0x101c7a (fun s => s.RIP = 0x101c7a) (movR64R64Effect 0x101c7a 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x101c7d (movR64R64Effect 0x101c7d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x101c7d (fun s => s.RIP = 0x101c7d) (movR64R64Effect 0x101c7d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x101c80 (movzxR32M8Effect 0x101c80 4 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 66) (.exec 0x101c80 (LoadPre 0x101c80 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x101c80 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x101c80 4 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.exec 0x101c84 (StorePre 0x101c84 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x101c84 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101c84 7 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 59]
    (.letOp (n := 68) (.out 0x101c8b (movR64M64Effect 0x101c8b 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 69) (.exec 0x101c8b (LoadPre 0x101c8b (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101c8b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c8b 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.exec 0x101c8f (StorePre 0x101c8f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x101c8f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c8f 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 59]
    (.letOp (n := 71) (.out 0x101c97 (movR64M64Effect 0x101c97 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 72) (.exec 0x101c97 (LoadPre 0x101c97 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101c97 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c97 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.exec 0x101c9b (StorePre 0x101c9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x101c9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c9b 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 59]
    (.letOp (n := 74) (.out 0x101ca3 (movR64M64Effect 0x101ca3 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 75) (.exec 0x101ca3 (LoadPre 0x101ca3 (fun s => AddrMode.addr (.base 6 .none) s (0x101ca3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101ca3 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x101ca6 (movR64M64Effect 0x101ca6 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 77) (.exec 0x101ca6 (LoadPre 0x101ca6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101ca6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101ca6 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 78) (.exec 0x101caa (StorePre 0x101caa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x101caa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101caa 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 59]
    (.letOp (n := 79) (.exec 0x101cb2 (StorePre 0x101cb2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x101cb2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cb2 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 59]
    (.letOp (n := 80) (.out 0x101cba (movR64R64Effect 0x101cba 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 81) (.exec 0x101cba (fun s => s.RIP = 0x101cba) (movR64R64Effect 0x101cba 7 4) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 82) (.out 0x101cbd (leaR64Effect 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 83) (.exec 0x101cbd (fun s => s.RIP = 0x101cbd) (leaR64Effect 0x101cbd 6 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 84) (.out 0x101cc5 (callEffect (fun _ => 0x10ff00) 0x101cca) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 85) (.exec 0x101cc5 (PushPre 0x101cc5 5) (callEffect (fun _ => 0x10ff00) 0x101cca) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 86) (.const ⟨64, 0x101cca⟩) #v[]
    (.terminate (.call ⟨.l10ff00, RegMap.args [(0, 74), (1, 76), (2, 2), (3, 63), (4, 84), (5, 5), (6, 82), (7, 80), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩ { target := .l101cca, kept := #v[], arity := rfl, guard := some (Fin.last 86) })))))))))))))))))))))))))))))))))))

def bytes_l101c63 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0F, 0x1F, 0x00, 0x41, 0x56, 0x53,
    0x48, 0x81, 0xEC, 0xE8, 0x01, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xFB, 0x0F, 0xB6, 0x46,
    0x20, 0x88, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24,
    0x10, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0x48, 0x8D, 0xB4, 0x24, 0xF8, 0x00,
    0x00, 0x00, 0xE8, 0x36, 0xE2, 0x00, 0x00]

theorem code_l101c63 : ∀ x ∈ codeRange 0x101c63 bytes_l101c63, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c63 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101cca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101cca (cmpM8Imm8Effect 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101cca (LoadPre 0x101cca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101cca + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101cca 5 (.sib 4 none 0 (.d8 0x78)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101dcb, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101cd5, RegMap.args [(3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101cca : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x78, 0x01, 0x0F, 0x85, 0xF6, 0x00, 0x00, 0x00]

theorem code_l101cca : ∀ x ∈ codeRange 0x101cca bytes_l101cca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cca 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101cd5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101cd5 (leaR64Effect 0x101cd5 7 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101cd5 (fun s => s.RIP = 0x101cd5) (leaR64Effect 0x101cd5 7 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101cdd (movR64R64Effect 0x101cdd 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x101cdd (fun s => s.RIP = 0x101cdd) (movR64R64Effect 0x101cdd 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101ce0 (movR32Imm32Effect 0x101ce0 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x101ce0 (fun s => s.RIP = 0x101ce0) (movR32Imm32Effect 0x101ce0 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x101ce5 (RepPre 0x101ce5 (RepMovsqPre 0x101ce5)) (repMovsqEffect 0x101ce5) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x101ce8 (movzxR32M8Effect 0x101ce8 5 0 (.base 14 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 61) (.exec 0x101ce8 (LoadPre 0x101ce8 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x101ce8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101ce8 5 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.exec 0x101ced (StorePre 0x101ced 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101ced + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x101ced 7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x101cf4 (movR64M64Effect 0x101cf4 0 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 64) (.exec 0x101cf4 (LoadPre 0x101cf4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x101cf4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101cf4 0 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.exec 0x101cf8 (StorePre 0x101cf8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101cf8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101cf8 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x101d00 (movR64M64Effect 0x101d00 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 67) (.exec 0x101d00 (LoadPre 0x101d00 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x101d00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d00 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.exec 0x101d04 (StorePre 0x101d04 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x101d04 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d04 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x101d0c (movR64M64Effect 0x101d0c 0 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 70) (.exec 0x101d0c (LoadPre 0x101d0c (fun s => AddrMode.addr (.base 14 .none) s (0x101d0c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101d0c 0 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x101d0f (movR64M64Effect 0x101d0f 1 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 72) (.exec 0x101d0f (LoadPre 0x101d0f (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x101d0f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101d0f 1 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.exec 0x101d13 (StorePre 0x101d13 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101d13 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d13 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.exec 0x101d1b (StorePre 0x101d1b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101d1b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101d1b 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 75) (.out 0x101d23 (movR64R64Effect 0x101d23 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x101d23 (fun s => s.RIP = 0x101d23) (movR64R64Effect 0x101d23 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x101d26 (leaR64Effect 0x101d26 6 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x101d26 (fun s => s.RIP = 0x101d26) (leaR64Effect 0x101d26 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101d2e (callEffect (fun _ => 0x10ff00) 0x101d33) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x101d2e (PushPre 0x101d2e 5) (callEffect (fun _ => 0x10ff00) 0x101d33) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x101d33⟩) #v[]
    (.terminate (.call ⟨.l10ff00, RegMap.args [(0, 69), (1, 71), (3, 3), (4, 79), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l101d33, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l101cd5 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x70, 0x01, 0x00, 0x00, 0x48, 0x89, 0xE6, 0xB9, 0x0F, 0x00, 0x00, 0x00,
    0xF3, 0x48, 0xA5, 0x41, 0x0F, 0xB6, 0x46, 0x20, 0x88, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x49,
    0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x46, 0x10, 0x48,
    0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x06, 0x49, 0x8B, 0x4E, 0x08, 0x48, 0x89,
    0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89,
    0xE7, 0x48, 0x8D, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0xE8, 0xCD, 0xE1, 0x00, 0x00]

theorem code_l101cd5 : ∀ x ∈ codeRange 0x101cd5 bytes_l101cd5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cd5 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d33 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d33 (cmpM8Imm8Effect 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101d33 (LoadPre 0x101d33 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101d33 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x101d33 5 (.sib 4 none 0 (.d8 0x78)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101dcb, RegMap.args [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101d3e, RegMap.args [(3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101d33 : List UInt8 :=
  [0x80, 0x7C, 0x24, 0x78, 0x01, 0x0F, 0x85, 0x8D, 0x00, 0x00, 0x00]

theorem code_l101d33 : ∀ x ∈ codeRange 0x101d33 bytes_l101d33, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d33 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d3e (leaR64Effect 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101d3e (fun s => s.RIP = 0x101d3e) (leaR64Effect 0x101d3e 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101d46 (movR64R64Effect 0x101d46 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x101d46 (fun s => s.RIP = 0x101d46) (movR64R64Effect 0x101d46 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101d49 (movR32Imm32Effect 0x101d49 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x101d49 (fun s => s.RIP = 0x101d49) (movR32Imm32Effect 0x101d49 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x101d4e (movR64R64Effect 0x101d4e 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 60) (.exec 0x101d4e (fun s => s.RIP = 0x101d4e) (movR64R64Effect 0x101d4e 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.exec 0x101d51 (RepPre 0x101d51 (RepMovsqPre 0x101d51)) (repMovsqEffect 0x101d51) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 59, 57, 22]
    (.letOp (n := 62) (.out 0x101d54 (movR64R64Effect 0x101d54 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 63) (.exec 0x101d54 (fun s => s.RIP = 0x101d54) (movR64R64Effect 0x101d54 14 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x101d57 (leaR64Effect 0x101d57 6 (.sib 4 none 0 (.d32 0x170))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 65) (.exec 0x101d57 (fun s => s.RIP = 0x101d57) (leaR64Effect 0x101d57 6 (.sib 4 none 0 (.d32 0x170))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x101d5f (movR32Imm32Effect 0x101d5f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 67) (.exec 0x101d5f (fun s => s.RIP = 0x101d5f) (movR32Imm32Effect 0x101d5f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x101d64 (movR64R64Effect 0x101d64 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 69) (.exec 0x101d64 (fun s => s.RIP = 0x101d64) (movR64R64Effect 0x101d64 7 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 70) (.exec 0x101d67 (RepPre 0x101d67 (RepMovsqPre 0x101d67)) (repMovsqEffect 0x101d67) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[64, 68, 66, 22]
    (.letOp (n := 71) (.out 0x101d6a (movR64R64Effect 0x101d6a 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[62]
    (.letOp (n := 72) (.exec 0x101d6a (fun s => s.RIP = 0x101d6a) (movR64R64Effect 0x101d6a 7 14) (Reg.operands [.gpr 14] [])) #v[62]
    (.letOp (n := 73) (.out 0x101d6d (movR64R64Effect 0x101d6d 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 74) (.exec 0x101d6d (fun s => s.RIP = 0x101d6d) (movR64R64Effect 0x101d6d 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 75) (.out 0x101d70 (callEffect (fun _ => 0x10a410) 0x101d75) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x101d70 (PushPre 0x101d70 5) (callEffect (fun _ => 0x10a410) 0x101d75) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x101d75⟩) #v[]
    (.terminate (.call ⟨.l10a410, RegMap.args [(0, 53), (3, 3), (4, 75), (5, 5), (6, 73), (7, 71), (12, 12), (13, 13), (14, 62), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l101d75, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l101d3e : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE6, 0xB9, 0x0F, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x49, 0x89, 0xE6, 0x48, 0x8D, 0xB4, 0x24, 0x70, 0x01, 0x00,
    0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xF3, 0x48, 0xA5, 0x4C, 0x89, 0xF7, 0x48,
    0x89, 0xC6, 0xE8, 0x9B, 0x86, 0x00, 0x00]

theorem code_l101d3e : ∀ x ∈ codeRange 0x101d3e bytes_l101d3e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d3e 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d75 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d75 (leaR64Effect 0x101d75 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101d75 (fun s => s.RIP = 0x101d75) (leaR64Effect 0x101d75 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101d7d (movR32Imm32Effect 0x101d7d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x101d7d (fun s => s.RIP = 0x101d7d) (movR32Imm32Effect 0x101d7d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101d82 (movR64R64Effect 0x101d82 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x101d82 (fun s => s.RIP = 0x101d82) (movR64R64Effect 0x101d82 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x101d85 (movR64R64Effect 0x101d85 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x101d85 (fun s => s.RIP = 0x101d85) (movR64R64Effect 0x101d85 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.exec 0x101d88 (RepPre 0x101d88 (RepMovsqPre 0x101d88)) (repMovsqEffect 0x101d88) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 55, 22]
    (.letOp (n := 62) (.out 0x101d8b (movR64R64Effect 0x101d8b 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x101d8b (fun s => s.RIP = 0x101d8b) (movR64R64Effect 0x101d8b 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x101d8e (movR64R64Effect 0x101d8e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 65) (.exec 0x101d8e (fun s => s.RIP = 0x101d8e) (movR64R64Effect 0x101d8e 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 66) (.out 0x101d91 (callEffect (fun _ => 0x110070) 0x101d96) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x101d91 (PushPre 0x101d91 5) (callEffect (fun _ => 0x110070) 0x101d96) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x101d96⟩) #v[]
    (.terminate (.call ⟨.l110070, RegMap.args [(0, 53), (3, 3), (4, 66), (5, 5), (6, 64), (7, 62), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l101d96, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l101d75 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7,
    0x4C, 0x89, 0xF6, 0xF3, 0x48, 0xA5, 0x48, 0x89, 0xE7, 0x48, 0x89, 0xC6, 0xE8, 0xDA, 0xE2, 0x00,
    0x00]

theorem code_l101d75 : ∀ x ∈ codeRange 0x101d75 bytes_l101d75, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d75 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d96 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d96 (movzxR32M8Effect 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101d96 (LoadPre 0x101d96 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101d96 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d96 5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x101d9b (StorePre 0x101d9b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x101d9b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101d9b 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x101d9e (movR64M64Effect 0x101d9e 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x101d9e (LoadPre 0x101d9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101d9e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101d9e 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101da3 (StorePre 0x101da3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101da3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101da3 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x101da7 (movR64M64Effect 0x101da7 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101da7 (LoadPre 0x101da7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101da7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101da7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101dac (StorePre 0x101dac 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x101dac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101dac 0 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x101db0 (movR64M64Effect 0x101db0 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x101db0 (LoadPre 0x101db0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101db0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101db0 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x101db4 (movR64M64Effect 0x101db4 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x101db4 (LoadPre 0x101db4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101db4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101db4 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x101db9 (StorePre 0x101db9 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101db9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101db9 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 67) (.exec 0x101dbd (StorePre 0x101dbd 3 (fun s => AddrMode.addr (.base 3 .none) s (0x101dbd + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101dbd 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 68) (.out 0x101dc0 (addR64Imm32Effect 0x101dc0 4 0x1e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x101dc0 (fun s => s.RIP = 0x101dc0) (addR64Imm32Effect 0x101dc0 4 0x1e8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x101dc7 (popR64Effect 0x101dc7 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 71) (.out 0x101dc7 (popR64Effect 0x101dc7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x101dc7 (PopPre 0x101dc7) (popR64Effect 0x101dc7 1 3) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x101dc8 (popR64Effect 0x101dc8 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 74) (.out 0x101dc8 (popR64Effect 0x101dc8 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x101dc8 (PopPre 0x101dc8) (popR64Effect 0x101dc8 2 14) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x101dca (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[74]
    (.letOp (n := 77) (.out 0x101dca (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x101dca (RetPre 0x101dca) (retEffect) (Reg.operands [.gpr 4] [])) #v[74]
    (.terminate (.ret (RegMap.args [(0, 62), (1, 64), (2, 2), (3, 70), (4, 77), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 73), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79) (some ⟨76, by decide⟩))))))))))))))))))))))))))))

def bytes_l101d96 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x20, 0x88, 0x43, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x43,
    0x18, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8B, 0x04, 0x24, 0x48, 0x8B,
    0x4C, 0x24, 0x08, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x03, 0x48, 0x81, 0xC4, 0xE8, 0x01, 0x00,
    0x00, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l101d96 : ∀ x ∈ codeRange 0x101d96 bytes_l101d96, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d96 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dcb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101dcb (PushPre 0x101dcb 5) (callEffect (fun _ => 0x100a30) 0x101dd0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x101dd0⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l101dd0, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l101dcb : List UInt8 :=
  [0xE8, 0x60, 0xEC, 0xFF, 0xFF]

theorem code_l101dcb : ∀ x ∈ codeRange 0x101dcb bytes_l101dcb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dcb 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101dd0 (pushR64Effect 0x101dd0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x101dd0 (PushPre 0x101dd0 2) (pushR64Effect 0x101dd0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x101dd2 (pushR64Effect 0x101dd2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x101dd2 (PushPre 0x101dd2 1) (pushR64Effect 0x101dd2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x101dd3 (subR64Imm32Effect 0x101dd3 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x101dd3 (fun s => s.RIP = 0x101dd3) (subR64Imm32Effect 0x101dd3 4 0xe8) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x101dda (movR64R64Effect 0x101dda 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 60) (.exec 0x101dda (fun s => s.RIP = 0x101dda) (movR64R64Effect 0x101dda 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.out 0x101ddd (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 62) (.exec 0x101ddd (fun s => s.RIP = 0x101ddd) (leaR64Effect 0x101ddd 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 63) (.out 0x101de5 (callEffect (fun _ => 0x106390) 0x101dea) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 64) (.exec 0x101de5 (PushPre 0x101de5 5) (callEffect (fun _ => 0x106390) 0x101dea) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 65) (.const ⟨64, 0x101dea⟩) #v[]
    (.terminate (.call ⟨.l106390, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l101dea, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l101dd0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xFE, 0x48, 0x8D, 0xBC,
    0x24, 0x88, 0x00, 0x00, 0x00, 0xE8, 0xA6, 0x45, 0x00, 0x00]

theorem code_l101dd0 : ∀ x ∈ codeRange 0x101dd0 bytes_l101dd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dd0 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101dea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101dea (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x101dea (LoadPre 0x101dea (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101dea + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101dea 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101df2 (cmpR64Imm8Effect 0x101df2 3 0x1) (EffectPart.reads (.flag .ZF) [.gpr 3] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x101df2 (fun s => s.RIP = 0x101df2) (cmpR64Imm8Effect 0x101df2 3 0x1) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l101e62, RegMap.args [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l101df8, RegMap.args [(1, 1), (2, 2), (3, 53), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l101dea : List UInt8 :=
  [0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x83, 0xFB, 0x01, 0x74, 0x6A]

theorem code_l101dea : ∀ x ∈ codeRange 0x101dea bytes_l101dea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1dea 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101df8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101df8 (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 54) (.exec 0x101df8 (fun s => s.RIP = 0x101df8) (leaR64Effect 0x101df8 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101e00 (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x101e00 (fun s => s.RIP = 0x101e00) (leaR64Effect 0x101e00 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e05 (xorR32R32Effect 0x101e05 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x101e05 (fun s => s.RIP = 0x101e05) (xorR32R32Effect 0x101e05 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x101e07 (callEffect (fun _ => 0x1215e0) 0x101e0c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101e07 (PushPre 0x101e07 5) (callEffect (fun _ => 0x1215e0) 0x101e0c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101e0c⟩) #v[]
    (.terminate (.call ⟨.l1215e0, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101e0c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101df8 : List UInt8 :=
  [0x48, 0x8D, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x0F, 0x31, 0xD2, 0xE8,
    0xD4, 0xF7, 0x01, 0x00]

theorem code_l101df8 : ∀ x ∈ codeRange 0x101df8 bytes_l101df8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1df8 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e0c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e0c (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x101e0c (LoadPre 0x101e0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101e0c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e0c 5 1 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101e11 (cmpR64Imm8Effect 0x101e11 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x101e11 (fun s => s.RIP = 0x101e11) (cmpR64Imm8Effect 0x101e11 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x101e15 (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x101e15 (fun s => s.RIP = 0x101e15) (atFlags (condHolds 2) (setccR8Effect 0x101e15 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x101e18 (movR8Imm8Effect 0x101e18 2 2 0x3d) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 60) (.exec 0x101e18 (fun s => s.RIP = 0x101e18) (movR8Imm8Effect 0x101e18 2 2 0x3d) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 61) (.out 0x101e1a (shrR8ClEffect 0x101e1a 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x101e1a (fun s => s.RIP = 0x101e1a) (shrR8ClEffect 0x101e1a 2 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x101e1c (testR8R8Effect 0x101e1c 2 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[57, 61]
    (.letOp (n := 64) (.exec 0x101e1c (fun s => s.RIP = 0x101e1c) (testR8R8Effect 0x101e1c 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[57, 61]
    (.letOp (n := 65) (.pure (condOp 5)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l101e4c, RegMap.args [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l101e20, RegMap.args [(0, 57), (1, 53), (2, 61), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l101e0c : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x0F, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0xB2, 0x3D, 0xD2, 0xEA,
    0x84, 0xD0, 0x75, 0x2C]

theorem code_l101e0c : ∀ x ∈ codeRange 0x101e0c bytes_l101e0c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e0c 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101e20 (StorePre 0x101e20 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101e20 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x101e20 8 (.sib 4 none 0 (.d8 0x50)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x101e28 (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x101e28 (fun s => s.RIP = 0x101e28) (leaR64Effect 0x101e28 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x101e2d (movR32Imm32Effect 0x101e2d 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x101e2d (fun s => s.RIP = 0x101e2d) (movR32Imm32Effect 0x101e2d 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x101e32 (movR64Imm32Effect 0x101e32 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x101e32 (fun s => s.RIP = 0x101e32) (movR64Imm32Effect 0x101e32 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x101e39 (movR64Imm32Effect 0x101e39 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x101e39 (fun s => s.RIP = 0x101e39) (movR64Imm32Effect 0x101e39 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x101e40 (movR64Imm32Effect 0x101e40 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x101e40 (fun s => s.RIP = 0x101e40) (movR64Imm32Effect 0x101e40 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x101e47 (callEffect (fun _ => 0x1295a0) 0x101e4c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x101e47 (PushPre 0x101e47 5) (callEffect (fun _ => 0x1295a0) 0x101e4c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x101e4c⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l101e4c, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l101e20 : List UInt8 :=
  [0xC7, 0x44, 0x24, 0x50, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x54, 0x24, 0x50, 0xBE, 0x0B, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48, 0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00,
    0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0x54, 0x77, 0x02, 0x00]

theorem code_l101e20 : ∀ x ∈ codeRange 0x101e20 bytes_l101e20, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e20 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e4c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e4c (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 54) (.exec 0x101e4c (LoadPre 0x101e4c (fun s => AddrMode.addr (.abs (some 1) 3 0x2022b8) s (0x101e4c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101e4c 2 (.abs (some 1) 3 0x2022b8)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x101e54 (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x101e54 (fun s => s.RIP = 0x101e54) (leaR64Effect 0x101e54 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e59 (movR64R64Effect 0x101e59 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 58) (.exec 0x101e59 (fun s => s.RIP = 0x101e59) (movR64R64Effect 0x101e59 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x101e5c (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101e5c (GoesTo (CallMemPre 0x101e5c (.rip 0x101f6e)) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) 0x12a820) (callEffect (callMemPtr 0x101e5c (.rip 0x101f6e)) (0x101e5c + BitVec.ofNat 64 (callMemLen (.rip 0x101f6e)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101e62⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(1, 1), (2, 53), (3, 3), (4, 59), (5, 5), (6, 55), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101e62, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101e4c : List UInt8 :=
  [0x48, 0x8B, 0x14, 0xCD, 0xB8, 0x22, 0x20, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x0F, 0x4C, 0x89, 0xF7,
    0xFF, 0x15, 0x6E, 0x1F, 0x10, 0x00]

theorem code_l101e4c : ∀ x ∈ codeRange 0x101e4c bytes_l101e4c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e4c 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e62 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e62 (movR32R32Effect 0x101e62 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x101e62 (fun s => s.RIP = 0x101e62) (movR32R32Effect 0x101e62 2 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101e64 (addR64Imm32Effect 0x101e64 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x101e64 (fun s => s.RIP = 0x101e64) (addR64Imm32Effect 0x101e64 4 0xe8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101e6b (popR64Effect 0x101e6b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x101e6b (popR64Effect 0x101e6b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x101e6b (PopPre 0x101e6b) (popR64Effect 0x101e6b 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x101e6c (popR64Effect 0x101e6c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x101e6c (popR64Effect 0x101e6c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x101e6c (PopPre 0x101e6c) (popR64Effect 0x101e6c 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x101e6e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x101e6e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x101e6e (RetPre 0x101e6e) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l101e62 : List UInt8 :=
  [0x89, 0xD8, 0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l101e62 : ∀ x ∈ codeRange 0x101e62 bytes_l101e62, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e62 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106390 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106390 (pushR64Effect 0x106390 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x106390 (PushPre 0x106390 2) (pushR64Effect 0x106390 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x106392 (pushR64Effect 0x106392 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x106392 (PushPre 0x106392 2) (pushR64Effect 0x106392 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x106394 (pushR64Effect 0x106394 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x106394 (PushPre 0x106394 2) (pushR64Effect 0x106394 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x106396 (pushR64Effect 0x106396 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x106396 (PushPre 0x106396 1) (pushR64Effect 0x106396 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x106397 (subR64Imm32Effect 0x106397 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x106397 (fun s => s.RIP = 0x106397) (subR64Imm32Effect 0x106397 4 0x138) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x10639e (testR64R64Effect 0x10639e 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 64) (.exec 0x10639e (fun s => s.RIP = 0x10639e) (testR64R64Effect 0x10639e 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 65) (.pure (condOp 4)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l106560, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l1063a7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106390 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x38, 0x01, 0x00, 0x00, 0x48, 0x85,
    0xD2, 0x0F, 0x84, 0xB9, 0x01, 0x00, 0x00]

theorem code_l106390 : ∀ x ∈ codeRange 0x106390 bytes_l106390, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6390 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063a7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063a7 (movzxR32M8Effect 0x1063a7 3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x1063a7 (LoadPre 0x1063a7 (fun s => AddrMode.addr (.base 6 .none) s (0x1063a7 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1063a7 3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1063aa (cmpR64Imm8Effect 0x1063aa 1 0x6) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[53]
    (.letOp (n := 56) (.exec 0x1063aa (fun s => s.RIP = 0x1063aa) (cmpR64Imm8Effect 0x1063aa 1 0x6) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1063ae (atFlags (condHolds 2) (setccR8Effect 0x1063ae 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 55]
    (.letOp (n := 58) (.exec 0x1063ae (fun s => s.RIP = 0x1063ae) (atFlags (condHolds 2) (setccR8Effect 0x1063ae 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 55]
    (.letOp (n := 59) (.out 0x1063b1 (movR8Imm8Effect 0x1063b1 3 8 0x3d) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 60) (.exec 0x1063b1 (fun s => s.RIP = 0x1063b1) (movR8Imm8Effect 0x1063b1 3 8 0x3d) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 61) (.out 0x1063b4 (shrR8ClEffect 0x1063b4 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[59, 53]
    (.letOp (n := 62) (.exec 0x1063b4 (fun s => s.RIP = 0x1063b4) (shrR8ClEffect 0x1063b4 3 8) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 53]
    (.letOp (n := 63) (.out 0x1063b7 (andR8R8Effect 0x1063b7 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x1063b7 (fun s => s.RIP = 0x1063b7) (andR8R8Effect 0x1063b7 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x1063ba (cmpR8Imm8Effect 0x1063ba 4 8 0x1) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[63]
    (.letOp (n := 66) (.exec 0x1063ba (fun s => s.RIP = 0x1063ba) (cmpR8Imm8Effect 0x1063ba 4 8 0x1) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.pure (condOp 5)) #v[65]
    (.terminate (.condBr (Fin.last 67) ⟨.l106560, RegMap.args [(0, 57), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ ⟨.l1063c4, RegMap.args [(0, 57), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l1063a7 : List UInt8 :=
  [0x0F, 0xB6, 0x0E, 0x48, 0x83, 0xF9, 0x06, 0x0F, 0x92, 0xC0, 0x41, 0xB0, 0x3D, 0x41, 0xD2, 0xE8,
    0x41, 0x20, 0xC0, 0x41, 0x80, 0xF8, 0x01, 0x0F, 0x85, 0x9C, 0x01, 0x00, 0x00]

theorem code_l1063a7 : ∀ x ∈ codeRange 0x1063a7 bytes_l1063a7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63a7 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063c4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063c4 (cmpR64M64Effect 0x1063c4 2 (.abs (some 1) 3 0x202548)) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[2, 1]
    (.letOp (n := 54) (.exec 0x1063c4 (LoadPre 0x1063c4 (fun s => AddrMode.addr (.abs (some 1) 3 0x202548) s (0x1063c4 + BitVec.ofNat 64 8)) 8) (cmpR64M64Effect 0x1063c4 2 (.abs (some 1) 3 0x202548)) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l106560, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1063d2, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1063c4 : List UInt8 :=
  [0x48, 0x3B, 0x14, 0xCD, 0x48, 0x25, 0x20, 0x00, 0x0F, 0x85, 0x8E, 0x01, 0x00, 0x00]

theorem code_l1063c4 : ∀ x ∈ codeRange 0x1063c4 bytes_l1063c4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63c4 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1063d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1063d2 (movR64R64Effect 0x1063d2 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 54) (.exec 0x1063d2 (fun s => s.RIP = 0x1063d2) (movR64R64Effect 0x1063d2 15 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1063d5 (movR32Imm32Effect 0x1063d5 5 1 0x41) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1063d5 (fun s => s.RIP = 0x1063d5) (movR32Imm32Effect 0x1063d5 5 1 0x41) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1063da (subR64R64Effect 0x1063da 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[55, 2]
    (.letOp (n := 58) (.exec 0x1063da (fun s => s.RIP = 0x1063da) (subR64R64Effect 0x1063da 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[55, 2]
    (.letOp (n := 59) (.out 0x1063dd (xorR32R32Effect 0x1063dd 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 60) (.exec 0x1063dd (fun s => s.RIP = 0x1063dd) (xorR32R32Effect 0x1063dd 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 61) (.out 0x1063e0 (cmpR64Imm8Effect 0x1063e0 2 0x41) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 62) (.exec 0x1063e0 (fun s => s.RIP = 0x1063e0) (cmpR64Imm8Effect 0x1063e0 2 0x41) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.out 0x1063e4 (movR32Imm32Effect 0x1063e4 5 0 0x0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 64) (.exec 0x1063e4 (fun s => s.RIP = 0x1063e4) (movR32Imm32Effect 0x1063e4 5 0 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1063e9 (atFlags (condHolds 2) (cmovR64R64Effect 0x1063e9 4 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[63, 57, 61]
    (.letOp (n := 66) (.exec 0x1063e9 (fun s => s.RIP = 0x1063e9) (atFlags (condHolds 2) (cmovR64R64Effect 0x1063e9 4 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[63, 57, 61]
    (.letOp (n := 67) (.out 0x1063ed (leaR64Effect 0x1063ed 7 (.sib 4 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 2] []) (.reg (.gpr 7))) #v[4, 2]
    (.letOp (n := 68) (.exec 0x1063ed (fun s => s.RIP = 0x1063ed) (leaR64Effect 0x1063ed 7 (.sib 4 (some 2) 0 .none)) (Reg.operands [.gpr 4, .gpr 2] [])) #v[4, 2]
    (.letOp (n := 69) (.out 0x1063f1 (addR64Imm32Effect 0x1063f1 7 0xa0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x1063f1 (fun s => s.RIP = 0x1063f1) (addR64Imm32Effect 0x1063f1 7 0xa0) (Reg.operands [.gpr 7] [])) #v[67]
    (.letOp (n := 71) (.out 0x1063f8 (movR64R64Effect 0x1063f8 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 72) (.exec 0x1063f8 (fun s => s.RIP = 0x1063f8) (movR64R64Effect 0x1063f8 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x1063fb (xorR32R32Effect 0x1063fb 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 74) (.exec 0x1063fb (fun s => s.RIP = 0x1063fb) (xorR32R32Effect 0x1063fb 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 75) (.out 0x1063fd (movR64R64Effect 0x1063fd 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 76) (.exec 0x1063fd (fun s => s.RIP = 0x1063fd) (movR64R64Effect 0x1063fd 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 77) (.out 0x106400 (movR64R64Effect 0x106400 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 78) (.exec 0x106400 (fun s => s.RIP = 0x106400) (movR64R64Effect 0x106400 2 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 79) (.out 0x106403 (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x106403 (GoesTo (CallMemPre 0x106403 (.rip 0xfda07)) (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) 0x12a700) (callEffect (callMemPtr 0x106403 (.rip 0xfda07)) (0x106403 + BitVec.ofNat 64 (callMemLen (.rip 0xfda07)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x106409⟩) #v[]
    (.terminate (.call ⟨.l12a700, RegMap.args [(0, 65), (1, 57), (2, 77), (3, 71), (4, 79), (5, 5), (6, 73), (7, 69), (9, 9), (10, 10), (11, 11), (12, 59), (13, 13), (14, 75), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l106409, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1063d2 : List UInt8 :=
  [0x49, 0x89, 0xFF, 0xB9, 0x41, 0x00, 0x00, 0x00, 0x48, 0x29, 0xD1, 0x45, 0x31, 0xE4, 0x48, 0x83,
    0xFA, 0x41, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x0F, 0x42, 0xC1, 0x48, 0x8D, 0x3C, 0x14, 0x48,
    0x81, 0xC7, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF3, 0x31, 0xF6, 0x49, 0x89, 0xD6, 0x48, 0x89,
    0xC2, 0xFF, 0x15, 0x07, 0xDA, 0x0F, 0x00]

theorem code_l1063d2 : ∀ x ∈ codeRange 0x1063d2 bytes_l1063d2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x63d2 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106409 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106409 (leaR64Effect 0x106409 7 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x106409 (fun s => s.RIP = 0x106409) (leaR64Effect 0x106409 7 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106411 (movR64R64Effect 0x106411 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 56) (.exec 0x106411 (fun s => s.RIP = 0x106411) (movR64R64Effect 0x106411 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x106414 (movR64R64Effect 0x106414 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 58) (.exec 0x106414 (fun s => s.RIP = 0x106414) (movR64R64Effect 0x106414 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x106417 (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106417 (GoesTo (CallMemPre 0x106417 (.rip 0xfd9b3)) (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) 0x12a820) (callEffect (callMemPtr 0x106417 (.rip 0xfd9b3)) (0x106417 + BitVec.ofNat 64 (callMemLen (.rip 0xfd9b3)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10641d⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10641d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106409 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xF2, 0xFF, 0x15,
    0xB3, 0xD9, 0x0F, 0x00]

theorem code_l106409 : ∀ x ∈ codeRange 0x106409 bytes_l106409, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6409 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10641d_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x106499 (movR64M64Effect 0x106499 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x106499 (LoadPre 0x106499 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106499 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106499 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10649e (movR64M64Effect 0x10649e 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x10649e (LoadPre 0x10649e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10649e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10649e 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1064a3 (StorePre 0x1064a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1064a3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064a3 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 88) (.exec 0x1064a8 (StorePre 0x1064a8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x1064a8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064a8 1 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 89) (.out 0x1064ad (movR64M64Effect 0x1064ad 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x1064ad (LoadPre 0x1064ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1064ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064ad 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.exec 0x1064b2 (StorePre 0x1064b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x1064b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064b2 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.out 0x1064b7 (movR64M64Effect 0x1064b7 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 93) (.exec 0x1064b7 (LoadPre 0x1064b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1064b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064b7 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.exec 0x1064bc (StorePre 0x1064bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x27)) s (0x1064bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064bc 0 (.sib 4 none 0 (.d8 0x27))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x1064c1 (movR64M64Effect 0x1064c1 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 96) (.exec 0x1064c1 (LoadPre 0x1064c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1064c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064c1 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.exec 0x1064c6 (StorePre 0x1064c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2f)) s (0x1064c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064c6 0 (.sib 4 none 0 (.d8 0x2f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x1064cb (movR64M64Effect 0x1064cb 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 99) (.exec 0x1064cb (LoadPre 0x1064cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1064cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064cb 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.exec 0x1064d0 (StorePre 0x1064d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x37)) s (0x1064d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064d0 0 (.sib 4 none 0 (.d8 0x37))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 101) (.out 0x1064d5 (movR64M64Effect 0x1064d5 0 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 102) (.exec 0x1064d5 (LoadPre 0x1064d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1064d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1064d5 0 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.exec 0x1064da (StorePre 0x1064da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3d)) s (0x1064da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1064da 0 (.sib 4 none 0 (.d8 0x3d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[101, 4]
    (.letOp (n := 104) (.out 0x1064df (leaR64Effect 0x1064df 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 105) (.exec 0x1064df (fun s => s.RIP = 0x1064df) (leaR64Effect 0x1064df 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x1064e7 (leaR64Effect 0x1064e7 6 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 107) (.exec 0x1064e7 (fun s => s.RIP = 0x1064e7) (leaR64Effect 0x1064e7 6 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 108) (.out 0x1064ec (movR64R64Effect 0x1064ec 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[104]
    (.letOp (n := 109) (.exec 0x1064ec (fun s => s.RIP = 0x1064ec) (movR64R64Effect 0x1064ec 7 3) (Reg.operands [.gpr 3] [])) #v[104]
    (.letOp (n := 110) (.out 0x1064ef (callEffect (fun _ => 0x121480) 0x1064f4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 111) (.exec 0x1064ef (PushPre 0x1064ef 5) (callEffect (fun _ => 0x121480) 0x1064f4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.const ⟨64, 0x1064f4⟩) #v[]
    (.terminate (.call ⟨.l121480, RegMap.args [(0, 101), (1, 85), (3, 104), (4, 110), (5, 5), (6, 106), (7, 108), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 113⟩ { target := .l1064f4, kept := #v[], arity := rfl, guard := some (Fin.last 112) })))))))))))))))))))))))))))))))

def bytes_l10641d_1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x0F, 0x48,
    0x89, 0x4C, 0x24, 0x17, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x1F, 0x48, 0x8B,
    0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x27, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44,
    0x24, 0x2F, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x37, 0x48, 0x8B, 0x44, 0x24,
    0x76, 0x48, 0x89, 0x44, 0x24, 0x3D, 0x48, 0x8D, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D,
    0x74, 0x24, 0x04, 0x48, 0x89, 0xDF, 0xE8, 0x8C, 0xAF, 0x01, 0x00]

theorem code_l10641d_1 : ∀ x ∈ codeRange 0x106499 bytes_l10641d_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6499 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10641d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10641d (movR32M32LowEffect 0x10641d 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10641d (LoadPre 0x10641d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10641d + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10641d 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106424 (movR32M32LowEffect 0x106424 1 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x106424 (LoadPre 0x106424 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x106424 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106424 1 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10642b (StorePre 0x10642b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10642b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10642b 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x10642f (StorePre 0x10642f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10642f + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10642f 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x106433 (movR32M32LowEffect 0x106433 0 (.sib 4 none 0 (.d32 0xa7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x106433 (LoadPre 0x106433 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa7)) s (0x106433 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106433 0 (.sib 4 none 0 (.d32 0xa7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10643a (movR64M64Effect 0x10643a 1 (.sib 4 none 0 (.d32 0xab))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x10643a (LoadPre 0x10643a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xab)) s (0x10643a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10643a 1 (.sib 4 none 0 (.d32 0xab))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x106442 (StorePre 0x106442 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106442 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106442 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x106447 (movR64M64Effect 0x106447 1 (.sib 4 none 0 (.d32 0xb3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x106447 (LoadPre 0x106447 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb3)) s (0x106447 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106447 1 (.sib 4 none 0 (.d32 0xb3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10644f (StorePre 0x10644f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10644f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10644f 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x106454 (movR64M64Effect 0x106454 1 (.sib 4 none 0 (.d32 0xbb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x106454 (LoadPre 0x106454 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbb)) s (0x106454 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106454 1 (.sib 4 none 0 (.d32 0xbb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10645c (StorePre 0x10645c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10645c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10645c 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x106461 (movR64M64Effect 0x106461 1 (.sib 4 none 0 (.d32 0xc3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 71) (.exec 0x106461 (LoadPre 0x106461 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc3)) s (0x106461 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106461 1 (.sib 4 none 0 (.d32 0xc3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x106469 (StorePre 0x106469 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x106469 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106469 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x10646e (movR64M64Effect 0x10646e 1 (.sib 4 none 0 (.d32 0xcb))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x10646e (LoadPre 0x10646e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcb)) s (0x10646e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10646e 1 (.sib 4 none 0 (.d32 0xcb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x106476 (StorePre 0x106476 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106476 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106476 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x10647b (movR64M64Effect 0x10647b 1 (.sib 4 none 0 (.d32 0xd3))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 77) (.exec 0x10647b (LoadPre 0x10647b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd3)) s (0x10647b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10647b 1 (.sib 4 none 0 (.d32 0xd3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x106483 (StorePre 0x106483 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x106483 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106483 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x106488 (movR64M64Effect 0x106488 1 (.sib 4 none 0 (.d32 0xd9))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 80) (.exec 0x106488 (LoadPre 0x106488 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd9)) s (0x106488 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x106488 1 (.sib 4 none 0 (.d32 0xd9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x106490 (StorePre 0x106490 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x106490 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106490 1 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x106495 (StorePre 0x106495 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106495 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106495 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (b_l10641d_1))))))))))))))))))))))))))))))

def bytes_l10641d : List UInt8 :=
  [0x8B, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x8B, 0x8C, 0x24, 0xA3, 0x00, 0x00, 0x00, 0x89, 0x44,
    0x24, 0x04, 0x89, 0x4C, 0x24, 0x07, 0x8B, 0x84, 0x24, 0xA7, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x8C,
    0x24, 0xAB, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x48, 0x8B, 0x8C, 0x24, 0xB3, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x8C, 0x24, 0xBB, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x8C, 0x24, 0xC3, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24,
    0x60, 0x48, 0x8B, 0x8C, 0x24, 0xCB, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x48, 0x8B,
    0x8C, 0x24, 0xD3, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x70, 0x48, 0x8B, 0x8C, 0x24, 0xD9,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x24, 0x76, 0x89, 0x44, 0x24, 0x0B] ++ bytes_l10641d_1

theorem code_l10641d : ∀ x ∈ codeRange 0x10641d bytes_l10641d, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x641d 124 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10641d_1

@[cfg_block] def b_l1064f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1064f4 (leaR64Effect 0x1064f4 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1064f4 (fun s => s.RIP = 0x1064f4) (leaR64Effect 0x1064f4 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1064f9 (movR32Imm32Effect 0x1064f9 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x1064f9 (fun s => s.RIP = 0x1064f9) (movR32Imm32Effect 0x1064f9 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1064fe (movR64R64Effect 0x1064fe 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x1064fe (fun s => s.RIP = 0x1064fe) (movR64R64Effect 0x1064fe 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x106501 (repMovsqEffect 0x106501) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[57, 53, 55, 22]
    (.letOp (n := 60) (.exec 0x106501 (RepPre 0x106501 (RepMovsqPre 0x106501)) (repMovsqEffect 0x106501) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[57, 53, 55, 22]
    (.letOp (n := 61) (.out 0x106504 (movzxR32M8Effect 0x106504 5 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 62) (.exec 0x106504 (LoadPre 0x106504 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x106504 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106504 5 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x106509 (movzxR32R8Effect 0x106509 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x106509 (fun s => s.RIP = 0x106509) (movzxR32R8Effect 0x106509 3 1 0) (Reg.operands [.gpr 0] [])) #v[61]
    (.letOp (n := 65) (.out 0x10650c (leaR32Effect 0x10650c 3 2 (.base 1 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 66) (.exec 0x10650c (fun s => s.RIP = 0x10650c) (leaR32Effect 0x10650c 3 2 (.base 1 (.d8 0xfe))) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x10650f (cmpR32Imm8Effect 0x10650f 3 2 0x4) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[65]
    (.letOp (n := 68) (.exec 0x10650f (fun s => s.RIP = 0x10650f) (cmpR32Imm8Effect 0x10650f 3 2 0x4) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.pure (condOp 2)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l106518, RegMap.args [(0, 61), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l106514, RegMap.args [(0, 61), (1, 63), (2, 65), (3, 3), (4, 4), (5, 5), (6, 59), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (16, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1064f4 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xF3, 0x48, 0xA5,
    0x0F, 0xB6, 0x44, 0x24, 0x04, 0x0F, 0xB6, 0xC8, 0x8D, 0x51, 0xFE, 0x83, 0xFA, 0x04, 0x72, 0x04]

theorem code_l1064f4 : ∀ x ∈ codeRange 0x1064f4 bytes_l1064f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x64f4 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106514 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106514 (testR32R32Effect 0x106514 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x106514 (fun s => s.RIP = 0x106514) (testR32R32Effect 0x106514 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10657a, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l106518, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l106514 : List UInt8 :=
  [0x85, 0xC9, 0x75, 0x62]

theorem code_l106514 : ∀ x ∈ codeRange 0x106514 bytes_l106514, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6514 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106518 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106518 (movzxR32M8Effect 0x106518 8 1 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106518 (LoadPre 0x106518 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x106518 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x106518 8 1 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106520 (andR8Imm8Effect 0x106520 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x106520 (fun s => s.RIP = 0x106520) (andR8Imm8Effect 0x106520 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x106523 (testR8R8Effect 0x106523 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 58) (.exec 0x106523 (fun s => s.RIP = 0x106523) (testR8R8Effect 0x106523 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 59) (.out 0x106525 (movzxR32R8Effect 0x106525 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 60) (.exec 0x106525 (fun s => s.RIP = 0x106525) (movzxR32R8Effect 0x106525 3 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 61) (.out 0x106528 (atFlags (condHolds 4) (cmovR32R32Effect 0x106528 4 0 12)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[59, 12, 57]
    (.letOp (n := 62) (.exec 0x106528 (fun s => s.RIP = 0x106528) (atFlags (condHolds 4) (cmovR32R32Effect 0x106528 4 0 12)) (Reg.operands [.gpr 0, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 12, 57]
    (.letOp (n := 63) (.exec 0x10652c (StorePre 0x10652c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10652c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10652c 7 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x106533 (leaR64Effect 0x106533 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x106533 (fun s => s.RIP = 0x106533) (leaR64Effect 0x106533 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x10653b (cmpM8Imm8Effect 0x10653b 8 (.sib 4 none 0 (.d32 0xa0)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 67) (.exec 0x10653b (LoadPre 0x10653b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10653b + BitVec.ofNat 64 8)) 1) (cmpM8Imm8Effect 0x10653b 8 (.sib 4 none 0 (.d32 0xa0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x106543 (movR64R64Effect 0x106543 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 69) (.exec 0x106543 (fun s => s.RIP = 0x106543) (movR64R64Effect 0x106543 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 70) (.pure (condOp 4)) #v[66]
    (.terminate (.condBr (Fin.last 70) ⟨.l106560, RegMap.args [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l106548, RegMap.args [(0, 64), (1, 55), (2, 2), (4, 4), (5, 5), (6, 6), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l106518 : List UInt8 :=
  [0x0F, 0xB6, 0x8C, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x80, 0xE1, 0x01, 0x84, 0xC0, 0x0F, 0xB6, 0xC1,
    0x41, 0x0F, 0x44, 0xC4, 0x88, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x84, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x80, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x74, 0x18]

theorem code_l106518 : ∀ x ∈ codeRange 0x106518 bytes_l106518, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6518 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106548 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106548 (addR64Imm8Effect 0x106548 7 0x8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 54) (.exec 0x106548 (fun s => s.RIP = 0x106548) (addR64Imm8Effect 0x106548 7 0x8) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x10654c (leaR64Effect 0x10654c 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10654c (fun s => s.RIP = 0x10654c) (leaR64Effect 0x10654c 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106551 (movR32Imm32Effect 0x106551 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x106551 (fun s => s.RIP = 0x106551) (movR32Imm32Effect 0x106551 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x106556 (repMovsqEffect 0x106556) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 6))) #v[55, 53, 57, 22]
    (.letOp (n := 60) (.out 0x106556 (repMovsqEffect 0x106556) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 7, .gpr 1, .df] []) (.reg (.gpr 1))) #v[55, 53, 57, 22]
    (.letOp (n := 61) (.exec 0x106556 (RepPre 0x106556 (RepMovsqPre 0x106556)) (repMovsqEffect 0x106556) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[55, 53, 57, 22]
    (.letOp (n := 62) (.out 0x106559 (movR64R64Effect 0x106559 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 63) (.exec 0x106559 (fun s => s.RIP = 0x106559) (movR64R64Effect 0x106559 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 64) (.out 0x10655c (xorR32R32Effect 0x10655c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 65) (.exec 0x10655c (fun s => s.RIP = 0x10655c) (xorR32R32Effect 0x10655c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l106565, RegMap.args [(0, 64), (1, 60), (2, 2), (4, 4), (5, 5), (6, 59), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l106548 : List UInt8 :=
  [0x48, 0x83, 0xC7, 0x08, 0x48, 0x8D, 0x74, 0x24, 0x48, 0xB9, 0x0B, 0x00, 0x00, 0x00, 0xF3, 0x48,
    0xA5, 0x4C, 0x89, 0xFF, 0x31, 0xC0, 0xEB, 0x05]

theorem code_l106548 : ∀ x ∈ codeRange 0x106548 bytes_l106548, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6548 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106560 (movR32Imm32Effect 0x106560 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x106560 (fun s => s.RIP = 0x106560) (movR32Imm32Effect 0x106560 5 0 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l106565, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l106560 : List UInt8 :=
  [0xB8, 0x01, 0x00, 0x00, 0x00]

theorem code_l106560 : ∀ x ∈ codeRange 0x106560 bytes_l106560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6560 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106565 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106565 (StorePre 0x106565 3 (fun s => AddrMode.addr (.base 7 .none) s (0x106565 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106565 0 (.base 7 .none)) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 7]
    (.letOp (n := 54) (.out 0x106568 (movR64R64Effect 0x106568 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 55) (.exec 0x106568 (fun s => s.RIP = 0x106568) (movR64R64Effect 0x106568 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 56) (.out 0x10656b (addR64Imm32Effect 0x10656b 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x10656b (fun s => s.RIP = 0x10656b) (addR64Imm32Effect 0x10656b 4 0x138) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x106572 (popR64Effect 0x106572 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[56]
    (.letOp (n := 59) (.out 0x106572 (popR64Effect 0x106572 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x106572 (PopPre 0x106572) (popR64Effect 0x106572 1 3) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x106573 (popR64Effect 0x106573 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[59]
    (.letOp (n := 62) (.out 0x106573 (popR64Effect 0x106573 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x106573 (PopPre 0x106573) (popR64Effect 0x106573 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x106575 (popR64Effect 0x106575 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x106575 (popR64Effect 0x106575 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x106575 (PopPre 0x106575) (popR64Effect 0x106575 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x106577 (popR64Effect 0x106577 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x106577 (popR64Effect 0x106577 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x106577 (PopPre 0x106577) (popR64Effect 0x106577 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x106579 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[68]
    (.letOp (n := 71) (.out 0x106579 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x106579 (RetPre 0x106579) (retEffect) (Reg.operands [.gpr 4] [])) #v[68]
    (.terminate (.ret (RegMap.args [(0, 54), (1, 1), (2, 2), (3, 58), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 61), (13, 13), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 73) (some ⟨70, by decide⟩))))))))))))))))))))))

def bytes_l106565 : List UInt8 :=
  [0x48, 0x89, 0x07, 0x48, 0x89, 0xF8, 0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C,
    0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l106565 : ∀ x ∈ codeRange 0x106565 bytes_l106565, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6565 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10657a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10657a (StorePre 0x10657a 11 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x10657a + BitVec.ofNat 64 11)) 4) (movM32Imm32Effect 0x10657a 11 (.sib 4 none 0 (.d32 0x100)) 0x3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.out 0x106585 (leaR64Effect 0x106585 2 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x106585 (fun s => s.RIP = 0x106585) (leaR64Effect 0x106585 2 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10658d (movR32Imm32Effect 0x10658d 5 6 0xb) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 57) (.exec 0x10658d (fun s => s.RIP = 0x10658d) (movR32Imm32Effect 0x10658d 5 6 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x106592 (movR64Imm32Effect 0x106592 7 0x202800) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 59) (.exec 0x106592 (fun s => s.RIP = 0x106592) (movR64Imm32Effect 0x106592 7 0x202800) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x106599 (movR64Imm32Effect 0x106599 1 0x2027e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x106599 (fun s => s.RIP = 0x106599) (movR64Imm32Effect 0x106599 1 0x2027e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1065a0 (movR64Imm32Effect 0x1065a0 8 0x202810) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 63) (.exec 0x1065a0 (fun s => s.RIP = 0x1065a0) (movR64Imm32Effect 0x1065a0 8 0x202810) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1065a7 (callEffect (fun _ => 0x1295a0) 0x1065ac) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x1065a7 (PushPre 0x1065a7 5) (callEffect (fun _ => 0x1295a0) 0x1065ac) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x1065ac⟩) #v[]
    (.terminate (.call ⟨.l1295a0, RegMap.args [(1, 60), (2, 54), (4, 64), (5, 5), (6, 56), (7, 58), (8, 62)] 67⟩ { target := .l1065ac, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l10657a : List UInt8 :=
  [0xC7, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0x00,
    0x01, 0x00, 0x00, 0xBE, 0x0B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x00, 0x28, 0x20, 0x00, 0x48,
    0xC7, 0xC1, 0xE0, 0x27, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x10, 0x28, 0x20, 0x00, 0xE8, 0xF4, 0x2F,
    0x02, 0x00]

theorem code_l10657a : ∀ x ∈ codeRange 0x10657a bytes_l10657a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x657a 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1065ac (fun s => s.RIP = 0x1065ac) (fun _ => nopEffect 0x1065ac 4) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x1065b0 (pushR64Effect 0x1065b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x1065b0 (PushPre 0x1065b0 1) (pushR64Effect 0x1065b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x1065b1 (pushR64Effect 0x1065b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x1065b1 (PushPre 0x1065b1 2) (pushR64Effect 0x1065b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x1065b3 (pushR64Effect 0x1065b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x1065b3 (PushPre 0x1065b3 2) (pushR64Effect 0x1065b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x1065b5 (pushR64Effect 0x1065b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x1065b5 (PushPre 0x1065b5 2) (pushR64Effect 0x1065b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x1065b7 (pushR64Effect 0x1065b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x1065b7 (PushPre 0x1065b7 2) (pushR64Effect 0x1065b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x1065b9 (pushR64Effect 0x1065b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x1065b9 (PushPre 0x1065b9 1) (pushR64Effect 0x1065b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x1065ba (subR64Imm8Effect 0x1065ba 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x1065ba (fun s => s.RIP = 0x1065ba) (subR64Imm8Effect 0x1065ba 4 0x18) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.out 0x1065be (cmpR32Imm32Effect 0x1065be 6 2 0x100) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 69) (.exec 0x1065be (fun s => s.RIP = 0x1065be) (cmpR32Imm32Effect 0x1065be 6 2 0x100) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 70) (.pure (condOp 3)) #v[68]
    (.terminate (.condBr (Fin.last 70) ⟨.l106764, RegMap.args [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l1065ca, RegMap.args [(2, 2), (3, 3), (4, 66), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1065ac : List UInt8 :=
  [0x0F, 0x1F, 0x40, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83,
    0xEC, 0x18, 0x81, 0xFA, 0x00, 0x01, 0x00, 0x00, 0x0F, 0x83, 0x9A, 0x01, 0x00, 0x00]

theorem code_l1065ac : ∀ x ∈ codeRange 0x1065ac bytes_l1065ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x65ac 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ca_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x10661b (StorePre 0x10661b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10661b 4 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x10661f (movzxR32M8Effect 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x10661f (LoadPre 0x10661f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10661f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10661f 5 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x106624 (StorePre 0x106624 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106624 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106624 4 1 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 90) (.out 0x106628 (movzxR32M8Effect 0x106628 5 6 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 91) (.exec 0x106628 (LoadPre 0x106628 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106628 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106628 5 6 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.exec 0x10662d (StorePre 0x10662d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10662d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10662d 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 93) (.out 0x106631 (movzxR32M8Effect 0x106631 6 8 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 94) (.exec 0x106631 (LoadPre 0x106631 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106631 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106631 6 8 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.exec 0x106637 (StorePre 0x106637 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106637 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106637 4 1 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 96) (.out 0x10663b (movzxR32M8Effect 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 97) (.exec 0x10663b (LoadPre 0x10663b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x10663b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10663b 6 11 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x106641 (andR32Imm8Effect 0x106641 3 2 0x3f) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 99) (.out 0x106641 (andR32Imm8Effect 0x106641 3 2 0x3f) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 100) (.exec 0x106641 (fun s => s.RIP = 0x106641) (andR32Imm8Effect 0x106641 3 2 0x3f) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 101) (.exec 0x106644 (StorePre 0x106644 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106644 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x106644 5 (.sib 4 none 0 (.d8 0xe)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 99]
    (.letOp (n := 102) (.out 0x106649 (atFlags (condHolds 5) (setccR8Effect 0x106649 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[7, 99]
    (.letOp (n := 103) (.exec 0x106649 (fun s => s.RIP = 0x106649) (atFlags (condHolds 5) (setccR8Effect 0x106649 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[7, 99]
    (.letOp (n := 104) (.exec 0x10664d (fun s => s.RIP = 0x10664d) (leaR64Effect 0x10664d 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x106652 (movzxR32M8Effect 0x106652 5 1 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 106) (.exec 0x106652 (LoadPre 0x106652 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106652 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106652 5 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x106657 (negR32Effect 0x106657 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 108) (.exec 0x106657 (fun s => s.RIP = 0x106657) (negR32Effect 0x106657 2 1) (Reg.operands [.gpr 1] [])) #v[105]
    (.letOp (n := 109) (.out 0x106659 (xorR32Imm8Effect 0x106659 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[98]
    (.letOp (n := 110) (.exec 0x106659 (fun s => s.RIP = 0x106659) (xorR32Imm8Effect 0x106659 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[98]
    (.letOp (n := 111) (.out 0x10665c (andR32R32Effect 0x10665c 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x10665c (fun s => s.RIP = 0x10665c) (andR32R32Effect 0x10665c 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x10665e (cmpR32Imm8Effect 0x10665e 3 2 0x1) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[111]
    (.letOp (n := 114) (.exec 0x10665e (fun s => s.RIP = 0x10665e) (cmpR32Imm8Effect 0x10665e 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 115) (.pure (condOp 4)) #v[113]
    (.terminate (.condBr (Fin.last 115) ⟨.l10677c, RegMap.args [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 113), (22, 22), (39, 39), (50, 50), (51, 51)] 116⟩ ⟨.l106667, RegMap.args [(0, 87), (1, 107), (2, 111), (3, 60), (4, 4), (5, 80), (6, 90), (7, 102), (8, 93), (9, 70), (10, 58), (11, 96), (12, 73), (13, 54), (14, 76), (15, 56), (19, 113), (22, 22), (39, 39), (50, 50), (51, 51)] 116⟩)))))))))))))))))))))))))))))))

def bytes_l1065ca_1 : List UInt8 :=
  [0x88, 0x4C, 0x24, 0x0B, 0x0F, 0xB6, 0x44, 0x24, 0x0B, 0x88, 0x4C, 0x24, 0x0B, 0x0F, 0xB6, 0x74,
    0x24, 0x0B, 0x88, 0x4C, 0x24, 0x0D, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0D, 0x88, 0x4C, 0x24, 0x0D,
    0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x0D, 0x83, 0xE2, 0x3F, 0x0F, 0x95, 0x44, 0x24, 0x0E, 0x40, 0x0F,
    0x95, 0xC7, 0x48, 0x8D, 0x4C, 0x24, 0x0E, 0x0F, 0xB6, 0x4C, 0x24, 0x0E, 0xF7, 0xD9, 0x83, 0xF2,
    0x01, 0x21, 0xCA, 0x83, 0xFA, 0x01, 0x0F, 0x84, 0x15, 0x01, 0x00, 0x00]

theorem code_l1065ca_1 : ∀ x ∈ codeRange 0x10661b bytes_l1065ca_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x661b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1065ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1065ca (StorePre 0x1065ca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1065ca + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1065ca 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x1065cf (movR64M64Effect 0x1065cf 13 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 55) (.exec 0x1065cf (LoadPre 0x1065cf (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1065cf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065cf 13 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 56) (.out 0x1065d3 (movR64M64Effect 0x1065d3 15 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 57) (.exec 0x1065d3 (LoadPre 0x1065d3 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1065d3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065d3 15 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x1065d7 (movR64M64Effect 0x1065d7 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 59) (.exec 0x1065d7 (LoadPre 0x1065d7 (fun s => AddrMode.addr (.base 6 .none) s (0x1065d7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1065d7 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x1065da (movR64M64Effect 0x1065da 3 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 61) (.exec 0x1065da (LoadPre 0x1065da (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1065da + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1065da 3 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.out 0x1065de (movR32R32Effect 0x1065de 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 63) (.exec 0x1065de (fun s => s.RIP = 0x1065de) (movR32R32Effect 0x1065de 2 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 64) (.out 0x1065e0 (shrR8Effect 0x1065e0 3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[62]
    (.letOp (n := 65) (.exec 0x1065e0 (fun s => s.RIP = 0x1065e0) (shrR8Effect 0x1065e0 3 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.out 0x1065e3 (andAlImm8Effect 0x1065e3 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x1065e3 (fun s => s.RIP = 0x1065e3) (andAlImm8Effect 0x1065e3 0x1) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.exec 0x1065e5 (StorePre 0x1065e5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065e5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065e5 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.exec 0x1065e9 (fun s => s.RIP = 0x1065e9) (leaR64Effect 0x1065e9 6 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1065ee (movzxR32M8Effect 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 71) (.exec 0x1065ee (LoadPre 0x1065ee (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065ee + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065ee 6 9 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1065f4 (StorePre 0x1065f4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065f4 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 73) (.out 0x1065f8 (movzxR32M8Effect 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x1065f8 (LoadPre 0x1065f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065f8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1065f8 6 12 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x1065fe (StorePre 0x1065fe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1065fe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1065fe 4 0 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 76) (.out 0x106602 (movzxR32M8Effect 0x106602 6 14 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 77) (.exec 0x106602 (LoadPre 0x106602 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x106602 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x106602 6 14 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.exec 0x106608 (StorePre 0x106608 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106608 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x106608 4 0 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 79) (.exec 0x10660c (fun s => s.RIP = 0x10660c) (leaR64Effect 0x10660c 11 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x106611 (movzxR32M8Effect 0x106611 5 5 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 81) (.exec 0x106611 (LoadPre 0x106611 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x106611 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106611 5 5 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x106616 (movR32R32Effect 0x106616 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 83) (.exec 0x106616 (fun s => s.RIP = 0x106616) (movR32R32Effect 0x106616 2 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 84) (.out 0x106618 (shrR32Effect 0x106618 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[82]
    (.letOp (n := 85) (.exec 0x106618 (fun s => s.RIP = 0x106618) (shrR32Effect 0x106618 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (b_l1065ca_1)))))))))))))))))))))))))))))))))

def bytes_l1065ca : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x6E, 0x18, 0x4C, 0x8B, 0x7E, 0x10, 0x4C, 0x8B, 0x16,
    0x48, 0x8B, 0x5E, 0x08, 0x89, 0xD0, 0xC0, 0xE8, 0x06, 0x24, 0x01, 0x88, 0x44, 0x24, 0x0B, 0x48,
    0x8D, 0x74, 0x24, 0x0B, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x0B, 0x88, 0x44, 0x24, 0x0B, 0x44, 0x0F,
    0xB6, 0x64, 0x24, 0x0B, 0x88, 0x44, 0x24, 0x0B, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0B, 0x88, 0x44,
    0x24, 0x0D, 0x4C, 0x8D, 0x5C, 0x24, 0x0D, 0x0F, 0xB6, 0x6C, 0x24, 0x0D, 0x89, 0xD1, 0xC1, 0xE9,
    0x07] ++ bytes_l1065ca_1

theorem code_l1065ca : ∀ x ∈ codeRange 0x1065ca bytes_l1065ca, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x65ca 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1065ca_1

@[cfg_block] def b_l106667_3 : Block Op Label signature Reg.count 168 :=
  .letOp (n := 168) (.out 0x10672e (xorR64R64Effect 0x10672e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[159, 111]
    (.letOp (n := 169) (.exec 0x10672e (fun s => s.RIP = 0x10672e) (xorR64R64Effect 0x10672e 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[159, 111]
    (.letOp (n := 170) (.out 0x106731 (andR64R64Effect 0x106731 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[168, 166]
    (.letOp (n := 171) (.exec 0x106731 (fun s => s.RIP = 0x106731) (andR64R64Effect 0x106731 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[168, 166]
    (.letOp (n := 172) (.out 0x106734 (xorR64R64Effect 0x106734 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[170, 111]
    (.letOp (n := 173) (.exec 0x106734 (fun s => s.RIP = 0x106734) (xorR64R64Effect 0x106734 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[170, 111]
    (.letOp (n := 174) (.exec 0x106737 (StorePre 0x106737 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x106737 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106737 5 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 175) (.exec 0x10673c (fun s => s.RIP = 0x10673c) (leaR64Effect 0x10673c 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 176) (.out 0x106741 (movR64M64Effect 0x106741 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 177) (.exec 0x106741 (LoadPre 0x106741 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106741 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106741 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 178) (.exec 0x106746 (StorePre 0x106746 3 (fun s => AddrMode.addr (.base 0 .none) s (0x106746 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x106746 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[172, 176]
    (.letOp (n := 179) (.exec 0x106749 (StorePre 0x106749 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x106749 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106749 11 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[161, 176]
    (.letOp (n := 180) (.exec 0x10674d (StorePre 0x10674d 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10674d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10674d 9 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[138, 176]
    (.letOp (n := 181) (.exec 0x106751 (StorePre 0x106751 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x106751 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x106751 10 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[127, 176]
    (.letOp (n := 182) (.out 0x106755 (addR64Imm8Effect 0x106755 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 183) (.exec 0x106755 (fun s => s.RIP = 0x106755) (addR64Imm8Effect 0x106755 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 184) (.out 0x106759 (popR64Effect 0x106759 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[182]
    (.letOp (n := 185) (.out 0x106759 (popR64Effect 0x106759 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[182]
    (.letOp (n := 186) (.exec 0x106759 (PopPre 0x106759) (popR64Effect 0x106759 1 3) (Reg.operands [.gpr 4] [])) #v[182]
    (.letOp (n := 187) (.out 0x10675a (popR64Effect 0x10675a 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[185]
    (.letOp (n := 188) (.out 0x10675a (popR64Effect 0x10675a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[185]
    (.letOp (n := 189) (.exec 0x10675a (PopPre 0x10675a) (popR64Effect 0x10675a 2 12) (Reg.operands [.gpr 4] [])) #v[185]
    (.letOp (n := 190) (.out 0x10675c (popR64Effect 0x10675c 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[188]
    (.letOp (n := 191) (.out 0x10675c (popR64Effect 0x10675c 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[188]
    (.letOp (n := 192) (.exec 0x10675c (PopPre 0x10675c) (popR64Effect 0x10675c 2 13) (Reg.operands [.gpr 4] [])) #v[188]
    (.letOp (n := 193) (.out 0x10675e (popR64Effect 0x10675e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[191]
    (.letOp (n := 194) (.out 0x10675e (popR64Effect 0x10675e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[191]
    (.letOp (n := 195) (.exec 0x10675e (PopPre 0x10675e) (popR64Effect 0x10675e 2 14) (Reg.operands [.gpr 4] [])) #v[191]
    (.letOp (n := 196) (.out 0x106760 (popR64Effect 0x106760 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[194]
    (.letOp (n := 197) (.out 0x106760 (popR64Effect 0x106760 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[194]
    (.letOp (n := 198) (.exec 0x106760 (PopPre 0x106760) (popR64Effect 0x106760 2 15) (Reg.operands [.gpr 4] [])) #v[194]
    (.letOp (n := 199) (.out 0x106762 (popR64Effect 0x106762 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[197]
    (.letOp (n := 200) (.out 0x106762 (popR64Effect 0x106762 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[197]
    (.letOp (n := 201) (.exec 0x106762 (PopPre 0x106762) (popR64Effect 0x106762 1 5) (Reg.operands [.gpr 4] [])) #v[197]
    (.letOp (n := 202) (.out 0x106763 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[200]
    (.letOp (n := 203) (.out 0x106763 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[200]
    (.letOp (n := 204) (.exec 0x106763 (RetPre 0x106763) (retEffect) (Reg.operands [.gpr 4] [])) #v[200]
    (.terminate (.ret (RegMap.args [(0, 176), (1, 166), (2, 103), (3, 184), (4, 203), (5, 199), (6, 87), (7, 7), (8, 172), (9, 138), (10, 127), (11, 161), (12, 187), (13, 190), (14, 193), (15, 196), (22, 22), (39, 39), (50, 50), (51, 51)] 205) (some ⟨202, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l106667_3 : List UInt8 :=
  [0x49, 0x31, 0xC0, 0x49, 0x21, 0xC8, 0x49, 0x31, 0xC0, 0x40, 0x88, 0x7C, 0x24, 0x0F, 0x48, 0x8D,
    0x44, 0x24, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x00, 0x4C, 0x89, 0x58, 0x08, 0x4C,
    0x89, 0x48, 0x10, 0x4C, 0x89, 0x50, 0x18, 0x48, 0x83, 0xC4, 0x18, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l106667_3 : ∀ x ∈ codeRange 0x10672e bytes_l106667_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x672e 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106667_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x1066e8 (movzxR32M8Effect 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 131) (.exec 0x1066e8 (LoadPre 0x1066e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1066e8 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 132) (.out 0x1066ed (negR64Effect 0x1066ed 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[130]
    (.letOp (n := 133) (.exec 0x1066ed (fun s => s.RIP = 0x1066ed) (negR64Effect 0x1066ed 1) (Reg.operands [.gpr 1] [])) #v[130]
    (.letOp (n := 134) (.out 0x1066f0 (xorR64R64Effect 0x1066f0 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[121, 71]
    (.letOp (n := 135) (.exec 0x1066f0 (fun s => s.RIP = 0x1066f0) (xorR64R64Effect 0x1066f0 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[121, 71]
    (.letOp (n := 136) (.out 0x1066f3 (andR64R64Effect 0x1066f3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[134, 132]
    (.letOp (n := 137) (.exec 0x1066f3 (fun s => s.RIP = 0x1066f3) (andR64R64Effect 0x1066f3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[134, 132]
    (.letOp (n := 138) (.out 0x1066f6 (xorR64R64Effect 0x1066f6 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[136, 71]
    (.letOp (n := 139) (.exec 0x1066f6 (fun s => s.RIP = 0x1066f6) (xorR64R64Effect 0x1066f6 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[136, 71]
    (.letOp (n := 140) (.out 0x1066f9 (movR64R64Effect 0x1066f9 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[87]
    (.letOp (n := 141) (.exec 0x1066f9 (fun s => s.RIP = 0x1066f9) (movR64R64Effect 0x1066f9 11 6) (Reg.operands [.gpr 6] [])) #v[87]
    (.letOp (n := 142) (.out 0x1066fc (movR32R32Effect 0x1066fc 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 143) (.exec 0x1066fc (fun s => s.RIP = 0x1066fc) (movR32R32Effect 0x1066fc 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 144) (.out 0x1066fe (shrdR64R64ClEffect 0x1066fe 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[140, 71, 142]
    (.letOp (n := 145) (.exec 0x1066fe (fun s => s.RIP = 0x1066fe) (shrdR64R64ClEffect 0x1066fe 4 11 8) (Reg.operands [.gpr 11, .gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[140, 71, 142]
    (.letOp (n := 146) (.exec 0x106702 (StorePre 0x106702 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106702 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106702 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 147) (.out 0x106707 (movzxR32M8Effect 0x106707 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 148) (.exec 0x106707 (LoadPre 0x106707 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106707 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106707 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x10670c (negR64Effect 0x10670c 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[147]
    (.letOp (n := 150) (.exec 0x10670c (fun s => s.RIP = 0x10670c) (negR64Effect 0x10670c 1) (Reg.operands [.gpr 1] [])) #v[147]
    (.letOp (n := 151) (.out 0x10670f (xorR64R64Effect 0x10670f 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[144, 87]
    (.letOp (n := 152) (.exec 0x10670f (fun s => s.RIP = 0x10670f) (xorR64R64Effect 0x10670f 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[144, 87]
    (.letOp (n := 153) (.out 0x106712 (andR64R64Effect 0x106712 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[151, 149]
    (.letOp (n := 154) (.exec 0x106712 (fun s => s.RIP = 0x106712) (andR64R64Effect 0x106712 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[151, 149]
    (.letOp (n := 155) (.out 0x106715 (movR64R64Effect 0x106715 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 156) (.exec 0x106715 (fun s => s.RIP = 0x106715) (movR64R64Effect 0x106715 8 0) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 157) (.out 0x106718 (movR32R32Effect 0x106718 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 158) (.exec 0x106718 (fun s => s.RIP = 0x106718) (movR32R32Effect 0x106718 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 159) (.out 0x10671a (shrdR64R64ClEffect 0x10671a 4 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[155, 87, 157]
    (.letOp (n := 160) (.exec 0x10671a (fun s => s.RIP = 0x10671a) (shrdR64R64ClEffect 0x10671a 4 8 6) (Reg.operands [.gpr 8, .gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155, 87, 157]
    (.letOp (n := 161) (.out 0x10671e (xorR64R64Effect 0x10671e 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[153, 87]
    (.letOp (n := 162) (.exec 0x10671e (fun s => s.RIP = 0x10671e) (xorR64R64Effect 0x10671e 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[153, 87]
    (.letOp (n := 163) (.exec 0x106721 (StorePre 0x106721 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106721 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x106721 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 164) (.out 0x106726 (movzxR32M8Effect 0x106726 5 1 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 165) (.exec 0x106726 (LoadPre 0x106726 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106726 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x106726 5 1 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 166) (.out 0x10672b (negR64Effect 0x10672b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[164]
    (.letOp (n := 167) (.exec 0x10672b (fun s => s.RIP = 0x10672b) (negR64Effect 0x10672b 1) (Reg.operands [.gpr 1] [])) #v[164]
    (b_l106667_3))))))))))))))))))))))))))))))))))))))

def bytes_l106667_2 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9, 0x4D, 0x31, 0xC1, 0x49, 0x21, 0xC9, 0x4D, 0x31,
    0xC1, 0x49, 0x89, 0xF3, 0x89, 0xD1, 0x4D, 0x0F, 0xAD, 0xC3, 0x40, 0x88, 0x7C, 0x24, 0x0C, 0x0F,
    0xB6, 0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9, 0x49, 0x31, 0xF3, 0x49, 0x21, 0xCB, 0x49, 0x89, 0xC0,
    0x89, 0xD1, 0x49, 0x0F, 0xAD, 0xF0, 0x49, 0x31, 0xF3, 0x40, 0x88, 0x7C, 0x24, 0x0C, 0x0F, 0xB6,
    0x4C, 0x24, 0x0C, 0x48, 0xF7, 0xD9] ++ bytes_l106667_3

theorem code_l106667_2 : ∀ x ∈ codeRange 0x1066e8 bytes_l106667_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x66e8 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_3

@[cfg_block] def b_l106667_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1066a3 (andR64R64Effect 0x1066a3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[91, 89]
    (.letOp (n := 94) (.exec 0x1066a3 (fun s => s.RIP = 0x1066a3) (andR64R64Effect 0x1066a3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[91, 89]
    (.letOp (n := 95) (.out 0x1066a6 (xorR64R64Effect 0x1066a6 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[93, 10]
    (.letOp (n := 96) (.exec 0x1066a6 (fun s => s.RIP = 0x1066a6) (xorR64R64Effect 0x1066a6 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[93, 10]
    (.letOp (n := 97) (.out 0x1066a9 (xorR64R64Effect 0x1066a9 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[69, 95]
    (.letOp (n := 98) (.exec 0x1066a9 (fun s => s.RIP = 0x1066a9) (xorR64R64Effect 0x1066a9 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[69, 95]
    (.letOp (n := 99) (.out 0x1066ac (negR64Effect 0x1066ac 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 100) (.exec 0x1066ac (fun s => s.RIP = 0x1066ac) (negR64Effect 0x1066ac 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 101) (.out 0x1066af (andR64R64Effect 0x1066af 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x1066af (fun s => s.RIP = 0x1066af) (andR64R64Effect 0x1066af 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x1066b2 (xorR8Imm8Effect 0x1066b2 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 104) (.exec 0x1066b2 (fun s => s.RIP = 0x1066b2) (xorR8Imm8Effect 0x1066b2 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 105) (.out 0x1066b5 (movR64R64Effect 0x1066b5 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 11] []) (.reg (.gpr 10))) #v[59]
    (.letOp (n := 106) (.exec 0x1066b5 (fun s => s.RIP = 0x1066b5) (movR64R64Effect 0x1066b5 10 11) (Reg.operands [.gpr 11] [])) #v[59]
    (.letOp (n := 107) (.out 0x1066b8 (movR32R32Effect 0x1066b8 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 108) (.exec 0x1066b8 (fun s => s.RIP = 0x1066b8) (movR32R32Effect 0x1066b8 2 1 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 109) (.out 0x1066ba (shrR64ClEffect 0x1066ba 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[105, 107]
    (.letOp (n := 110) (.exec 0x1066ba (fun s => s.RIP = 0x1066ba) (shrR64ClEffect 0x1066ba 3 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105, 107]
    (.letOp (n := 111) (.out 0x1066bd (xorR64R64Effect 0x1066bd 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[101, 95]
    (.letOp (n := 112) (.exec 0x1066bd (fun s => s.RIP = 0x1066bd) (xorR64R64Effect 0x1066bd 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[101, 95]
    (.letOp (n := 113) (.exec 0x1066c0 (StorePre 0x1066c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066c0 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066c0 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 114) (.exec 0x1066c5 (fun s => s.RIP = 0x1066c5) (leaR64Effect 0x1066c5 3 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 115) (.out 0x1066ca (movzxR32M8Effect 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 116) (.exec 0x1066ca (LoadPre 0x1066ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066ca + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1066ca 6 14 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x1066d0 (negR64Effect 0x1066d0 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[115]
    (.letOp (n := 118) (.exec 0x1066d0 (fun s => s.RIP = 0x1066d0) (negR64Effect 0x1066d0 14) (Reg.operands [.gpr 14] [])) #v[115]
    (.letOp (n := 119) (.out 0x1066d3 (movR64R64Effect 0x1066d3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[71]
    (.letOp (n := 120) (.exec 0x1066d3 (fun s => s.RIP = 0x1066d3) (movR64R64Effect 0x1066d3 9 8) (Reg.operands [.gpr 8] [])) #v[71]
    (.letOp (n := 121) (.out 0x1066d6 (shrdR64R64ClEffect 0x1066d6 4 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[119, 59, 107]
    (.letOp (n := 122) (.exec 0x1066d6 (fun s => s.RIP = 0x1066d6) (shrdR64R64ClEffect 0x1066d6 4 9 11) (Reg.operands [.gpr 9, .gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119, 59, 107]
    (.letOp (n := 123) (.out 0x1066da (xorR64R64Effect 0x1066da 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[109, 59]
    (.letOp (n := 124) (.exec 0x1066da (fun s => s.RIP = 0x1066da) (xorR64R64Effect 0x1066da 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[109, 59]
    (.letOp (n := 125) (.out 0x1066dd (andR64R64Effect 0x1066dd 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[123, 117]
    (.letOp (n := 126) (.exec 0x1066dd (fun s => s.RIP = 0x1066dd) (andR64R64Effect 0x1066dd 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[123, 117]
    (.letOp (n := 127) (.out 0x1066e0 (xorR64R64Effect 0x1066e0 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[125, 59]
    (.letOp (n := 128) (.exec 0x1066e0 (fun s => s.RIP = 0x1066e0) (xorR64R64Effect 0x1066e0 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[125, 59]
    (.letOp (n := 129) (.exec 0x1066e3 (StorePre 0x1066e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1066e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1066e3 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (b_l106667_2)))))))))))))))))))))))))))))))))))))

def bytes_l106667_1 : List UInt8 :=
  [0x49, 0x21, 0xD9, 0x4D, 0x31, 0xD1, 0x4D, 0x31, 0xCE, 0x48, 0xF7, 0xD8, 0x4C, 0x21, 0xF0, 0x80,
    0xF2, 0x01, 0x4D, 0x89, 0xDA, 0x89, 0xD1, 0x49, 0xD3, 0xEA, 0x4C, 0x31, 0xC8, 0x40, 0x88, 0x7C,
    0x24, 0x0C, 0x48, 0x8D, 0x5C, 0x24, 0x0C, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x0C, 0x49, 0xF7, 0xDE,
    0x4D, 0x89, 0xC1, 0x4D, 0x0F, 0xAD, 0xD9, 0x4D, 0x31, 0xDA, 0x4D, 0x21, 0xF2, 0x4D, 0x31, 0xDA,
    0x40, 0x88, 0x7C, 0x24, 0x0C] ++ bytes_l106667_2

theorem code_l106667_1 : ∀ x ∈ codeRange 0x1066a3 bytes_l106667_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x66a3 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_2

@[cfg_block] def b_l106667 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106667 (decR64Effect 0x106667 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 54) (.exec 0x106667 (fun s => s.RIP = 0x106667) (decR64Effect 0x106667 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[11]
    (.letOp (n := 55) (.out 0x10666a (decR64Effect 0x10666a 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x10666a (fun s => s.RIP = 0x10666a) (decR64Effect 0x10666a 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 57) (.out 0x10666d (andR64R64Effect 0x10666d 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x10666d (fun s => s.RIP = 0x10666d) (andR64R64Effect 0x10666d 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x106670 (andR64R64Effect 0x106670 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[53, 57]
    (.letOp (n := 60) (.exec 0x106670 (fun s => s.RIP = 0x106670) (andR64R64Effect 0x106670 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[53, 57]
    (.letOp (n := 61) (.out 0x106673 (decR64Effect 0x106673 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 62) (.exec 0x106673 (fun s => s.RIP = 0x106673) (decR64Effect 0x106673 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 63) (.out 0x106676 (xorR64R64Effect 0x106676 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[13, 15]
    (.letOp (n := 64) (.exec 0x106676 (fun s => s.RIP = 0x106676) (xorR64R64Effect 0x106676 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 15]
    (.letOp (n := 65) (.out 0x106679 (negR64Effect 0x106679 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x106679 (fun s => s.RIP = 0x106679) (negR64Effect 0x106679 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x10667c (andR64R64Effect 0x10667c 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x10667c (fun s => s.RIP = 0x10667c) (andR64R64Effect 0x10667c 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x10667f (xorR64R64Effect 0x10667f 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[67, 15]
    (.letOp (n := 70) (.exec 0x10667f (fun s => s.RIP = 0x10667f) (xorR64R64Effect 0x10667f 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[67, 15]
    (.letOp (n := 71) (.out 0x106682 (andR64R64Effect 0x106682 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[61, 69]
    (.letOp (n := 72) (.exec 0x106682 (fun s => s.RIP = 0x106682) (andR64R64Effect 0x106682 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[61, 69]
    (.letOp (n := 73) (.out 0x106685 (xorR64R64Effect 0x106685 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[15, 3]
    (.letOp (n := 74) (.exec 0x106685 (fun s => s.RIP = 0x106685) (xorR64R64Effect 0x106685 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 75) (.out 0x106688 (negR64Effect 0x106688 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 76) (.exec 0x106688 (fun s => s.RIP = 0x106688) (negR64Effect 0x106688 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 77) (.out 0x10668b (andR64R64Effect 0x10668b 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[75, 73]
    (.letOp (n := 78) (.exec 0x10668b (fun s => s.RIP = 0x10668b) (andR64R64Effect 0x10668b 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[75, 73]
    (.letOp (n := 79) (.out 0x10668e (xorR64R64Effect 0x10668e 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[77, 3]
    (.letOp (n := 80) (.exec 0x10668e (fun s => s.RIP = 0x10668e) (xorR64R64Effect 0x10668e 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 81) (.out 0x106691 (xorR64R64Effect 0x106691 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[57, 79]
    (.letOp (n := 82) (.exec 0x106691 (fun s => s.RIP = 0x106691) (xorR64R64Effect 0x106691 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[57, 79]
    (.letOp (n := 83) (.out 0x106694 (negR64Effect 0x106694 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 84) (.exec 0x106694 (fun s => s.RIP = 0x106694) (negR64Effect 0x106694 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 85) (.out 0x106697 (andR64R64Effect 0x106697 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[83, 81]
    (.letOp (n := 86) (.exec 0x106697 (fun s => s.RIP = 0x106697) (andR64R64Effect 0x106697 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[83, 81]
    (.letOp (n := 87) (.out 0x10669a (xorR64R64Effect 0x10669a 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[85, 79]
    (.letOp (n := 88) (.exec 0x10669a (fun s => s.RIP = 0x10669a) (xorR64R64Effect 0x10669a 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[85, 79]
    (.letOp (n := 89) (.out 0x10669d (xorR64R64Effect 0x10669d 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[3, 10]
    (.letOp (n := 90) (.exec 0x10669d (fun s => s.RIP = 0x10669d) (xorR64R64Effect 0x10669d 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[3, 10]
    (.letOp (n := 91) (.out 0x1066a0 (negR64Effect 0x1066a0 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 92) (.exec 0x1066a0 (fun s => s.RIP = 0x1066a0) (negR64Effect 0x1066a0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (b_l106667_1))))))))))))))))))))))))))))))))))))))))

def bytes_l106667 : List UInt8 :=
  [0x49, 0xFF, 0xCB, 0x48, 0xFF, 0xCD, 0x4C, 0x21, 0xED, 0x49, 0x21, 0xEB, 0x49, 0xFF, 0xC8, 0x4D,
    0x31, 0xFD, 0x49, 0xF7, 0xDE, 0x4D, 0x21, 0xEE, 0x4D, 0x31, 0xFE, 0x4D, 0x21, 0xF0, 0x49, 0x31,
    0xDF, 0x49, 0xF7, 0xDC, 0x4D, 0x21, 0xFC, 0x49, 0x31, 0xDC, 0x4C, 0x31, 0xE5, 0x48, 0xF7, 0xDE,
    0x48, 0x21, 0xEE, 0x4C, 0x31, 0xE6, 0x4C, 0x31, 0xD3, 0x49, 0xF7, 0xD9] ++ bytes_l106667_1

theorem code_l106667 : ∀ x ∈ codeRange 0x106667 bytes_l106667, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6667 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106667_1

@[cfg_block] def b_l106764 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106764 (movR32Imm32Effect 0x106764 5 6 0x37) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x106764 (fun s => s.RIP = 0x106764) (movR32Imm32Effect 0x106764 5 6 0x37) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106769 (movR64Imm32Effect 0x106769 7 0x20249c) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x106769 (fun s => s.RIP = 0x106769) (movR64Imm32Effect 0x106769 7 0x20249c) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106770 (movR64Imm32Effect 0x106770 2 0x2024b8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x106770 (fun s => s.RIP = 0x106770) (movR64Imm32Effect 0x106770 2 0x2024b8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x106777 (callEffect (fun _ => 0x129770) 0x10677c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x106777 (PushPre 0x106777 5) (callEffect (fun _ => 0x129770) 0x10677c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10677c⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l10677c, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l106764 : List UInt8 :=
  [0xBE, 0x37, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x9C, 0x24, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0xB8,
    0x24, 0x20, 0x00, 0xE8, 0xF4, 0x2F, 0x02, 0x00]

theorem code_l106764 : ∀ x ∈ codeRange 0x106764 bytes_l106764, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6764 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10677c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10677c (movR32Imm32Effect 0x10677c 5 6 0x10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x10677c (fun s => s.RIP = 0x10677c) (movR32Imm32Effect 0x10677c 5 6 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106781 (movR64Imm32Effect 0x106781 7 0x2024d0) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x106781 (fun s => s.RIP = 0x106781) (movR64Imm32Effect 0x106781 7 0x2024d0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x106788 (movR64Imm32Effect 0x106788 2 0x202500) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x106788 (fun s => s.RIP = 0x106788) (movR64Imm32Effect 0x106788 2 0x202500) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10678f (callEffect (fun _ => 0x129560) 0x106794) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10678f (PushPre 0x10678f 5) (callEffect (fun _ => 0x129560) 0x106794) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x106794⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l106794, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10677c : List UInt8 :=
  [0xBE, 0x10, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0xD0, 0x24, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x00,
    0x25, 0x20, 0x00, 0xE8, 0xCC, 0x2D, 0x02, 0x00]

theorem code_l10677c : ∀ x ∈ codeRange 0x10677c bytes_l10677c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x677c 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106794 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x106794 (fun s => s.RIP = 0x106794) (fun _ => nopEffect 0x106794 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10679e (fun s => s.RIP = 0x10679e) (fun _ => nopEffect 0x10679e 2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1067a0 (movR64M64Effect 0x1067a0 7 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x1067a0 (LoadPre 0x1067a0 (fun s => AddrMode.addr (.base 7 .none) s (0x1067a0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1067a0 7 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l127cd0, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (14, 14), (15, 15)] 57⟩)))))

def bytes_l106794 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90, 0x48, 0x8B, 0x3F, 0xE9,
    0x28, 0x15, 0x02, 0x00]

theorem code_l106794 : ∀ x ∈ codeRange 0x106794 bytes_l106794, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6794 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1084e0_13 : Block Op Label signature Reg.count 554 :=
  .letOp (n := 554) (.out 0x10885c (andR8M8Effect 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[552, 65]
    (.letOp (n := 555) (.exec 0x10885c (LoadPre 0x10885c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10885c + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x10885c 4 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[552, 65]
    (.letOp (n := 556) (.exec 0x108860 (StorePre 0x108860 3 (fun s => AddrMode.addr (.base 7 .none) s (0x108860 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108860 6 (.base 7 .none)) (Reg.operands [.gpr 6, .gpr 7] [])) #v[501, 7]
    (.letOp (n := 557) (.exec 0x108863 (StorePre 0x108863 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x108863 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108863 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[512, 7]
    (.letOp (n := 558) (.exec 0x108867 (StorePre 0x108867 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108867 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108867 8 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[523, 7]
    (.letOp (n := 559) (.exec 0x10886b (StorePre 0x10886b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10886b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886b 9 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[534, 7]
    (.letOp (n := 560) (.exec 0x10886f (StorePre 0x10886f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10886f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10886f 10 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[546, 7]
    (.letOp (n := 561) (.out 0x108873 (movR64R64Effect 0x108873 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[550]
    (.letOp (n := 562) (.exec 0x108873 (fun s => s.RIP = 0x108873) (movR64R64Effect 0x108873 0 2) (Reg.operands [.gpr 2] [])) #v[550]
    (.letOp (n := 563) (.out 0x108876 (orR8R8Effect 0x108876 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[561, 554]
    (.letOp (n := 564) (.exec 0x108876 (fun s => s.RIP = 0x108876) (orR8R8Effect 0x108876 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[561, 554]
    (.letOp (n := 565) (.exec 0x108878 (StorePre 0x108878 3 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x108878 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108878 3 0 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[563, 7]
    (.letOp (n := 566) (.out 0x10887b (addR64Imm8Effect 0x10887b 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 567) (.exec 0x10887b (fun s => s.RIP = 0x10887b) (addR64Imm8Effect 0x10887b 4 0x40) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 568) (.out 0x10887f (popR64Effect 0x10887f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[566]
    (.letOp (n := 569) (.out 0x10887f (popR64Effect 0x10887f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[566]
    (.letOp (n := 570) (.exec 0x10887f (PopPre 0x10887f) (popR64Effect 0x10887f 1 3) (Reg.operands [.gpr 4] [])) #v[566]
    (.letOp (n := 571) (.out 0x108880 (popR64Effect 0x108880 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[569]
    (.letOp (n := 572) (.out 0x108880 (popR64Effect 0x108880 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[569]
    (.letOp (n := 573) (.exec 0x108880 (PopPre 0x108880) (popR64Effect 0x108880 2 12) (Reg.operands [.gpr 4] [])) #v[569]
    (.letOp (n := 574) (.out 0x108882 (popR64Effect 0x108882 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[572]
    (.letOp (n := 575) (.out 0x108882 (popR64Effect 0x108882 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[572]
    (.letOp (n := 576) (.exec 0x108882 (PopPre 0x108882) (popR64Effect 0x108882 2 13) (Reg.operands [.gpr 4] [])) #v[572]
    (.letOp (n := 577) (.out 0x108884 (popR64Effect 0x108884 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[575]
    (.letOp (n := 578) (.out 0x108884 (popR64Effect 0x108884 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[575]
    (.letOp (n := 579) (.exec 0x108884 (PopPre 0x108884) (popR64Effect 0x108884 2 14) (Reg.operands [.gpr 4] [])) #v[575]
    (.letOp (n := 580) (.out 0x108886 (popR64Effect 0x108886 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[578]
    (.letOp (n := 581) (.out 0x108886 (popR64Effect 0x108886 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[578]
    (.letOp (n := 582) (.exec 0x108886 (PopPre 0x108886) (popR64Effect 0x108886 2 15) (Reg.operands [.gpr 4] [])) #v[578]
    (.letOp (n := 583) (.out 0x108888 (popR64Effect 0x108888 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[581]
    (.letOp (n := 584) (.out 0x108888 (popR64Effect 0x108888 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[581]
    (.letOp (n := 585) (.exec 0x108888 (PopPre 0x108888) (popR64Effect 0x108888 1 5) (Reg.operands [.gpr 4] [])) #v[581]
    (.letOp (n := 586) (.out 0x108889 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[584]
    (.letOp (n := 587) (.out 0x108889 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[584]
    (.letOp (n := 588) (.exec 0x108889 (RetPre 0x108889) (retEffect) (Reg.operands [.gpr 4] [])) #v[584]
    (.terminate (.ret (RegMap.args [(0, 563), (1, 554), (2, 550), (3, 568), (4, 587), (5, 583), (6, 501), (7, 7), (8, 523), (9, 534), (10, 546), (11, 517), (12, 571), (13, 574), (14, 577), (15, 580), (22, 22), (39, 39), (50, 50), (51, 51)] 589) (some ⟨586, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_13 : List UInt8 :=
  [0x22, 0x4C, 0x24, 0x20, 0x48, 0x89, 0x37, 0x48, 0x89, 0x47, 0x08, 0x4C, 0x89, 0x47, 0x10, 0x4C,
    0x89, 0x4F, 0x18, 0x4C, 0x89, 0x57, 0x20, 0x48, 0x89, 0xD0, 0x08, 0xC8, 0x88, 0x47, 0x28, 0x48,
    0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1084e0_13 : ∀ x ∈ codeRange 0x10885c bytes_l1084e0_13, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x885c 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l1084e0_12 : Block Op Label signature Reg.count 517 :=
  .letOp (n := 517) (.out 0x10881b (xorR64R64Effect 0x10881b 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[473, 357]
    (.letOp (n := 518) (.exec 0x10881b (fun s => s.RIP = 0x10881b) (xorR64R64Effect 0x10881b 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[473, 357]
    (.letOp (n := 519) (.out 0x10881e (negR64Effect 0x10881e 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[515]
    (.letOp (n := 520) (.exec 0x10881e (fun s => s.RIP = 0x10881e) (negR64Effect 0x10881e 8) (Reg.operands [.gpr 8] [])) #v[515]
    (.letOp (n := 521) (.out 0x108821 (andR64R64Effect 0x108821 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[519, 517]
    (.letOp (n := 522) (.exec 0x108821 (fun s => s.RIP = 0x108821) (andR64R64Effect 0x108821 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[519, 517]
    (.letOp (n := 523) (.out 0x108824 (xorR64R64Effect 0x108824 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[521, 357]
    (.letOp (n := 524) (.exec 0x108824 (fun s => s.RIP = 0x108824) (xorR64R64Effect 0x108824 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[521, 357]
    (.letOp (n := 525) (.exec 0x108827 (StorePre 0x108827 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108827 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108827 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 526) (.out 0x10882a (movzxR32M8Effect 0x10882a 5 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 527) (.exec 0x10882a (LoadPre 0x10882a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10882a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10882a 5 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 528) (.out 0x10882f (xorR64R64Effect 0x10882f 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[476, 384]
    (.letOp (n := 529) (.exec 0x10882f (fun s => s.RIP = 0x10882f) (xorR64R64Effect 0x10882f 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[476, 384]
    (.letOp (n := 530) (.out 0x108832 (negR64Effect 0x108832 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[526]
    (.letOp (n := 531) (.exec 0x108832 (fun s => s.RIP = 0x108832) (negR64Effect 0x108832 9) (Reg.operands [.gpr 9] [])) #v[526]
    (.letOp (n := 532) (.out 0x108835 (andR64R64Effect 0x108835 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[530, 528]
    (.letOp (n := 533) (.exec 0x108835 (fun s => s.RIP = 0x108835) (andR64R64Effect 0x108835 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[530, 528]
    (.letOp (n := 534) (.out 0x108838 (xorR64R64Effect 0x108838 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[532, 384]
    (.letOp (n := 535) (.exec 0x108838 (fun s => s.RIP = 0x108838) (xorR64R64Effect 0x108838 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[532, 384]
    (.letOp (n := 536) (.exec 0x10883b (StorePre 0x10883b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10883b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10883b 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 537) (.exec 0x10883e (fun s => s.RIP = 0x10883e) (movR64R64Effect 0x10883e 10 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 538) (.out 0x108841 (movzxR32M8Effect 0x108841 5 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 539) (.exec 0x108841 (LoadPre 0x108841 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108841 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108841 5 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 540) (.out 0x108846 (xorR64R64Effect 0x108846 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[489, 439]
    (.letOp (n := 541) (.exec 0x108846 (fun s => s.RIP = 0x108846) (xorR64R64Effect 0x108846 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[489, 439]
    (.letOp (n := 542) (.out 0x108849 (negR64Effect 0x108849 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[538]
    (.letOp (n := 543) (.exec 0x108849 (fun s => s.RIP = 0x108849) (negR64Effect 0x108849 10) (Reg.operands [.gpr 10] [])) #v[538]
    (.letOp (n := 544) (.out 0x10884c (andR64R64Effect 0x10884c 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[542, 540]
    (.letOp (n := 545) (.exec 0x10884c (fun s => s.RIP = 0x10884c) (andR64R64Effect 0x10884c 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[542, 540]
    (.letOp (n := 546) (.out 0x10884f (xorR64R64Effect 0x10884f 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[544, 439]
    (.letOp (n := 547) (.exec 0x10884f (fun s => s.RIP = 0x10884f) (xorR64R64Effect 0x10884f 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[544, 439]
    (.letOp (n := 548) (.out 0x108852 (movR64M64Effect 0x108852 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 549) (.exec 0x108852 (LoadPre 0x108852 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108852 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108852 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 550) (.out 0x108857 (andR8R8Effect 0x108857 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[548, 459]
    (.letOp (n := 551) (.exec 0x108857 (fun s => s.RIP = 0x108857) (andR8R8Effect 0x108857 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[548, 459]
    (.letOp (n := 552) (.out 0x108859 (xorR8Imm8Effect 0x108859 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[459]
    (.letOp (n := 553) (.exec 0x108859 (fun s => s.RIP = 0x108859) (xorR8Imm8Effect 0x108859 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[459]
    (b_l1084e0_13)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_12 : List UInt8 :=
  [0x4D, 0x31, 0xCB, 0x49, 0xF7, 0xD8, 0x4D, 0x21, 0xD8, 0x4D, 0x31, 0xC8, 0x88, 0x0C, 0x24, 0x44,
    0x0F, 0xB6, 0x0C, 0x24, 0x4D, 0x31, 0xD5, 0x49, 0xF7, 0xD9, 0x4D, 0x21, 0xE9, 0x4D, 0x31, 0xD1,
    0x88, 0x0C, 0x24, 0x49, 0x89, 0xE2, 0x44, 0x0F, 0xB6, 0x14, 0x24, 0x48, 0x31, 0xDA, 0x49, 0xF7,
    0xDA, 0x49, 0x21, 0xD2, 0x49, 0x31, 0xDA, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x20, 0xCA, 0x80, 0xF1,
    0x01] ++ bytes_l1084e0_13

theorem code_l1084e0_12 : ∀ x ∈ codeRange 0x10881b bytes_l1084e0_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x881b 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_13

def b_l1084e0_11 : Block Op Label signature Reg.count 483 :=
  .letOp (n := 483) (.exec 0x1087d9 (StorePre 0x1087d9 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087d9 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x1087d9 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 477]
    (.letOp (n := 484) (.exec 0x1087dd (fun s => s.RIP = 0x1087dd) (movR64R64Effect 0x1087dd 2 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 485) (.out 0x1087e0 (movzxR32M8Effect 0x1087e0 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 486) (.exec 0x1087e0 (LoadPre 0x1087e0 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087e0 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087e0 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 487) (.out 0x1087e4 (andR32Imm8Effect 0x1087e4 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[485]
    (.letOp (n := 488) (.exec 0x1087e4 (fun s => s.RIP = 0x1087e4) (andR32Imm8Effect 0x1087e4 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[485]
    (.letOp (n := 489) (.out 0x1087e7 (addR64R64Effect 0x1087e7 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[487, 481]
    (.letOp (n := 490) (.exec 0x1087e7 (fun s => s.RIP = 0x1087e7) (addR64R64Effect 0x1087e7 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[487, 481]
    (.letOp (n := 491) (.exec 0x1087ea (StorePre 0x1087ea 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087ea + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x1087ea 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 492) (.exec 0x1087ed (fun s => s.RIP = 0x1087ed) (movR64R64Effect 0x1087ed 15 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 493) (.out 0x1087f0 (xorR64R64Effect 0x1087f0 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[463, 300]
    (.letOp (n := 494) (.exec 0x1087f0 (fun s => s.RIP = 0x1087f0) (xorR64R64Effect 0x1087f0 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[463, 300]
    (.letOp (n := 495) (.out 0x1087f3 (movzxR32M8Effect 0x1087f3 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 496) (.exec 0x1087f3 (LoadPre 0x1087f3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087f3 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1087f3 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 497) (.out 0x1087f7 (negR64Effect 0x1087f7 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[495]
    (.letOp (n := 498) (.exec 0x1087f7 (fun s => s.RIP = 0x1087f7) (negR64Effect 0x1087f7 6) (Reg.operands [.gpr 6] [])) #v[495]
    (.letOp (n := 499) (.out 0x1087fa (andR64R64Effect 0x1087fa 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[497, 493]
    (.letOp (n := 500) (.exec 0x1087fa (fun s => s.RIP = 0x1087fa) (andR64R64Effect 0x1087fa 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[497, 493]
    (.letOp (n := 501) (.out 0x1087fd (xorR64R64Effect 0x1087fd 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[499, 300]
    (.letOp (n := 502) (.exec 0x1087fd (fun s => s.RIP = 0x1087fd) (xorR64R64Effect 0x1087fd 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[499, 300]
    (.letOp (n := 503) (.exec 0x108800 (StorePre 0x108800 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108800 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108800 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 504) (.out 0x108803 (movzxR32M8Effect 0x108803 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 505) (.exec 0x108803 (LoadPre 0x108803 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108803 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108803 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 506) (.out 0x108807 (xorR64R64Effect 0x108807 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[468, 330]
    (.letOp (n := 507) (.exec 0x108807 (fun s => s.RIP = 0x108807) (xorR64R64Effect 0x108807 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[468, 330]
    (.letOp (n := 508) (.out 0x10880a (negR64Effect 0x10880a 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[504]
    (.letOp (n := 509) (.exec 0x10880a (fun s => s.RIP = 0x10880a) (negR64Effect 0x10880a 0) (Reg.operands [.gpr 0] [])) #v[504]
    (.letOp (n := 510) (.out 0x10880d (andR64R64Effect 0x10880d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[508, 506]
    (.letOp (n := 511) (.exec 0x10880d (fun s => s.RIP = 0x10880d) (andR64R64Effect 0x10880d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[508, 506]
    (.letOp (n := 512) (.out 0x108810 (xorR64R64Effect 0x108810 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[510, 330]
    (.letOp (n := 513) (.exec 0x108810 (fun s => s.RIP = 0x108810) (xorR64R64Effect 0x108810 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[510, 330]
    (.letOp (n := 514) (.exec 0x108813 (StorePre 0x108813 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108813 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108813 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[459, 65]
    (.letOp (n := 515) (.out 0x108816 (movzxR32M8Effect 0x108816 5 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 516) (.exec 0x108816 (LoadPre 0x108816 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108816 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108816 5 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1084e0_12))))))))))))))))))))))))))))))))))

def bytes_l1084e0_11 : List UInt8 :=
  [0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x14, 0x24, 0x83, 0xE2, 0x01, 0x48, 0x01,
    0xF2, 0x88, 0x0C, 0x24, 0x49, 0x89, 0xE7, 0x49, 0x31, 0xC4, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0xF7,
    0xDE, 0x4C, 0x21, 0xE6, 0x48, 0x31, 0xC6, 0x88, 0x0C, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x4D, 0x31,
    0xC6, 0x48, 0xF7, 0xD8, 0x4C, 0x21, 0xF0, 0x4C, 0x31, 0xC0, 0x88, 0x0C, 0x24, 0x44, 0x0F, 0xB6,
    0x04, 0x24] ++ bytes_l1084e0_12

theorem code_l1084e0_11 : ∀ x ∈ codeRange 0x1087d9 bytes_l1084e0_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x87d9 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_12

def b_l1084e0_10 : Block Op Label signature Reg.count 441 :=
  .letOp (n := 441) (.out 0x10878d (andR64R64Effect 0x10878d 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[435, 439]
    (.letOp (n := 442) (.exec 0x10878d (fun s => s.RIP = 0x10878d) (andR64R64Effect 0x10878d 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[435, 439]
    (.letOp (n := 443) (.out 0x108790 (orR64R64Effect 0x108790 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[441, 433]
    (.letOp (n := 444) (.exec 0x108790 (fun s => s.RIP = 0x108790) (orR64R64Effect 0x108790 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[441, 433]
    (.letOp (n := 445) (.out 0x108793 (shrR64Effect 0x108793 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[443]
    (.letOp (n := 446) (.exec 0x108793 (fun s => s.RIP = 0x108793) (shrR64Effect 0x108793 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[443]
    (.letOp (n := 447) (.exec 0x108797 (StorePre 0x108797 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108797 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108797 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[445, 65]
    (.letOp (n := 448) (.exec 0x10879b (fun s => s.RIP = 0x10879b) (movR64R64Effect 0x10879b 1 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 449) (.out 0x10879e (movzxR32M8Effect 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 450) (.exec 0x10879e (LoadPre 0x10879e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10879e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10879e 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 451) (.out 0x1087a3 (andR8Imm8Effect 0x1087a3 3 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[449]
    (.letOp (n := 452) (.exec 0x1087a3 (fun s => s.RIP = 0x1087a3) (andR8Imm8Effect 0x1087a3 3 1 0x1) (Reg.operands [.gpr 1] [])) #v[449]
    (.letOp (n := 453) (.out 0x1087a6 (cmpMImm8Effect 0x1087a6 5 64 (.sib 4 none 0 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[65]
    (.letOp (n := 454) (.exec 0x1087a6 (LoadPre 0x1087a6 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1087a6 + BitVec.ofNat 64 5)) 8) (cmpMImm8Effect 0x1087a6 5 64 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 455) (.out 0x1087ab (movzxR32R8Effect 0x1087ab 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[451]
    (.letOp (n := 456) (.exec 0x1087ab (fun s => s.RIP = 0x1087ab) (movzxR32R8Effect 0x1087ab 3 1 1) (Reg.operands [.gpr 1] [])) #v[451]
    (.letOp (n := 457) (.out 0x1087ae (movR32Imm32Effect 0x1087ae 6 13 0x0) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 458) (.exec 0x1087ae (fun s => s.RIP = 0x1087ae) (movR32Imm32Effect 0x1087ae 6 13 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 459) (.out 0x1087b4 (atFlags (condHolds 4) (cmovR32R32Effect 0x1087b4 4 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[455, 457, 453]
    (.letOp (n := 460) (.exec 0x1087b4 (fun s => s.RIP = 0x1087b4) (atFlags (condHolds 4) (cmovR32R32Effect 0x1087b4 4 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[455, 457, 453]
    (.letOp (n := 461) (.out 0x1087b8 (movR64R64Effect 0x1087b8 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[300]
    (.letOp (n := 462) (.exec 0x1087b8 (fun s => s.RIP = 0x1087b8) (movR64R64Effect 0x1087b8 12 0) (Reg.operands [.gpr 0] [])) #v[300]
    (.letOp (n := 463) (.out 0x1087bb (negR64Effect 0x1087bb 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[461]
    (.letOp (n := 464) (.out 0x1087bb (negR64Effect 0x1087bb 12) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[461]
    (.letOp (n := 465) (.exec 0x1087bb (fun s => s.RIP = 0x1087bb) (negR64Effect 0x1087bb 12) (Reg.operands [.gpr 12] [])) #v[461]
    (.letOp (n := 466) (.out 0x1087be (movR32Imm32Effect 0x1087be 6 14 0x0) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 467) (.exec 0x1087be (fun s => s.RIP = 0x1087be) (movR32Imm32Effect 0x1087be 6 14 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 468) (.out 0x1087c4 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[466, 330, 464]
    (.letOp (n := 469) (.out 0x1087c4 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[466, 330, 464]
    (.letOp (n := 470) (.exec 0x1087c4 (fun s => s.RIP = 0x1087c4) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087c4 14 8)) (Reg.operands [.gpr 14, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[466, 330, 464]
    (.letOp (n := 471) (.out 0x1087c7 (movR32Imm32Effect 0x1087c7 6 11 0x0) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 472) (.exec 0x1087c7 (fun s => s.RIP = 0x1087c7) (movR32Imm32Effect 0x1087c7 6 11 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 473) (.out 0x1087cd (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[471, 357, 469]
    (.letOp (n := 474) (.out 0x1087cd (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[471, 357, 469]
    (.letOp (n := 475) (.exec 0x1087cd (fun s => s.RIP = 0x1087cd) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087cd 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[471, 357, 469]
    (.letOp (n := 476) (.out 0x1087d0 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[457, 384, 474]
    (.letOp (n := 477) (.out 0x1087d0 (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[457, 384, 474]
    (.letOp (n := 478) (.exec 0x1087d0 (fun s => s.RIP = 0x1087d0) (atFlags StatusFlags.CF (sbbR64R64Effect 0x1087d0 13 10)) (Reg.operands [.gpr 13, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[457, 384, 474]
    (.letOp (n := 479) (.out 0x1087d3 (movR64R64Effect 0x1087d3 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[439]
    (.letOp (n := 480) (.exec 0x1087d3 (fun s => s.RIP = 0x1087d3) (movR64R64Effect 0x1087d3 6 3) (Reg.operands [.gpr 3] [])) #v[439]
    (.letOp (n := 481) (.out 0x1087d6 (notR64Effect 0x1087d6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[479]
    (.letOp (n := 482) (.exec 0x1087d6 (fun s => s.RIP = 0x1087d6) (notR64Effect 0x1087d6 6) (Reg.operands [.gpr 6] [])) #v[479]
    (b_l1084e0_11))))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_10 : List UInt8 :=
  [0x48, 0x21, 0xD9, 0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x89,
    0xE1, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x80, 0xE1, 0x01, 0x48, 0x83, 0x3C, 0x24, 0x00, 0x0F, 0xB6,
    0xC9, 0x41, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x41, 0x0F, 0x44, 0xCD, 0x49, 0x89, 0xC4, 0x49, 0xF7,
    0xDC, 0x41, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xC6, 0x41, 0xBB, 0x00, 0x00, 0x00, 0x00,
    0x4D, 0x19, 0xCB, 0x4D, 0x19, 0xD5, 0x48, 0x89, 0xDE, 0x48, 0xF7, 0xD6] ++ bytes_l1084e0_11

theorem code_l1084e0_10 : ∀ x ∈ codeRange 0x10878d bytes_l1084e0_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x878d 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_11

def b_l1084e0_9 : Block Op Label signature Reg.count 401 :=
  .letOp (n := 401) (.out 0x10874b (xorR32R32Effect 0x10874b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[398, 398]
    (.letOp (n := 402) (.exec 0x10874b (fun s => s.RIP = 0x10874b) (xorR32R32Effect 0x10874b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[398, 398]
    (.letOp (n := 403) (.out 0x10874d (subR64M64Effect 0x10874d 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[401, 65]
    (.letOp (n := 404) (.exec 0x10874d (LoadPre 0x10874d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10874d + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10874d 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[401, 65]
    (.letOp (n := 405) (.out 0x108751 (movR64M64Effect 0x108751 11 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 406) (.exec 0x108751 (LoadPre 0x108751 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108751 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108751 11 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 407) (.out 0x108756 (andR32Imm8Effect 0x108756 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[405]
    (.letOp (n := 408) (.exec 0x108756 (fun s => s.RIP = 0x108756) (andR32Imm8Effect 0x108756 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[405]
    (.letOp (n := 409) (.out 0x10875a (movR64M64Effect 0x10875a 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 410) (.exec 0x10875a (LoadPre 0x10875a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10875a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10875a 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 411) (.out 0x10875f (movR64R64Effect 0x10875f 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[409]
    (.letOp (n := 412) (.exec 0x10875f (fun s => s.RIP = 0x10875f) (movR64R64Effect 0x10875f 2 6) (Reg.operands [.gpr 6] [])) #v[409]
    (.letOp (n := 413) (.out 0x108762 (notR64Effect 0x108762 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[411]
    (.letOp (n := 414) (.exec 0x108762 (fun s => s.RIP = 0x108762) (notR64Effect 0x108762 2) (Reg.operands [.gpr 2] [])) #v[411]
    (.letOp (n := 415) (.out 0x108765 (addR64R64Effect 0x108765 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[413, 407]
    (.letOp (n := 416) (.exec 0x108765 (fun s => s.RIP = 0x108765) (addR64R64Effect 0x108765 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[413, 407]
    (.letOp (n := 417) (.out 0x108768 (xorR64R64Effect 0x108768 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[415, 409]
    (.letOp (n := 418) (.exec 0x108768 (fun s => s.RIP = 0x108768) (xorR64R64Effect 0x108768 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[415, 409]
    (.letOp (n := 419) (.out 0x10876b (negR64Effect 0x10876b 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[316]
    (.letOp (n := 420) (.exec 0x10876b (fun s => s.RIP = 0x10876b) (negR64Effect 0x10876b 14) (Reg.operands [.gpr 14] [])) #v[316]
    (.letOp (n := 421) (.out 0x10876e (andR64R64Effect 0x10876e 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[419, 417]
    (.letOp (n := 422) (.exec 0x10876e (fun s => s.RIP = 0x10876e) (andR64R64Effect 0x10876e 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[419, 417]
    (.letOp (n := 423) (.out 0x108771 (xorR64R64Effect 0x108771 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[421, 409]
    (.letOp (n := 424) (.exec 0x108771 (fun s => s.RIP = 0x108771) (xorR64R64Effect 0x108771 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[421, 409]
    (.letOp (n := 425) (.out 0x108774 (movR64R64Effect 0x108774 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[156]
    (.letOp (n := 426) (.exec 0x108774 (fun s => s.RIP = 0x108774) (movR64R64Effect 0x108774 2 1) (Reg.operands [.gpr 1] [])) #v[156]
    (.letOp (n := 427) (.out 0x108777 (subR64R64Effect 0x108777 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[425, 423]
    (.letOp (n := 428) (.exec 0x108777 (fun s => s.RIP = 0x108777) (subR64R64Effect 0x108777 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[425, 423]
    (.letOp (n := 429) (.out 0x10877a (notR64Effect 0x10877a 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[156]
    (.letOp (n := 430) (.exec 0x10877a (fun s => s.RIP = 0x10877a) (notR64Effect 0x10877a 1) (Reg.operands [.gpr 1] [])) #v[156]
    (.letOp (n := 431) (.out 0x10877d (movR64R64Effect 0x10877d 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[423]
    (.letOp (n := 432) (.exec 0x10877d (fun s => s.RIP = 0x10877d) (movR64R64Effect 0x10877d 6 14) (Reg.operands [.gpr 14] [])) #v[423]
    (.letOp (n := 433) (.out 0x108780 (andR64R64Effect 0x108780 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[431, 429]
    (.letOp (n := 434) (.exec 0x108780 (fun s => s.RIP = 0x108780) (andR64R64Effect 0x108780 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[431, 429]
    (.letOp (n := 435) (.out 0x108783 (orR64R64Effect 0x108783 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[429, 423]
    (.letOp (n := 436) (.exec 0x108783 (fun s => s.RIP = 0x108783) (orR64R64Effect 0x108783 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[429, 423]
    (.letOp (n := 437) (.out 0x108786 (sarR64Effect 0x108786 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[403]
    (.letOp (n := 438) (.exec 0x108786 (fun s => s.RIP = 0x108786) (sarR64Effect 0x108786 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[403]
    (.letOp (n := 439) (.out 0x10878a (addR64R64Effect 0x10878a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[437, 427]
    (.letOp (n := 440) (.exec 0x10878a (fun s => s.RIP = 0x10878a) (addR64R64Effect 0x10878a 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[437, 427]
    (b_l1084e0_10))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_9 : List UInt8 :=
  [0x31, 0xDB, 0x48, 0x2B, 0x1C, 0x24, 0x4C, 0x8B, 0x5C, 0x24, 0x38, 0x41, 0x83, 0xE3, 0x01, 0x48,
    0x8B, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xD2, 0x4C, 0x01, 0xDA, 0x48, 0x31, 0xF2,
    0x49, 0xF7, 0xDE, 0x49, 0x21, 0xD6, 0x49, 0x31, 0xF6, 0x48, 0x89, 0xCA, 0x4C, 0x29, 0xF2, 0x48,
    0xF7, 0xD1, 0x4C, 0x89, 0xF6, 0x48, 0x21, 0xCE, 0x4C, 0x09, 0xF1, 0x48, 0xC1, 0xFB, 0x3F, 0x48,
    0x01, 0xD3] ++ bytes_l1084e0_10

theorem code_l1084e0_9 : ∀ x ∈ codeRange 0x10874b bytes_l1084e0_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x874b 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_10

def b_l1084e0_8 : Block Op Label signature Reg.count 363 :=
  .letOp (n := 363) (.out 0x108709 (andR64R64Effect 0x108709 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[361, 359]
    (.letOp (n := 364) (.exec 0x108709 (fun s => s.RIP = 0x108709) (andR64R64Effect 0x108709 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[361, 359]
    (.letOp (n := 365) (.out 0x10870c (orR64R64Effect 0x10870c 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[359, 283]
    (.letOp (n := 366) (.exec 0x10870c (fun s => s.RIP = 0x10870c) (orR64R64Effect 0x10870c 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[359, 283]
    (.letOp (n := 367) (.out 0x10870f (andR64R64Effect 0x10870f 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9] []) (.reg (.gpr 12))) #v[365, 357]
    (.letOp (n := 368) (.exec 0x10870f (fun s => s.RIP = 0x10870f) (andR64R64Effect 0x10870f 12 9) (Reg.operands [.gpr 12, .gpr 9] [])) #v[365, 357]
    (.letOp (n := 369) (.out 0x108712 (orR64R64Effect 0x108712 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[367, 363]
    (.letOp (n := 370) (.exec 0x108712 (fun s => s.RIP = 0x108712) (orR64R64Effect 0x108712 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[367, 363]
    (.letOp (n := 371) (.out 0x108715 (shrR64Effect 0x108715 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[369]
    (.letOp (n := 372) (.exec 0x108715 (fun s => s.RIP = 0x108715) (shrR64Effect 0x108715 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[369]
    (.letOp (n := 373) (.exec 0x108719 (StorePre 0x108719 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108719 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108719 12 (.sib 4 none 0 .none)) (Reg.operands [.gpr 12, .gpr 4] [])) #v[371, 65]
    (.letOp (n := 374) (.out 0x10871d (xorR32R32Effect 0x10871d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[314, 314]
    (.letOp (n := 375) (.exec 0x10871d (fun s => s.RIP = 0x10871d) (xorR32R32Effect 0x10871d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[314, 314]
    (.letOp (n := 376) (.out 0x108720 (subR64M64Effect 0x108720 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[374, 65]
    (.letOp (n := 377) (.exec 0x108720 (LoadPre 0x108720 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108720 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x108720 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[374, 65]
    (.letOp (n := 378) (.out 0x108724 (movR64R64Effect 0x108724 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[153]
    (.letOp (n := 379) (.exec 0x108724 (fun s => s.RIP = 0x108724) (movR64R64Effect 0x108724 2 3) (Reg.operands [.gpr 3] [])) #v[153]
    (.letOp (n := 380) (.out 0x108727 (subR64R64Effect 0x108727 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[378, 294]
    (.letOp (n := 381) (.exec 0x108727 (fun s => s.RIP = 0x108727) (subR64R64Effect 0x108727 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[378, 294]
    (.letOp (n := 382) (.out 0x10872a (sarR64Effect 0x10872a 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[376]
    (.letOp (n := 383) (.exec 0x10872a (fun s => s.RIP = 0x10872a) (sarR64Effect 0x10872a 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[376]
    (.letOp (n := 384) (.out 0x10872e (addR64R64Effect 0x10872e 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[382, 380]
    (.letOp (n := 385) (.exec 0x10872e (fun s => s.RIP = 0x10872e) (addR64R64Effect 0x10872e 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[382, 380]
    (.letOp (n := 386) (.out 0x108731 (notR64Effect 0x108731 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[153]
    (.letOp (n := 387) (.exec 0x108731 (fun s => s.RIP = 0x108731) (notR64Effect 0x108731 3) (Reg.operands [.gpr 3] [])) #v[153]
    (.letOp (n := 388) (.out 0x108734 (movR64R64Effect 0x108734 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[294]
    (.letOp (n := 389) (.exec 0x108734 (fun s => s.RIP = 0x108734) (movR64R64Effect 0x108734 2 15) (Reg.operands [.gpr 15] [])) #v[294]
    (.letOp (n := 390) (.out 0x108737 (andR64R64Effect 0x108737 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[388, 386]
    (.letOp (n := 391) (.exec 0x108737 (fun s => s.RIP = 0x108737) (andR64R64Effect 0x108737 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[388, 386]
    (.letOp (n := 392) (.out 0x10873a (orR64R64Effect 0x10873a 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[386, 294]
    (.letOp (n := 393) (.exec 0x10873a (fun s => s.RIP = 0x10873a) (orR64R64Effect 0x10873a 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[386, 294]
    (.letOp (n := 394) (.out 0x10873d (andR64R64Effect 0x10873d 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[392, 384]
    (.letOp (n := 395) (.exec 0x10873d (fun s => s.RIP = 0x10873d) (andR64R64Effect 0x10873d 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[392, 384]
    (.letOp (n := 396) (.out 0x108740 (orR64R64Effect 0x108740 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[394, 390]
    (.letOp (n := 397) (.exec 0x108740 (fun s => s.RIP = 0x108740) (orR64R64Effect 0x108740 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[394, 390]
    (.letOp (n := 398) (.out 0x108743 (shrR64Effect 0x108743 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[396]
    (.letOp (n := 399) (.exec 0x108743 (fun s => s.RIP = 0x108743) (shrR64Effect 0x108743 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[396]
    (.letOp (n := 400) (.exec 0x108747 (StorePre 0x108747 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108747 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108747 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 3, .gpr 4] [])) #v[398, 65]
    (b_l1084e0_9))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_8 : List UInt8 :=
  [0x4C, 0x21, 0xE2, 0x49, 0x09, 0xEC, 0x4D, 0x21, 0xCC, 0x49, 0x09, 0xD4, 0x49, 0xC1, 0xEC, 0x3F,
    0x4C, 0x89, 0x24, 0x24, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x14, 0x24, 0x48, 0x89, 0xDA, 0x4C, 0x29,
    0xFA, 0x49, 0xC1, 0xFA, 0x3F, 0x49, 0x01, 0xD2, 0x48, 0xF7, 0xD3, 0x4C, 0x89, 0xFA, 0x48, 0x21,
    0xDA, 0x4C, 0x09, 0xFB, 0x4C, 0x21, 0xD3, 0x48, 0x09, 0xD3, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89,
    0x1C, 0x24] ++ bytes_l1084e0_9

theorem code_l1084e0_8 : ∀ x ∈ codeRange 0x108709 bytes_l1084e0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8709 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_9

def b_l1084e0_7 : Block Op Label signature Reg.count 324 :=
  .letOp (n := 324) (.out 0x1086c8 (movR64R64Effect 0x1086c8 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 325) (.exec 0x1086c8 (fun s => s.RIP = 0x1086c8) (movR64R64Effect 0x1086c8 2 9) (Reg.operands [.gpr 9] [])) #v[147]
    (.letOp (n := 326) (.out 0x1086cb (subR64R64Effect 0x1086cb 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[324, 269]
    (.letOp (n := 327) (.exec 0x1086cb (fun s => s.RIP = 0x1086cb) (subR64R64Effect 0x1086cb 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[324, 269]
    (.letOp (n := 328) (.out 0x1086ce (sarR64Effect 0x1086ce 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[322]
    (.letOp (n := 329) (.exec 0x1086ce (fun s => s.RIP = 0x1086ce) (sarR64Effect 0x1086ce 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[322]
    (.letOp (n := 330) (.out 0x1086d2 (addR64R64Effect 0x1086d2 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[328, 326]
    (.letOp (n := 331) (.exec 0x1086d2 (fun s => s.RIP = 0x1086d2) (addR64R64Effect 0x1086d2 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[328, 326]
    (.letOp (n := 332) (.out 0x1086d5 (notR64Effect 0x1086d5 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[147]
    (.letOp (n := 333) (.exec 0x1086d5 (fun s => s.RIP = 0x1086d5) (notR64Effect 0x1086d5 9) (Reg.operands [.gpr 9] [])) #v[147]
    (.letOp (n := 334) (.out 0x1086d8 (movR64R64Effect 0x1086d8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[269]
    (.letOp (n := 335) (.exec 0x1086d8 (fun s => s.RIP = 0x1086d8) (movR64R64Effect 0x1086d8 2 13) (Reg.operands [.gpr 13] [])) #v[269]
    (.letOp (n := 336) (.out 0x1086db (andR64R64Effect 0x1086db 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[334, 332]
    (.letOp (n := 337) (.exec 0x1086db (fun s => s.RIP = 0x1086db) (andR64R64Effect 0x1086db 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[334, 332]
    (.letOp (n := 338) (.out 0x1086de (orR64R64Effect 0x1086de 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[332, 269]
    (.letOp (n := 339) (.exec 0x1086de (fun s => s.RIP = 0x1086de) (orR64R64Effect 0x1086de 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[332, 269]
    (.letOp (n := 340) (.out 0x1086e1 (andR64R64Effect 0x1086e1 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[338, 330]
    (.letOp (n := 341) (.exec 0x1086e1 (fun s => s.RIP = 0x1086e1) (andR64R64Effect 0x1086e1 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[338, 330]
    (.letOp (n := 342) (.out 0x1086e4 (orR64R64Effect 0x1086e4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[340, 336]
    (.letOp (n := 343) (.exec 0x1086e4 (fun s => s.RIP = 0x1086e4) (orR64R64Effect 0x1086e4 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[340, 336]
    (.letOp (n := 344) (.out 0x1086e7 (shrR64Effect 0x1086e7 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[342]
    (.letOp (n := 345) (.exec 0x1086e7 (fun s => s.RIP = 0x1086e7) (shrR64Effect 0x1086e7 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342]
    (.letOp (n := 346) (.exec 0x1086eb (StorePre 0x1086eb 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086eb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086eb 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[344, 65]
    (.letOp (n := 347) (.out 0x1086ef (xorR32R32Effect 0x1086ef 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[344, 344]
    (.letOp (n := 348) (.exec 0x1086ef (fun s => s.RIP = 0x1086ef) (xorR32R32Effect 0x1086ef 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[344, 344]
    (.letOp (n := 349) (.out 0x1086f2 (subR64M64Effect 0x1086f2 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[347, 65]
    (.letOp (n := 350) (.exec 0x1086f2 (LoadPre 0x1086f2 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086f2 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086f2 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[347, 65]
    (.letOp (n := 351) (.out 0x1086f6 (movR64R64Effect 0x1086f6 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[150]
    (.letOp (n := 352) (.exec 0x1086f6 (fun s => s.RIP = 0x1086f6) (movR64R64Effect 0x1086f6 2 12) (Reg.operands [.gpr 12] [])) #v[150]
    (.letOp (n := 353) (.out 0x1086f9 (subR64R64Effect 0x1086f9 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[351, 283]
    (.letOp (n := 354) (.exec 0x1086f9 (fun s => s.RIP = 0x1086f9) (subR64R64Effect 0x1086f9 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[351, 283]
    (.letOp (n := 355) (.out 0x1086fc (sarR64Effect 0x1086fc 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[349]
    (.letOp (n := 356) (.exec 0x1086fc (fun s => s.RIP = 0x1086fc) (sarR64Effect 0x1086fc 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[349]
    (.letOp (n := 357) (.out 0x108700 (addR64R64Effect 0x108700 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[355, 353]
    (.letOp (n := 358) (.exec 0x108700 (fun s => s.RIP = 0x108700) (addR64R64Effect 0x108700 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[355, 353]
    (.letOp (n := 359) (.out 0x108703 (notR64Effect 0x108703 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[150]
    (.letOp (n := 360) (.exec 0x108703 (fun s => s.RIP = 0x108703) (notR64Effect 0x108703 12) (Reg.operands [.gpr 12] [])) #v[150]
    (.letOp (n := 361) (.out 0x108706 (movR64R64Effect 0x108706 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[283]
    (.letOp (n := 362) (.exec 0x108706 (fun s => s.RIP = 0x108706) (movR64R64Effect 0x108706 2 5) (Reg.operands [.gpr 5] [])) #v[283]
    (b_l1084e0_8)))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_7 : List UInt8 :=
  [0x4C, 0x89, 0xCA, 0x4C, 0x29, 0xEA, 0x49, 0xC1, 0xF8, 0x3F, 0x49, 0x01, 0xD0, 0x49, 0xF7, 0xD1,
    0x4C, 0x89, 0xEA, 0x4C, 0x21, 0xCA, 0x4D, 0x09, 0xE9, 0x4D, 0x21, 0xC1, 0x49, 0x09, 0xD1, 0x49,
    0xC1, 0xE9, 0x3F, 0x4C, 0x89, 0x0C, 0x24, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x0C, 0x24, 0x4C, 0x89,
    0xE2, 0x48, 0x29, 0xEA, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xD1, 0x49, 0xF7, 0xD4, 0x48, 0x89,
    0xEA] ++ bytes_l1084e0_8

theorem code_l1084e0_7 : ∀ x ∈ codeRange 0x1086c8 bytes_l1084e0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x86c8 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_8

def b_l1084e0_6 : Block Op Label signature Reg.count 288 :=
  .letOp (n := 288) (.out 0x108684 (movzxR32M8Effect 0x108684 5 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 289) (.exec 0x108684 (LoadPre 0x108684 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108684 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108684 5 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 290) (.out 0x108689 (negR64Effect 0x108689 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[288]
    (.letOp (n := 291) (.exec 0x108689 (fun s => s.RIP = 0x108689) (negR64Effect 0x108689 15) (Reg.operands [.gpr 15] [])) #v[288]
    (.letOp (n := 292) (.out 0x10868c (andR64R64Effect 0x10868c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[290, 286]
    (.letOp (n := 293) (.exec 0x10868c (fun s => s.RIP = 0x10868c) (andR64R64Effect 0x10868c 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[290, 286]
    (.letOp (n := 294) (.out 0x10868f (xorR64R64Effect 0x10868f 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[292, 201]
    (.letOp (n := 295) (.exec 0x10868f (fun s => s.RIP = 0x10868f) (xorR64R64Effect 0x10868f 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[292, 201]
    (.letOp (n := 296) (.exec 0x108692 (StorePre 0x108692 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108692 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108692 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 297) (.exec 0x108696 (fun s => s.RIP = 0x108696) (movR64R64Effect 0x108696 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 298) (.out 0x108699 (movR64R64Effect 0x108699 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[102]
    (.letOp (n := 299) (.exec 0x108699 (fun s => s.RIP = 0x108699) (movR64R64Effect 0x108699 0 10) (Reg.operands [.gpr 10] [])) #v[102]
    (.letOp (n := 300) (.out 0x10869c (subR64R64Effect 0x10869c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[298, 256]
    (.letOp (n := 301) (.exec 0x10869c (fun s => s.RIP = 0x10869c) (subR64R64Effect 0x10869c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[298, 256]
    (.letOp (n := 302) (.out 0x10869f (notR64Effect 0x10869f 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[102]
    (.letOp (n := 303) (.exec 0x10869f (fun s => s.RIP = 0x10869f) (notR64Effect 0x10869f 10) (Reg.operands [.gpr 10] [])) #v[102]
    (.letOp (n := 304) (.out 0x1086a2 (movR64R64Effect 0x1086a2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[256]
    (.letOp (n := 305) (.exec 0x1086a2 (fun s => s.RIP = 0x1086a2) (movR64R64Effect 0x1086a2 2 6) (Reg.operands [.gpr 6] [])) #v[256]
    (.letOp (n := 306) (.out 0x1086a5 (andR64R64Effect 0x1086a5 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[304, 302]
    (.letOp (n := 307) (.exec 0x1086a5 (fun s => s.RIP = 0x1086a5) (andR64R64Effect 0x1086a5 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[304, 302]
    (.letOp (n := 308) (.out 0x1086a8 (orR64R64Effect 0x1086a8 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[302, 256]
    (.letOp (n := 309) (.exec 0x1086a8 (fun s => s.RIP = 0x1086a8) (orR64R64Effect 0x1086a8 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[302, 256]
    (.letOp (n := 310) (.out 0x1086ab (andR64R64Effect 0x1086ab 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[308, 300]
    (.letOp (n := 311) (.exec 0x1086ab (fun s => s.RIP = 0x1086ab) (andR64R64Effect 0x1086ab 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[308, 300]
    (.letOp (n := 312) (.out 0x1086ae (orR64R64Effect 0x1086ae 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[310, 306]
    (.letOp (n := 313) (.exec 0x1086ae (fun s => s.RIP = 0x1086ae) (orR64R64Effect 0x1086ae 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[310, 306]
    (.letOp (n := 314) (.out 0x1086b1 (shrR64Effect 0x1086b1 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[312]
    (.letOp (n := 315) (.exec 0x1086b1 (fun s => s.RIP = 0x1086b1) (shrR64Effect 0x1086b1 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[312]
    (.letOp (n := 316) (.out 0x1086b5 (movzxR32M8Effect 0x1086b5 5 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 317) (.exec 0x1086b5 (LoadPre 0x1086b5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1086b5 5 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 318) (.exec 0x1086ba (StorePre 0x1086ba 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086ba + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1086ba 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[314, 65]
    (.letOp (n := 319) (.exec 0x1086be (fun s => s.RIP = 0x1086be) (movR64R64Effect 0x1086be 11 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 320) (.out 0x1086c1 (xorR32R32Effect 0x1086c1 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[275, 275]
    (.letOp (n := 321) (.exec 0x1086c1 (fun s => s.RIP = 0x1086c1) (xorR32R32Effect 0x1086c1 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[275, 275]
    (.letOp (n := 322) (.out 0x1086c4 (subR64M64Effect 0x1086c4 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[320, 65]
    (.letOp (n := 323) (.exec 0x1086c4 (LoadPre 0x1086c4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1086c4 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x1086c4 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[320, 65]
    (b_l1084e0_7))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_6 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x3C, 0x24, 0x49, 0xF7, 0xDF, 0x49, 0x21, 0xD7, 0x49, 0x31, 0xC7, 0x44, 0x88,
    0x1C, 0x24, 0x48, 0x89, 0xE0, 0x4C, 0x89, 0xD0, 0x48, 0x29, 0xF0, 0x49, 0xF7, 0xD2, 0x48, 0x89,
    0xF2, 0x4C, 0x21, 0xD2, 0x49, 0x09, 0xF2, 0x49, 0x21, 0xC2, 0x49, 0x09, 0xD2, 0x49, 0xC1, 0xEA,
    0x3F, 0x44, 0x0F, 0xB6, 0x34, 0x24, 0x4C, 0x89, 0x14, 0x24, 0x49, 0x89, 0xE3, 0x45, 0x31, 0xC0,
    0x4C, 0x2B, 0x04, 0x24] ++ bytes_l1084e0_7

theorem code_l1084e0_6 : ∀ x ∈ codeRange 0x108684 bytes_l1084e0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8684 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_7

def b_l1084e0_5 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x108640 (negR64Effect 0x108640 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[250]
    (.letOp (n := 253) (.exec 0x108640 (fun s => s.RIP = 0x108640) (negR64Effect 0x108640 6) (Reg.operands [.gpr 6] [])) #v[250]
    (.letOp (n := 254) (.out 0x108643 (andR64R64Effect 0x108643 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[252, 248]
    (.letOp (n := 255) (.exec 0x108643 (fun s => s.RIP = 0x108643) (andR64R64Effect 0x108643 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[252, 248]
    (.letOp (n := 256) (.out 0x108646 (xorR64R64Effect 0x108646 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[254, 219]
    (.letOp (n := 257) (.exec 0x108646 (fun s => s.RIP = 0x108646) (xorR64R64Effect 0x108646 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[254, 219]
    (.letOp (n := 258) (.exec 0x108649 (StorePre 0x108649 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108649 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108649 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 259) (.out 0x10864d (movR64R64Effect 0x10864d 14 4) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 260) (.exec 0x10864d (fun s => s.RIP = 0x10864d) (movR64R64Effect 0x10864d 14 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 261) (.out 0x108650 (xorR64R64Effect 0x108650 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[228, 192]
    (.letOp (n := 262) (.exec 0x108650 (fun s => s.RIP = 0x108650) (xorR64R64Effect 0x108650 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[228, 192]
    (.letOp (n := 263) (.out 0x108653 (movzxR32M8Effect 0x108653 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 264) (.exec 0x108653 (LoadPre 0x108653 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108653 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108653 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 265) (.out 0x108658 (negR64Effect 0x108658 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[263]
    (.letOp (n := 266) (.exec 0x108658 (fun s => s.RIP = 0x108658) (negR64Effect 0x108658 13) (Reg.operands [.gpr 13] [])) #v[263]
    (.letOp (n := 267) (.out 0x10865b (andR64R64Effect 0x10865b 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[265, 261]
    (.letOp (n := 268) (.exec 0x10865b (fun s => s.RIP = 0x10865b) (andR64R64Effect 0x10865b 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[265, 261]
    (.letOp (n := 269) (.out 0x10865e (xorR64R64Effect 0x10865e 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[267, 192]
    (.letOp (n := 270) (.exec 0x10865e (fun s => s.RIP = 0x10865e) (xorR64R64Effect 0x10865e 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[267, 192]
    (.letOp (n := 271) (.exec 0x108661 (StorePre 0x108661 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108661 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108661 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 272) (.exec 0x108665 (fun s => s.RIP = 0x108665) (movR64R64Effect 0x108665 15 14) (Reg.operands [.gpr 14] [])) #v[259]
    (.letOp (n := 273) (.out 0x108668 (movR64M64Effect 0x108668 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 274) (.exec 0x108668 (LoadPre 0x108668 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108668 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108668 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 275) (.out 0x10866d (xorR64R64Effect 0x10866d 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[233, 273]
    (.letOp (n := 276) (.exec 0x10866d (fun s => s.RIP = 0x10866d) (xorR64R64Effect 0x10866d 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[233, 273]
    (.letOp (n := 277) (.out 0x108670 (movzxR32M8Effect 0x108670 4 5 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[65]
    (.letOp (n := 278) (.exec 0x108670 (LoadPre 0x108670 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108670 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108670 4 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 279) (.out 0x108674 (negR64Effect 0x108674 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[277]
    (.letOp (n := 280) (.exec 0x108674 (fun s => s.RIP = 0x108674) (negR64Effect 0x108674 5) (Reg.operands [.gpr 5] [])) #v[277]
    (.letOp (n := 281) (.out 0x108677 (andR64R64Effect 0x108677 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[279, 275]
    (.letOp (n := 282) (.exec 0x108677 (fun s => s.RIP = 0x108677) (andR64R64Effect 0x108677 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[279, 275]
    (.letOp (n := 283) (.out 0x10867a (xorR64R64Effect 0x10867a 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[281, 273]
    (.letOp (n := 284) (.exec 0x10867a (fun s => s.RIP = 0x10867a) (xorR64R64Effect 0x10867a 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[281, 273]
    (.letOp (n := 285) (.exec 0x10867d (StorePre 0x10867d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10867d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10867d 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 286) (.out 0x108681 (xorR64R64Effect 0x108681 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[238, 201]
    (.letOp (n := 287) (.exec 0x108681 (fun s => s.RIP = 0x108681) (xorR64R64Effect 0x108681 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[238, 201]
    (b_l1084e0_6))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_5 : List UInt8 :=
  [0x48, 0xF7, 0xDE, 0x4C, 0x21, 0xEE, 0x4C, 0x31, 0xF6, 0x44, 0x88, 0x1C, 0x24, 0x49, 0x89, 0xE6,
    0x4C, 0x31, 0xFD, 0x44, 0x0F, 0xB6, 0x2C, 0x24, 0x49, 0xF7, 0xDD, 0x49, 0x21, 0xED, 0x4D, 0x31,
    0xFD, 0x44, 0x88, 0x1C, 0x24, 0x4D, 0x89, 0xF7, 0x4C, 0x8B, 0x74, 0x24, 0x30, 0x4D, 0x31, 0xF0,
    0x0F, 0xB6, 0x2C, 0x24, 0x48, 0xF7, 0xDD, 0x4C, 0x21, 0xC5, 0x4C, 0x31, 0xF5, 0x44, 0x88, 0x1C,
    0x24, 0x48, 0x31, 0xC2] ++ bytes_l1084e0_6

theorem code_l1084e0_5 : ∀ x ∈ codeRange 0x108640 bytes_l1084e0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8640 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_6

def b_l1084e0_4 : Block Op Label signature Reg.count 214 :=
  .letOp (n := 214) (.out 0x1085f2 (xorR8R8Effect 0x1085f2 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[212, 184]
    (.letOp (n := 215) (.exec 0x1085f2 (fun s => s.RIP = 0x1085f2) (xorR8R8Effect 0x1085f2 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[212, 184]
    (.letOp (n := 216) (.exec 0x1085f5 (StorePre 0x1085f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085f5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1085f5 5 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[214, 65]
    (.letOp (n := 217) (.out 0x1085fa (xorR8Imm8Effect 0x1085fa 4 11 0x1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[214]
    (.letOp (n := 218) (.exec 0x1085fa (fun s => s.RIP = 0x1085fa) (xorR8Imm8Effect 0x1085fa 4 11 0x1) (Reg.operands [.gpr 11] [])) #v[214]
    (.letOp (n := 219) (.out 0x1085fe (movR64M64Effect 0x1085fe 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 220) (.exec 0x1085fe (LoadPre 0x1085fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1085fe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085fe 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 221) (.out 0x108603 (movR64R64Effect 0x108603 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[219]
    (.letOp (n := 222) (.exec 0x108603 (fun s => s.RIP = 0x108603) (movR64R64Effect 0x108603 13 14) (Reg.operands [.gpr 14] [])) #v[219]
    (.letOp (n := 223) (.out 0x108606 (negR64Effect 0x108606 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[221]
    (.letOp (n := 224) (.out 0x108606 (negR64Effect 0x108606 13) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[221]
    (.letOp (n := 225) (.exec 0x108606 (fun s => s.RIP = 0x108606) (negR64Effect 0x108606 13) (Reg.operands [.gpr 13] [])) #v[221]
    (.letOp (n := 226) (.out 0x108609 (movR32Imm32Effect 0x108609 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 227) (.exec 0x108609 (fun s => s.RIP = 0x108609) (movR32Imm32Effect 0x108609 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 228) (.out 0x10860e (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[226, 192, 224]
    (.letOp (n := 229) (.out 0x10860e (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[226, 192, 224]
    (.letOp (n := 230) (.exec 0x10860e (fun s => s.RIP = 0x10860e) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10860e 5 15)) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[226, 192, 224]
    (.letOp (n := 231) (.out 0x108611 (movR32Imm32Effect 0x108611 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 232) (.exec 0x108611 (fun s => s.RIP = 0x108611) (movR32Imm32Effect 0x108611 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 233) (.out 0x108617 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[231, 198, 229]
    (.letOp (n := 234) (.out 0x108617 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[231, 198, 229]
    (.letOp (n := 235) (.exec 0x108617 (fun s => s.RIP = 0x108617) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108617 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[231, 198, 229]
    (.letOp (n := 236) (.out 0x10861a (movR32Imm32Effect 0x10861a 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 237) (.exec 0x10861a (fun s => s.RIP = 0x10861a) (movR32Imm32Effect 0x10861a 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 238) (.out 0x10861f (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[236, 201, 234]
    (.letOp (n := 239) (.out 0x10861f (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[236, 201, 234]
    (.letOp (n := 240) (.exec 0x10861f (fun s => s.RIP = 0x10861f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x10861f 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 201, 234]
    (.letOp (n := 241) (.exec 0x108622 (StorePre 0x108622 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108622 + BitVec.ofNat 64 4)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108622 4 (.sib 4 none 0 .none))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 239]
    (.letOp (n := 242) (.exec 0x108626 (fun s => s.RIP = 0x108626) (movR64R64Effect 0x108626 6 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 243) (.out 0x108629 (movzxR32M8Effect 0x108629 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 244) (.exec 0x108629 (LoadPre 0x108629 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108629 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108629 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 245) (.exec 0x10862d (StorePre 0x10862d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10862d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10862d 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[243, 65]
    (.letOp (n := 246) (.exec 0x108632 (StorePre 0x108632 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108632 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108632 4 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[217, 65]
    (.letOp (n := 247) (.exec 0x108636 (fun s => s.RIP = 0x108636) (movR64R64Effect 0x108636 6 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 248) (.out 0x108639 (xorR64R64Effect 0x108639 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[223, 219]
    (.letOp (n := 249) (.exec 0x108639 (fun s => s.RIP = 0x108639) (xorR64R64Effect 0x108639 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[223, 219]
    (.letOp (n := 250) (.out 0x10863c (movzxR32M8Effect 0x10863c 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 251) (.exec 0x10863c (LoadPre 0x10863c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10863c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10863c 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1084e0_5))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_4 : List UInt8 :=
  [0x45, 0x30, 0xC3, 0x44, 0x88, 0x5C, 0x24, 0x10, 0x41, 0x80, 0xF3, 0x01, 0x4C, 0x8B, 0x74, 0x24,
    0x28, 0x4D, 0x89, 0xF5, 0x49, 0xF7, 0xDD, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x19, 0xFD, 0x41,
    0xB8, 0x00, 0x00, 0x00, 0x00, 0x49, 0x19, 0xF0, 0xBA, 0x00, 0x00, 0x00, 0x00, 0x48, 0x19, 0xC2,
    0x0F, 0x93, 0x04, 0x24, 0x48, 0x89, 0xE6, 0x0F, 0xB6, 0x34, 0x24, 0x48, 0x89, 0x74, 0x24, 0x38,
    0x44, 0x88, 0x1C, 0x24, 0x48, 0x89, 0xE6, 0x4D, 0x31, 0xF5, 0x0F, 0xB6, 0x34, 0x24] ++ bytes_l1084e0_5

theorem code_l1084e0_4 : ∀ x ∈ codeRange 0x1085f2 bytes_l1084e0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x85f2 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_5

def b_l1084e0_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x1085a1 (movR64R64Effect 0x1085a1 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 174) (.exec 0x1085a1 (fun s => s.RIP = 0x1085a1) (movR64R64Effect 0x1085a1 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 175) (.out 0x1085a4 (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[173, 67]
    (.letOp (n := 176) (.out 0x1085a4 (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[173, 67]
    (.letOp (n := 177) (.exec 0x1085a4 (LoadPre 0x1085a4 (fun s => AddrMode.addr (.base 11 (.d8 0x10)) s (0x1085a4 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085a4 4 (.base 11 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[173, 67]
    (.letOp (n := 178) (.out 0x1085a8 (movR64R64Effect 0x1085a8 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[175]
    (.letOp (n := 179) (.exec 0x1085a8 (fun s => s.RIP = 0x1085a8) (movR64R64Effect 0x1085a8 14 0) (Reg.operands [.gpr 0] [])) #v[175]
    (.letOp (n := 180) (.out 0x1085ab (movR64R64Effect 0x1085ab 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[176]
    (.letOp (n := 181) (.exec 0x1085ab (fun s => s.RIP = 0x1085ab) (movR64R64Effect 0x1085ab 5 2) (Reg.operands [.gpr 2] [])) #v[176]
    (.letOp (n := 182) (.out 0x1085ae (movR64M64Effect 0x1085ae 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 183) (.exec 0x1085ae (LoadPre 0x1085ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085ae 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 184) (.out 0x1085b3 (xorR8M8Effect 0x1085b3 4 8 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[182, 6]
    (.letOp (n := 185) (.exec 0x1085b3 (LoadPre 0x1085b3 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1085b3 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085b3 4 8 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 6] [])) #v[182, 6]
    (.letOp (n := 186) (.exec 0x1085b7 (StorePre 0x1085b7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1085b7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085b7 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[184, 65]
    (.letOp (n := 187) (.out 0x1085bc (movR64R64Effect 0x1085bc 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 188) (.exec 0x1085bc (fun s => s.RIP = 0x1085bc) (movR64R64Effect 0x1085bc 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 189) (.out 0x1085bf (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[187, 67]
    (.letOp (n := 190) (.out 0x1085bf (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[187, 67]
    (.letOp (n := 191) (.exec 0x1085bf (LoadPre 0x1085bf (fun s => AddrMode.addr (.base 11 (.d8 0x18)) s (0x1085bf + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x1085bf 4 (.base 11 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[187, 67]
    (.letOp (n := 192) (.out 0x1085c3 (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[171, 65]
    (.letOp (n := 193) (.out 0x1085c3 (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[171, 65]
    (.letOp (n := 194) (.exec 0x1085c3 (LoadPre 0x1085c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1085c3 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x1085c3 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[171, 65]
    (.letOp (n := 195) (.out 0x1085c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[178, 65, 193]
    (.letOp (n := 196) (.out 0x1085c8 (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[178, 65, 193]
    (.letOp (n := 197) (.exec 0x1085c8 (LoadPre 0x1085c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085c8 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x1085c8 14 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[178, 65, 193]
    (.letOp (n := 198) (.out 0x1085cd (movR64R64Effect 0x1085cd 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[195]
    (.letOp (n := 199) (.exec 0x1085cd (fun s => s.RIP = 0x1085cd) (movR64R64Effect 0x1085cd 6 14) (Reg.operands [.gpr 14] [])) #v[195]
    (.letOp (n := 200) (.exec 0x1085d0 (StorePre 0x1085d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1085d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085d0 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[195, 65]
    (.letOp (n := 201) (.out 0x1085d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[189, 180, 196]
    (.letOp (n := 202) (.out 0x1085d5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[189, 180, 196]
    (.letOp (n := 203) (.exec 0x1085d5 (fun s => s.RIP = 0x1085d5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1085d5 0 5)) (Reg.operands [.gpr 0, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[189, 180, 196]
    (.letOp (n := 204) (.out 0x1085d8 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1085d8 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[190, 202]
    (.letOp (n := 205) (.exec 0x1085d8 (fun s => s.RIP = 0x1085d8) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1085d8 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[190, 202]
    (.letOp (n := 206) (.exec 0x1085dc (StorePre 0x1085dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1085dc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085dc 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[204, 65]
    (.letOp (n := 207) (.out 0x1085e1 (movR64M64Effect 0x1085e1 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 208) (.exec 0x1085e1 (LoadPre 0x1085e1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085e1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1085e1 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 209) (.out 0x1085e6 (xorR8M8Effect 0x1085e6 4 2 (.base 11 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[207, 67]
    (.letOp (n := 210) (.exec 0x1085e6 (LoadPre 0x1085e6 (fun s => AddrMode.addr (.base 11 (.d8 0x20)) s (0x1085e6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x1085e6 4 2 (.base 11 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 11] [])) #v[207, 67]
    (.letOp (n := 211) (.exec 0x1085ea (StorePre 0x1085ea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1085ea + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1085ea 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[209, 65]
    (.letOp (n := 212) (.out 0x1085ef (movR32R32Effect 0x1085ef 3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[209]
    (.letOp (n := 213) (.exec 0x1085ef (fun s => s.RIP = 0x1085ef) (movR32R32Effect 0x1085ef 3 11 2) (Reg.operands [.gpr 2] [])) #v[209]
    (b_l1084e0_4)))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_3 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x63, 0x10, 0x49, 0x89, 0xC6, 0x48, 0x89, 0xD5, 0x4C, 0x8B, 0x44,
    0x24, 0x20, 0x44, 0x32, 0x46, 0x20, 0x4C, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x89, 0xE8, 0x49, 0xF7,
    0x63, 0x18, 0x4C, 0x03, 0x7C, 0x24, 0x10, 0x4C, 0x13, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xF6, 0x4C,
    0x89, 0x74, 0x24, 0x30, 0x48, 0x11, 0xE8, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x89, 0x54, 0x24, 0x08,
    0x48, 0x8B, 0x54, 0x24, 0x18, 0x41, 0x32, 0x53, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x41, 0x89,
    0xD3] ++ bytes_l1084e0_4

theorem code_l1084e0_3 : ∀ x ∈ codeRange 0x1085a1 bytes_l1084e0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x85a1 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_4

def b_l1084e0_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x10855c (movR64R64Effect 0x10855c 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[126]
    (.letOp (n := 131) (.exec 0x10855c (fun s => s.RIP = 0x10855c) (movR64R64Effect 0x10855c 5 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 132) (.out 0x10855f (negR64Effect 0x10855f 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[119]
    (.letOp (n := 133) (.exec 0x10855f (fun s => s.RIP = 0x10855f) (negR64Effect 0x10855f 13) (Reg.operands [.gpr 13] [])) #v[119]
    (.letOp (n := 134) (.out 0x108562 (andR64R64Effect 0x108562 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[132, 121]
    (.letOp (n := 135) (.exec 0x108562 (fun s => s.RIP = 0x108562) (andR64R64Effect 0x108562 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[132, 121]
    (.letOp (n := 136) (.out 0x108565 (movR64R64Effect 0x108565 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 137) (.exec 0x108565 (fun s => s.RIP = 0x108565) (movR64R64Effect 0x108565 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 138) (.out 0x108568 (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[136, 6]
    (.letOp (n := 139) (.out 0x108568 (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[136, 6]
    (.letOp (n := 140) (.exec 0x108568 (LoadPre 0x108568 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108568 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108568 4 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[136, 6]
    (.letOp (n := 141) (.out 0x10856c (movR64R64Effect 0x10856c 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[138]
    (.letOp (n := 142) (.exec 0x10856c (fun s => s.RIP = 0x10856c) (movR64R64Effect 0x10856c 3 0) (Reg.operands [.gpr 0] [])) #v[138]
    (.letOp (n := 143) (.out 0x10856f (movR64R64Effect 0x10856f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[139]
    (.letOp (n := 144) (.exec 0x10856f (fun s => s.RIP = 0x10856f) (movR64R64Effect 0x10856f 1 2) (Reg.operands [.gpr 2] [])) #v[139]
    (.letOp (n := 145) (.out 0x108572 (xorR64R64Effect 0x108572 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[134, 8]
    (.letOp (n := 146) (.exec 0x108572 (fun s => s.RIP = 0x108572) (xorR64R64Effect 0x108572 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[134, 8]
    (.letOp (n := 147) (.out 0x108575 (addR64R64Effect 0x108575 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[115, 104]
    (.letOp (n := 148) (.out 0x108575 (addR64R64Effect 0x108575 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[115, 104]
    (.letOp (n := 149) (.exec 0x108575 (fun s => s.RIP = 0x108575) (addR64R64Effect 0x108575 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[115, 104]
    (.letOp (n := 150) (.out 0x108578 (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[128, 117, 148]
    (.letOp (n := 151) (.out 0x108578 (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[128, 117, 148]
    (.letOp (n := 152) (.exec 0x108578 (fun s => s.RIP = 0x108578) (atFlags StatusFlags.CF (adcR64R64Effect 0x108578 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[128, 117, 148]
    (.letOp (n := 153) (.out 0x10857b (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[141, 130, 151]
    (.letOp (n := 154) (.out 0x10857b (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[141, 130, 151]
    (.letOp (n := 155) (.exec 0x10857b (fun s => s.RIP = 0x10857b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10857b 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[141, 130, 151]
    (.letOp (n := 156) (.out 0x10857e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10857e 1 0x0)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[143, 154]
    (.letOp (n := 157) (.exec 0x10857e (fun s => s.RIP = 0x10857e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10857e 1 0x0)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[143, 154]
    (.letOp (n := 158) (.out 0x108582 (movR64R64Effect 0x108582 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 159) (.exec 0x108582 (fun s => s.RIP = 0x108582) (movR64R64Effect 0x108582 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 160) (.out 0x108585 (mulM64Effect 0x108585 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[158, 67]
    (.letOp (n := 161) (.out 0x108585 (mulM64Effect 0x108585 3 (.base 11 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[158, 67]
    (.letOp (n := 162) (.exec 0x108585 (LoadPre 0x108585 (fun s => AddrMode.addr (.base 11 .none) s (0x108585 + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x108585 3 (.base 11 .none)) (Reg.operands [.gpr 0, .gpr 11] [])) #v[158, 67]
    (.letOp (n := 163) (.exec 0x108588 (StorePre 0x108588 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108588 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108588 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[161, 65]
    (.letOp (n := 164) (.exec 0x10858d (StorePre 0x10858d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10858d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10858d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[160, 65]
    (.letOp (n := 165) (.out 0x108592 (movR64R64Effect 0x108592 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 166) (.exec 0x108592 (fun s => s.RIP = 0x108592) (movR64R64Effect 0x108592 0 13) (Reg.operands [.gpr 13] [])) #v[145]
    (.letOp (n := 167) (.out 0x108595 (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[165, 67]
    (.letOp (n := 168) (.out 0x108595 (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 11] []) (.reg (.gpr 2))) #v[165, 67]
    (.letOp (n := 169) (.exec 0x108595 (LoadPre 0x108595 (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x108595 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108595 4 (.base 11 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 11] [])) #v[165, 67]
    (.letOp (n := 170) (.exec 0x108599 (StorePre 0x108599 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108599 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108599 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[168, 65]
    (.letOp (n := 171) (.out 0x10859e (movR64R64Effect 0x10859e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[167]
    (.letOp (n := 172) (.exec 0x10859e (fun s => s.RIP = 0x10859e) (movR64R64Effect 0x10859e 15 0) (Reg.operands [.gpr 0] [])) #v[167]
    (b_l1084e0_3)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_2 : List UInt8 :=
  [0x48, 0x89, 0xD5, 0x49, 0xF7, 0xDD, 0x49, 0x21, 0xCD, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x18,
    0x48, 0x89, 0xC3, 0x48, 0x89, 0xD1, 0x4D, 0x31, 0xC5, 0x4D, 0x01, 0xF1, 0x4D, 0x11, 0xFC, 0x48,
    0x11, 0xEB, 0x48, 0x83, 0xD1, 0x00, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x23, 0x48, 0x89, 0x54, 0x24,
    0x10, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0x63, 0x08, 0x48, 0x89, 0x54,
    0x24, 0x08, 0x49, 0x89, 0xC7] ++ bytes_l1084e0_3

theorem code_l1084e0_2 : ∀ x ∈ codeRange 0x10855c bytes_l1084e0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x855c 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_3

def b_l1084e0_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x108519 (movR64R64Effect 0x108519 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 91) (.exec 0x108519 (fun s => s.RIP = 0x108519) (movR64R64Effect 0x108519 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 92) (.out 0x10851c (shrR64Effect 0x10851c 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[90]
    (.letOp (n := 93) (.exec 0x10851c (fun s => s.RIP = 0x10851c) (shrR64Effect 0x10851c 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[90]
    (.letOp (n := 94) (.exec 0x108520 (StorePre 0x108520 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x108520 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108520 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 65]
    (.letOp (n := 95) (.exec 0x108525 (StorePre 0x108525 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108525 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108525 3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 65]
    (.letOp (n := 96) (.exec 0x108528 (fun s => s.RIP = 0x108528) (movR64R64Effect 0x108528 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 97) (.out 0x10852b (movR64R64Effect 0x10852b 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 98) (.exec 0x10852b (fun s => s.RIP = 0x10852b) (movR64R64Effect 0x10852b 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 99) (.out 0x10852e (mulM64Effect 0x10852e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[97, 6]
    (.letOp (n := 100) (.out 0x10852e (mulM64Effect 0x10852e 3 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[97, 6]
    (.letOp (n := 101) (.exec 0x10852e (LoadPre 0x10852e (fun s => AddrMode.addr (.base 6 .none) s (0x10852e + BitVec.ofNat 64 3)) 8) (mulM64Effect 0x10852e 3 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[97, 6]
    (.letOp (n := 102) (.out 0x108531 (movR64R64Effect 0x108531 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[99]
    (.letOp (n := 103) (.exec 0x108531 (fun s => s.RIP = 0x108531) (movR64R64Effect 0x108531 10 0) (Reg.operands [.gpr 0] [])) #v[99]
    (.letOp (n := 104) (.out 0x108534 (movR64R64Effect 0x108534 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[100]
    (.letOp (n := 105) (.exec 0x108534 (fun s => s.RIP = 0x108534) (movR64R64Effect 0x108534 14 2) (Reg.operands [.gpr 2] [])) #v[100]
    (.letOp (n := 106) (.out 0x108537 (movR64R64Effect 0x108537 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 107) (.exec 0x108537 (fun s => s.RIP = 0x108537) (movR64R64Effect 0x108537 1 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 108) (.out 0x10853a (negR64Effect 0x10853a 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[106]
    (.letOp (n := 109) (.exec 0x10853a (fun s => s.RIP = 0x10853a) (negR64Effect 0x10853a 1) (Reg.operands [.gpr 1] [])) #v[106]
    (.letOp (n := 110) (.out 0x10853d (movR64R64Effect 0x10853d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 111) (.exec 0x10853d (fun s => s.RIP = 0x10853d) (movR64R64Effect 0x10853d 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 112) (.out 0x108540 (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[110, 6]
    (.letOp (n := 113) (.out 0x108540 (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[110, 6]
    (.letOp (n := 114) (.exec 0x108540 (LoadPre 0x108540 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108540 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108540 4 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[110, 6]
    (.letOp (n := 115) (.out 0x108544 (movR64R64Effect 0x108544 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[112]
    (.letOp (n := 116) (.exec 0x108544 (fun s => s.RIP = 0x108544) (movR64R64Effect 0x108544 9 0) (Reg.operands [.gpr 0] [])) #v[112]
    (.letOp (n := 117) (.out 0x108547 (movR64R64Effect 0x108547 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[113]
    (.letOp (n := 118) (.exec 0x108547 (fun s => s.RIP = 0x108547) (movR64R64Effect 0x108547 15 2) (Reg.operands [.gpr 2] [])) #v[113]
    (.letOp (n := 119) (.out 0x10854a (movzxR32M8Effect 0x10854a 5 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 120) (.exec 0x10854a (LoadPre 0x10854a (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10854a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10854a 5 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 121) (.out 0x10854f (xorR64R64Effect 0x10854f 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[108, 8]
    (.letOp (n := 122) (.exec 0x10854f (fun s => s.RIP = 0x10854f) (xorR64R64Effect 0x10854f 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[108, 8]
    (.letOp (n := 123) (.out 0x108552 (movR64R64Effect 0x108552 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[88]
    (.letOp (n := 124) (.exec 0x108552 (fun s => s.RIP = 0x108552) (movR64R64Effect 0x108552 0 3) (Reg.operands [.gpr 3] [])) #v[88]
    (.letOp (n := 125) (.out 0x108555 (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[123, 6]
    (.letOp (n := 126) (.out 0x108555 (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 6] []) (.reg (.gpr 2))) #v[123, 6]
    (.letOp (n := 127) (.exec 0x108555 (LoadPre 0x108555 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108555 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x108555 4 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[123, 6]
    (.letOp (n := 128) (.out 0x108559 (movR64R64Effect 0x108559 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[125]
    (.letOp (n := 129) (.exec 0x108559 (fun s => s.RIP = 0x108559) (movR64R64Effect 0x108559 12 0) (Reg.operands [.gpr 0] [])) #v[125]
    (b_l1084e0_2))))))))))))))))))))))))))))))))))))))))

def bytes_l1084e0_1 : List UInt8 :=
  [0x4C, 0x89, 0xC0, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x18, 0x88, 0x04, 0x24, 0x48,
    0x89, 0xE0, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x26, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD6, 0x4C, 0x89,
    0xC1, 0x48, 0xF7, 0xD9, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x08, 0x49, 0x89, 0xC1, 0x49, 0x89,
    0xD7, 0x44, 0x0F, 0xB6, 0x2C, 0x24, 0x4C, 0x31, 0xC1, 0x48, 0x89, 0xD8, 0x48, 0xF7, 0x66, 0x10,
    0x49, 0x89, 0xC4] ++ bytes_l1084e0_2

theorem code_l1084e0_1 : ∀ x ∈ codeRange 0x108519 bytes_l1084e0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8519 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_2

def b_l1084e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1084e0 (pushR64Effect 0x1084e0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1084e0 (PushPre 0x1084e0 1) (pushR64Effect 0x1084e0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1084e1 (pushR64Effect 0x1084e1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1084e1 (PushPre 0x1084e1 2) (pushR64Effect 0x1084e1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1084e3 (pushR64Effect 0x1084e3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1084e3 (PushPre 0x1084e3 2) (pushR64Effect 0x1084e3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1084e5 (pushR64Effect 0x1084e5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1084e5 (PushPre 0x1084e5 2) (pushR64Effect 0x1084e5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1084e7 (pushR64Effect 0x1084e7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1084e7 (PushPre 0x1084e7 2) (pushR64Effect 0x1084e7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1084e9 (pushR64Effect 0x1084e9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1084e9 (PushPre 0x1084e9 1) (pushR64Effect 0x1084e9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1084ea (subR64Imm8Effect 0x1084ea 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1084ea (fun s => s.RIP = 0x1084ea) (subR64Imm8Effect 0x1084ea 4 0x40) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1084ee (movR64R64Effect 0x1084ee 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 68) (.exec 0x1084ee (fun s => s.RIP = 0x1084ee) (movR64R64Effect 0x1084ee 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1084f1 (movR64R64Effect 0x1084f1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 70) (.exec 0x1084f1 (fun s => s.RIP = 0x1084f1) (movR64R64Effect 0x1084f1 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 71) (.out 0x1084f4 (shrR64Effect 0x1084f4 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x1084f4 (fun s => s.RIP = 0x1084f4) (shrR64Effect 0x1084f4 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x1084f8 (StorePre 0x1084f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1084f8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1084f8 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 74) (.out 0x1084fd (movR64R64Effect 0x1084fd 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 75) (.exec 0x1084fd (fun s => s.RIP = 0x1084fd) (movR64R64Effect 0x1084fd 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 76) (.out 0x108500 (negR64Effect 0x108500 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 77) (.exec 0x108500 (fun s => s.RIP = 0x108500) (negR64Effect 0x108500 0) (Reg.operands [.gpr 0] [])) #v[74]
    (.letOp (n := 78) (.exec 0x108503 (StorePre 0x108503 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108503 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x108503 3 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 79) (.exec 0x108506 (fun s => s.RIP = 0x108506) (movR64R64Effect 0x108506 2 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.out 0x108509 (movzxR32M8Effect 0x108509 4 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 81) (.exec 0x108509 (LoadPre 0x108509 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x108509 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x108509 4 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 82) (.out 0x10850d (xorR64R64Effect 0x10850d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[76, 1]
    (.letOp (n := 83) (.exec 0x10850d (fun s => s.RIP = 0x10850d) (xorR64R64Effect 0x10850d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[76, 1]
    (.letOp (n := 84) (.out 0x108510 (negR64Effect 0x108510 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[80]
    (.letOp (n := 85) (.exec 0x108510 (fun s => s.RIP = 0x108510) (negR64Effect 0x108510 3) (Reg.operands [.gpr 3] [])) #v[80]
    (.letOp (n := 86) (.out 0x108513 (andR64R64Effect 0x108513 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[84, 82]
    (.letOp (n := 87) (.exec 0x108513 (fun s => s.RIP = 0x108513) (andR64R64Effect 0x108513 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[84, 82]
    (.letOp (n := 88) (.out 0x108516 (xorR64R64Effect 0x108516 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[86, 1]
    (.letOp (n := 89) (.exec 0x108516 (fun s => s.RIP = 0x108516) (xorR64R64Effect 0x108516 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[86, 1]
    (b_l1084e0_1)))))))))))))))))))))))))))))))))))))

def bytes_l1084e0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x40, 0x49, 0x89,
    0xD3, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0xC8,
    0x48, 0xF7, 0xD8, 0x88, 0x14, 0x24, 0x48, 0x89, 0xE2, 0x0F, 0xB6, 0x1C, 0x24, 0x48, 0x31, 0xC8,
    0x48, 0xF7, 0xDB, 0x48, 0x21, 0xC3, 0x48, 0x31, 0xCB] ++ bytes_l1084e0_1

theorem code_l1084e0 : ∀ x ∈ codeRange 0x1084e0 bytes_l1084e0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x84e0 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1084e0_1

@[cfg_block] def b_l108890 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108890 (pushR64Effect 0x108890 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108890 (PushPre 0x108890 1) (pushR64Effect 0x108890 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108891 (pushR64Effect 0x108891 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x108891 (PushPre 0x108891 2) (pushR64Effect 0x108891 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x108893 (pushR64Effect 0x108893 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[55, 3]
    (.letOp (n := 58) (.exec 0x108893 (PushPre 0x108893 1) (pushR64Effect 0x108893 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 59) (.out 0x108894 (subR64Imm8Effect 0x108894 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x108894 (fun s => s.RIP = 0x108894) (subR64Imm8Effect 0x108894 4 0x30) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x108898 (movR32R32Effect 0x108898 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 62) (.exec 0x108898 (fun s => s.RIP = 0x108898) (movR32R32Effect 0x108898 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 63) (.out 0x10889b (movR64R64Effect 0x10889b 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 64) (.exec 0x10889b (fun s => s.RIP = 0x10889b) (movR64R64Effect 0x10889b 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 65) (.out 0x10889e (movR64R64Effect 0x10889e 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 66) (.exec 0x10889e (fun s => s.RIP = 0x10889e) (movR64R64Effect 0x10889e 7 4) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 67) (.out 0x1088a1 (callEffect (fun _ => 0x1084e0) 0x1088a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 68) (.exec 0x1088a1 (PushPre 0x1088a1 5) (callEffect (fun _ => 0x1084e0) 0x1088a6) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 69) (.const ⟨64, 0x1088a6⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(1, 1), (2, 2), (3, 63), (4, 67), (5, 61), (6, 6), (7, 65), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1088a6, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l108890 : List UInt8 :=
  [0x55, 0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x44, 0x89, 0xCD, 0x48, 0x89, 0xFB, 0x48, 0x89,
    0xE7, 0xE8, 0x3A, 0xFC, 0xFF, 0xFF]

theorem code_l108890 : ∀ x ∈ codeRange 0x108890 bytes_l108890, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8890 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088a6 (movR32Imm32Effect 0x1088a6 5 0 0x40) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1088a6 (fun s => s.RIP = 0x1088a6) (movR32Imm32Effect 0x1088a6 5 0 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1088ab (subR32R32Effect 0x1088ab 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[53, 5]
    (.letOp (n := 56) (.exec 0x1088ab (fun s => s.RIP = 0x1088ab) (subR32R32Effect 0x1088ab 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 57) (.out 0x1088ad (cmpR32Imm8Effect 0x1088ad 3 0 0x40) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[55]
    (.letOp (n := 58) (.exec 0x1088ad (fun s => s.RIP = 0x1088ad) (cmpR32Imm8Effect 0x1088ad 3 0 0x40) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l108952, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1088b6, RegMap.args [(0, 55), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1088a6 : List UInt8 :=
  [0xB8, 0x40, 0x00, 0x00, 0x00, 0x29, 0xE8, 0x83, 0xF8, 0x40, 0x0F, 0x83, 0x9C, 0x00, 0x00, 0x00]

theorem code_l1088a6 : ∀ x ∈ codeRange 0x1088a6 bytes_l1088a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88a6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088b6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088b6 (cmpR32Imm8Effect 0x1088b6 3 5 0x40) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.exec 0x1088b6 (fun s => s.RIP = 0x1088b6) (cmpR32Imm8Effect 0x1088b6 3 5 0x40) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10893a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1088bb, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1088b6 : List UInt8 :=
  [0x83, 0xFD, 0x40, 0x73, 0x7F]

theorem code_l1088b6 : ∀ x ∈ codeRange 0x1088b6 bytes_l1088b6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88b6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088bb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088bb (testR32R32Effect 0x1088bb 2 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 54) (.exec 0x1088bb (fun s => s.RIP = 0x1088bb) (testR32R32Effect 0x1088bb 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10896a, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1088c3, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1088bb : List UInt8 :=
  [0x85, 0xED, 0x0F, 0x84, 0xA7, 0x00, 0x00, 0x00]

theorem code_l1088bb : ∀ x ∈ codeRange 0x1088bb bytes_l1088bb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88bb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088c3_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x108906 (movR32R32Effect 0x108906 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 94) (.exec 0x108906 (fun s => s.RIP = 0x108906) (movR32R32Effect 0x108906 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 95) (.out 0x108908 (shrR64ClEffect 0x108908 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[91, 93]
    (.letOp (n := 96) (.exec 0x108908 (fun s => s.RIP = 0x108908) (shrR64ClEffect 0x108908 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91, 93]
    (.letOp (n := 97) (.out 0x10890b (movR32R32Effect 0x10890b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 98) (.exec 0x10890b (fun s => s.RIP = 0x10890b) (movR32R32Effect 0x10890b 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 99) (.out 0x10890d (shlR64ClEffect 0x10890d 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[55, 97]
    (.letOp (n := 100) (.exec 0x10890d (fun s => s.RIP = 0x10890d) (shlR64ClEffect 0x10890d 3 6) (Reg.operands [.gpr 6, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55, 97]
    (.letOp (n := 101) (.out 0x108910 (movR32R32Effect 0x108910 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 102) (.exec 0x108910 (fun s => s.RIP = 0x108910) (movR32R32Effect 0x108910 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 103) (.out 0x108912 (shrR64ClEffect 0x108912 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53, 101]
    (.letOp (n := 104) (.exec 0x108912 (fun s => s.RIP = 0x108912) (shrR64ClEffect 0x108912 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53, 101]
    (.letOp (n := 105) (.out 0x108915 (orR64R64Effect 0x108915 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[85, 75]
    (.letOp (n := 106) (.exec 0x108915 (fun s => s.RIP = 0x108915) (orR64R64Effect 0x108915 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[85, 75]
    (.letOp (n := 107) (.out 0x108918 (orR64R64Effect 0x108918 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[95, 89]
    (.letOp (n := 108) (.exec 0x108918 (fun s => s.RIP = 0x108918) (orR64R64Effect 0x108918 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[95, 89]
    (.letOp (n := 109) (.out 0x10891b (orR64R64Effect 0x10891b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[103, 99]
    (.letOp (n := 110) (.exec 0x10891b (fun s => s.RIP = 0x10891b) (orR64R64Effect 0x10891b 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[103, 99]
    (.letOp (n := 111) (.exec 0x10891e (StorePre 0x10891e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10891e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10891e 2 (.base 3 .none)) (Reg.operands [.gpr 2, .gpr 3] [])) #v[109, 3]
    (.letOp (n := 112) (.exec 0x108921 (StorePre 0x108921 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x108921 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108921 14 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[107, 3]
    (.letOp (n := 113) (.exec 0x108925 (StorePre 0x108925 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x108925 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108925 11 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[105, 3]
    (.letOp (n := 114) (.exec 0x108929 (StorePre 0x108929 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x108929 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108929 9 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 115) (.exec 0x10892d (StorePre 0x10892d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10892d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10892d 4 10 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[77, 3]
    (.letOp (n := 116) (.out 0x108931 (addR64Imm8Effect 0x108931 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 117) (.exec 0x108931 (fun s => s.RIP = 0x108931) (addR64Imm8Effect 0x108931 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x108935 (popR64Effect 0x108935 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[116]
    (.letOp (n := 119) (.out 0x108935 (popR64Effect 0x108935 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[116]
    (.letOp (n := 120) (.exec 0x108935 (PopPre 0x108935) (popR64Effect 0x108935 1 3) (Reg.operands [.gpr 4] [])) #v[116]
    (.letOp (n := 121) (.out 0x108936 (popR64Effect 0x108936 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[119]
    (.letOp (n := 122) (.out 0x108936 (popR64Effect 0x108936 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[119]
    (.letOp (n := 123) (.exec 0x108936 (PopPre 0x108936) (popR64Effect 0x108936 2 14) (Reg.operands [.gpr 4] [])) #v[119]
    (.letOp (n := 124) (.out 0x108938 (popR64Effect 0x108938 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[122]
    (.letOp (n := 125) (.out 0x108938 (popR64Effect 0x108938 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[122]
    (.letOp (n := 126) (.exec 0x108938 (PopPre 0x108938) (popR64Effect 0x108938 1 5) (Reg.operands [.gpr 4] [])) #v[122]
    (.letOp (n := 127) (.out 0x108939 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[125]
    (.letOp (n := 128) (.out 0x108939 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[125]
    (.letOp (n := 129) (.exec 0x108939 (RetPre 0x108939) (retEffect) (Reg.operands [.gpr 4] [])) #v[125]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 101), (2, 109), (3, 118), (4, 128), (5, 124), (6, 99), (7, 89), (8, 75), (9, 79), (10, 77), (11, 105), (12, 12), (13, 13), (14, 121), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 130) (some ⟨127, by decide⟩)))))))))))))))))))))))))))))))))))))))

def bytes_l1088c3_1 : List UInt8 :=
  [0x89, 0xE9, 0x49, 0xD3, 0xEE, 0x89, 0xC1, 0x48, 0xD3, 0xE6, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4D,
    0x09, 0xC3, 0x49, 0x09, 0xFE, 0x48, 0x09, 0xF2, 0x48, 0x89, 0x13, 0x4C, 0x89, 0x73, 0x08, 0x4C,
    0x89, 0x5B, 0x10, 0x4C, 0x89, 0x4B, 0x18, 0x44, 0x88, 0x53, 0x20, 0x48, 0x83, 0xC4, 0x30, 0x5B,
    0x41, 0x5E, 0x5D, 0xC3]

theorem code_l1088c3_1 : ∀ x ∈ codeRange 0x108906 bytes_l1088c3_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8906 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1088c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1088c3 (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1088c3 (LoadPre 0x1088c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1088c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1088c3 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1088c7 (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1088c7 (LoadPre 0x1088c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1088c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088c7 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1088cc (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1088cc (LoadPre 0x1088cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1088cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088cc 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1088d1 (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x1088d1 (LoadPre 0x1088d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1088d1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d1 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1088d6 (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 62) (.exec 0x1088d6 (LoadPre 0x1088d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1088d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1088d6 11 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1088db (movR32R32Effect 0x1088db 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 64) (.exec 0x1088db (fun s => s.RIP = 0x1088db) (movR32R32Effect 0x1088db 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 65) (.out 0x1088dd (shlR64ClEffect 0x1088dd 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[61, 63]
    (.letOp (n := 66) (.exec 0x1088dd (fun s => s.RIP = 0x1088dd) (shlR64ClEffect 0x1088dd 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61, 63]
    (.letOp (n := 67) (.out 0x1088e0 (movR64R64Effect 0x1088e0 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[59]
    (.letOp (n := 68) (.exec 0x1088e0 (fun s => s.RIP = 0x1088e0) (movR64R64Effect 0x1088e0 9 8) (Reg.operands [.gpr 8] [])) #v[59]
    (.letOp (n := 69) (.out 0x1088e3 (movR32R32Effect 0x1088e3 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 70) (.exec 0x1088e3 (fun s => s.RIP = 0x1088e3) (movR32R32Effect 0x1088e3 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x1088e5 (shrR64ClEffect 0x1088e5 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x1088e5 (fun s => s.RIP = 0x1088e5) (shrR64ClEffect 0x1088e5 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 69]
    (.letOp (n := 73) (.out 0x1088e8 (movR32R32Effect 0x1088e8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 74) (.exec 0x1088e8 (fun s => s.RIP = 0x1088e8) (movR32R32Effect 0x1088e8 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 75) (.out 0x1088ea (shlR64ClEffect 0x1088ea 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[59, 73]
    (.letOp (n := 76) (.exec 0x1088ea (fun s => s.RIP = 0x1088ea) (shlR64ClEffect 0x1088ea 3 8) (Reg.operands [.gpr 8, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 73]
    (.letOp (n := 77) (.out 0x1088ed (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 78) (.exec 0x1088ed (LoadPre 0x1088ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1088ed + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1088ed 6 10 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1088f3 (orR64R64Effect 0x1088f3 9 11) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11] []) (.reg (.gpr 9))) #v[71, 65]
    (.letOp (n := 80) (.exec 0x1088f3 (fun s => s.RIP = 0x1088f3) (orR64R64Effect 0x1088f3 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[71, 65]
    (.letOp (n := 81) (.out 0x1088f6 (movR64R64Effect 0x1088f6 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 82) (.exec 0x1088f6 (fun s => s.RIP = 0x1088f6) (movR64R64Effect 0x1088f6 11 7) (Reg.operands [.gpr 7] [])) #v[57]
    (.letOp (n := 83) (.out 0x1088f9 (movR32R32Effect 0x1088f9 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 84) (.exec 0x1088f9 (fun s => s.RIP = 0x1088f9) (movR32R32Effect 0x1088f9 2 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 85) (.out 0x1088fb (shrR64ClEffect 0x1088fb 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[81, 83]
    (.letOp (n := 86) (.exec 0x1088fb (fun s => s.RIP = 0x1088fb) (shrR64ClEffect 0x1088fb 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81, 83]
    (.letOp (n := 87) (.out 0x1088fe (movR32R32Effect 0x1088fe 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 88) (.exec 0x1088fe (fun s => s.RIP = 0x1088fe) (movR32R32Effect 0x1088fe 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 89) (.out 0x108900 (shlR64ClEffect 0x108900 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57, 87]
    (.letOp (n := 90) (.exec 0x108900 (fun s => s.RIP = 0x108900) (shlR64ClEffect 0x108900 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57, 87]
    (.letOp (n := 91) (.out 0x108903 (movR64R64Effect 0x108903 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 92) (.exec 0x108903 (fun s => s.RIP = 0x108903) (movR64R64Effect 0x108903 14 6) (Reg.operands [.gpr 6] [])) #v[55]
    (b_l1088c3_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1088c3 : List UInt8 :=
  [0x48, 0x8B, 0x14, 0x24, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B,
    0x44, 0x24, 0x18, 0x4C, 0x8B, 0x5C, 0x24, 0x20, 0x89, 0xC1, 0x49, 0xD3, 0xE3, 0x4D, 0x89, 0xC1,
    0x89, 0xE9, 0x49, 0xD3, 0xE9, 0x89, 0xC1, 0x49, 0xD3, 0xE0, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x28,
    0x4D, 0x09, 0xD9, 0x49, 0x89, 0xFB, 0x89, 0xE9, 0x49, 0xD3, 0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7,
    0x49, 0x89, 0xF6] ++ bytes_l1088c3_1

theorem code_l1088c3 : ∀ x ∈ codeRange 0x1088c3 bytes_l1088c3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x88c3 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1088c3_1

@[cfg_block] def b_l10893a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10893a (movR32Imm32Effect 0x10893a 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x10893a (fun s => s.RIP = 0x10893a) (movR32Imm32Effect 0x10893a 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10893f (movR64Imm32Effect 0x10893f 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x10893f (fun s => s.RIP = 0x10893f) (movR64Imm32Effect 0x10893f 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108946 (movR64Imm32Effect 0x108946 2 0x202b58) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108946 (fun s => s.RIP = 0x108946) (movR64Imm32Effect 0x108946 2 0x202b58) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10894d (callEffect (fun _ => 0x129560) 0x108952) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10894d (PushPre 0x10894d 5) (callEffect (fun _ => 0x129560) 0x108952) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108952⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l108952, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10893a : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x58,
    0x2B, 0x20, 0x00, 0xE8, 0x0E, 0x0C, 0x02, 0x00]

theorem code_l10893a : ∀ x ∈ codeRange 0x10893a bytes_l10893a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x893a 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108952 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108952 (movR32Imm32Effect 0x108952 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x108952 (fun s => s.RIP = 0x108952) (movR32Imm32Effect 0x108952 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108957 (movR64Imm32Effect 0x108957 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x108957 (fun s => s.RIP = 0x108957) (movR64Imm32Effect 0x108957 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10895e (movR64Imm32Effect 0x10895e 2 0x202b08) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x10895e (fun s => s.RIP = 0x10895e) (movR64Imm32Effect 0x10895e 2 0x202b08) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108965 (callEffect (fun _ => 0x129560) 0x10896a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108965 (PushPre 0x108965 5) (callEffect (fun _ => 0x129560) 0x10896a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10896a⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l10896a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108952 : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x08,
    0x2B, 0x20, 0x00, 0xE8, 0xF6, 0x0B, 0x02, 0x00]

theorem code_l108952 : ∀ x ∈ codeRange 0x108952 bytes_l108952, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8952 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10896a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10896a (movR32Imm32Effect 0x10896a 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10896a (fun s => s.RIP = 0x10896a) (movR32Imm32Effect 0x10896a 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10896f (movR32Imm32Effect 0x10896f 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x10896f (fun s => s.RIP = 0x10896f) (movR32Imm32Effect 0x10896f 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108974 (movR64Imm32Effect 0x108974 2 0x202b20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108974 (fun s => s.RIP = 0x108974) (movR64Imm32Effect 0x108974 2 0x202b20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10897b (callEffect (fun _ => 0x1295f2) 0x108980) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10897b (PushPre 0x10897b 5) (callEffect (fun _ => 0x1295f2) 0x108980) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108980⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l108980, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10896a : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20,
    0x00, 0xE8, 0x72, 0x0C, 0x02, 0x00]

theorem code_l10896a : ∀ x ∈ codeRange 0x10896a bytes_l10896a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x896a 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108980 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108980 (pushR64Effect 0x108980 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108980 (PushPre 0x108980 1) (pushR64Effect 0x108980 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108981 (pushR64Effect 0x108981 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x108981 (PushPre 0x108981 2) (pushR64Effect 0x108981 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x108983 (pushR64Effect 0x108983 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x108983 (PushPre 0x108983 2) (pushR64Effect 0x108983 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x108985 (pushR64Effect 0x108985 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108985 (PushPre 0x108985 2) (pushR64Effect 0x108985 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108987 (pushR64Effect 0x108987 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x108987 (PushPre 0x108987 2) (pushR64Effect 0x108987 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x108989 (pushR64Effect 0x108989 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x108989 (PushPre 0x108989 1) (pushR64Effect 0x108989 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10898a (subR64Imm8Effect 0x10898a 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10898a (fun s => s.RIP = 0x10898a) (subR64Imm8Effect 0x10898a 4 0x78) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10898e (movR32R32Effect 0x10898e 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[9]
    (.letOp (n := 68) (.exec 0x10898e (fun s => s.RIP = 0x10898e) (movR32R32Effect 0x10898e 3 5 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x108991 (movR64R64Effect 0x108991 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x108991 (fun s => s.RIP = 0x108991) (movR64R64Effect 0x108991 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x108994 (leaR64Effect 0x108994 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x108994 (fun s => s.RIP = 0x108994) (leaR64Effect 0x108994 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x108999 (callEffect (fun _ => 0x1084e0) 0x10899e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x108999 (PushPre 0x108999 5) (callEffect (fun _ => 0x1084e0) 0x10899e) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x10899e⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(1, 1), (2, 2), (3, 69), (4, 73), (5, 67), (6, 6), (7, 71), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l10899e, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l108980 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x78, 0x44, 0x89,
    0xCD, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0xE8, 0x42, 0xFB, 0xFF, 0xFF]

theorem code_l108980 : ∀ x ∈ codeRange 0x108980 bytes_l108980, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8980 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10899e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10899e (movR32Imm32Effect 0x10899e 5 1 0x40) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x10899e (fun s => s.RIP = 0x10899e) (movR32Imm32Effect 0x10899e 5 1 0x40) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x1089a3 (StorePre 0x1089a3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1089a3 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1089a3 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 56) (.out 0x1089a7 (subR32R32Effect 0x1089a7 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[53, 5]
    (.letOp (n := 57) (.exec 0x1089a7 (fun s => s.RIP = 0x1089a7) (subR32R32Effect 0x1089a7 2 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 58) (.out 0x1089a9 (cmpR32Imm8Effect 0x1089a9 3 1 0x40) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[56]
    (.letOp (n := 59) (.exec 0x1089a9 (fun s => s.RIP = 0x1089a9) (cmpR32Imm8Effect 0x1089a9 3 1 0x40) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 60) (.pure (condOp 3)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l108df9, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l1089b2, RegMap.args [(1, 56), (3, 3), (4, 4), (5, 5), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l10899e : List UInt8 :=
  [0xB9, 0x40, 0x00, 0x00, 0x00, 0x89, 0x6C, 0x24, 0x44, 0x29, 0xE9, 0x83, 0xF9, 0x40, 0x0F, 0x83,
    0x47, 0x04, 0x00, 0x00]

theorem code_l10899e : ∀ x ∈ codeRange 0x10899e bytes_l10899e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x899e 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1089b2_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x108b73 (movzxR32M8Effect 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 287) (.exec 0x108b73 (LoadPre 0x108b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b73 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b73 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 288) (.exec 0x108b78 (StorePre 0x108b78 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b78 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b78 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 289) (.out 0x108b7d (movzxR32M8Effect 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 290) (.exec 0x108b7d (LoadPre 0x108b7d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b7d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b7d 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 291) (.exec 0x108b83 (StorePre 0x108b83 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b83 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b83 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 292) (.out 0x108b88 (movzxR32M8Effect 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 293) (.exec 0x108b88 (LoadPre 0x108b88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b88 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108b88 6 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.exec 0x108b8e (StorePre 0x108b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b8e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b8e 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 295) (.out 0x108b93 (movzxR32M8Effect 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 296) (.exec 0x108b93 (LoadPre 0x108b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b93 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b93 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 297) (.exec 0x108b98 (StorePre 0x108b98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b98 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b98 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 298) (.out 0x108b9d (leaR64Effect 0x108b9d 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 299) (.exec 0x108b9d (fun s => s.RIP = 0x108b9d) (leaR64Effect 0x108b9d 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 300) (.out 0x108ba2 (atFlags (condHolds 5) (setccR8Effect 0x108ba2 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[298, 279]
    (.letOp (n := 301) (.exec 0x108ba2 (fun s => s.RIP = 0x108ba2) (atFlags (condHolds 5) (setccR8Effect 0x108ba2 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[298, 279]
    (.letOp (n := 302) (.out 0x108ba6 (cmpMImm8Effect 0x108ba6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (EffectPart.reads (.flag .CF) [.gpr 4] []) (.flag .CF)) #v[4]
    (.letOp (n := 303) (.exec 0x108ba6 (LoadPre 0x108ba6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108ba6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108ba6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 304) (.pure (condOp 3)) #v[302]
    (.terminate (.condBr (Fin.last 304) ⟨.l108df9, RegMap.args [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)] 305⟩ ⟨.l108bb1, RegMap.args [(0, 247), (1, 1), (2, 286), (3, 260), (4, 4), (5, 270), (6, 282), (7, 295), (8, 265), (9, 300), (10, 273), (11, 183), (12, 156), (13, 210), (14, 292), (15, 289), (16, 302), (22, 22), (39, 39), (50, 50), (51, 51)] 305⟩))))))))))))))))))))

def bytes_l1089b2_6 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10,
    0x0F, 0x95, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10,
    0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x4C, 0x8D, 0x4C, 0x24, 0x10, 0x41,
    0x0F, 0x95, 0xC1, 0x83, 0x7C, 0x24, 0x44, 0x40, 0x0F, 0x83, 0x48, 0x02, 0x00, 0x00]

theorem code_l1089b2_6 : ∀ x ∈ codeRange 0x108b73 bytes_l1089b2_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8b73 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1089b2_5 : Block Op Label signature Reg.count 249 :=
  .letOp (n := 249) (.out 0x108b1f (andR64R64Effect 0x108b1f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[243, 247]
    (.letOp (n := 250) (.exec 0x108b1f (fun s => s.RIP = 0x108b1f) (andR64R64Effect 0x108b1f 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[243, 247]
    (.letOp (n := 251) (.out 0x108b22 (orR64R64Effect 0x108b22 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[249, 241]
    (.letOp (n := 252) (.exec 0x108b22 (fun s => s.RIP = 0x108b22) (orR64R64Effect 0x108b22 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[249, 241]
    (.letOp (n := 253) (.out 0x108b25 (shrR64Effect 0x108b25 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[251]
    (.letOp (n := 254) (.exec 0x108b25 (fun s => s.RIP = 0x108b25) (shrR64Effect 0x108b25 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[251]
    (.letOp (n := 255) (.exec 0x108b29 (StorePre 0x108b29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b29 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[253, 4]
    (.letOp (n := 256) (.exec 0x108b2e (fun s => s.RIP = 0x108b2e) (leaR64Effect 0x108b2e 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 257) (.exec 0x108b33 (StorePre 0x108b33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108b33 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108b33 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[123, 4]
    (.letOp (n := 258) (.out 0x108b38 (movR64R64Effect 0x108b38 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 259) (.exec 0x108b38 (fun s => s.RIP = 0x108b38) (movR64R64Effect 0x108b38 3 5) (Reg.operands [.gpr 5] [])) #v[123]
    (.letOp (n := 260) (.out 0x108b3b (negR64Effect 0x108b3b 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[258]
    (.letOp (n := 261) (.out 0x108b3b (negR64Effect 0x108b3b 3) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[258]
    (.letOp (n := 262) (.exec 0x108b3b (fun s => s.RIP = 0x108b3b) (negR64Effect 0x108b3b 3) (Reg.operands [.gpr 3] [])) #v[258]
    (.letOp (n := 263) (.out 0x108b3e (movR32Imm32Effect 0x108b3e 6 8 0x0) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 264) (.exec 0x108b3e (fun s => s.RIP = 0x108b3e) (movR32Imm32Effect 0x108b3e 6 8 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 265) (.out 0x108b44 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[263, 156, 261]
    (.letOp (n := 266) (.out 0x108b44 (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[263, 156, 261]
    (.letOp (n := 267) (.exec 0x108b44 (fun s => s.RIP = 0x108b44) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b44 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[263, 156, 261]
    (.letOp (n := 268) (.out 0x108b47 (movR32Imm32Effect 0x108b47 5 5 0x0) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 269) (.exec 0x108b47 (fun s => s.RIP = 0x108b47) (movR32Imm32Effect 0x108b47 5 5 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 270) (.out 0x108b4c (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[268, 183, 266]
    (.letOp (n := 271) (.out 0x108b4c (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[268, 183, 266]
    (.letOp (n := 272) (.exec 0x108b4c (fun s => s.RIP = 0x108b4c) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4c 5 11)) (Reg.operands [.gpr 5, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[268, 183, 266]
    (.letOp (n := 273) (.out 0x108b4f (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[220, 210, 271]
    (.letOp (n := 274) (.out 0x108b4f (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[220, 210, 271]
    (.letOp (n := 275) (.exec 0x108b4f (fun s => s.RIP = 0x108b4f) (atFlags StatusFlags.CF (sbbR64R64Effect 0x108b4f 10 13)) (Reg.operands [.gpr 10, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[220, 210, 271]
    (.letOp (n := 276) (.out 0x108b52 (movR64M64Effect 0x108b52 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 277) (.exec 0x108b52 (LoadPre 0x108b52 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b52 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108b52 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 278) (.exec 0x108b57 (StorePre 0x108b57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b57 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 3) (setccM8Effect 0x108b57 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 274]
    (.letOp (n := 279) (.out 0x108b5c (testR64R64Effect 0x108b5c 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[276, 276]
    (.letOp (n := 280) (.exec 0x108b5c (fun s => s.RIP = 0x108b5c) (testR64R64Effect 0x108b5c 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[276, 276]
    (.letOp (n := 281) (.exec 0x108b5f (fun s => s.RIP = 0x108b5f) (leaR64Effect 0x108b5f 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 282) (.out 0x108b64 (movzxR32M8Effect 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 283) (.exec 0x108b64 (LoadPre 0x108b64 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b64 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108b64 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.exec 0x108b69 (StorePre 0x108b69 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b69 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 5) (setccM8Effect 0x108b69 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 279]
    (.letOp (n := 285) (.exec 0x108b6e (fun s => s.RIP = 0x108b6e) (leaR64Effect 0x108b6e 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1089b2_6)))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_5 : List UInt8 :=
  [0x49, 0x21, 0xC6, 0x49, 0x09, 0xFE, 0x49, 0xC1, 0xEE, 0x3F, 0x4C, 0x89, 0x74, 0x24, 0x10, 0x48,
    0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0x6C, 0x24, 0x48, 0x48, 0x89, 0xEB, 0x48, 0xF7, 0xDB, 0x41,
    0xB8, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x19, 0xE0, 0xBD, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x19, 0xDD,
    0x4D, 0x19, 0xEA, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x0F, 0x93, 0x44, 0x24, 0x10, 0x48, 0x85, 0xD2,
    0x48, 0x8D, 0x54, 0x24, 0x10, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x0F, 0x95, 0x44, 0x24, 0x10, 0x48,
    0x8D, 0x7C, 0x24, 0x10] ++ bytes_l1089b2_6

theorem code_l1089b2_5 : ∀ x ∈ codeRange 0x108b1f bytes_l1089b2_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8b1f 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_6

@[cfg_block] def b_l1089b2_4 : Block Op Label signature Reg.count 210 :=
  .letOp (n := 210) (.out 0x108ade (addR64R64Effect 0x108ade 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[208, 206]
    (.letOp (n := 211) (.exec 0x108ade (fun s => s.RIP = 0x108ade) (addR64R64Effect 0x108ade 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[208, 206]
    (.letOp (n := 212) (.out 0x108ae1 (notR64Effect 0x108ae1 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[111]
    (.letOp (n := 213) (.exec 0x108ae1 (fun s => s.RIP = 0x108ae1) (notR64Effect 0x108ae1 7) (Reg.operands [.gpr 7] [])) #v[111]
    (.letOp (n := 214) (.out 0x108ae4 (movR64R64Effect 0x108ae4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[116]
    (.letOp (n := 215) (.exec 0x108ae4 (fun s => s.RIP = 0x108ae4) (movR64R64Effect 0x108ae4 8 0) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 216) (.out 0x108ae7 (andR64R64Effect 0x108ae7 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[214, 212]
    (.letOp (n := 217) (.exec 0x108ae7 (fun s => s.RIP = 0x108ae7) (andR64R64Effect 0x108ae7 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[214, 212]
    (.letOp (n := 218) (.out 0x108aea (orR64R64Effect 0x108aea 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[212, 116]
    (.letOp (n := 219) (.exec 0x108aea (fun s => s.RIP = 0x108aea) (orR64R64Effect 0x108aea 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[212, 116]
    (.letOp (n := 220) (.out 0x108aed (xorR32R32Effect 0x108aed 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[113, 113]
    (.letOp (n := 221) (.exec 0x108aed (fun s => s.RIP = 0x108aed) (xorR32R32Effect 0x108aed 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[113, 113]
    (.letOp (n := 222) (.out 0x108af0 (andR64R64Effect 0x108af0 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[218, 210]
    (.letOp (n := 223) (.exec 0x108af0 (fun s => s.RIP = 0x108af0) (andR64R64Effect 0x108af0 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[218, 210]
    (.letOp (n := 224) (.out 0x108af3 (orR64R64Effect 0x108af3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[222, 216]
    (.letOp (n := 225) (.exec 0x108af3 (fun s => s.RIP = 0x108af3) (orR64R64Effect 0x108af3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[222, 216]
    (.letOp (n := 226) (.out 0x108af6 (shrR64Effect 0x108af6 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[224]
    (.letOp (n := 227) (.exec 0x108af6 (fun s => s.RIP = 0x108af6) (shrR64Effect 0x108af6 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[224]
    (.letOp (n := 228) (.exec 0x108afa (StorePre 0x108afa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108afa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108afa 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[226, 4]
    (.letOp (n := 229) (.out 0x108aff (xorR32R32Effect 0x108aff 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[116, 116]
    (.letOp (n := 230) (.exec 0x108aff (fun s => s.RIP = 0x108aff) (xorR32R32Effect 0x108aff 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[116, 116]
    (.letOp (n := 231) (.out 0x108b01 (subR64M64Effect 0x108b01 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[229, 4]
    (.letOp (n := 232) (.exec 0x108b01 (LoadPre 0x108b01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108b01 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108b01 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[229, 4]
    (.letOp (n := 233) (.out 0x108b06 (movR64R64Effect 0x108b06 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[133]
    (.letOp (n := 234) (.exec 0x108b06 (fun s => s.RIP = 0x108b06) (movR64R64Effect 0x108b06 6 14) (Reg.operands [.gpr 14] [])) #v[133]
    (.letOp (n := 235) (.out 0x108b09 (subR64R64Effect 0x108b09 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[233, 119]
    (.letOp (n := 236) (.exec 0x108b09 (fun s => s.RIP = 0x108b09) (subR64R64Effect 0x108b09 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[233, 119]
    (.letOp (n := 237) (.out 0x108b0c (notR64Effect 0x108b0c 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[133]
    (.letOp (n := 238) (.exec 0x108b0c (fun s => s.RIP = 0x108b0c) (notR64Effect 0x108b0c 14) (Reg.operands [.gpr 14] [])) #v[133]
    (.letOp (n := 239) (.out 0x108b0f (movR64R64Effect 0x108b0f 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 240) (.exec 0x108b0f (fun s => s.RIP = 0x108b0f) (movR64R64Effect 0x108b0f 7 2) (Reg.operands [.gpr 2] [])) #v[119]
    (.letOp (n := 241) (.out 0x108b12 (andR64R64Effect 0x108b12 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[239, 237]
    (.letOp (n := 242) (.exec 0x108b12 (fun s => s.RIP = 0x108b12) (andR64R64Effect 0x108b12 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[239, 237]
    (.letOp (n := 243) (.out 0x108b15 (orR64R64Effect 0x108b15 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[237, 119]
    (.letOp (n := 244) (.exec 0x108b15 (fun s => s.RIP = 0x108b15) (orR64R64Effect 0x108b15 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[237, 119]
    (.letOp (n := 245) (.out 0x108b18 (sarR64Effect 0x108b18 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[231]
    (.letOp (n := 246) (.exec 0x108b18 (fun s => s.RIP = 0x108b18) (sarR64Effect 0x108b18 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[231]
    (.letOp (n := 247) (.out 0x108b1c (addR64R64Effect 0x108b1c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[245, 235]
    (.letOp (n := 248) (.exec 0x108b1c (fun s => s.RIP = 0x108b1c) (addR64R64Effect 0x108b1c 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[245, 235]
    (b_l1089b2_5)))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_4 : List UInt8 :=
  [0x4D, 0x01, 0xC5, 0x48, 0xF7, 0xD7, 0x49, 0x89, 0xC0, 0x49, 0x21, 0xF8, 0x48, 0x09, 0xC7, 0x45,
    0x31, 0xD2, 0x4C, 0x21, 0xEF, 0x4C, 0x09, 0xC7, 0x48, 0xC1, 0xEF, 0x3F, 0x48, 0x89, 0x7C, 0x24,
    0x10, 0x31, 0xC0, 0x48, 0x2B, 0x44, 0x24, 0x10, 0x4C, 0x89, 0xF6, 0x48, 0x29, 0xD6, 0x49, 0xF7,
    0xD6, 0x48, 0x89, 0xD7, 0x4C, 0x21, 0xF7, 0x49, 0x09, 0xD6, 0x48, 0xC1, 0xF8, 0x3F, 0x48, 0x01,
    0xF0] ++ bytes_l1089b2_5

theorem code_l1089b2_4 : ∀ x ∈ codeRange 0x108ade bytes_l1089b2_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8ade 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_5

@[cfg_block] def b_l1089b2_3 : Block Op Label signature Reg.count 172 :=
  .letOp (n := 172) (.exec 0x108a97 (StorePre 0x108a97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a97 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a97 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 173) (.out 0x108a9c (xorR32R32Effect 0x108a9c 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[108, 108]
    (.letOp (n := 174) (.exec 0x108a9c (fun s => s.RIP = 0x108a9c) (xorR32R32Effect 0x108a9c 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[108, 108]
    (.letOp (n := 175) (.out 0x108a9f (subR64M64Effect 0x108a9f 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[173, 4]
    (.letOp (n := 176) (.exec 0x108a9f (LoadPre 0x108a9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a9f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a9f 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[173, 4]
    (.letOp (n := 177) (.out 0x108aa4 (movR64R64Effect 0x108aa4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[68]
    (.letOp (n := 178) (.exec 0x108aa4 (fun s => s.RIP = 0x108aa4) (movR64R64Effect 0x108aa4 8 3) (Reg.operands [.gpr 3] [])) #v[68]
    (.letOp (n := 179) (.out 0x108aa7 (subR64R64Effect 0x108aa7 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[177, 113]
    (.letOp (n := 180) (.exec 0x108aa7 (fun s => s.RIP = 0x108aa7) (subR64R64Effect 0x108aa7 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[177, 113]
    (.letOp (n := 181) (.out 0x108aaa (sarR64Effect 0x108aaa 4 11 63) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[175]
    (.letOp (n := 182) (.exec 0x108aaa (fun s => s.RIP = 0x108aaa) (sarR64Effect 0x108aaa 4 11 63) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 183) (.out 0x108aae (addR64R64Effect 0x108aae 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[181, 179]
    (.letOp (n := 184) (.exec 0x108aae (fun s => s.RIP = 0x108aae) (addR64R64Effect 0x108aae 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[181, 179]
    (.letOp (n := 185) (.out 0x108ab1 (notR64Effect 0x108ab1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 186) (.exec 0x108ab1 (fun s => s.RIP = 0x108ab1) (notR64Effect 0x108ab1 3) (Reg.operands [.gpr 3] [])) #v[68]
    (.letOp (n := 187) (.out 0x108ab4 (movR64R64Effect 0x108ab4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[113]
    (.letOp (n := 188) (.exec 0x108ab4 (fun s => s.RIP = 0x108ab4) (movR64R64Effect 0x108ab4 8 10) (Reg.operands [.gpr 10] [])) #v[113]
    (.letOp (n := 189) (.out 0x108ab7 (andR64R64Effect 0x108ab7 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[187, 185]
    (.letOp (n := 190) (.exec 0x108ab7 (fun s => s.RIP = 0x108ab7) (andR64R64Effect 0x108ab7 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[187, 185]
    (.letOp (n := 191) (.out 0x108aba (orR64R64Effect 0x108aba 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[185, 113]
    (.letOp (n := 192) (.exec 0x108aba (fun s => s.RIP = 0x108aba) (orR64R64Effect 0x108aba 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[185, 113]
    (.letOp (n := 193) (.out 0x108abd (andR64R64Effect 0x108abd 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[191, 183]
    (.letOp (n := 194) (.exec 0x108abd (fun s => s.RIP = 0x108abd) (andR64R64Effect 0x108abd 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[191, 183]
    (.letOp (n := 195) (.out 0x108ac0 (orR64R64Effect 0x108ac0 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[193, 189]
    (.letOp (n := 196) (.exec 0x108ac0 (fun s => s.RIP = 0x108ac0) (orR64R64Effect 0x108ac0 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[193, 189]
    (.letOp (n := 197) (.out 0x108ac3 (shrR64Effect 0x108ac3 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[195]
    (.letOp (n := 198) (.exec 0x108ac3 (fun s => s.RIP = 0x108ac3) (shrR64Effect 0x108ac3 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.exec 0x108ac7 (StorePre 0x108ac7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108ac7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108ac7 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[197, 4]
    (.letOp (n := 200) (.out 0x108acc (xorR32R32Effect 0x108acc 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[100, 100]
    (.letOp (n := 201) (.exec 0x108acc (fun s => s.RIP = 0x108acc) (xorR32R32Effect 0x108acc 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[100, 100]
    (.letOp (n := 202) (.out 0x108acf (subR64M64Effect 0x108acf 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[200, 4]
    (.letOp (n := 203) (.exec 0x108acf (LoadPre 0x108acf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108acf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108acf 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[200, 4]
    (.letOp (n := 204) (.out 0x108ad4 (movR64R64Effect 0x108ad4 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 205) (.exec 0x108ad4 (fun s => s.RIP = 0x108ad4) (movR64R64Effect 0x108ad4 8 7) (Reg.operands [.gpr 7] [])) #v[111]
    (.letOp (n := 206) (.out 0x108ad7 (subR64R64Effect 0x108ad7 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[204, 116]
    (.letOp (n := 207) (.exec 0x108ad7 (fun s => s.RIP = 0x108ad7) (subR64R64Effect 0x108ad7 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[204, 116]
    (.letOp (n := 208) (.out 0x108ada (sarR64Effect 0x108ada 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[202]
    (.letOp (n := 209) (.exec 0x108ada (fun s => s.RIP = 0x108ada) (sarR64Effect 0x108ada 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[202]
    (b_l1089b2_4))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_3 : List UInt8 :=
  [0x4C, 0x89, 0x44, 0x24, 0x10, 0x45, 0x31, 0xDB, 0x4C, 0x2B, 0x5C, 0x24, 0x10, 0x49, 0x89, 0xD8,
    0x4D, 0x29, 0xD0, 0x49, 0xC1, 0xFB, 0x3F, 0x4D, 0x01, 0xC3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD0,
    0x49, 0x21, 0xD8, 0x4C, 0x09, 0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xC3, 0x48, 0xC1, 0xEB, 0x3F,
    0x48, 0x89, 0x5C, 0x24, 0x10, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x6C, 0x24, 0x10, 0x49, 0x89, 0xF8,
    0x49, 0x29, 0xC0, 0x49, 0xC1, 0xFD, 0x3F] ++ bytes_l1089b2_4

theorem code_l1089b2_3 : ∀ x ∈ codeRange 0x108a97 bytes_l1089b2_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a97 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_4

@[cfg_block] def b_l1089b2_2 : Block Op Label signature Reg.count 135 :=
  .letOp (n := 135) (.out 0x108a4d (andR64R64Effect 0x108a4d 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[131, 123]
    (.letOp (n := 136) (.exec 0x108a4d (fun s => s.RIP = 0x108a4d) (andR64R64Effect 0x108a4d 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[131, 123]
    (.letOp (n := 137) (.out 0x108a50 (orR64R64Effect 0x108a50 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[135, 129]
    (.letOp (n := 138) (.exec 0x108a50 (fun s => s.RIP = 0x108a50) (orR64R64Effect 0x108a50 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[135, 129]
    (.letOp (n := 139) (.out 0x108a53 (movzxR32M8Effect 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 140) (.exec 0x108a53 (LoadPre 0x108a53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x108a53 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108a53 6 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 141) (.exec 0x108a59 (StorePre 0x108a59 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108a59 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108a59 5 9 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[139, 4]
    (.letOp (n := 142) (.out 0x108a5e (shrR64Effect 0x108a5e 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[137]
    (.letOp (n := 143) (.exec 0x108a5e (fun s => s.RIP = 0x108a5e) (shrR64Effect 0x108a5e 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 144) (.exec 0x108a62 (StorePre 0x108a62 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a62 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a62 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[142, 4]
    (.letOp (n := 145) (.exec 0x108a67 (fun s => s.RIP = 0x108a67) (leaR64Effect 0x108a67 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 146) (.out 0x108a6c (xorR32R32Effect 0x108a6c 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[90, 90]
    (.letOp (n := 147) (.exec 0x108a6c (fun s => s.RIP = 0x108a6c) (xorR32R32Effect 0x108a6c 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[90, 90]
    (.letOp (n := 148) (.out 0x108a6f (subR64M64Effect 0x108a6f 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[146, 4]
    (.letOp (n := 149) (.exec 0x108a6f (LoadPre 0x108a6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108a6f + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108a6f 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[146, 4]
    (.letOp (n := 150) (.out 0x108a74 (movR64R64Effect 0x108a74 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[66]
    (.letOp (n := 151) (.exec 0x108a74 (fun s => s.RIP = 0x108a74) (movR64R64Effect 0x108a74 15 8) (Reg.operands [.gpr 8] [])) #v[66]
    (.letOp (n := 152) (.out 0x108a77 (subR64R64Effect 0x108a77 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[150, 108]
    (.letOp (n := 153) (.exec 0x108a77 (fun s => s.RIP = 0x108a77) (subR64R64Effect 0x108a77 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[150, 108]
    (.letOp (n := 154) (.out 0x108a7a (sarR64Effect 0x108a7a 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[148]
    (.letOp (n := 155) (.exec 0x108a7a (fun s => s.RIP = 0x108a7a) (sarR64Effect 0x108a7a 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148]
    (.letOp (n := 156) (.out 0x108a7e (addR64R64Effect 0x108a7e 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[154, 152]
    (.letOp (n := 157) (.exec 0x108a7e (fun s => s.RIP = 0x108a7e) (addR64R64Effect 0x108a7e 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[154, 152]
    (.letOp (n := 158) (.out 0x108a81 (notR64Effect 0x108a81 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[66]
    (.letOp (n := 159) (.exec 0x108a81 (fun s => s.RIP = 0x108a81) (notR64Effect 0x108a81 8) (Reg.operands [.gpr 8] [])) #v[66]
    (.letOp (n := 160) (.out 0x108a84 (movR64R64Effect 0x108a84 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[108]
    (.letOp (n := 161) (.exec 0x108a84 (fun s => s.RIP = 0x108a84) (movR64R64Effect 0x108a84 15 11) (Reg.operands [.gpr 11] [])) #v[108]
    (.letOp (n := 162) (.out 0x108a87 (andR64R64Effect 0x108a87 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[160, 158]
    (.letOp (n := 163) (.exec 0x108a87 (fun s => s.RIP = 0x108a87) (andR64R64Effect 0x108a87 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[160, 158]
    (.letOp (n := 164) (.out 0x108a8a (orR64R64Effect 0x108a8a 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[158, 108]
    (.letOp (n := 165) (.exec 0x108a8a (fun s => s.RIP = 0x108a8a) (orR64R64Effect 0x108a8a 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[158, 108]
    (.letOp (n := 166) (.out 0x108a8d (andR64R64Effect 0x108a8d 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[164, 156]
    (.letOp (n := 167) (.exec 0x108a8d (fun s => s.RIP = 0x108a8d) (andR64R64Effect 0x108a8d 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[164, 156]
    (.letOp (n := 168) (.out 0x108a90 (orR64R64Effect 0x108a90 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[166, 162]
    (.letOp (n := 169) (.exec 0x108a90 (fun s => s.RIP = 0x108a90) (orR64R64Effect 0x108a90 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[166, 162]
    (.letOp (n := 170) (.out 0x108a93 (shrR64Effect 0x108a93 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[168]
    (.letOp (n := 171) (.exec 0x108a93 (fun s => s.RIP = 0x108a93) (shrR64Effect 0x108a93 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[168]
    (b_l1089b2_3)))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_2 : List UInt8 :=
  [0x48, 0x21, 0xEE, 0x4C, 0x09, 0xFE, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x38, 0x44, 0x88, 0x4C, 0x24,
    0x0F, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x10, 0x48, 0x8D, 0x74, 0x24, 0x10, 0x45,
    0x31, 0xE4, 0x4C, 0x2B, 0x64, 0x24, 0x10, 0x4D, 0x89, 0xC7, 0x4D, 0x29, 0xDF, 0x49, 0xC1, 0xFC,
    0x3F, 0x4D, 0x01, 0xFC, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xDF, 0x4D, 0x21, 0xC7, 0x4D, 0x09, 0xD8,
    0x4D, 0x21, 0xE0, 0x4D, 0x09, 0xF8, 0x49, 0xC1, 0xE8, 0x3F] ++ bytes_l1089b2_3

theorem code_l1089b2_2 : ∀ x ∈ codeRange 0x108a4d bytes_l1089b2_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a4d 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_3

@[cfg_block] def b_l1089b2_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x108a06 (movR64M64Effect 0x108a06 0 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 93) (.exec 0x108a06 (LoadPre 0x108a06 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x108a06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a06 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 94) (.exec 0x108a0a (StorePre 0x108a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a0a 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (.letOp (n := 95) (.out 0x108a0f (mulR64Effect 0x108a0f 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 92]
    (.letOp (n := 96) (.out 0x108a0f (mulR64Effect 0x108a0f 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 92]
    (.letOp (n := 97) (.exec 0x108a0f (fun s => s.RIP = 0x108a0f) (mulR64Effect 0x108a0f 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 92]
    (.letOp (n := 98) (.out 0x108a12 (movR64R64Effect 0x108a12 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[95]
    (.letOp (n := 99) (.exec 0x108a12 (fun s => s.RIP = 0x108a12) (movR64R64Effect 0x108a12 10 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 100) (.out 0x108a15 (movR64R64Effect 0x108a15 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[96]
    (.letOp (n := 101) (.exec 0x108a15 (fun s => s.RIP = 0x108a15) (movR64R64Effect 0x108a15 13 2) (Reg.operands [.gpr 2] [])) #v[96]
    (.letOp (n := 102) (.out 0x108a18 (movR64M64Effect 0x108a18 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 103) (.exec 0x108a18 (LoadPre 0x108a18 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x108a18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108a18 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 104) (.exec 0x108a1c (StorePre 0x108a1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108a1c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108a1c 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x108a21 (mulR64Effect 0x108a21 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 102]
    (.letOp (n := 106) (.out 0x108a21 (mulR64Effect 0x108a21 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 102]
    (.letOp (n := 107) (.exec 0x108a21 (fun s => s.RIP = 0x108a21) (mulR64Effect 0x108a21 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 102]
    (.letOp (n := 108) (.out 0x108a24 (addR64R64Effect 0x108a24 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[88, 78]
    (.letOp (n := 109) (.out 0x108a24 (addR64R64Effect 0x108a24 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[88, 78]
    (.letOp (n := 110) (.exec 0x108a24 (fun s => s.RIP = 0x108a24) (addR64R64Effect 0x108a24 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[88, 78]
    (.letOp (n := 111) (.out 0x108a27 (movR64M64Effect 0x108a27 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 112) (.exec 0x108a27 (LoadPre 0x108a27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x108a27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a27 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x108a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[98, 90, 109]
    (.letOp (n := 114) (.out 0x108a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[98, 90, 109]
    (.letOp (n := 115) (.exec 0x108a2c (fun s => s.RIP = 0x108a2c) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2c 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 90, 109]
    (.letOp (n := 116) (.out 0x108a2f (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[105, 100, 114]
    (.letOp (n := 117) (.out 0x108a2f (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[105, 100, 114]
    (.letOp (n := 118) (.exec 0x108a2f (fun s => s.RIP = 0x108a2f) (atFlags StatusFlags.CF (adcR64R64Effect 0x108a2f 0 13)) (Reg.operands [.gpr 0, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[105, 100, 114]
    (.letOp (n := 119) (.out 0x108a32 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x108a32 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[106, 117]
    (.letOp (n := 120) (.exec 0x108a32 (fun s => s.RIP = 0x108a32) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x108a32 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[106, 117]
    (.letOp (n := 121) (.out 0x108a36 (movR64R64Effect 0x108a36 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 122) (.exec 0x108a36 (fun s => s.RIP = 0x108a36) (movR64R64Effect 0x108a36 5 6) (Reg.operands [.gpr 6] [])) #v[56]
    (.letOp (n := 123) (.out 0x108a39 (subR64R64Effect 0x108a39 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[121, 80]
    (.letOp (n := 124) (.exec 0x108a39 (fun s => s.RIP = 0x108a39) (subR64R64Effect 0x108a39 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[121, 80]
    (.letOp (n := 125) (.out 0x108a3c (notR64Effect 0x108a3c 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[56]
    (.letOp (n := 126) (.exec 0x108a3c (fun s => s.RIP = 0x108a3c) (notR64Effect 0x108a3c 6) (Reg.operands [.gpr 6] [])) #v[56]
    (.letOp (n := 127) (.out 0x108a3f (movR64R64Effect 0x108a3f 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[80]
    (.letOp (n := 128) (.exec 0x108a3f (fun s => s.RIP = 0x108a3f) (movR64R64Effect 0x108a3f 15 14) (Reg.operands [.gpr 14] [])) #v[80]
    (.letOp (n := 129) (.out 0x108a42 (andR64R64Effect 0x108a42 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[127, 125]
    (.letOp (n := 130) (.exec 0x108a42 (fun s => s.RIP = 0x108a42) (andR64R64Effect 0x108a42 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[127, 125]
    (.letOp (n := 131) (.out 0x108a45 (orR64R64Effect 0x108a45 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[125, 80]
    (.letOp (n := 132) (.exec 0x108a45 (fun s => s.RIP = 0x108a45) (orR64R64Effect 0x108a45 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[125, 80]
    (.letOp (n := 133) (.out 0x108a48 (movR64M64Effect 0x108a48 14 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 134) (.exec 0x108a48 (LoadPre 0x108a48 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x108a48 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108a48 14 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1089b2_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2_1 : List UInt8 :=
  [0x48, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x44, 0x24, 0x60, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xC2, 0x49,
    0x89, 0xD5, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x89, 0x44, 0x24, 0x68, 0x49, 0xF7, 0xE1, 0x4D, 0x01,
    0xFB, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x4D, 0x11, 0xE2, 0x4C, 0x11, 0xE8, 0x48, 0x83, 0xD2, 0x00,
    0x48, 0x89, 0xF5, 0x4C, 0x29, 0xF5, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xF7, 0x49, 0x21, 0xF7, 0x4C,
    0x09, 0xF6, 0x4C, 0x8B, 0x74, 0x24, 0x30] ++ bytes_l1089b2_2

theorem code_l1089b2_1 : ∀ x ∈ codeRange 0x108a06 bytes_l1089b2_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8a06 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_2

@[cfg_block] def b_l1089b2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1089b2 (StorePre 0x1089b2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1089b2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089b2 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 54) (.out 0x1089b7 (movR64M64Effect 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1089b7 (LoadPre 0x1089b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1089b7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089b7 7 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1089bf (movR64M64Effect 0x1089bf 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x1089bf (LoadPre 0x1089bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1089bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089bf 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1089c4 (movR64M64Effect 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 59) (.exec 0x1089c4 (LoadPre 0x1089c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1089c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1089c4 9 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1089cc (imulR64R64Effect 0x1089cc 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[58, 56]
    (.letOp (n := 61) (.exec 0x1089cc (fun s => s.RIP = 0x1089cc) (imulR64R64Effect 0x1089cc 4 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[58, 56]
    (.letOp (n := 62) (.out 0x1089d0 (shlR64ClEffect 0x1089d0 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[60, 1]
    (.letOp (n := 63) (.exec 0x1089d0 (fun s => s.RIP = 0x1089d0) (shlR64ClEffect 0x1089d0 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60, 1]
    (.letOp (n := 64) (.out 0x1089d3 (shrR64ClEffect 0x1089d3 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[62, 1]
    (.letOp (n := 65) (.exec 0x1089d3 (fun s => s.RIP = 0x1089d3) (shrR64ClEffect 0x1089d3 3 9) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62, 1]
    (.letOp (n := 66) (.out 0x1089d6 (movR64M64Effect 0x1089d6 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 67) (.exec 0x1089d6 (LoadPre 0x1089d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1089d6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089d6 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x1089db (movR64M64Effect 0x1089db 3 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 69) (.exec 0x1089db (LoadPre 0x1089db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1089db + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1089db 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x1089e0 (movR64M64Effect 0x1089e0 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[54]
    (.letOp (n := 71) (.exec 0x1089e0 (LoadPre 0x1089e0 (fun s => AddrMode.addr (.base 7 .none) s (0x1089e0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1089e0 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 72) (.out 0x1089e3 (movR64M64Effect 0x1089e3 10 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[54]
    (.letOp (n := 73) (.exec 0x1089e3 (LoadPre 0x1089e3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1089e3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1089e3 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[54]
    (.letOp (n := 74) (.exec 0x1089e7 (StorePre 0x1089e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1089e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089e7 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 75) (.out 0x1089ec (mulR64Effect 0x1089ec 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 70]
    (.letOp (n := 76) (.out 0x1089ec (mulR64Effect 0x1089ec 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 70]
    (.letOp (n := 77) (.exec 0x1089ec (fun s => s.RIP = 0x1089ec) (mulR64Effect 0x1089ec 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 70]
    (.letOp (n := 78) (.out 0x1089ef (movR64R64Effect 0x1089ef 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[76]
    (.letOp (n := 79) (.exec 0x1089ef (fun s => s.RIP = 0x1089ef) (movR64R64Effect 0x1089ef 15 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 80) (.out 0x1089f2 (movR64R64Effect 0x1089f2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[75]
    (.letOp (n := 81) (.exec 0x1089f2 (fun s => s.RIP = 0x1089f2) (movR64R64Effect 0x1089f2 14 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 82) (.exec 0x1089f5 (StorePre 0x1089f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1089f5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1089f5 10 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 83) (.out 0x1089fa (movR64R64Effect 0x1089fa 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[72]
    (.letOp (n := 84) (.exec 0x1089fa (fun s => s.RIP = 0x1089fa) (movR64R64Effect 0x1089fa 0 10) (Reg.operands [.gpr 10] [])) #v[72]
    (.letOp (n := 85) (.out 0x1089fd (mulR64Effect 0x1089fd 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[64, 83]
    (.letOp (n := 86) (.out 0x1089fd (mulR64Effect 0x1089fd 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[64, 83]
    (.letOp (n := 87) (.exec 0x1089fd (fun s => s.RIP = 0x1089fd) (mulR64Effect 0x1089fd 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[64, 83]
    (.letOp (n := 88) (.out 0x108a00 (movR64R64Effect 0x108a00 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[85]
    (.letOp (n := 89) (.exec 0x108a00 (fun s => s.RIP = 0x108a00) (movR64R64Effect 0x108a00 11 0) (Reg.operands [.gpr 0] [])) #v[85]
    (.letOp (n := 90) (.out 0x108a03 (movR64R64Effect 0x108a03 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[86]
    (.letOp (n := 91) (.exec 0x108a03 (fun s => s.RIP = 0x108a03) (movR64R64Effect 0x108a03 12 2) (Reg.operands [.gpr 2] [])) #v[86]
    (b_l1089b2_1)))))))))))))))))))))))))))))))))))))))

def bytes_l1089b2 : List UInt8 :=
  [0x48, 0x89, 0x5C, 0x24, 0x70, 0x48, 0x8B, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74,
    0x24, 0x10, 0x4C, 0x8B, 0x8C, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0xAF, 0xCE, 0x49, 0xD3,
    0xE1, 0x49, 0xD3, 0xE9, 0x4C, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x5C, 0x24, 0x20, 0x48, 0x8B,
    0x07, 0x4C, 0x8B, 0x57, 0x08, 0x48, 0x89, 0x44, 0x24, 0x50, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD7,
    0x49, 0x89, 0xC6, 0x4C, 0x89, 0x54, 0x24, 0x58, 0x4C, 0x89, 0xD0, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xC3, 0x49, 0x89, 0xD4] ++ bytes_l1089b2_1

theorem code_l1089b2 : ∀ x ∈ codeRange 0x1089b2 bytes_l1089b2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x89b2 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1089b2_1

@[cfg_block] def b_l108bb1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x108bb1 (StorePre 0x108bb1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108bb1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x108bb1 5 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x108bb6 (cmpMImm8Effect 0x108bb6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 55) (.exec 0x108bb6 (LoadPre 0x108bb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108bb6 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x108bb6 5 32 (.sib 4 none 0 (.d8 0x44)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.pure (condOp 4)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l108e11, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l108bc1, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l108bb1 : List UInt8 :=
  [0x44, 0x88, 0x4C, 0x24, 0x0E, 0x83, 0x7C, 0x24, 0x44, 0x00, 0x0F, 0x84, 0x50, 0x02, 0x00, 0x00]

theorem code_l108bb1 : ∀ x ∈ codeRange 0x108bb1 bytes_l108bb1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8bb1 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108bc1_8 : Block Op Label signature Reg.count 358 :=
  .letOp (n := 358) (.exec 0x108dde (StorePre 0x108dde 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108dde + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dde 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[341, 354]
    (.letOp (n := 359) (.exec 0x108de2 (StorePre 0x108de2 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108de2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108de2 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[352, 354]
    (.letOp (n := 360) (.exec 0x108de6 (StorePre 0x108de6 4 (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x108de6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108de6 4 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 6] [])) #v[284, 354]
    (.letOp (n := 361) (.out 0x108dea (addR64Imm8Effect 0x108dea 4 0x78) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 362) (.exec 0x108dea (fun s => s.RIP = 0x108dea) (addR64Imm8Effect 0x108dea 4 0x78) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 363) (.out 0x108dee (popR64Effect 0x108dee 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[361]
    (.letOp (n := 364) (.out 0x108dee (popR64Effect 0x108dee 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[361]
    (.letOp (n := 365) (.exec 0x108dee (PopPre 0x108dee) (popR64Effect 0x108dee 1 3) (Reg.operands [.gpr 4] [])) #v[361]
    (.letOp (n := 366) (.out 0x108def (popR64Effect 0x108def 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[364]
    (.letOp (n := 367) (.out 0x108def (popR64Effect 0x108def 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[364]
    (.letOp (n := 368) (.exec 0x108def (PopPre 0x108def) (popR64Effect 0x108def 2 12) (Reg.operands [.gpr 4] [])) #v[364]
    (.letOp (n := 369) (.out 0x108df1 (popR64Effect 0x108df1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[367]
    (.letOp (n := 370) (.out 0x108df1 (popR64Effect 0x108df1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[367]
    (.letOp (n := 371) (.exec 0x108df1 (PopPre 0x108df1) (popR64Effect 0x108df1 2 13) (Reg.operands [.gpr 4] [])) #v[367]
    (.letOp (n := 372) (.out 0x108df3 (popR64Effect 0x108df3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[370]
    (.letOp (n := 373) (.out 0x108df3 (popR64Effect 0x108df3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[370]
    (.letOp (n := 374) (.exec 0x108df3 (PopPre 0x108df3) (popR64Effect 0x108df3 2 14) (Reg.operands [.gpr 4] [])) #v[370]
    (.letOp (n := 375) (.out 0x108df5 (popR64Effect 0x108df5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[373]
    (.letOp (n := 376) (.out 0x108df5 (popR64Effect 0x108df5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[373]
    (.letOp (n := 377) (.exec 0x108df5 (PopPre 0x108df5) (popR64Effect 0x108df5 2 15) (Reg.operands [.gpr 4] [])) #v[373]
    (.letOp (n := 378) (.out 0x108df7 (popR64Effect 0x108df7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[376]
    (.letOp (n := 379) (.out 0x108df7 (popR64Effect 0x108df7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[376]
    (.letOp (n := 380) (.exec 0x108df7 (PopPre 0x108df7) (popR64Effect 0x108df7 1 5) (Reg.operands [.gpr 4] [])) #v[376]
    (.letOp (n := 381) (.out 0x108df8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[379]
    (.letOp (n := 382) (.out 0x108df8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[379]
    (.letOp (n := 383) (.exec 0x108df8 (RetPre 0x108df8) (retEffect) (Reg.operands [.gpr 4] [])) #v[379]
    (.terminate (.ret (RegMap.args [(0, 330), (1, 352), (2, 341), (3, 363), (4, 382), (5, 378), (6, 354), (7, 255), (8, 319), (9, 191), (10, 309), (11, 346), (12, 366), (13, 369), (14, 372), (15, 375), (22, 22), (39, 39), (50, 50), (51, 51)] 384) (some ⟨381, by decide⟩))))))))))))))))))))))))))))

def bytes_l108bc1_8 : List UInt8 :=
  [0x48, 0x89, 0x56, 0x10, 0x48, 0x89, 0x4E, 0x18, 0x40, 0x88, 0x6E, 0x20, 0x48, 0x83, 0xC4, 0x78,
    0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l108bc1_8 : ∀ x ∈ codeRange 0x108dde bytes_l108bc1_8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8dde 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108bc1_7 : Block Op Label signature Reg.count 322 :=
  .letOp (n := 322) (.out 0x108d97 (movzxR32M8Effect 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 323) (.exec 0x108d97 (LoadPre 0x108d97 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d97 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d97 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 324) (.out 0x108d9c (xorR64R64Effect 0x108d9c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[151, 191]
    (.letOp (n := 325) (.exec 0x108d9c (fun s => s.RIP = 0x108d9c) (xorR64R64Effect 0x108d9c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[151, 191]
    (.letOp (n := 326) (.out 0x108d9f (negR64Effect 0x108d9f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[322]
    (.letOp (n := 327) (.exec 0x108d9f (fun s => s.RIP = 0x108d9f) (negR64Effect 0x108d9f 0) (Reg.operands [.gpr 0] [])) #v[322]
    (.letOp (n := 328) (.out 0x108da2 (andR64R64Effect 0x108da2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[326, 324]
    (.letOp (n := 329) (.exec 0x108da2 (fun s => s.RIP = 0x108da2) (andR64R64Effect 0x108da2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[326, 324]
    (.letOp (n := 330) (.out 0x108da5 (xorR64R64Effect 0x108da5 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[328, 191]
    (.letOp (n := 331) (.exec 0x108da5 (fun s => s.RIP = 0x108da5) (xorR64R64Effect 0x108da5 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[328, 191]
    (.letOp (n := 332) (.exec 0x108da8 (StorePre 0x108da8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108da8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108da8 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 333) (.out 0x108dac (movzxR32M8Effect 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 334) (.exec 0x108dac (LoadPre 0x108dac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dac + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dac 5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 335) (.out 0x108db1 (xorR64R64Effect 0x108db1 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[131, 222]
    (.letOp (n := 336) (.exec 0x108db1 (fun s => s.RIP = 0x108db1) (xorR64R64Effect 0x108db1 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[131, 222]
    (.letOp (n := 337) (.out 0x108db4 (negR64Effect 0x108db4 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[333]
    (.letOp (n := 338) (.exec 0x108db4 (fun s => s.RIP = 0x108db4) (negR64Effect 0x108db4 2) (Reg.operands [.gpr 2] [])) #v[333]
    (.letOp (n := 339) (.out 0x108db7 (andR64R64Effect 0x108db7 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[337, 335]
    (.letOp (n := 340) (.exec 0x108db7 (fun s => s.RIP = 0x108db7) (andR64R64Effect 0x108db7 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[337, 335]
    (.letOp (n := 341) (.out 0x108dba (xorR64R64Effect 0x108dba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[339, 222]
    (.letOp (n := 342) (.exec 0x108dba (fun s => s.RIP = 0x108dba) (xorR64R64Effect 0x108dba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[339, 222]
    (.letOp (n := 343) (.exec 0x108dbd (StorePre 0x108dbd 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dbd + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108dbd 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 344) (.out 0x108dc1 (movzxR32M8Effect 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 345) (.exec 0x108dc1 (LoadPre 0x108dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108dc1 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108dc1 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 346) (.out 0x108dc6 (xorR64R64Effect 0x108dc6 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[245, 255]
    (.letOp (n := 347) (.exec 0x108dc6 (fun s => s.RIP = 0x108dc6) (xorR64R64Effect 0x108dc6 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[245, 255]
    (.letOp (n := 348) (.out 0x108dc9 (negR64Effect 0x108dc9 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[344]
    (.letOp (n := 349) (.exec 0x108dc9 (fun s => s.RIP = 0x108dc9) (negR64Effect 0x108dc9 1) (Reg.operands [.gpr 1] [])) #v[344]
    (.letOp (n := 350) (.out 0x108dcc (andR64R64Effect 0x108dcc 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[348, 346]
    (.letOp (n := 351) (.exec 0x108dcc (fun s => s.RIP = 0x108dcc) (andR64R64Effect 0x108dcc 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[348, 346]
    (.letOp (n := 352) (.out 0x108dcf (xorR64R64Effect 0x108dcf 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[350, 255]
    (.letOp (n := 353) (.exec 0x108dcf (fun s => s.RIP = 0x108dcf) (xorR64R64Effect 0x108dcf 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[350, 255]
    (.letOp (n := 354) (.out 0x108dd2 (movR64M64Effect 0x108dd2 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 355) (.exec 0x108dd2 (LoadPre 0x108dd2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x108dd2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108dd2 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 356) (.exec 0x108dd7 (StorePre 0x108dd7 3 (fun s => AddrMode.addr (.base 6 .none) s (0x108dd7 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x108dd7 8 (.base 6 .none)) (Reg.operands [.gpr 8, .gpr 6] [])) #v[319, 354]
    (.letOp (n := 357) (.exec 0x108dda (StorePre 0x108dda 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108dda + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x108dda 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[330, 354]
    (b_l108bc1_8))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_7 : List UInt8 :=
  [0x0F, 0xB6, 0x44, 0x24, 0x10, 0x4C, 0x31, 0xCB, 0x48, 0xF7, 0xD8, 0x48, 0x21, 0xD8, 0x4C, 0x31,
    0xC8, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49, 0x31, 0xF4, 0x48, 0xF7, 0xDA,
    0x4C, 0x21, 0xE2, 0x48, 0x31, 0xF2, 0x88, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x49,
    0x31, 0xFB, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x48, 0x31, 0xF9, 0x48, 0x8B, 0x74, 0x24, 0x70,
    0x4C, 0x89, 0x06, 0x48, 0x89, 0x46, 0x08] ++ bytes_l108bc1_8

theorem code_l108bc1_7 : ∀ x ∈ codeRange 0x108d97 bytes_l108bc1_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d97 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_8

@[cfg_block] def b_l108bc1_6 : Block Op Label signature Reg.count 288 :=
  .letOp (n := 288) (.out 0x108d48 (atFlags (condHolds 4) (setccR8Effect 0x108d48 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[276, 286]
    (.letOp (n := 289) (.exec 0x108d48 (fun s => s.RIP = 0x108d48) (atFlags (condHolds 4) (setccR8Effect 0x108d48 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[276, 286]
    (.letOp (n := 290) (.out 0x108d4b (andR8R8Effect 0x108d4b 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[288, 280]
    (.letOp (n := 291) (.exec 0x108d4b (fun s => s.RIP = 0x108d4b) (andR8R8Effect 0x108d4b 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[288, 280]
    (.letOp (n := 292) (.exec 0x108d4e (StorePre 0x108d4e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d4e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d4e 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 293) (.exec 0x108d52 (fun s => s.RIP = 0x108d52) (leaR64Effect 0x108d52 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 294) (.out 0x108d57 (movzxR32M8Effect 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 295) (.exec 0x108d57 (LoadPre 0x108d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d57 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d57 6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 296) (.out 0x108d5d (decR64Effect 0x108d5d 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[294]
    (.letOp (n := 297) (.exec 0x108d5d (fun s => s.RIP = 0x108d5d) (decR64Effect 0x108d5d 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[294]
    (.letOp (n := 298) (.out 0x108d60 (andR64R64Effect 0x108d60 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[296, 280]
    (.letOp (n := 299) (.exec 0x108d60 (fun s => s.RIP = 0x108d60) (andR64R64Effect 0x108d60 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[296, 280]
    (.letOp (n := 300) (.out 0x108d63 (sarR64Effect 0x108d63 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[298]
    (.letOp (n := 301) (.exec 0x108d63 (fun s => s.RIP = 0x108d63) (sarR64Effect 0x108d63 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[298]
    (.letOp (n := 302) (.out 0x108d67 (addR64R64Effect 0x108d67 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[300, 278]
    (.letOp (n := 303) (.exec 0x108d67 (fun s => s.RIP = 0x108d67) (addR64R64Effect 0x108d67 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[300, 278]
    (.letOp (n := 304) (.out 0x108d6a (shrR64Effect 0x108d6a 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[302]
    (.letOp (n := 305) (.exec 0x108d6a (fun s => s.RIP = 0x108d6a) (shrR64Effect 0x108d6a 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[302]
    (.letOp (n := 306) (.exec 0x108d6e (StorePre 0x108d6e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d6e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d6e 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[304, 4]
    (.letOp (n := 307) (.exec 0x108d73 (fun s => s.RIP = 0x108d73) (leaR64Effect 0x108d73 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 308) (.exec 0x108d78 (StorePre 0x108d78 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d78 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d78 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (.letOp (n := 309) (.out 0x108d7c (leaR64Effect 0x108d7c 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 310) (.exec 0x108d7c (fun s => s.RIP = 0x108d7c) (leaR64Effect 0x108d7c 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 311) (.out 0x108d81 (movzxR32M8Effect 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 312) (.exec 0x108d81 (LoadPre 0x108d81 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d81 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108d81 6 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 313) (.out 0x108d87 (xorR64R64Effect 0x108d87 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[153, 159]
    (.letOp (n := 314) (.exec 0x108d87 (fun s => s.RIP = 0x108d87) (xorR64R64Effect 0x108d87 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[153, 159]
    (.letOp (n := 315) (.out 0x108d8a (negR64Effect 0x108d8a 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[311]
    (.letOp (n := 316) (.exec 0x108d8a (fun s => s.RIP = 0x108d8a) (negR64Effect 0x108d8a 8) (Reg.operands [.gpr 8] [])) #v[311]
    (.letOp (n := 317) (.out 0x108d8d (andR64R64Effect 0x108d8d 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[315, 313]
    (.letOp (n := 318) (.exec 0x108d8d (fun s => s.RIP = 0x108d8d) (andR64R64Effect 0x108d8d 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[315, 313]
    (.letOp (n := 319) (.out 0x108d90 (xorR64R64Effect 0x108d90 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[317, 159]
    (.letOp (n := 320) (.exec 0x108d90 (fun s => s.RIP = 0x108d90) (xorR64R64Effect 0x108d90 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[317, 159]
    (.letOp (n := 321) (.exec 0x108d93 (StorePre 0x108d93 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d93 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108d93 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[290, 4]
    (b_l108bc1_7))))))))))))))))))))))))))))))))))

def bytes_l108bc1_6 : List UInt8 :=
  [0x0F, 0x94, 0xC1, 0x44, 0x20, 0xC1, 0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D, 0x54, 0x24, 0x10, 0x44,
    0x0F, 0xB6, 0x54, 0x24, 0x10, 0x49, 0xFF, 0xCA, 0x4D, 0x21, 0xC2, 0x49, 0xC1, 0xFA, 0x3F, 0x4D,
    0x01, 0xEA, 0x49, 0xC1, 0xEA, 0x3F, 0x4C, 0x89, 0x54, 0x24, 0x10, 0x4C, 0x8D, 0x44, 0x24, 0x10,
    0x88, 0x4C, 0x24, 0x10, 0x4C, 0x8D, 0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x10, 0x48,
    0x31, 0xC2, 0x49, 0xF7, 0xD8, 0x49, 0x21, 0xD0, 0x49, 0x31, 0xC0, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l108bc1_7

theorem code_l108bc1_6 : ∀ x ∈ codeRange 0x108d48 bytes_l108bc1_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d48 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_7

@[cfg_block] def b_l108bc1_5 : Block Op Label signature Reg.count 249 :=
  .letOp (n := 249) (.out 0x108d01 (movR64M64Effect 0x108d01 14 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 250) (.exec 0x108d01 (LoadPre 0x108d01 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x108d01 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108d01 14 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 251) (.out 0x108d06 (subR64R64Effect 0x108d06 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[247, 249]
    (.letOp (n := 252) (.exec 0x108d06 (fun s => s.RIP = 0x108d06) (subR64R64Effect 0x108d06 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[247, 249]
    (.letOp (n := 253) (.out 0x108d09 (sarR64Effect 0x108d09 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[243]
    (.letOp (n := 254) (.exec 0x108d09 (fun s => s.RIP = 0x108d09) (sarR64Effect 0x108d09 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[243]
    (.letOp (n := 255) (.out 0x108d0d (addR64R64Effect 0x108d0d 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[253, 251]
    (.letOp (n := 256) (.exec 0x108d0d (fun s => s.RIP = 0x108d0d) (addR64R64Effect 0x108d0d 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[253, 251]
    (.letOp (n := 257) (.out 0x108d10 (movR64R64Effect 0x108d10 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[245]
    (.letOp (n := 258) (.exec 0x108d10 (fun s => s.RIP = 0x108d10) (movR64R64Effect 0x108d10 8 11) (Reg.operands [.gpr 11] [])) #v[245]
    (.letOp (n := 259) (.out 0x108d13 (notR64Effect 0x108d13 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[257]
    (.letOp (n := 260) (.exec 0x108d13 (fun s => s.RIP = 0x108d13) (notR64Effect 0x108d13 8) (Reg.operands [.gpr 8] [])) #v[257]
    (.letOp (n := 261) (.out 0x108d16 (movR64R64Effect 0x108d16 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[249]
    (.letOp (n := 262) (.exec 0x108d16 (fun s => s.RIP = 0x108d16) (movR64R64Effect 0x108d16 10 14) (Reg.operands [.gpr 14] [])) #v[249]
    (.letOp (n := 263) (.out 0x108d19 (andR64R64Effect 0x108d19 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[261, 259]
    (.letOp (n := 264) (.exec 0x108d19 (fun s => s.RIP = 0x108d19) (andR64R64Effect 0x108d19 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[261, 259]
    (.letOp (n := 265) (.out 0x108d1c (orR64R64Effect 0x108d1c 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[259, 249]
    (.letOp (n := 266) (.exec 0x108d1c (fun s => s.RIP = 0x108d1c) (orR64R64Effect 0x108d1c 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[259, 249]
    (.letOp (n := 267) (.out 0x108d1f (andR64R64Effect 0x108d1f 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[265, 255]
    (.letOp (n := 268) (.exec 0x108d1f (fun s => s.RIP = 0x108d1f) (andR64R64Effect 0x108d1f 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[265, 255]
    (.letOp (n := 269) (.out 0x108d22 (orR64R64Effect 0x108d22 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[267, 263]
    (.letOp (n := 270) (.exec 0x108d22 (fun s => s.RIP = 0x108d22) (orR64R64Effect 0x108d22 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[267, 263]
    (.letOp (n := 271) (.out 0x108d25 (shrR64Effect 0x108d25 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[269]
    (.letOp (n := 272) (.exec 0x108d25 (fun s => s.RIP = 0x108d25) (shrR64Effect 0x108d25 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[269]
    (.letOp (n := 273) (.exec 0x108d29 (StorePre 0x108d29 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d29 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108d29 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[271, 4]
    (.letOp (n := 274) (.out 0x108d2e (xorR32R32Effect 0x108d2e 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[271, 271]
    (.letOp (n := 275) (.exec 0x108d2e (fun s => s.RIP = 0x108d2e) (xorR32R32Effect 0x108d2e 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[271, 271]
    (.letOp (n := 276) (.out 0x108d31 (movR32R32Effect 0x108d31 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 277) (.exec 0x108d31 (fun s => s.RIP = 0x108d31) (movR32R32Effect 0x108d31 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 278) (.out 0x108d33 (shrR64ClEffect 0x108d33 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[93, 276]
    (.letOp (n := 279) (.exec 0x108d33 (fun s => s.RIP = 0x108d33) (shrR64ClEffect 0x108d33 3 13) (Reg.operands [.gpr 13, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93, 276]
    (.letOp (n := 280) (.out 0x108d36 (subR64M64Effect 0x108d36 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[274, 4]
    (.letOp (n := 281) (.exec 0x108d36 (LoadPre 0x108d36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108d36 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108d36 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[274, 4]
    (.letOp (n := 282) (.out 0x108d3b (movzxR32M8Effect 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 283) (.exec 0x108d3b (LoadPre 0x108d3b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x108d3b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x108d3b 5 5 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 284) (.out 0x108d40 (xorR8M8Effect 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[282, 4]
    (.letOp (n := 285) (.exec 0x108d40 (LoadPre 0x108d40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x108d40 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x108d40 5 5 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[282, 4]
    (.letOp (n := 286) (.out 0x108d45 (testR64R64Effect 0x108d45 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[278, 278]
    (.letOp (n := 287) (.exec 0x108d45 (fun s => s.RIP = 0x108d45) (testR64R64Effect 0x108d45 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[278, 278]
    (b_l108bc1_6)))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_5 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x68, 0x4D, 0x29, 0xF0, 0x48, 0xC1, 0xFF, 0x3F, 0x4C, 0x01, 0xC7, 0x4D,
    0x89, 0xD8, 0x49, 0xF7, 0xD0, 0x4D, 0x89, 0xF2, 0x4D, 0x21, 0xC2, 0x4D, 0x09, 0xF0, 0x49, 0x21,
    0xF8, 0x4D, 0x09, 0xD0, 0x49, 0xC1, 0xE8, 0x3F, 0x4C, 0x89, 0x44, 0x24, 0x10, 0x45, 0x31, 0xC0,
    0x89, 0xE9, 0x49, 0xD3, 0xED, 0x4C, 0x2B, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x6C, 0x24, 0x0F, 0x40,
    0x32, 0x6C, 0x24, 0x0E, 0x4D, 0x85, 0xED] ++ bytes_l108bc1_6

theorem code_l108bc1_5 : ∀ x ∈ codeRange 0x108d01 bytes_l108bc1_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8d01 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_6

@[cfg_block] def b_l108bc1_4 : Block Op Label signature Reg.count 210 :=
  .letOp (n := 210) (.out 0x108cbd (xorR32R32Effect 0x108cbd 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[207, 207]
    (.letOp (n := 211) (.exec 0x108cbd (fun s => s.RIP = 0x108cbd) (xorR32R32Effect 0x108cbd 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[207, 207]
    (.letOp (n := 212) (.out 0x108cbf (subR64M64Effect 0x108cbf 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[210, 4]
    (.letOp (n := 213) (.exec 0x108cbf (LoadPre 0x108cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cbf + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cbf 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[210, 4]
    (.letOp (n := 214) (.out 0x108cc4 (movR64R64Effect 0x108cc4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 215) (.exec 0x108cc4 (fun s => s.RIP = 0x108cc4) (movR64R64Effect 0x108cc4 7 12) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 216) (.out 0x108cc7 (movR64M64Effect 0x108cc7 14 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 217) (.exec 0x108cc7 (LoadPre 0x108cc7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108cc7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108cc7 14 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 218) (.out 0x108ccc (subR64R64Effect 0x108ccc 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[214, 216]
    (.letOp (n := 219) (.exec 0x108ccc (fun s => s.RIP = 0x108ccc) (subR64R64Effect 0x108ccc 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[214, 216]
    (.letOp (n := 220) (.out 0x108ccf (sarR64Effect 0x108ccf 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[212]
    (.letOp (n := 221) (.exec 0x108ccf (fun s => s.RIP = 0x108ccf) (sarR64Effect 0x108ccf 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[212]
    (.letOp (n := 222) (.out 0x108cd3 (addR64R64Effect 0x108cd3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[220, 218]
    (.letOp (n := 223) (.exec 0x108cd3 (fun s => s.RIP = 0x108cd3) (addR64R64Effect 0x108cd3 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[220, 218]
    (.letOp (n := 224) (.out 0x108cd6 (movR64R64Effect 0x108cd6 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 225) (.exec 0x108cd6 (fun s => s.RIP = 0x108cd6) (movR64R64Effect 0x108cd6 7 12) (Reg.operands [.gpr 12] [])) #v[131]
    (.letOp (n := 226) (.out 0x108cd9 (notR64Effect 0x108cd9 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[224]
    (.letOp (n := 227) (.exec 0x108cd9 (fun s => s.RIP = 0x108cd9) (notR64Effect 0x108cd9 7) (Reg.operands [.gpr 7] [])) #v[224]
    (.letOp (n := 228) (.out 0x108cdc (movR64R64Effect 0x108cdc 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[216]
    (.letOp (n := 229) (.exec 0x108cdc (fun s => s.RIP = 0x108cdc) (movR64R64Effect 0x108cdc 8 14) (Reg.operands [.gpr 14] [])) #v[216]
    (.letOp (n := 230) (.out 0x108cdf (andR64R64Effect 0x108cdf 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[228, 226]
    (.letOp (n := 231) (.exec 0x108cdf (fun s => s.RIP = 0x108cdf) (andR64R64Effect 0x108cdf 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[228, 226]
    (.letOp (n := 232) (.out 0x108ce2 (orR64R64Effect 0x108ce2 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[226, 216]
    (.letOp (n := 233) (.exec 0x108ce2 (fun s => s.RIP = 0x108ce2) (orR64R64Effect 0x108ce2 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[226, 216]
    (.letOp (n := 234) (.out 0x108ce5 (andR64R64Effect 0x108ce5 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[232, 222]
    (.letOp (n := 235) (.exec 0x108ce5 (fun s => s.RIP = 0x108ce5) (andR64R64Effect 0x108ce5 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[232, 222]
    (.letOp (n := 236) (.out 0x108ce8 (orR64R64Effect 0x108ce8 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[234, 230]
    (.letOp (n := 237) (.exec 0x108ce8 (fun s => s.RIP = 0x108ce8) (orR64R64Effect 0x108ce8 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[234, 230]
    (.letOp (n := 238) (.out 0x108ceb (shrR64Effect 0x108ceb 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[236]
    (.letOp (n := 239) (.exec 0x108ceb (fun s => s.RIP = 0x108ceb) (shrR64Effect 0x108ceb 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[236]
    (.letOp (n := 240) (.exec 0x108cef (StorePre 0x108cef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cef 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[238, 4]
    (.letOp (n := 241) (.out 0x108cf4 (xorR32R32Effect 0x108cf4 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[238, 238]
    (.letOp (n := 242) (.exec 0x108cf4 (fun s => s.RIP = 0x108cf4) (xorR32R32Effect 0x108cf4 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[238, 238]
    (.letOp (n := 243) (.out 0x108cf6 (subR64M64Effect 0x108cf6 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[241, 4]
    (.letOp (n := 244) (.exec 0x108cf6 (LoadPre 0x108cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cf6 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108cf6 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[241, 4]
    (.letOp (n := 245) (.out 0x108cfb (orR64R64Effect 0x108cfb 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[115, 101]
    (.letOp (n := 246) (.exec 0x108cfb (fun s => s.RIP = 0x108cfb) (orR64R64Effect 0x108cfb 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[115, 101]
    (.letOp (n := 247) (.out 0x108cfe (movR64R64Effect 0x108cfe 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 11] []) (.reg (.gpr 8))) #v[245]
    (.letOp (n := 248) (.exec 0x108cfe (fun s => s.RIP = 0x108cfe) (movR64R64Effect 0x108cfe 8 11) (Reg.operands [.gpr 11] [])) #v[245]
    (b_l108bc1_5)))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_4 : List UInt8 :=
  [0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x10, 0x4C, 0x89, 0xE7, 0x4C, 0x8B, 0x74, 0x24, 0x60, 0x4C,
    0x29, 0xF7, 0x48, 0xC1, 0xFE, 0x3F, 0x48, 0x01, 0xFE, 0x4C, 0x89, 0xE7, 0x48, 0xF7, 0xD7, 0x4D,
    0x89, 0xF0, 0x49, 0x21, 0xF8, 0x4C, 0x09, 0xF7, 0x48, 0x21, 0xF7, 0x4C, 0x09, 0xC7, 0x48, 0xC1,
    0xEF, 0x3F, 0x48, 0x89, 0x7C, 0x24, 0x10, 0x31, 0xFF, 0x48, 0x2B, 0x7C, 0x24, 0x10, 0x4D, 0x09,
    0xD3, 0x4D, 0x89, 0xD8] ++ bytes_l108bc1_5

theorem code_l108bc1_4 : ∀ x ∈ codeRange 0x108cbd bytes_l108bc1_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8cbd 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_5

@[cfg_block] def b_l108bc1_3 : Block Op Label signature Reg.count 173 :=
  .letOp (n := 173) (.out 0x108c74 (orR64R64Effect 0x108c74 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[171, 167]
    (.letOp (n := 174) (.exec 0x108c74 (fun s => s.RIP = 0x108c74) (orR64R64Effect 0x108c74 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[171, 167]
    (.letOp (n := 175) (.out 0x108c77 (shrR64Effect 0x108c77 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[173]
    (.letOp (n := 176) (.exec 0x108c77 (fun s => s.RIP = 0x108c77) (shrR64Effect 0x108c77 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[173]
    (.letOp (n := 177) (.exec 0x108c7b (StorePre 0x108c7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108c7b 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.exec 0x108c80 (fun s => s.RIP = 0x108c80) (leaR64Effect 0x108c80 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 179) (.out 0x108c85 (xorR32R32Effect 0x108c85 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 180) (.exec 0x108c85 (fun s => s.RIP = 0x108c85) (xorR32R32Effect 0x108c85 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 181) (.out 0x108c88 (subR64M64Effect 0x108c88 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[179, 4]
    (.letOp (n := 182) (.exec 0x108c88 (LoadPre 0x108c88 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108c88 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x108c88 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[179, 4]
    (.letOp (n := 183) (.out 0x108c8d (movR64R64Effect 0x108c8d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[151]
    (.letOp (n := 184) (.exec 0x108c8d (fun s => s.RIP = 0x108c8d) (movR64R64Effect 0x108c8d 6 3) (Reg.operands [.gpr 3] [])) #v[151]
    (.letOp (n := 185) (.out 0x108c90 (movR64M64Effect 0x108c90 8 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 186) (.exec 0x108c90 (LoadPre 0x108c90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x108c90 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c90 8 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 187) (.out 0x108c95 (subR64R64Effect 0x108c95 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[183, 185]
    (.letOp (n := 188) (.exec 0x108c95 (fun s => s.RIP = 0x108c95) (subR64R64Effect 0x108c95 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[183, 185]
    (.letOp (n := 189) (.out 0x108c98 (sarR64Effect 0x108c98 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[181]
    (.letOp (n := 190) (.exec 0x108c98 (fun s => s.RIP = 0x108c98) (sarR64Effect 0x108c98 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[181]
    (.letOp (n := 191) (.out 0x108c9c (addR64R64Effect 0x108c9c 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[189, 187]
    (.letOp (n := 192) (.exec 0x108c9c (fun s => s.RIP = 0x108c9c) (addR64R64Effect 0x108c9c 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[189, 187]
    (.letOp (n := 193) (.out 0x108c9f (movR64R64Effect 0x108c9f 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[151]
    (.letOp (n := 194) (.exec 0x108c9f (fun s => s.RIP = 0x108c9f) (movR64R64Effect 0x108c9f 6 3) (Reg.operands [.gpr 3] [])) #v[151]
    (.letOp (n := 195) (.out 0x108ca2 (notR64Effect 0x108ca2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[193]
    (.letOp (n := 196) (.exec 0x108ca2 (fun s => s.RIP = 0x108ca2) (notR64Effect 0x108ca2 6) (Reg.operands [.gpr 6] [])) #v[193]
    (.letOp (n := 197) (.out 0x108ca5 (movR64R64Effect 0x108ca5 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[185]
    (.letOp (n := 198) (.exec 0x108ca5 (fun s => s.RIP = 0x108ca5) (movR64R64Effect 0x108ca5 7 8) (Reg.operands [.gpr 8] [])) #v[185]
    (.letOp (n := 199) (.out 0x108ca8 (andR64R64Effect 0x108ca8 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[197, 195]
    (.letOp (n := 200) (.exec 0x108ca8 (fun s => s.RIP = 0x108ca8) (andR64R64Effect 0x108ca8 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[197, 195]
    (.letOp (n := 201) (.out 0x108cab (orR64R64Effect 0x108cab 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[195, 185]
    (.letOp (n := 202) (.exec 0x108cab (fun s => s.RIP = 0x108cab) (orR64R64Effect 0x108cab 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[195, 185]
    (.letOp (n := 203) (.out 0x108cae (andR64R64Effect 0x108cae 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[201, 191]
    (.letOp (n := 204) (.exec 0x108cae (fun s => s.RIP = 0x108cae) (andR64R64Effect 0x108cae 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[201, 191]
    (.letOp (n := 205) (.out 0x108cb1 (orR64R64Effect 0x108cb1 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[203, 199]
    (.letOp (n := 206) (.exec 0x108cb1 (fun s => s.RIP = 0x108cb1) (orR64R64Effect 0x108cb1 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[203, 199]
    (.letOp (n := 207) (.out 0x108cb4 (shrR64Effect 0x108cb4 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[205]
    (.letOp (n := 208) (.exec 0x108cb4 (fun s => s.RIP = 0x108cb4) (shrR64Effect 0x108cb4 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[205]
    (.letOp (n := 209) (.exec 0x108cb8 (StorePre 0x108cb8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108cb8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108cb8 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[207, 4]
    (b_l108bc1_4)))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_3 : List UInt8 :=
  [0x48, 0x09, 0xF1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x8D, 0x4C, 0x24,
    0x10, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0xDE, 0x4C, 0x8B, 0x44, 0x24,
    0x58, 0x4C, 0x29, 0xC6, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xF1, 0x48, 0x89, 0xDE, 0x48, 0xF7,
    0xD6, 0x4C, 0x89, 0xC7, 0x48, 0x21, 0xF7, 0x4C, 0x09, 0xC6, 0x4C, 0x21, 0xCE, 0x48, 0x09, 0xFE,
    0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x10] ++ bytes_l108bc1_4

theorem code_l108bc1_3 : ∀ x ∈ codeRange 0x108c74 bytes_l108bc1_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c74 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_4

@[cfg_block] def b_l108bc1_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x108c3a (movR32R32Effect 0x108c3a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 134) (.exec 0x108c3a (fun s => s.RIP = 0x108c3a) (movR32R32Effect 0x108c3a 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 135) (.out 0x108c3c (shlR64ClEffect 0x108c3c 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[67, 133]
    (.letOp (n := 136) (.exec 0x108c3c (fun s => s.RIP = 0x108c3c) (shlR64ClEffect 0x108c3c 3 14) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67, 133]
    (.letOp (n := 137) (.out 0x108c3f (movR64R64Effect 0x108c3f 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[75]
    (.letOp (n := 138) (.exec 0x108c3f (fun s => s.RIP = 0x108c3f) (movR64R64Effect 0x108c3f 3 15) (Reg.operands [.gpr 15] [])) #v[75]
    (.letOp (n := 139) (.out 0x108c42 (movR32R32Effect 0x108c42 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 140) (.exec 0x108c42 (fun s => s.RIP = 0x108c42) (movR32R32Effect 0x108c42 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 141) (.out 0x108c44 (shrR64ClEffect 0x108c44 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[137, 139]
    (.letOp (n := 142) (.exec 0x108c44 (fun s => s.RIP = 0x108c44) (shrR64ClEffect 0x108c44 3 3) (Reg.operands [.gpr 3, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137, 139]
    (.letOp (n := 143) (.out 0x108c47 (movR32R32Effect 0x108c47 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 144) (.exec 0x108c47 (fun s => s.RIP = 0x108c47) (movR32R32Effect 0x108c47 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 145) (.out 0x108c49 (shlR64ClEffect 0x108c49 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[75, 143]
    (.letOp (n := 146) (.exec 0x108c49 (fun s => s.RIP = 0x108c49) (shlR64ClEffect 0x108c49 3 15) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75, 143]
    (.letOp (n := 147) (.out 0x108c4c (movR32R32Effect 0x108c4c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 148) (.exec 0x108c4c (fun s => s.RIP = 0x108c4c) (movR32R32Effect 0x108c4c 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 149) (.out 0x108c4e (shrR64ClEffect 0x108c4e 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[129, 147]
    (.letOp (n := 150) (.exec 0x108c4e (fun s => s.RIP = 0x108c4e) (shrR64ClEffect 0x108c4e 3 2) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[129, 147]
    (.letOp (n := 151) (.out 0x108c51 (orR64R64Effect 0x108c51 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[141, 135]
    (.letOp (n := 152) (.exec 0x108c51 (fun s => s.RIP = 0x108c51) (orR64R64Effect 0x108c51 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[141, 135]
    (.letOp (n := 153) (.out 0x108c54 (orR64R64Effect 0x108c54 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[149, 145]
    (.letOp (n := 154) (.exec 0x108c54 (fun s => s.RIP = 0x108c54) (orR64R64Effect 0x108c54 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[149, 145]
    (.letOp (n := 155) (.out 0x108c57 (movR64R64Effect 0x108c57 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[153]
    (.letOp (n := 156) (.exec 0x108c57 (fun s => s.RIP = 0x108c57) (movR64R64Effect 0x108c57 0 2) (Reg.operands [.gpr 2] [])) #v[153]
    (.letOp (n := 157) (.out 0x108c5a (movR64M64Effect 0x108c5a 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 158) (.exec 0x108c5a (LoadPre 0x108c5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x108c5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c5a 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 159) (.out 0x108c5f (subR64R64Effect 0x108c5f 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[155, 157]
    (.letOp (n := 160) (.exec 0x108c5f (fun s => s.RIP = 0x108c5f) (subR64R64Effect 0x108c5f 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[155, 157]
    (.letOp (n := 161) (.out 0x108c62 (movR64R64Effect 0x108c62 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[153]
    (.letOp (n := 162) (.exec 0x108c62 (fun s => s.RIP = 0x108c62) (movR64R64Effect 0x108c62 1 2) (Reg.operands [.gpr 2] [])) #v[153]
    (.letOp (n := 163) (.out 0x108c65 (notR64Effect 0x108c65 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[161]
    (.letOp (n := 164) (.exec 0x108c65 (fun s => s.RIP = 0x108c65) (notR64Effect 0x108c65 1) (Reg.operands [.gpr 1] [])) #v[161]
    (.letOp (n := 165) (.out 0x108c68 (movR64R64Effect 0x108c68 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[157]
    (.letOp (n := 166) (.exec 0x108c68 (fun s => s.RIP = 0x108c68) (movR64R64Effect 0x108c68 6 7) (Reg.operands [.gpr 7] [])) #v[157]
    (.letOp (n := 167) (.out 0x108c6b (andR64R64Effect 0x108c6b 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x108c6b (fun s => s.RIP = 0x108c6b) (andR64R64Effect 0x108c6b 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[165, 163]
    (.letOp (n := 169) (.out 0x108c6e (orR64R64Effect 0x108c6e 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[163, 157]
    (.letOp (n := 170) (.exec 0x108c6e (fun s => s.RIP = 0x108c6e) (orR64R64Effect 0x108c6e 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[163, 157]
    (.letOp (n := 171) (.out 0x108c71 (andR64R64Effect 0x108c71 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[169, 159]
    (.letOp (n := 172) (.exec 0x108c71 (fun s => s.RIP = 0x108c71) (andR64R64Effect 0x108c71 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[169, 159]
    (b_l108bc1_3))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_2 : List UInt8 :=
  [0x89, 0xC1, 0x49, 0xD3, 0xE6, 0x4C, 0x89, 0xFB, 0x89, 0xE9, 0x48, 0xD3, 0xEB, 0x89, 0xC1, 0x49,
    0xD3, 0xE7, 0x89, 0xE9, 0x48, 0xD3, 0xEA, 0x4C, 0x09, 0xF3, 0x4C, 0x09, 0xFA, 0x48, 0x89, 0xD0,
    0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x29, 0xF8, 0x48, 0x89, 0xD1, 0x48, 0xF7, 0xD1, 0x48, 0x89,
    0xFE, 0x48, 0x21, 0xCE, 0x48, 0x09, 0xF9, 0x48, 0x21, 0xC1] ++ bytes_l108bc1_3

theorem code_l108bc1_2 : ∀ x ∈ codeRange 0x108c3a bytes_l108bc1_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c3a 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_3

@[cfg_block] def b_l108bc1_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x108c00 (xorR64R64Effect 0x108c00 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[91, 0]
    (.letOp (n := 94) (.exec 0x108c00 (fun s => s.RIP = 0x108c00) (xorR64R64Effect 0x108c00 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[91, 0]
    (.letOp (n := 95) (.out 0x108c03 (movR32R32Effect 0x108c03 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 96) (.exec 0x108c03 (fun s => s.RIP = 0x108c03) (movR32R32Effect 0x108c03 2 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 97) (.out 0x108c05 (movR64R64Effect 0x108c05 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[93]
    (.letOp (n := 98) (.exec 0x108c05 (fun s => s.RIP = 0x108c05) (movR64R64Effect 0x108c05 10 13) (Reg.operands [.gpr 13] [])) #v[93]
    (.letOp (n := 99) (.out 0x108c08 (movR32R32Effect 0x108c08 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 100) (.exec 0x108c08 (fun s => s.RIP = 0x108c08) (movR32R32Effect 0x108c08 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 101) (.out 0x108c0a (shlR64ClEffect 0x108c0a 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[97, 99]
    (.letOp (n := 102) (.exec 0x108c0a (fun s => s.RIP = 0x108c0a) (shlR64ClEffect 0x108c0a 3 10) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97, 99]
    (.letOp (n := 103) (.out 0x108c0d (movR64M64Effect 0x108c0d 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 104) (.exec 0x108c0d (LoadPre 0x108c0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x108c0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108c0d 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x108c12 (xorR64R64Effect 0x108c12 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[3, 103]
    (.letOp (n := 106) (.exec 0x108c12 (fun s => s.RIP = 0x108c12) (xorR64R64Effect 0x108c12 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[3, 103]
    (.letOp (n := 107) (.out 0x108c15 (negR64Effect 0x108c15 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 108) (.exec 0x108c15 (fun s => s.RIP = 0x108c15) (negR64Effect 0x108c15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 109) (.out 0x108c18 (movR64R64Effect 0x108c18 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[59]
    (.letOp (n := 110) (.exec 0x108c18 (fun s => s.RIP = 0x108c18) (movR64R64Effect 0x108c18 11 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 111) (.out 0x108c1b (movR32M32LowEffect 0x108c1b 5 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 112) (.exec 0x108c1b (LoadPre 0x108c1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x108c1b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x108c1b 5 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x108c1f (movR32R32Effect 0x108c1f 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 114) (.exec 0x108c1f (fun s => s.RIP = 0x108c1f) (movR32R32Effect 0x108c1f 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 115) (.out 0x108c21 (shrR64ClEffect 0x108c21 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[109, 113]
    (.letOp (n := 116) (.exec 0x108c21 (fun s => s.RIP = 0x108c21) (shrR64ClEffect 0x108c21 3 11) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109, 113]
    (.letOp (n := 117) (.out 0x108c24 (movR32R32Effect 0x108c24 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 118) (.exec 0x108c24 (fun s => s.RIP = 0x108c24) (movR32R32Effect 0x108c24 2 1 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 119) (.out 0x108c26 (shlR64ClEffect 0x108c26 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[59, 117]
    (.letOp (n := 120) (.exec 0x108c26 (fun s => s.RIP = 0x108c26) (shlR64ClEffect 0x108c26 3 7) (Reg.operands [.gpr 7, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59, 117]
    (.letOp (n := 121) (.out 0x108c29 (movR64R64Effect 0x108c29 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 122) (.exec 0x108c29 (fun s => s.RIP = 0x108c29) (movR64R64Effect 0x108c29 12 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 123) (.out 0x108c2c (movR32R32Effect 0x108c2c 2 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[111]
    (.letOp (n := 124) (.exec 0x108c2c (fun s => s.RIP = 0x108c2c) (movR32R32Effect 0x108c2c 2 1 5) (Reg.operands [.gpr 5] [])) #v[111]
    (.letOp (n := 125) (.out 0x108c2e (shrR64ClEffect 0x108c2e 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[121, 123]
    (.letOp (n := 126) (.exec 0x108c2e (fun s => s.RIP = 0x108c2e) (shrR64ClEffect 0x108c2e 3 12) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121, 123]
    (.letOp (n := 127) (.out 0x108c31 (andR64R64Effect 0x108c31 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[107, 105]
    (.letOp (n := 128) (.exec 0x108c31 (fun s => s.RIP = 0x108c31) (andR64R64Effect 0x108c31 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[107, 105]
    (.letOp (n := 129) (.out 0x108c34 (xorR64R64Effect 0x108c34 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[127, 103]
    (.letOp (n := 130) (.exec 0x108c34 (fun s => s.RIP = 0x108c34) (xorR64R64Effect 0x108c34 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[127, 103]
    (.letOp (n := 131) (.out 0x108c37 (orR64R64Effect 0x108c37 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[125, 119]
    (.letOp (n := 132) (.exec 0x108c37 (fun s => s.RIP = 0x108c37) (orR64R64Effect 0x108c37 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[125, 119]
    (b_l108bc1_2))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1_1 : List UInt8 :=
  [0x49, 0x31, 0xC5, 0x89, 0xC8, 0x4D, 0x89, 0xEA, 0x89, 0xC1, 0x49, 0xD3, 0xE2, 0x48, 0x8B, 0x74,
    0x24, 0x48, 0x48, 0x31, 0xF3, 0x48, 0xF7, 0xDA, 0x49, 0x89, 0xFB, 0x8B, 0x6C, 0x24, 0x44, 0x89,
    0xE9, 0x49, 0xD3, 0xEB, 0x89, 0xC1, 0x48, 0xD3, 0xE7, 0x4D, 0x89, 0xF4, 0x89, 0xE9, 0x49, 0xD3,
    0xEC, 0x48, 0x21, 0xDA, 0x48, 0x31, 0xF2, 0x49, 0x09, 0xFC] ++ bytes_l108bc1_2

theorem code_l108bc1_1 : ∀ x ∈ codeRange 0x108c00 bytes_l108bc1_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8c00 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_2

@[cfg_block] def b_l108bc1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108bc1 (xorR64R64Effect 0x108bc1 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[10, 13]
    (.letOp (n := 54) (.exec 0x108bc1 (fun s => s.RIP = 0x108bc1) (xorR64R64Effect 0x108bc1 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[10, 13]
    (.letOp (n := 55) (.out 0x108bc4 (negR64Effect 0x108bc4 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x108bc4 (fun s => s.RIP = 0x108bc4) (negR64Effect 0x108bc4 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x108bc7 (andR64R64Effect 0x108bc7 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x108bc7 (fun s => s.RIP = 0x108bc7) (andR64R64Effect 0x108bc7 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x108bca (xorR64R64Effect 0x108bca 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108bca (fun s => s.RIP = 0x108bca) (xorR64R64Effect 0x108bca 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108bcd (xorR64R64Effect 0x108bcd 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[5, 11]
    (.letOp (n := 62) (.exec 0x108bcd (fun s => s.RIP = 0x108bcd) (xorR64R64Effect 0x108bcd 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[5, 11]
    (.letOp (n := 63) (.out 0x108bd0 (negR64Effect 0x108bd0 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 64) (.exec 0x108bd0 (fun s => s.RIP = 0x108bd0) (negR64Effect 0x108bd0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x108bd3 (andR64R64Effect 0x108bd3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x108bd3 (fun s => s.RIP = 0x108bd3) (andR64R64Effect 0x108bd3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x108bd6 (xorR64R64Effect 0x108bd6 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[65, 11]
    (.letOp (n := 68) (.exec 0x108bd6 (fun s => s.RIP = 0x108bd6) (xorR64R64Effect 0x108bd6 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[65, 11]
    (.letOp (n := 69) (.out 0x108bd9 (xorR64R64Effect 0x108bd9 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[8, 12]
    (.letOp (n := 70) (.exec 0x108bd9 (fun s => s.RIP = 0x108bd9) (xorR64R64Effect 0x108bd9 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[8, 12]
    (.letOp (n := 71) (.out 0x108bdc (negR64Effect 0x108bdc 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 72) (.exec 0x108bdc (fun s => s.RIP = 0x108bdc) (negR64Effect 0x108bdc 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 73) (.out 0x108bdf (andR64R64Effect 0x108bdf 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x108bdf (fun s => s.RIP = 0x108bdf) (andR64R64Effect 0x108bdf 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x108be2 (xorR64R64Effect 0x108be2 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[73, 12]
    (.letOp (n := 76) (.exec 0x108be2 (fun s => s.RIP = 0x108be2) (xorR64R64Effect 0x108be2 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[73, 12]
    (.letOp (n := 77) (.out 0x108be5 (andR32Imm8Effect 0x108be5 3 6 0x1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 78) (.exec 0x108be5 (fun s => s.RIP = 0x108be5) (andR32Imm8Effect 0x108be5 3 6 0x1) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.out 0x108be8 (movR64R64Effect 0x108be8 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[0]
    (.letOp (n := 80) (.exec 0x108be8 (fun s => s.RIP = 0x108be8) (movR64R64Effect 0x108be8 8 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 81) (.out 0x108beb (notR64Effect 0x108beb 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 82) (.exec 0x108beb (fun s => s.RIP = 0x108beb) (notR64Effect 0x108beb 8) (Reg.operands [.gpr 8] [])) #v[79]
    (.letOp (n := 83) (.out 0x108bee (addR64R64Effect 0x108bee 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[81, 77]
    (.letOp (n := 84) (.exec 0x108bee (fun s => s.RIP = 0x108bee) (addR64R64Effect 0x108bee 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[81, 77]
    (.letOp (n := 85) (.out 0x108bf1 (xorR64R64Effect 0x108bf1 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[83, 0]
    (.letOp (n := 86) (.exec 0x108bf1 (fun s => s.RIP = 0x108bf1) (xorR64R64Effect 0x108bf1 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[83, 0]
    (.letOp (n := 87) (.out 0x108bf4 (movzxR32M8Effect 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 88) (.exec 0x108bf4 (LoadPre 0x108bf4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x108bf4 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x108bf4 6 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x108bfa (negR64Effect 0x108bfa 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[87]
    (.letOp (n := 90) (.exec 0x108bfa (fun s => s.RIP = 0x108bfa) (negR64Effect 0x108bfa 13) (Reg.operands [.gpr 13] [])) #v[87]
    (.letOp (n := 91) (.out 0x108bfd (andR64R64Effect 0x108bfd 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x108bfd (fun s => s.RIP = 0x108bfd) (andR64R64Effect 0x108bfd 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[89, 85]
    (b_l108bc1_1))))))))))))))))))))))))))))))))))))))))

def bytes_l108bc1 : List UInt8 :=
  [0x4D, 0x31, 0xEA, 0x48, 0xF7, 0xDF, 0x4C, 0x21, 0xD7, 0x4C, 0x31, 0xEF, 0x4C, 0x31, 0xDD, 0x49,
    0xF7, 0xDE, 0x49, 0x21, 0xEE, 0x4D, 0x31, 0xDE, 0x4D, 0x31, 0xE0, 0x49, 0xF7, 0xDF, 0x4D, 0x21,
    0xC7, 0x4D, 0x31, 0xE7, 0x83, 0xE6, 0x01, 0x49, 0x89, 0xC0, 0x49, 0xF7, 0xD0, 0x49, 0x01, 0xF0,
    0x49, 0x31, 0xC0, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10, 0x49, 0xF7, 0xDD, 0x4D, 0x21, 0xC5] ++ bytes_l108bc1_1

theorem code_l108bc1 : ∀ x ∈ codeRange 0x108bc1 bytes_l108bc1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8bc1 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108bc1_1

@[cfg_block] def b_l108df9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108df9 (movR32Imm32Effect 0x108df9 5 6 0x1b) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x108df9 (fun s => s.RIP = 0x108df9) (movR32Imm32Effect 0x108df9 5 6 0x1b) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108dfe (movR64Imm32Effect 0x108dfe 7 0x202b38) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x108dfe (fun s => s.RIP = 0x108dfe) (movR64Imm32Effect 0x108dfe 7 0x202b38) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108e05 (movR64Imm32Effect 0x108e05 2 0x202b58) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108e05 (fun s => s.RIP = 0x108e05) (movR64Imm32Effect 0x108e05 2 0x202b58) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108e0c (callEffect (fun _ => 0x129560) 0x108e11) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108e0c (PushPre 0x108e0c 5) (callEffect (fun _ => 0x129560) 0x108e11) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108e11⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l108e11, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108df9 : List UInt8 :=
  [0xBE, 0x1B, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x38, 0x2B, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0x58,
    0x2B, 0x20, 0x00, 0xE8, 0x4F, 0x07, 0x02, 0x00]

theorem code_l108df9 : ∀ x ∈ codeRange 0x108df9 bytes_l108df9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8df9 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e11 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108e11 (movR32Imm32Effect 0x108e11 5 7 0x4) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x108e11 (fun s => s.RIP = 0x108e11) (movR32Imm32Effect 0x108e11 5 7 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x108e16 (movR32Imm32Effect 0x108e16 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 56) (.exec 0x108e16 (fun s => s.RIP = 0x108e16) (movR32Imm32Effect 0x108e16 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x108e1b (movR64Imm32Effect 0x108e1b 2 0x202b20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x108e1b (fun s => s.RIP = 0x108e1b) (movR64Imm32Effect 0x108e1b 2 0x202b20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x108e22 (callEffect (fun _ => 0x1295f2) 0x108e27) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x108e22 (PushPre 0x108e22 5) (callEffect (fun _ => 0x1295f2) 0x108e27) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x108e27⟩) #v[]
    (.terminate (.call ⟨.l1295f2, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 55), (7, 53)] 62⟩ { target := .l108e27, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l108e11 : List UInt8 :=
  [0xBF, 0x04, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC2, 0x20, 0x2B, 0x20,
    0x00, 0xE8, 0xCB, 0x07, 0x02, 0x00]

theorem code_l108e11 : ∀ x ∈ codeRange 0x108e11 bytes_l108e11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8e11 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e27 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x108e27 (fun s => s.RIP = 0x108e27) (fun _ => nopEffect 0x108e27 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108e30, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l108e27 : List UInt8 :=
  [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l108e27 : ∀ x ∈ codeRange 0x108e27 bytes_l108e27, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8e27 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e30_2 : Block Op Label signature Reg.count 112 :=
  .letOp (n := 112) (.exec 0x108f23 (StorePre 0x108f23 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x108f23 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f23 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 113) (.out 0x108f2f (movR64M64Effect 0x108f2f 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 114) (.exec 0x108f2f (LoadPre 0x108f2f (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x108f2f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f2f 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 115) (.exec 0x108f33 (StorePre 0x108f33 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x108f33 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f33 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 65]
    (.letOp (n := 116) (.out 0x108f3b (movR64M64Effect 0x108f3b 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 117) (.exec 0x108f3b (LoadPre 0x108f3b (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x108f3b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f3b 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 118) (.exec 0x108f3f (StorePre 0x108f3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x108f3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f3f 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x108f47 (movR64M64Effect 0x108f47 0 (.base 8 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 120) (.exec 0x108f47 (LoadPre 0x108f47 (fun s => AddrMode.addr (.base 8 .none) s (0x108f47 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108f47 0 (.base 8 .none)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 121) (.out 0x108f4a (movR64M64Effect 0x108f4a 1 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[8]
    (.letOp (n := 122) (.exec 0x108f4a (LoadPre 0x108f4a (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x108f4a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108f4a 1 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 123) (.exec 0x108f4e (StorePre 0x108f4e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x108f4e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f4e 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[121, 65]
    (.letOp (n := 124) (.exec 0x108f56 (StorePre 0x108f56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x108f56 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108f56 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[119, 65]
    (.letOp (n := 125) (.exec 0x108f5e (StorePre 0x108f5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x108f5e + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108f5e (.sib 4 none 0 (.d32 0x118)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 126) (.out 0x108f66 (movR32Imm32Effect 0x108f66 5 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 127) (.exec 0x108f66 (fun s => s.RIP = 0x108f66) (movR32Imm32Effect 0x108f66 5 5 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 128) (.out 0x108f6b (movR32Imm32Effect 0x108f6b 5 2 0x24f) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 129) (.exec 0x108f6b (fun s => s.RIP = 0x108f6b) (movR32Imm32Effect 0x108f6b 5 2 0x24f) (Reg.operands [] [])) #v[]
    (.letOp (n := 130) (.out 0x108f70 (leaR64Effect 0x108f70 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 131) (.exec 0x108f70 (fun s => s.RIP = 0x108f70) (leaR64Effect 0x108f70 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.terminate (.br ⟨.l1091e4, RegMap.args [(0, 119), (1, 121), (2, 128), (3, 3), (4, 65), (5, 126), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 130), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 132⟩)))))))))))))))))))))

def bytes_l108e30_2 : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x18,
    0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x40, 0x10, 0x48, 0x89, 0x84, 0x24,
    0x08, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x00, 0x49, 0x8B, 0x48, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x00,
    0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0x18, 0x01,
    0x00, 0x00, 0x00, 0xBD, 0x01, 0x00, 0x00, 0x00, 0xBA, 0x4F, 0x02, 0x00, 0x00, 0x4C, 0x8D, 0x74,
    0x24, 0x10, 0xE9, 0x6A, 0x02, 0x00, 0x00]

theorem code_l108e30_2 : ∀ x ∈ codeRange 0x108f23 bytes_l108e30_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f23 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108e30_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x108e90 (StorePre 0x108e90 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x108e90 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e90 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 65]
    (.letOp (n := 87) (.out 0x108e98 (movR64M64Effect 0x108e98 0 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 88) (.exec 0x108e98 (LoadPre 0x108e98 (fun s => AddrMode.addr (.base 2 .none) s (0x108e98 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e98 0 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 89) (.exec 0x108e9b (StorePre 0x108e9b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x108e9b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e9b 2 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 90) (.out 0x108ea3 (movR64M64Effect 0x108ea3 1 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 91) (.exec 0x108ea3 (LoadPre 0x108ea3 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x108ea3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ea3 1 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 92) (.exec 0x108ea7 (StorePre 0x108ea7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x108ea7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ea7 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[90, 65]
    (.letOp (n := 93) (.exec 0x108eaf (StorePre 0x108eaf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x108eaf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108eaf 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 65]
    (.letOp (n := 94) (.exec 0x108eb4 (StorePre 0x108eb4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x108eb4 + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eb4 (.sib 4 none 0 (.d32 0x98)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.out 0x108ebc (movR64M64Effect 0x108ebc 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 96) (.exec 0x108ebc (LoadPre 0x108ebc (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108ebc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ebc 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 97) (.exec 0x108ec0 (StorePre 0x108ec0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x108ec0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ec0 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 65]
    (.letOp (n := 98) (.out 0x108ec8 (movR64M64Effect 0x108ec8 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 99) (.exec 0x108ec8 (LoadPre 0x108ec8 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108ec8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ec8 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 100) (.exec 0x108ecc (StorePre 0x108ecc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x108ecc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ecc 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 65]
    (.letOp (n := 101) (.out 0x108ed4 (movR64M64Effect 0x108ed4 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 102) (.exec 0x108ed4 (LoadPre 0x108ed4 (fun s => AddrMode.addr (.base 6 .none) s (0x108ed4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108ed4 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 103) (.out 0x108ed7 (movR64M64Effect 0x108ed7 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 104) (.exec 0x108ed7 (LoadPre 0x108ed7 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108ed7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108ed7 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 105) (.exec 0x108edb (StorePre 0x108edb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x108edb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108edb 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[103, 65]
    (.letOp (n := 106) (.exec 0x108ee3 (StorePre 0x108ee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x108ee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ee3 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[101, 65]
    (.letOp (n := 107) (.exec 0x108eeb (StorePre 0x108eeb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x108eeb + BitVec.ofNat 64 8)) 1) (movM8Imm8Effect 0x108eeb (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 108) (.exec 0x108ef3 (StorePre 0x108ef3 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x108ef3 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108ef3 (.sib 4 none 0 (.d32 0xf0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 109) (.exec 0x108eff (StorePre 0x108eff 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x108eff + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108eff (.sib 4 none 0 (.d32 0xe8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 110) (.exec 0x108f0b (StorePre 0x108f0b 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x108f0b + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f0b (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 111) (.exec 0x108f17 (StorePre 0x108f17 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x108f17 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x108f17 (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l108e30_2))))))))))))))))))))))))))

def bytes_l108e30_1 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x02, 0x48, 0x89, 0x94, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x4A, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x44, 0x24, 0x78, 0xC6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18,
    0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x8C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0xC6, 0x84, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00] ++ bytes_l108e30_2

theorem code_l108e30_1 : ∀ x ∈ codeRange 0x108e90 bytes_l108e30_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8e90 147 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e30_2

@[cfg_block] def b_l108e30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108e30 (pushR64Effect 0x108e30 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x108e30 (PushPre 0x108e30 1) (pushR64Effect 0x108e30 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x108e31 (pushR64Effect 0x108e31 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x108e31 (PushPre 0x108e31 2) (pushR64Effect 0x108e31 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x108e33 (pushR64Effect 0x108e33 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x108e33 (PushPre 0x108e33 2) (pushR64Effect 0x108e33 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x108e35 (pushR64Effect 0x108e35 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x108e35 (PushPre 0x108e35 2) (pushR64Effect 0x108e35 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x108e37 (pushR64Effect 0x108e37 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x108e37 (PushPre 0x108e37 2) (pushR64Effect 0x108e37 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x108e39 (pushR64Effect 0x108e39 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x108e39 (PushPre 0x108e39 1) (pushR64Effect 0x108e39 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x108e3a (subR64Imm32Effect 0x108e3a 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x108e3a (fun s => s.RIP = 0x108e3a) (subR64Imm32Effect 0x108e3a 4 0x168) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x108e41 (StorePre 0x108e41 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x108e41 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e41 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 65]
    (.letOp (n := 68) (.exec 0x108e49 (StorePre 0x108e49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x108e49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e49 7 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 69) (.out 0x108e51 (movR64M64Effect 0x108e51 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 70) (.exec 0x108e51 (LoadPre 0x108e51 (fun s => AddrMode.addr (.base 6 .none) s (0x108e51 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x108e51 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x108e54 (StorePre 0x108e54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x108e54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e54 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 72) (.out 0x108e5c (movR64M64Effect 0x108e5c 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 73) (.exec 0x108e5c (LoadPre 0x108e5c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x108e5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e5c 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.exec 0x108e60 (StorePre 0x108e60 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x108e60 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e60 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x108e68 (movR64M64Effect 0x108e68 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x108e68 (LoadPre 0x108e68 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x108e68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e68 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x108e6c (StorePre 0x108e6c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x108e6c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e6c 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 65]
    (.letOp (n := 78) (.out 0x108e74 (movR64M64Effect 0x108e74 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x108e74 (LoadPre 0x108e74 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x108e74 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e74 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.exec 0x108e78 (StorePre 0x108e78 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x108e78 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e78 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 65]
    (.letOp (n := 81) (.out 0x108e80 (movR64M64Effect 0x108e80 0 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 82) (.exec 0x108e80 (LoadPre 0x108e80 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x108e80 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e80 0 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 83) (.exec 0x108e84 (StorePre 0x108e84 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x108e84 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108e84 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.out 0x108e8c (movR64M64Effect 0x108e8c 0 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 85) (.exec 0x108e8c (LoadPre 0x108e8c (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x108e8c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x108e8c 0 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l108e30_1)))))))))))))))))))))))))))))))))

def bytes_l108e30 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x68, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0x40, 0x01, 0x00,
    0x00, 0x48, 0x8B, 0x06, 0x48, 0x89, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x08,
    0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24,
    0x20, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x48, 0x8B, 0x42, 0x18, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x42, 0x10] ++ bytes_l108e30_1

theorem code_l108e30 : ∀ x ∈ codeRange 0x108e30 bytes_l108e30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x8e30 96 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l108e30_1

@[cfg_block] def b_l108f80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108f80 (movR32Imm32Effect 0x108f80 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 54) (.exec 0x108f80 (fun s => s.RIP = 0x108f80) (movR32Imm32Effect 0x108f80 6 12 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x108f86 (StorePre 0x108f86 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108f86 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x108f86 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x108f8f (xorR32R32Effect 0x108f8f 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 57) (.exec 0x108f8f (fun s => s.RIP = 0x108f8f) (xorR32R32Effect 0x108f8f 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 58) (.out 0x108f91 (movR32Imm32Effect 0x108f91 6 15 0x1) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 59) (.exec 0x108f91 (fun s => s.RIP = 0x108f91) (movR32Imm32Effect 0x108f91 6 15 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l108f97, RegMap.args [(3, 56), (4, 4), (5, 5), (12, 53), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l108f80 : List UInt8 :=
  [0x41, 0xBC, 0x01, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x31,
    0xDB, 0x41, 0xBF, 0x01, 0x00, 0x00, 0x00]

theorem code_l108f80 : ∀ x ∈ codeRange 0x108f80 bytes_l108f80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f80 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108f97 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108f97 (movR64R64Effect 0x108f97 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 54) (.exec 0x108f97 (fun s => s.RIP = 0x108f97) (movR64R64Effect 0x108f97 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x108f9a (shrR64Effect 0x108f9a 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x108f9a (fun s => s.RIP = 0x108f9a) (shrR64Effect 0x108f9a 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x108f9e (StorePre 0x108f9e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x108f9e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108f9e 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x108fa3 (StorePre 0x108fa3 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fa3 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fa3 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x108fa7 (leaR64Effect 0x108fa7 13 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x108fa7 (fun s => s.RIP = 0x108fa7) (leaR64Effect 0x108fa7 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x108fac (movR64R64Effect 0x108fac 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 62) (.exec 0x108fac (fun s => s.RIP = 0x108fac) (movR64R64Effect 0x108fac 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x108faf (shrR64Effect 0x108faf 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x108faf (fun s => s.RIP = 0x108faf) (shrR64Effect 0x108faf 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x108fb3 (StorePre 0x108fb3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x108fb3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108fb3 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x108fbb (StorePre 0x108fbb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108fbb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108fbb 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.out 0x108fbf (movR64R64Effect 0x108fbf 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 68) (.exec 0x108fbf (fun s => s.RIP = 0x108fbf) (movR64R64Effect 0x108fbf 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 69) (.out 0x108fc2 (leaR64Effect 0x108fc2 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 70) (.exec 0x108fc2 (fun s => s.RIP = 0x108fc2) (leaR64Effect 0x108fc2 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x108fc7 (leaR64Effect 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x108fc7 (fun s => s.RIP = 0x108fc7) (leaR64Effect 0x108fc7 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x108fcf (movR64R64Effect 0x108fcf 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 74) (.exec 0x108fcf (fun s => s.RIP = 0x108fcf) (movR64R64Effect 0x108fcf 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 75) (.out 0x108fd2 (movR64R64Effect 0x108fd2 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 76) (.exec 0x108fd2 (fun s => s.RIP = 0x108fd2) (movR64R64Effect 0x108fd2 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 77) (.out 0x108fd5 (movR32M32Effect 0x108fd5 14 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 78) (.exec 0x108fd5 (LoadPre 0x108fd5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x108fd5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x108fd5 14 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x108fda (movR32R32Effect 0x108fda 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x108fda (fun s => s.RIP = 0x108fda) (movR32R32Effect 0x108fda 3 9 14) (Reg.operands [.gpr 14] [])) #v[77]
    (.letOp (n := 81) (.out 0x108fdd (callEffect (fun _ => 0x108890) 0x108fe2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x108fdd (PushPre 0x108fdd 5) (callEffect (fun _ => 0x108890) 0x108fe2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x108fe2⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(0, 63), (1, 73), (2, 71), (3, 3), (4, 81), (5, 5), (6, 69), (7, 67), (8, 75), (9, 79), (12, 12), (13, 59), (14, 77), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l108fe2, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l108f97 : List UInt8 :=
  [0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x60, 0x88, 0x44, 0x24, 0x07,
    0x4C, 0x8D, 0x6C, 0x24, 0x07, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x84, 0x24,
    0x50, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07, 0x4C, 0x89, 0xF7, 0x48, 0x8D, 0x74, 0x24, 0x78,
    0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF9, 0x49, 0x89, 0xD8, 0x44, 0x8B,
    0x74, 0x24, 0x74, 0x45, 0x89, 0xF1, 0xE8, 0xAE, 0xF8, 0xFF, 0xFF]

theorem code_l108f97 : ∀ x ∈ codeRange 0x108f97 bytes_l108f97, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8f97 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l108fe2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x108fe2 (movR64M64Effect 0x108fe2 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x108fe2 (LoadPre 0x108fe2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fe2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x108fe2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x108fe7 (movR64R64Effect 0x108fe7 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x108fe7 (fun s => s.RIP = 0x108fe7) (movR64R64Effect 0x108fe7 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x108fea (movR64R64Effect 0x108fea 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 58) (.exec 0x108fea (fun s => s.RIP = 0x108fea) (movR64R64Effect 0x108fea 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.exec 0x108fed (StorePre 0x108fed 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x108fed + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x108fed 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 60) (.out 0x108ff2 (shrR64Effect 0x108ff2 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 61) (.exec 0x108ff2 (fun s => s.RIP = 0x108ff2) (shrR64Effect 0x108ff2 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 62) (.exec 0x108ff6 (StorePre 0x108ff6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x108ff6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x108ff6 2 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.exec 0x108ffe (StorePre 0x108ffe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x108ffe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x108ffe 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 64) (.exec 0x109002 (fun s => s.RIP = 0x109002) (movR64R64Effect 0x109002 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 65) (.out 0x109005 (movR64R64Effect 0x109005 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 66) (.exec 0x109005 (fun s => s.RIP = 0x109005) (movR64R64Effect 0x109005 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x109008 (movR64R64Effect 0x109008 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[12]
    (.letOp (n := 68) (.exec 0x109008 (fun s => s.RIP = 0x109008) (movR64R64Effect 0x109008 8 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 69) (.exec 0x10900b (StorePre 0x10900b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10900b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10900b 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 70) (.out 0x109010 (shrR64Effect 0x109010 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 71) (.exec 0x109010 (fun s => s.RIP = 0x109010) (shrR64Effect 0x109010 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 72) (.exec 0x109014 (StorePre 0x109014 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109014 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x109014 5 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x109019 (leaR64Effect 0x109019 12 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x109019 (fun s => s.RIP = 0x109019) (leaR64Effect 0x109019 12 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x10901e (movR64R64Effect 0x10901e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 76) (.exec 0x10901e (fun s => s.RIP = 0x10901e) (movR64R64Effect 0x10901e 7 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 77) (.out 0x109021 (leaR64Effect 0x109021 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x109021 (fun s => s.RIP = 0x109021) (leaR64Effect 0x109021 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x109026 (leaR64Effect 0x109026 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 80) (.exec 0x109026 (fun s => s.RIP = 0x109026) (leaR64Effect 0x109026 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x10902e (movR32R32Effect 0x10902e 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[14]
    (.letOp (n := 82) (.exec 0x10902e (fun s => s.RIP = 0x10902e) (movR32R32Effect 0x10902e 3 9 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 83) (.out 0x109031 (callEffect (fun _ => 0x108890) 0x109036) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x109031 (PushPre 0x109031 5) (callEffect (fun _ => 0x108890) 0x109036) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x109036⟩) #v[]
    (.terminate (.call ⟨.l108890, RegMap.args [(1, 57), (2, 79), (3, 3), (4, 83), (5, 5), (6, 77), (7, 75), (8, 67), (9, 81), (12, 73), (13, 70), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l109036, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l108fe2 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89, 0xC2, 0x48, 0x89, 0xC1, 0x48, 0x89, 0x44, 0x24, 0x08,
    0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x94, 0x24, 0x58, 0x01, 0x00, 0x00, 0x88, 0x54, 0x24, 0x07,
    0x4C, 0x89, 0xE8, 0x4D, 0x89, 0xE5, 0x4D, 0x89, 0xE0, 0x4C, 0x89, 0x64, 0x24, 0x68, 0x49, 0xC1,
    0xED, 0x3F, 0x44, 0x88, 0x6C, 0x24, 0x07, 0x4C, 0x8D, 0x64, 0x24, 0x38, 0x4C, 0x89, 0xE7, 0x48,
    0x8D, 0x74, 0x24, 0x78, 0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x45, 0x89, 0xF1, 0xE8,
    0x5A, 0xF8, 0xFF, 0xFF]

theorem code_l108fe2 : ∀ x ∈ codeRange 0x108fe2 bytes_l108fe2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8fe2 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109036_1 : Block Op Label signature Reg.count 83 :=
  .letOp (n := 83) (.out 0x1090b4 (movR64M64Effect 0x1090b4 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x1090b4 (LoadPre 0x1090b4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1090b4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090b4 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.exec 0x1090b9 (StorePre 0x1090b9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090b9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090b9 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 86) (.exec 0x1090bd (fun s => s.RIP = 0x1090bd) (leaR64Effect 0x1090bd 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x1090c2 (movR64M64Effect 0x1090c2 1 (.sib 4 none 0 (.d32 0x150))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x1090c2 (LoadPre 0x1090c2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1090c2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090c2 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x1090ca (StorePre 0x1090ca 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1090ca + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1090ca 4 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.out 0x1090ce (leaR64Effect 0x1090ce 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 91) (.exec 0x1090ce (fun s => s.RIP = 0x1090ce) (leaR64Effect 0x1090ce 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x1090d3 (leaR64Effect 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 93) (.exec 0x1090d3 (fun s => s.RIP = 0x1090d3) (leaR64Effect 0x1090d3 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.out 0x1090db (leaR64Effect 0x1090db 2 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 95) (.exec 0x1090db (fun s => s.RIP = 0x1090db) (leaR64Effect 0x1090db 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x1090e3 (movR64R64Effect 0x1090e3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 97) (.exec 0x1090e3 (fun s => s.RIP = 0x1090e3) (movR64R64Effect 0x1090e3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 98) (.out 0x1090e6 (movR64R64Effect 0x1090e6 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 99) (.exec 0x1090e6 (fun s => s.RIP = 0x1090e6) (movR64R64Effect 0x1090e6 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 100) (.out 0x1090e9 (movR32R32Effect 0x1090e9 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 101) (.exec 0x1090e9 (fun s => s.RIP = 0x1090e9) (movR32R32Effect 0x1090e9 3 15 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 102) (.out 0x1090ec (movR32R32Effect 0x1090ec 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[14]
    (.letOp (n := 103) (.exec 0x1090ec (fun s => s.RIP = 0x1090ec) (movR32R32Effect 0x1090ec 3 9 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 104) (.out 0x1090ef (movR64M64Effect 0x1090ef 14 (.sib 4 none 0 (.d32 0x148))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 105) (.exec 0x1090ef (LoadPre 0x1090ef (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1090ef + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090ef 14 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x1090f7 (pushR64Effect 0x1090f7 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 104]
    (.letOp (n := 107) (.exec 0x1090f7 (PushPre 0x1090f7 2) (pushR64Effect 0x1090f7 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 104]
    (.letOp (n := 108) (.out 0x1090f9 (movR64M64Effect 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[106]
    (.letOp (n := 109) (.exec 0x1090f9 (LoadPre 0x1090f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1090f9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1090f9 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[106]
    (.letOp (n := 110) (.out 0x109101 (pushR64Effect 0x109101 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[106, 108]
    (.letOp (n := 111) (.exec 0x109101 (PushPre 0x109101 1) (pushR64Effect 0x109101 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[106, 108]
    (.letOp (n := 112) (.out 0x109102 (callEffect (fun _ => 0x108980) 0x109107) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[110]
    (.letOp (n := 113) (.exec 0x109102 (PushPre 0x109102 5) (callEffect (fun _ => 0x108980) 0x109107) (Reg.operands [.gpr 4] [])) #v[110]
    (.letOp (n := 114) (.const ⟨64, 0x109107⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(1, 96), (2, 94), (3, 108), (4, 112), (5, 5), (6, 92), (7, 90), (8, 98), (9, 102), (12, 12), (13, 13), (14, 104), (15, 100), (22, 22), (39, 39), (50, 50), (51, 51)] 115⟩ { target := .l109107, kept := #v[], arity := rfl, guard := some (Fin.last 114) })))))))))))))))))))))))))))))))))

def bytes_l109036_1 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x60, 0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x48, 0x8B,
    0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x07, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x48,
    0x8D, 0xB4, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xF9, 0x49, 0x89, 0xD8, 0x45, 0x89, 0xF7, 0x45, 0x89, 0xF1, 0x4C, 0x8B, 0xB4, 0x24, 0x48,
    0x01, 0x00, 0x00, 0x41, 0x56, 0x48, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x53, 0xE8, 0x79,
    0xF8, 0xFF, 0xFF]

theorem code_l109036_1 : ∀ x ∈ codeRange 0x1090b4 bytes_l109036_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x90b4 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109036 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109036 (movR64M64Effect 0x109036 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109036 (LoadPre 0x109036 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109036 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109036 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10903b (StorePre 0x10903b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10903b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10903b 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x109043 (movR64M64Effect 0x109043 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x109043 (LoadPre 0x109043 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109043 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109043 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x109048 (StorePre 0x109048 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109048 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109048 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x109050 (movR64M64Effect 0x109050 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x109050 (LoadPre 0x109050 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109050 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109050 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x109055 (StorePre 0x109055 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109055 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109055 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10905d (movR64M64Effect 0x10905d 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x10905d (LoadPre 0x10905d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10905d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10905d 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x109062 (movR64M64Effect 0x109062 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x109062 (LoadPre 0x109062 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109062 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109062 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x109067 (StorePre 0x109067 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109067 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109067 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x10906f (StorePre 0x10906f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10906f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10906f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.out 0x109074 (movR64M64Effect 0x109074 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 69) (.exec 0x109074 (LoadPre 0x109074 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109074 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109074 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.out 0x109078 (movR64M64Effect 0x109078 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 71) (.exec 0x109078 (LoadPre 0x109078 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109078 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109078 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.exec 0x10907d (StorePre 0x10907d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10907d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10907d 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 73) (.exec 0x109085 (StorePre 0x109085 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x109085 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109085 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 74) (.out 0x10908d (movR64M64Effect 0x10908d 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 75) (.exec 0x10908d (LoadPre 0x10908d (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x10908d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10908d 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 76) (.exec 0x109092 (StorePre 0x109092 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x109092 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109092 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x10909a (movR64M64Effect 0x10909a 0 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 78) (.exec 0x10909a (LoadPre 0x10909a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10909a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10909a 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 79) (.exec 0x10909f (StorePre 0x10909f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10909f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10909f 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x1090a7 (movR64M64Effect 0x1090a7 0 (.sib 12 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 81) (.exec 0x1090a7 (LoadPre 0x1090a7 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1090a7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1090a7 0 (.sib 12 none 0 (.d8 0x20))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 82) (.exec 0x1090ac (StorePre 0x1090ac 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1090ac + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1090ac 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (b_l109036_1))))))))))))))))))))))))))))))

def bytes_l109036 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48,
    0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x4C, 0x24,
    0x18, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x78, 0x49, 0x8B,
    0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24,
    0xB8, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84, 0x24, 0xC0, 0x00, 0x00,
    0x00, 0x49, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00] ++ bytes_l109036_1

theorem code_l109036 : ∀ x ∈ codeRange 0x109036 bytes_l109036, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9036 126 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109036_1

@[cfg_block] def b_l109107 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109107 (addR64Imm8Effect 0x109107 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x109107 (fun s => s.RIP = 0x109107) (addR64Imm8Effect 0x109107 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10910b (movR64M64Effect 0x10910b 0 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10910b (LoadPre 0x10910b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x10910b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10910b 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109113 (StorePre 0x109113 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109113 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109113 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.exec 0x109117 (fun s => s.RIP = 0x109117) (leaR64Effect 0x109117 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x10911c (StorePre 0x10911c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10911c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10911c 5 13 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 53]
    (.letOp (n := 60) (.out 0x109121 (movR64R64Effect 0x109121 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 61) (.exec 0x109121 (fun s => s.RIP = 0x109121) (movR64R64Effect 0x109121 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 62) (.out 0x109124 (leaR64Effect 0x109124 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 63) (.exec 0x109124 (fun s => s.RIP = 0x109124) (leaR64Effect 0x109124 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.out 0x10912c (leaR64Effect 0x10912c 2 (.sib 4 none 0 (.d32 0xf8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 65) (.exec 0x10912c (fun s => s.RIP = 0x10912c) (leaR64Effect 0x10912c 2 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x109134 (movR64M64Effect 0x109134 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x109134 (LoadPre 0x109134 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109134 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109134 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.out 0x109139 (movR64M64Effect 0x109139 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 69) (.exec 0x109139 (LoadPre 0x109139 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109139 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109139 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 70) (.out 0x10913e (movR32R32Effect 0x10913e 3 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 71) (.exec 0x10913e (fun s => s.RIP = 0x10913e) (movR32R32Effect 0x10913e 3 9 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 72) (.out 0x109141 (pushR64Effect 0x109141 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 73) (.exec 0x109141 (PushPre 0x109141 2) (pushR64Effect 0x109141 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 74) (.out 0x109143 (leaR64Effect 0x109143 14 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[72]
    (.letOp (n := 75) (.exec 0x109143 (fun s => s.RIP = 0x109143) (leaR64Effect 0x109143 14 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 76) (.out 0x109148 (pushR64Effect 0x109148 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[72, 3]
    (.letOp (n := 77) (.exec 0x109148 (PushPre 0x109148 1) (pushR64Effect 0x109148 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[72, 3]
    (.letOp (n := 78) (.out 0x109149 (callEffect (fun _ => 0x108980) 0x10914e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[76]
    (.letOp (n := 79) (.exec 0x109149 (PushPre 0x109149 5) (callEffect (fun _ => 0x108980) 0x10914e) (Reg.operands [.gpr 4] [])) #v[76]
    (.letOp (n := 80) (.const ⟨64, 0x10914e⟩) #v[]
    (.terminate (.call ⟨.l108980, RegMap.args [(1, 66), (2, 64), (3, 3), (4, 78), (5, 5), (6, 62), (7, 60), (8, 68), (9, 70), (12, 12), (13, 13), (14, 74), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l10914e, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l109107 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x84, 0x24, 0x58, 0x01, 0x00, 0x00, 0x88, 0x44, 0x24, 0x07,
    0x48, 0x8D, 0x44, 0x24, 0x07, 0x44, 0x88, 0x6C, 0x24, 0x07, 0x4C, 0x89, 0xE7, 0x48, 0x8D, 0xB4,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x94, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C,
    0x24, 0x08, 0x4C, 0x8B, 0x44, 0x24, 0x68, 0x45, 0x89, 0xF9, 0x41, 0x56, 0x4C, 0x8D, 0x74, 0x24,
    0x18, 0x53, 0xE8, 0x32, 0xF8, 0xFF, 0xFF]

theorem code_l109107 : ∀ x ∈ codeRange 0x109107 bytes_l109107, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9107 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10914e_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.exec 0x1091cb (StorePre 0x1091cb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1091cb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091cb 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[82, 53]
    (.letOp (n := 85) (.out 0x1091d3 (movR64M64Effect 0x1091d3 2 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 86) (.exec 0x1091d3 (LoadPre 0x1091d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091d3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1091d3 2 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 87) (.out 0x1091db (subR32R32Effect 0x1091db 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[85, 15]
    (.letOp (n := 88) (.out 0x1091db (subR32R32Effect 0x1091db 3 2 15) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 15] []) (.flag .ZF)) #v[85, 15]
    (.letOp (n := 89) (.exec 0x1091db (fun s => s.RIP = 0x1091db) (subR32R32Effect 0x1091db 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[85, 15]
    (.letOp (n := 90) (.pure (condOp 4)) #v[88]
    (.terminate (.condBr (Fin.last 90) ⟨.l1093fe, RegMap.args [(0, 82), (1, 72), (2, 87), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩ ⟨.l1091e4, RegMap.args [(0, 82), (1, 72), (2, 87), (3, 3), (4, 53), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 88), (22, 22), (39, 39), (50, 50), (51, 51)] 91⟩))))))))

def bytes_l10914e_1 : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00,
    0x44, 0x29, 0xFA, 0x0F, 0x84, 0x1A, 0x02, 0x00, 0x00]

theorem code_l10914e_1 : ∀ x ∈ codeRange 0x1091cb bytes_l10914e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x91cb 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10914e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10914e (addR64Imm8Effect 0x10914e 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10914e (fun s => s.RIP = 0x10914e) (addR64Imm8Effect 0x10914e 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109152 (movR64M64Effect 0x109152 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x109152 (LoadPre 0x109152 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109152 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109152 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x109157 (StorePre 0x109157 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x109157 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109157 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 53]
    (.letOp (n := 58) (.out 0x10915f (movR64M64Effect 0x10915f 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x10915f (LoadPre 0x10915f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10915f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10915f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 60) (.exec 0x109164 (StorePre 0x109164 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x109164 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109164 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 53]
    (.letOp (n := 61) (.out 0x10916c (movR64M64Effect 0x10916c 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x10916c (LoadPre 0x10916c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10916c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10916c 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.exec 0x109171 (StorePre 0x109171 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x109171 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109171 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 53]
    (.letOp (n := 64) (.out 0x109179 (movR64M64Effect 0x109179 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x109179 (LoadPre 0x109179 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109179 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109179 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 66) (.out 0x10917e (movR64M64Effect 0x10917e 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 67) (.exec 0x10917e (LoadPre 0x10917e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10917e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10917e 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 68) (.exec 0x109183 (StorePre 0x109183 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x109183 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109183 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 53]
    (.letOp (n := 69) (.exec 0x10918b (StorePre 0x10918b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10918b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10918b 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 53]
    (.letOp (n := 70) (.out 0x109193 (movR64M64Effect 0x109193 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 71) (.exec 0x109193 (LoadPre 0x109193 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x109193 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109193 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 72) (.out 0x109197 (movR64M64Effect 0x109197 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 73) (.exec 0x109197 (LoadPre 0x109197 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x109197 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109197 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 74) (.exec 0x10919c (StorePre 0x10919c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10919c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10919c 0 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 53]
    (.letOp (n := 75) (.exec 0x1091a4 (StorePre 0x1091a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x1091a4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091a4 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 53]
    (.letOp (n := 76) (.out 0x1091ac (movR64M64Effect 0x1091ac 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 77) (.exec 0x1091ac (LoadPre 0x1091ac (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1091ac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091ac 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 78) (.exec 0x1091b1 (StorePre 0x1091b1 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x1091b1 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091b1 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 53]
    (.letOp (n := 79) (.out 0x1091b9 (movR64M64Effect 0x1091b9 0 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 80) (.exec 0x1091b9 (LoadPre 0x1091b9 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x1091b9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091b9 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 81) (.exec 0x1091be (StorePre 0x1091be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x1091be + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091be 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 53]
    (.letOp (n := 82) (.out 0x1091c6 (movR64M64Effect 0x1091c6 0 (.sib 12 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 83) (.exec 0x1091c6 (LoadPre 0x1091c6 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x20)) s (0x1091c6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1091c6 0 (.sib 12 none 0 (.d8 0x20))) (Reg.operands [.gpr 12] [])) #v[12]
    (b_l10914e_1)))))))))))))))))))))))))))))))

def bytes_l10914e : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10,
    0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84,
    0x24, 0xD0, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89,
    0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x49, 0x8B,
    0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x18,
    0x48, 0x89, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x49, 0x8B, 0x44, 0x24, 0x20] ++ bytes_l10914e_1

theorem code_l10914e : ∀ x ∈ codeRange 0x10914e bytes_l10914e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x914e 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10914e_1

@[cfg_block] def b_l1091e4_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x10923b (StorePre 0x10923b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x10923b + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10923b 9 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 91) (.pure (condOp 4)) #v[76]
    (.terminate (.condBr (Fin.last 91) ⟨.l108f80, RegMap.args [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩ ⟨.l109246, RegMap.args [(0, 83), (1, 87), (2, 78), (3, 3), (4, 4), (5, 5), (6, 85), (9, 75), (14, 14), (19, 76), (22, 22), (39, 39), (50, 50), (51, 51)] 92⟩)))

def bytes_l1091e4_1 : List UInt8 :=
  [0x44, 0x89, 0x4C, 0x24, 0x74, 0x0F, 0x84, 0x3A, 0xFD, 0xFF, 0xFF]

theorem code_l1091e4_1 : ∀ x ∈ codeRange 0x10923b bytes_l1091e4_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x923b 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1091e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1091e4 (movR32R32Effect 0x1091e4 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[2]
    (.letOp (n := 54) (.exec 0x1091e4 (fun s => s.RIP = 0x1091e4) (movR32R32Effect 0x1091e4 2 0 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1091e6 (notR32Effect 0x1091e6 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1091e6 (fun s => s.RIP = 0x1091e6) (notR32Effect 0x1091e6 2 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1091e8 (leaR32Effect 0x1091e8 3 1 (.base 2 (.d8 0xc2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 58) (.exec 0x1091e8 (fun s => s.RIP = 0x1091e8) (leaR32Effect 0x1091e8 3 1 (.base 2 (.d8 0xc2))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x1091eb (andR32R32Effect 0x1091eb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x1091eb (fun s => s.RIP = 0x1091eb) (andR32R32Effect 0x1091eb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x1091ed (shrR32Effect 0x1091ed 3 1 31) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x1091ed (fun s => s.RIP = 0x1091ed) (shrR32Effect 0x1091ed 3 1 31) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x1091f0 (StorePre 0x1091f0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1091f0 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1091f4 (movzxR32M8Effect 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 65) (.exec 0x1091f4 (LoadPre 0x1091f4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1091f4 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1091f4 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1091f9 (negR32Effect 0x1091f9 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[64]
    (.letOp (n := 67) (.exec 0x1091f9 (fun s => s.RIP = 0x1091f9) (negR32Effect 0x1091f9 2 0) (Reg.operands [.gpr 0] [])) #v[64]
    (.letOp (n := 68) (.exec 0x1091fb (StorePre 0x1091fb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x1091fb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1091fb 2 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 69) (.out 0x109203 (movR32R32Effect 0x109203 3 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 70) (.exec 0x109203 (fun s => s.RIP = 0x109203) (movR32R32Effect 0x109203 3 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x109206 (xorR32Imm8Effect 0x109206 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 72) (.exec 0x109206 (fun s => s.RIP = 0x109206) (xorR32Imm8Effect 0x109206 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x10920a (andR32R32Effect 0x10920a 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[71, 66]
    (.letOp (n := 74) (.exec 0x10920a (fun s => s.RIP = 0x10920a) (andR32R32Effect 0x10920a 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[71, 66]
    (.letOp (n := 75) (.out 0x10920d (xorR32Imm8Effect 0x10920d 4 9 0x3e) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[73]
    (.letOp (n := 76) (.out 0x10920d (xorR32Imm8Effect 0x10920d 4 9 0x3e) (EffectPart.reads (.flag .ZF) [.gpr 9] []) (.flag .ZF)) #v[73]
    (.letOp (n := 77) (.exec 0x10920d (fun s => s.RIP = 0x10920d) (xorR32Imm8Effect 0x10920d 4 9 0x3e) (Reg.operands [.gpr 9] [])) #v[73]
    (.letOp (n := 78) (.out 0x109211 (movR64M64Effect 0x109211 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x109211 (LoadPre 0x109211 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109211 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109211 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x109216 (movzxR32M8Effect 0x109216 8 0 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 81) (.exec 0x109216 (LoadPre 0x109216 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109216 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x109216 8 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.exec 0x10921e (StorePre 0x10921e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10921e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10921e 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x109222 (movzxR32M8Effect 0x109222 5 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x109222 (LoadPre 0x109222 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109222 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109222 5 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x109227 (movR64M64Effect 0x109227 6 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 86) (.exec 0x109227 (LoadPre 0x109227 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x109227 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109227 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x10922f (movzxR32M8Effect 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 88) (.exec 0x10922f (LoadPre 0x10922f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10922f + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10922f 8 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.exec 0x109237 (StorePre 0x109237 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109237 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109237 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 4]
    (b_l1091e4_1)))))))))))))))))))))))))))))))))))))

def bytes_l1091e4 : List UInt8 :=
  [0x89, 0xD0, 0xF7, 0xD0, 0x8D, 0x4A, 0xC2, 0x21, 0xC1, 0xC1, 0xE9, 0x1F, 0x88, 0x4C, 0x24, 0x10,
    0x0F, 0xB6, 0x44, 0x24, 0x10, 0xF7, 0xD8, 0x48, 0x89, 0x94, 0x24, 0x60, 0x01, 0x00, 0x00, 0x41,
    0x89, 0xD1, 0x41, 0x83, 0xF1, 0x3E, 0x41, 0x21, 0xC1, 0x41, 0x83, 0xF1, 0x3E, 0x48, 0x8B, 0x54,
    0x24, 0x78, 0x0F, 0xB6, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x10, 0x0F, 0xB6,
    0x44, 0x24, 0x10, 0x48, 0x8B, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x8C, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l1091e4_1

theorem code_l1091e4 : ∀ x ∈ codeRange 0x1091e4 bytes_l1091e4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x91e4 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1091e4_1

@[cfg_block] def b_l109246_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.exec 0x109295 (fun s => s.RIP = 0x109295) (fun _ => nopEffect 0x109295 11) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1092a0, RegMap.args [(0, 83), (1, 69), (2, 71), (4, 4), (5, 5), (6, 87), (7, 85), (8, 55), (9, 9), (12, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))

def bytes_l109246_1 : List UInt8 :=
  [0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l109246_1 : ∀ x ∈ codeRange 0x109295 bytes_l109246_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9295 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109246 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109246 (movzxR32M8Effect 0x109246 5 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x109246 (LoadPre 0x109246 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109246 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109246 5 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10924b (movR64Imm64Effect 0x10924b 8 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x10924b (fun s => s.RIP = 0x10924b) (movR64Imm64Effect 0x10924b 8 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x109255 (andR64R64Effect 0x109255 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[6, 55]
    (.letOp (n := 58) (.exec 0x109255 (fun s => s.RIP = 0x109255) (andR64R64Effect 0x109255 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[6, 55]
    (.letOp (n := 59) (.out 0x109258 (movR64R64Effect 0x109258 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x109258 (fun s => s.RIP = 0x109258) (movR64R64Effect 0x109258 7 6) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x10925b (negR64Effect 0x10925b 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[59]
    (.letOp (n := 62) (.exec 0x10925b (fun s => s.RIP = 0x10925b) (negR64Effect 0x10925b 7) (Reg.operands [.gpr 7] [])) #v[59]
    (.letOp (n := 63) (.out 0x10925e (xorR64R64Effect 0x10925e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[61, 57]
    (.letOp (n := 64) (.exec 0x10925e (fun s => s.RIP = 0x10925e) (xorR64R64Effect 0x10925e 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[61, 57]
    (.letOp (n := 65) (.out 0x109261 (negR64Effect 0x109261 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 66) (.exec 0x109261 (fun s => s.RIP = 0x109261) (negR64Effect 0x109261 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 67) (.out 0x109264 (andR64R64Effect 0x109264 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x109264 (fun s => s.RIP = 0x109264) (andR64R64Effect 0x109264 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x109267 (xorR64R64Effect 0x109267 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[67, 57]
    (.letOp (n := 70) (.exec 0x109267 (fun s => s.RIP = 0x109267) (xorR64R64Effect 0x109267 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[67, 57]
    (.letOp (n := 71) (.out 0x10926a (andR64R64Effect 0x10926a 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 55]
    (.letOp (n := 72) (.exec 0x10926a (fun s => s.RIP = 0x10926a) (andR64R64Effect 0x10926a 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 55]
    (.letOp (n := 73) (.out 0x10926d (movR64R64Effect 0x10926d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x10926d (fun s => s.RIP = 0x10926d) (movR64R64Effect 0x10926d 6 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x109270 (negR64Effect 0x109270 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x109270 (fun s => s.RIP = 0x109270) (negR64Effect 0x109270 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 77) (.out 0x109273 (xorR64R64Effect 0x109273 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[75, 71]
    (.letOp (n := 78) (.exec 0x109273 (fun s => s.RIP = 0x109273) (xorR64R64Effect 0x109273 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[75, 71]
    (.letOp (n := 79) (.out 0x109276 (negR64Effect 0x109276 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 80) (.exec 0x109276 (fun s => s.RIP = 0x109276) (negR64Effect 0x109276 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 81) (.out 0x109279 (andR64R64Effect 0x109279 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x109279 (fun s => s.RIP = 0x109279) (andR64R64Effect 0x109279 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x10927c (xorR64R64Effect 0x10927c 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[81, 71]
    (.letOp (n := 84) (.exec 0x10927c (fun s => s.RIP = 0x10927c) (xorR64R64Effect 0x10927c 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[81, 71]
    (.letOp (n := 85) (.out 0x10927f (movR32Imm32Effect 0x10927f 5 7 0x1) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 86) (.exec 0x10927f (fun s => s.RIP = 0x10927f) (movR32Imm32Effect 0x10927f 5 7 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x109284 (xorR32R32Effect 0x109284 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[77, 77]
    (.letOp (n := 88) (.exec 0x109284 (fun s => s.RIP = 0x109284) (xorR32R32Effect 0x109284 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[77, 77]
    (.letOp (n := 89) (.exec 0x109286 (StorePre 0x109286 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109286 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x109286 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x10928f (movR32Imm32Effect 0x10928f 6 12 0x1) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 91) (.exec 0x10928f (fun s => s.RIP = 0x10928f) (movR32Imm32Effect 0x10928f 6 12 0x1) (Reg.operands [] [])) #v[]
    (b_l109246_1)))))))))))))))))))))))))))))))))))))))

def bytes_l109246 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x4C,
    0x21, 0xC6, 0x48, 0x89, 0xF7, 0x48, 0xF7, 0xDF, 0x48, 0x31, 0xF7, 0x48, 0xF7, 0xD9, 0x48, 0x21,
    0xF9, 0x48, 0x31, 0xF1, 0x4C, 0x21, 0xC2, 0x48, 0x89, 0xD6, 0x48, 0xF7, 0xDE, 0x48, 0x31, 0xD6,
    0x48, 0xF7, 0xD8, 0x48, 0x21, 0xF0, 0x48, 0x31, 0xD0, 0xBF, 0x01, 0x00, 0x00, 0x00, 0x31, 0xF6,
    0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x41, 0xBC, 0x01, 0x00, 0x00, 0x00] ++ bytes_l109246_1

theorem code_l109246 : ∀ x ∈ codeRange 0x109246 bytes_l109246, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9246 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109246_1

@[cfg_block] def b_l1092a0_4 : Block Op Label signature Reg.count 204 :=
  .letOp (n := 204) (.exec 0x1093cf (StorePre 0x1093cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093cf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1093cf 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 205) (.out 0x1093d4 (movR64R64Effect 0x1093d4 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[184]
    (.letOp (n := 206) (.exec 0x1093d4 (fun s => s.RIP = 0x1093d4) (movR64R64Effect 0x1093d4 14 9) (Reg.operands [.gpr 9] [])) #v[184]
    (.letOp (n := 207) (.out 0x1093d7 (movzxR32M8Effect 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 208) (.exec 0x1093d7 (LoadPre 0x1093d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093d7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093d7 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 209) (.out 0x1093dc (negR64Effect 0x1093dc 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[207]
    (.letOp (n := 210) (.exec 0x1093dc (fun s => s.RIP = 0x1093dc) (negR64Effect 0x1093dc 6) (Reg.operands [.gpr 6] [])) #v[207]
    (.letOp (n := 211) (.out 0x1093df (andR64R64Effect 0x1093df 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[209, 196]
    (.letOp (n := 212) (.exec 0x1093df (fun s => s.RIP = 0x1093df) (andR64R64Effect 0x1093df 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[209, 196]
    (.letOp (n := 213) (.out 0x1093e2 (movR32M32Effect 0x1093e2 9 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 214) (.exec 0x1093e2 (LoadPre 0x1093e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1093e2 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1093e2 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 215) (.out 0x1093e7 (addR64R64Effect 0x1093e7 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[149, 211]
    (.letOp (n := 216) (.exec 0x1093e7 (fun s => s.RIP = 0x1093e7) (addR64R64Effect 0x1093e7 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[149, 211]
    (.letOp (n := 217) (.out 0x1093ea (movR64R64Effect 0x1093ea 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[200]
    (.letOp (n := 218) (.exec 0x1093ea (fun s => s.RIP = 0x1093ea) (movR64R64Effect 0x1093ea 7 15) (Reg.operands [.gpr 15] [])) #v[200]
    (.letOp (n := 219) (.out 0x1093ed (movR64R64Effect 0x1093ed 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[202]
    (.letOp (n := 220) (.exec 0x1093ed (fun s => s.RIP = 0x1093ed) (movR64R64Effect 0x1093ed 6 3) (Reg.operands [.gpr 3] [])) #v[202]
    (.letOp (n := 221) (.out 0x1093f0 (decR32Effect 0x1093f0 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[213]
    (.letOp (n := 222) (.out 0x1093f0 (decR32Effect 0x1093f0 3 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[213]
    (.letOp (n := 223) (.exec 0x1093f0 (fun s => s.RIP = 0x1093f0) (decR32Effect 0x1093f0 3 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[213]
    (.letOp (n := 224) (.pure (condOp 5)) #v[222]
    (.terminate (.condBr (Fin.last 224) ⟨.l1092a0, RegMap.args [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 221), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (19, 222), (22, 22), (39, 39), (50, 50), (51, 51)] 225⟩ ⟨.l1093f9, RegMap.args [(0, 125), (1, 198), (2, 196), (3, 202), (4, 4), (5, 111), (6, 219), (7, 217), (8, 65), (9, 221), (10, 163), (11, 151), (12, 215), (13, 139), (14, 205), (15, 200), (19, 222), (22, 22), (39, 39), (50, 50), (51, 51)] 225⟩))))))))))))))))))))))

def bytes_l1092a0_4 : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x10, 0x4D, 0x89, 0xCE, 0x0F, 0xB6, 0x74, 0x24, 0x10, 0x48, 0xF7, 0xDE,
    0x48, 0x21, 0xD6, 0x44, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0x01, 0xF4, 0x4C, 0x89, 0xFF, 0x48, 0x89,
    0xDE, 0x41, 0xFF, 0xC9, 0x0F, 0x85, 0xA7, 0xFE, 0xFF, 0xFF]

theorem code_l1092a0_4 : ∀ x ∈ codeRange 0x1093cf bytes_l1092a0_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93cf 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1092a0_3 : Block Op Label signature Reg.count 165 :=
  .letOp (n := 165) (.out 0x10938d (xorR64R64Effect 0x10938d 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[161, 7]
    (.letOp (n := 166) (.exec 0x10938d (fun s => s.RIP = 0x10938d) (xorR64R64Effect 0x10938d 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[161, 7]
    (.letOp (n := 167) (.out 0x109390 (andR64R64Effect 0x109390 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[165, 163]
    (.letOp (n := 168) (.exec 0x109390 (fun s => s.RIP = 0x109390) (andR64R64Effect 0x109390 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[165, 163]
    (.letOp (n := 169) (.out 0x109393 (xorR64R64Effect 0x109393 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[147, 7]
    (.letOp (n := 170) (.exec 0x109393 (fun s => s.RIP = 0x109393) (xorR64R64Effect 0x109393 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[147, 7]
    (.letOp (n := 171) (.out 0x109396 (xorR64R64Effect 0x109396 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[167, 7]
    (.letOp (n := 172) (.exec 0x109396 (fun s => s.RIP = 0x109396) (xorR64R64Effect 0x109396 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[167, 7]
    (.letOp (n := 173) (.out 0x109399 (negR64Effect 0x109399 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[94]
    (.letOp (n := 174) (.exec 0x109399 (fun s => s.RIP = 0x109399) (negR64Effect 0x109399 9) (Reg.operands [.gpr 9] [])) #v[94]
    (.letOp (n := 175) (.out 0x10939c (andR64R64Effect 0x10939c 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[173, 171]
    (.letOp (n := 176) (.exec 0x10939c (fun s => s.RIP = 0x10939c) (andR64R64Effect 0x10939c 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[173, 171]
    (.letOp (n := 177) (.out 0x10939f (addR64R64Effect 0x10939f 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[141, 175]
    (.letOp (n := 178) (.exec 0x10939f (fun s => s.RIP = 0x10939f) (addR64R64Effect 0x10939f 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[141, 175]
    (.letOp (n := 179) (.exec 0x1093a2 (StorePre 0x1093a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1093a2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1093a2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[177, 4]
    (.letOp (n := 180) (.out 0x1093a7 (movR64R64Effect 0x1093a7 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 181) (.exec 0x1093a7 (fun s => s.RIP = 0x1093a7) (movR64R64Effect 0x1093a7 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 182) (.out 0x1093aa (negR64Effect 0x1093aa 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[180]
    (.letOp (n := 183) (.exec 0x1093aa (fun s => s.RIP = 0x1093aa) (negR64Effect 0x1093aa 2) (Reg.operands [.gpr 2] [])) #v[180]
    (.letOp (n := 184) (.out 0x1093ad (leaR64Effect 0x1093ad 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 185) (.exec 0x1093ad (fun s => s.RIP = 0x1093ad) (leaR64Effect 0x1093ad 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 186) (.out 0x1093b2 (movzxR32M8Effect 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 187) (.exec 0x1093b2 (LoadPre 0x1093b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1093b2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1093b2 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 188) (.out 0x1093b7 (negR64Effect 0x1093b7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[186]
    (.letOp (n := 189) (.exec 0x1093b7 (fun s => s.RIP = 0x1093b7) (negR64Effect 0x1093b7 7) (Reg.operands [.gpr 7] [])) #v[186]
    (.letOp (n := 190) (.out 0x1093ba (xorR64R64Effect 0x1093ba 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[182, 6]
    (.letOp (n := 191) (.exec 0x1093ba (fun s => s.RIP = 0x1093ba) (xorR64R64Effect 0x1093ba 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[182, 6]
    (.letOp (n := 192) (.out 0x1093bd (andR64R64Effect 0x1093bd 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[190, 188]
    (.letOp (n := 193) (.exec 0x1093bd (fun s => s.RIP = 0x1093bd) (andR64R64Effect 0x1093bd 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[190, 188]
    (.letOp (n := 194) (.out 0x1093c0 (xorR64R64Effect 0x1093c0 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[157, 6]
    (.letOp (n := 195) (.exec 0x1093c0 (fun s => s.RIP = 0x1093c0) (xorR64R64Effect 0x1093c0 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[157, 6]
    (.letOp (n := 196) (.out 0x1093c3 (xorR64R64Effect 0x1093c3 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[192, 6]
    (.letOp (n := 197) (.exec 0x1093c3 (fun s => s.RIP = 0x1093c3) (xorR64R64Effect 0x1093c3 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[192, 6]
    (.letOp (n := 198) (.out 0x1093c6 (sarR64Effect 0x1093c6 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[137]
    (.letOp (n := 199) (.exec 0x1093c6 (fun s => s.RIP = 0x1093c6) (sarR64Effect 0x1093c6 3 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 200) (.out 0x1093c9 (addR64R64Effect 0x1093c9 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[169, 169]
    (.letOp (n := 201) (.exec 0x1093c9 (fun s => s.RIP = 0x1093c9) (addR64R64Effect 0x1093c9 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[169, 169]
    (.letOp (n := 202) (.out 0x1093cc (addR64R64Effect 0x1093cc 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[194, 194]
    (.letOp (n := 203) (.exec 0x1093cc (fun s => s.RIP = 0x1093cc) (addR64R64Effect 0x1093cc 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[194, 194]
    (b_l1092a0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_3 : List UInt8 :=
  [0x48, 0x31, 0xFA, 0x4C, 0x21, 0xD2, 0x49, 0x31, 0xFF, 0x48, 0x31, 0xFA, 0x49, 0xF7, 0xD9, 0x49,
    0x21, 0xD1, 0x4D, 0x01, 0xCE, 0x4C, 0x89, 0x74, 0x24, 0x08, 0x48, 0x89, 0xF2, 0x48, 0xF7, 0xDA,
    0x4C, 0x8D, 0x4C, 0x24, 0x10, 0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x48, 0xF7, 0xDF, 0x48, 0x31, 0xF2,
    0x48, 0x21, 0xFA, 0x48, 0x31, 0xF3, 0x48, 0x31, 0xF2, 0x48, 0xD1, 0xF9, 0x4D, 0x01, 0xFF, 0x48,
    0x01, 0xDB] ++ bytes_l1092a0_4

theorem code_l1092a0_3 : ∀ x ∈ codeRange 0x10938d bytes_l1092a0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x938d 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_4

@[cfg_block] def b_l1092a0_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x10934c (xorR64R64Effect 0x10934c 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[119, 109]
    (.letOp (n := 126) (.exec 0x10934c (fun s => s.RIP = 0x10934c) (xorR64R64Effect 0x10934c 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[119, 109]
    (.letOp (n := 127) (.out 0x10934f (leaR64Effect 0x10934f 2 (.sib 3 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 1] []) (.reg (.gpr 2))) #v[123, 1]
    (.letOp (n := 128) (.exec 0x10934f (fun s => s.RIP = 0x10934f) (leaR64Effect 0x10934f 2 (.sib 3 (some 1) 0 .none)) (Reg.operands [.gpr 3, .gpr 1] [])) #v[123, 1]
    (.letOp (n := 129) (.out 0x109353 (subR64R64Effect 0x109353 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[1, 123]
    (.letOp (n := 130) (.exec 0x109353 (fun s => s.RIP = 0x109353) (subR64R64Effect 0x109353 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 123]
    (.letOp (n := 131) (.out 0x109356 (negR64Effect 0x109356 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[82]
    (.letOp (n := 132) (.exec 0x109356 (fun s => s.RIP = 0x109356) (negR64Effect 0x109356 15) (Reg.operands [.gpr 15] [])) #v[82]
    (.letOp (n := 133) (.out 0x109359 (xorR64R64Effect 0x109359 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[129, 127]
    (.letOp (n := 134) (.exec 0x109359 (fun s => s.RIP = 0x109359) (xorR64R64Effect 0x109359 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[129, 127]
    (.letOp (n := 135) (.out 0x10935c (andR64R64Effect 0x10935c 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[133, 131]
    (.letOp (n := 136) (.exec 0x10935c (fun s => s.RIP = 0x10935c) (andR64R64Effect 0x10935c 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[133, 131]
    (.letOp (n := 137) (.out 0x10935f (xorR64R64Effect 0x10935f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[135, 127]
    (.letOp (n := 138) (.exec 0x10935f (fun s => s.RIP = 0x10935f) (xorR64R64Effect 0x10935f 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[135, 127]
    (.letOp (n := 139) (.out 0x109362 (negR64Effect 0x109362 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[85]
    (.letOp (n := 140) (.exec 0x109362 (fun s => s.RIP = 0x109362) (negR64Effect 0x109362 13) (Reg.operands [.gpr 13] [])) #v[85]
    (.letOp (n := 141) (.out 0x109365 (movR64M64Effect 0x109365 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 142) (.exec 0x109365 (LoadPre 0x109365 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109365 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109365 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.out 0x10936a (movR64R64Effect 0x10936a 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[141]
    (.letOp (n := 144) (.exec 0x10936a (fun s => s.RIP = 0x10936a) (movR64R64Effect 0x10936a 15 14) (Reg.operands [.gpr 14] [])) #v[141]
    (.letOp (n := 145) (.out 0x10936d (xorR64R64Effect 0x10936d 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[143, 7]
    (.letOp (n := 146) (.exec 0x10936d (fun s => s.RIP = 0x10936d) (xorR64R64Effect 0x10936d 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[143, 7]
    (.letOp (n := 147) (.out 0x109370 (andR64R64Effect 0x109370 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[145, 139]
    (.letOp (n := 148) (.exec 0x109370 (fun s => s.RIP = 0x109370) (andR64R64Effect 0x109370 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[145, 139]
    (.letOp (n := 149) (.out 0x109373 (movR64M64Effect 0x109373 12 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 150) (.exec 0x109373 (LoadPre 0x109373 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109373 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109373 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x109378 (negR64Effect 0x109378 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[88]
    (.letOp (n := 152) (.exec 0x109378 (fun s => s.RIP = 0x109378) (negR64Effect 0x109378 11) (Reg.operands [.gpr 11] [])) #v[88]
    (.letOp (n := 153) (.out 0x10937b (movR64R64Effect 0x10937b 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[149]
    (.letOp (n := 154) (.exec 0x10937b (fun s => s.RIP = 0x10937b) (movR64R64Effect 0x10937b 3 12) (Reg.operands [.gpr 12] [])) #v[149]
    (.letOp (n := 155) (.out 0x10937e (xorR64R64Effect 0x10937e 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[153, 6]
    (.letOp (n := 156) (.exec 0x10937e (fun s => s.RIP = 0x10937e) (xorR64R64Effect 0x10937e 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[153, 6]
    (.letOp (n := 157) (.out 0x109381 (andR64R64Effect 0x109381 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x109381 (fun s => s.RIP = 0x109381) (andR64R64Effect 0x109381 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x109384 (movR64R64Effect 0x109384 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 160) (.exec 0x109384 (fun s => s.RIP = 0x109384) (movR64R64Effect 0x109384 2 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 161) (.out 0x109387 (negR64Effect 0x109387 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[159]
    (.letOp (n := 162) (.exec 0x109387 (fun s => s.RIP = 0x109387) (negR64Effect 0x109387 2) (Reg.operands [.gpr 2] [])) #v[159]
    (.letOp (n := 163) (.out 0x10938a (negR64Effect 0x10938a 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[91]
    (.letOp (n := 164) (.exec 0x10938a (fun s => s.RIP = 0x10938a) (negR64Effect 0x10938a 10) (Reg.operands [.gpr 10] [])) #v[91]
    (b_l1092a0_3))))))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_2 : List UInt8 :=
  [0x4C, 0x31, 0xF0, 0x48, 0x8D, 0x14, 0x0B, 0x48, 0x29, 0xD9, 0x49, 0xF7, 0xDF, 0x48, 0x31, 0xD1,
    0x4C, 0x21, 0xF9, 0x48, 0x31, 0xD1, 0x49, 0xF7, 0xDD, 0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4D, 0x89,
    0xF7, 0x49, 0x31, 0xFF, 0x4D, 0x21, 0xEF, 0x4C, 0x8B, 0x64, 0x24, 0x68, 0x49, 0xF7, 0xDB, 0x4C,
    0x89, 0xE3, 0x48, 0x31, 0xF3, 0x4C, 0x21, 0xDB, 0x48, 0x89, 0xFA, 0x48, 0xF7, 0xDA, 0x49, 0xF7,
    0xDA] ++ bytes_l1092a0_3

theorem code_l1092a0_2 : ∀ x ∈ codeRange 0x10934c bytes_l1092a0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x934c 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_3

@[cfg_block] def b_l1092a0_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x1092fe (movzxR32M8Effect 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 89) (.exec 0x1092fe (LoadPre 0x1092fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092fe + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092fe 6 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.exec 0x109304 (StorePre 0x109304 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109304 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x109304 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF])) #v[4, 67, 68, 69]
    (.letOp (n := 91) (.out 0x109309 (movzxR32M8Effect 0x109309 6 10 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 92) (.exec 0x109309 (LoadPre 0x109309 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109309 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109309 6 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x10930f (StorePre 0x10930f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10930f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10930f 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 94) (.out 0x109314 (movzxR32M8Effect 0x109314 6 9 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 95) (.exec 0x109314 (LoadPre 0x109314 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109314 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109314 6 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 96) (.exec 0x10931a (StorePre 0x10931a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10931a + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 15) (setccM8Effect 0x10931a 5 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF, .SF, .OF])) #v[4, 67, 68, 69]
    (.letOp (n := 97) (.out 0x10931f (movR32Imm32Effect 0x10931f 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 98) (.exec 0x10931f (fun s => s.RIP = 0x10931f) (movR32Imm32Effect 0x10931f 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x109324 (subR64R64Effect 0x109324 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[97, 5]
    (.letOp (n := 100) (.exec 0x109324 (fun s => s.RIP = 0x109324) (subR64R64Effect 0x109324 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[97, 5]
    (.letOp (n := 101) (.out 0x109327 (addR64Imm8Effect 0x109327 5 0x2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 102) (.exec 0x109327 (fun s => s.RIP = 0x109327) (addR64Imm8Effect 0x109327 5 0x2) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 103) (.out 0x10932b (negR64Effect 0x10932b 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[75]
    (.letOp (n := 104) (.exec 0x10932b (fun s => s.RIP = 0x10932b) (negR64Effect 0x10932b 14) (Reg.operands [.gpr 14] [])) #v[75]
    (.letOp (n := 105) (.out 0x10932e (xorR64R64Effect 0x10932e 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[99, 101]
    (.letOp (n := 106) (.exec 0x10932e (fun s => s.RIP = 0x10932e) (xorR64R64Effect 0x10932e 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[99, 101]
    (.letOp (n := 107) (.out 0x109331 (andR64R64Effect 0x109331 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x109331 (fun s => s.RIP = 0x109331) (andR64R64Effect 0x109331 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x109334 (movR64R64Effect 0x109334 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[0]
    (.letOp (n := 110) (.exec 0x109334 (fun s => s.RIP = 0x109334) (movR64R64Effect 0x109334 14 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 111) (.out 0x109337 (xorR64R64Effect 0x109337 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[101, 107]
    (.letOp (n := 112) (.exec 0x109337 (fun s => s.RIP = 0x109337) (xorR64R64Effect 0x109337 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[101, 107]
    (.letOp (n := 113) (.out 0x10933a (negR64Effect 0x10933a 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[79]
    (.letOp (n := 114) (.exec 0x10933a (fun s => s.RIP = 0x10933a) (negR64Effect 0x10933a 12) (Reg.operands [.gpr 12] [])) #v[79]
    (.letOp (n := 115) (.out 0x10933d (movR64R64Effect 0x10933d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 116) (.exec 0x10933d (fun s => s.RIP = 0x10933d) (movR64R64Effect 0x10933d 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 117) (.out 0x109340 (xorR64R64Effect 0x109340 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[115, 109]
    (.letOp (n := 118) (.exec 0x109340 (fun s => s.RIP = 0x109340) (xorR64R64Effect 0x109340 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[115, 109]
    (.letOp (n := 119) (.out 0x109343 (andR64R64Effect 0x109343 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[117, 113]
    (.letOp (n := 120) (.exec 0x109343 (fun s => s.RIP = 0x109343) (andR64R64Effect 0x109343 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[117, 113]
    (.letOp (n := 121) (.out 0x109346 (negR64Effect 0x109346 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[72]
    (.letOp (n := 122) (.exec 0x109346 (fun s => s.RIP = 0x109346) (negR64Effect 0x109346 3) (Reg.operands [.gpr 3] [])) #v[72]
    (.letOp (n := 123) (.out 0x109349 (andR64R64Effect 0x109349 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[121, 109]
    (.letOp (n := 124) (.exec 0x109349 (fun s => s.RIP = 0x109349) (andR64R64Effect 0x109349 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[121, 109]
    (b_l1092a0_2)))))))))))))))))))))))))))))))))))))

def bytes_l1092a0_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x0F, 0x9F, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x54, 0x24,
    0x10, 0x44, 0x88, 0x44, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x4C, 0x24, 0x10, 0x0F, 0x9F, 0x44, 0x24,
    0x10, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x48, 0x29, 0xEA, 0x48, 0x83, 0xC5, 0x02, 0x49, 0xF7, 0xDE,
    0x48, 0x31, 0xEA, 0x4C, 0x21, 0xF2, 0x49, 0x89, 0xC6, 0x48, 0x31, 0xD5, 0x49, 0xF7, 0xDC, 0x48,
    0x89, 0xC8, 0x4C, 0x31, 0xF0, 0x4C, 0x21, 0xE0, 0x48, 0xF7, 0xDB, 0x4C, 0x21, 0xF3] ++ bytes_l1092a0_2

theorem code_l1092a0_1 : ∀ x ∈ codeRange 0x1092fe bytes_l1092a0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x92fe 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_2

@[cfg_block] def b_l1092a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1092a0 (StorePre 0x1092a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1092a0 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1092a0 9 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.exec 0x1092a5 (StorePre 0x1092a5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1092a5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1092a5 12 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 55) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 56) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 57) (.out 0x1092aa (testR64R64Effect 0x1092aa 5 5) (EffectPart.reads (.flag .OF) [.gpr 5, .gpr 5] []) (.flag .OF)) #v[5, 5]
    (.letOp (n := 58) (.exec 0x1092aa (fun s => s.RIP = 0x1092aa) (testR64R64Effect 0x1092aa 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 59) (.out 0x1092ad (atFlags (condHolds 15) (setccR8Effect 0x1092ad 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF, .SF, .OF]) (.reg (.gpr 9))) #v[9, 55, 56, 57]
    (.letOp (n := 60) (.exec 0x1092ad (fun s => s.RIP = 0x1092ad) (atFlags (condHolds 15) (setccR8Effect 0x1092ad 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF, .SF, .OF])) #v[9, 55, 56, 57]
    (.letOp (n := 61) (.out 0x1092b1 (andR8R8Effect 0x1092b1 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[59, 1]
    (.letOp (n := 62) (.exec 0x1092b1 (fun s => s.RIP = 0x1092b1) (andR8R8Effect 0x1092b1 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[59, 1]
    (.letOp (n := 63) (.out 0x1092b4 (movR32R32Effect 0x1092b4 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 64) (.exec 0x1092b4 (fun s => s.RIP = 0x1092b4) (movR32R32Effect 0x1092b4 3 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x1092b7 (andR8Imm8Effect 0x1092b7 4 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 66) (.exec 0x1092b7 (fun s => s.RIP = 0x1092b7) (andR8Imm8Effect 0x1092b7 4 8 0x1) (Reg.operands [.gpr 8] [])) #v[63]
    (.letOp (n := 67) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 5] []) (.flag .ZF)) #v[5, 5]
    (.letOp (n := 68) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .SF) [.gpr 5, .gpr 5] []) (.flag .SF)) #v[5, 5]
    (.letOp (n := 69) (.out 0x1092bb (testR64R64Effect 0x1092bb 5 5) (EffectPart.reads (.flag .OF) [.gpr 5, .gpr 5] []) (.flag .OF)) #v[5, 5]
    (.letOp (n := 70) (.exec 0x1092bb (fun s => s.RIP = 0x1092bb) (testR64R64Effect 0x1092bb 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 71) (.exec 0x1092be (StorePre 0x1092be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092be + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092be 5 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 72) (.out 0x1092c3 (movzxR32M8Effect 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 73) (.exec 0x1092c3 (LoadPre 0x1092c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1092c3 5 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1092c8 (StorePre 0x1092c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092c8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092c8 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 75) (.out 0x1092cd (movzxR32M8Effect 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 76) (.exec 0x1092cd (LoadPre 0x1092cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092cd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092cd 6 14 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x1092d3 (StorePre 0x1092d3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092d3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092d3 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 78) (.exec 0x1092d8 (fun s => s.RIP = 0x1092d8) (leaR64Effect 0x1092d8 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1092dd (movzxR32M8Effect 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 80) (.exec 0x1092dd (LoadPre 0x1092dd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092dd + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092dd 6 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x1092e3 (StorePre 0x1092e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092e3 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 82) (.out 0x1092e8 (movzxR32M8Effect 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 83) (.exec 0x1092e8 (LoadPre 0x1092e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092e8 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092e8 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.exec 0x1092ee (StorePre 0x1092ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092ee + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092ee 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 85) (.out 0x1092f3 (movzxR32M8Effect 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 86) (.exec 0x1092f3 (LoadPre 0x1092f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f3 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1092f3 6 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x1092f9 (StorePre 0x1092f9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1092f9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1092f9 5 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[61, 4]
    (b_l1092a0_1)))))))))))))))))))))))))))))))))))

def bytes_l1092a0 : List UInt8 :=
  [0x44, 0x89, 0x4C, 0x24, 0x60, 0x4C, 0x89, 0x64, 0x24, 0x68, 0x48, 0x85, 0xED, 0x41, 0x0F, 0x9F,
    0xC1, 0x41, 0x20, 0xC9, 0x41, 0x89, 0xC8, 0x41, 0x80, 0xE0, 0x01, 0x48, 0x85, 0xED, 0x44, 0x88,
    0x44, 0x24, 0x10, 0x0F, 0xB6, 0x5C, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6,
    0x74, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x44, 0x0F, 0xB6,
    0x64, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x10, 0x44, 0x88,
    0x4C, 0x24, 0x10, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x10, 0x44, 0x88, 0x4C, 0x24, 0x10] ++ bytes_l1092a0_1

theorem code_l1092a0 : ∀ x ∈ codeRange 0x1092a0 bytes_l1092a0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x92a0 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1092a0_1

@[cfg_block] def b_l1093f9 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l108f97, RegMap.args (entryMap (live .l1093f9)) 53⟩)

def bytes_l1093f9 : List UInt8 :=
  [0xE9, 0x99, 0xFB, 0xFF, 0xFF]

theorem code_l1093f9 : ∀ x ∈ codeRange 0x1093f9 bytes_l1093f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93f9 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1093fe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1093fe (movR64M64Effect 0x1093fe 0 (.sib 4 none 0 (.d32 0x138))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1093fe (LoadPre 0x1093fe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x1093fe + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1093fe 0 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109406 (orR64M64Effect 0x109406 0 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x109406 (LoadPre 0x109406 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x109406 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109406 0 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.out 0x10940e (orR64M64Effect 0x10940e 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x10940e (LoadPre 0x10940e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10940e + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x10940e 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109416 (orR64M64Effect 0x109416 0 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109416 (LoadPre 0x109416 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x109416 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109416 0 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x10941e (atFlags (condHolds 5) (setccR8Effect 0x10941e 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 59]
    (.letOp (n := 62) (.exec 0x10941e (fun s => s.RIP = 0x10941e) (atFlags (condHolds 5) (setccR8Effect 0x10941e 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 59]
    (.letOp (n := 63) (.out 0x109421 (movR32M32LowEffect 0x109421 2 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 64) (.exec 0x109421 (LoadPre 0x109421 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x109421 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x109421 2 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x109428 (leaR64Effect 0x109428 6 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x109428 (fun s => s.RIP = 0x109428) (leaR64Effect 0x109428 6 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x109430 (movR64M64Effect 0x109430 14 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 68) (.exec 0x109430 (LoadPre 0x109430 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x109430 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x109430 14 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x109438 (movR64R64Effect 0x109438 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x109438 (fun s => s.RIP = 0x109438) (movR64R64Effect 0x109438 7 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 71) (.out 0x10943b (movR64M64Effect 0x10943b 1 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x10943b (LoadPre 0x10943b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10943b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10943b 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x109443 (callEffect (fun _ => 0x109c00) 0x109448) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 74) (.exec 0x109443 (PushPre 0x109443 5) (callEffect (fun _ => 0x109c00) 0x109448) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.const ⟨64, 0x109448⟩) #v[]
    (.terminate (.call ⟨.l109c00, RegMap.args [(1, 71), (2, 63), (3, 61), (4, 73), (5, 5), (6, 65), (7, 69), (12, 12), (13, 13), (14, 67), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l109448, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l1093fe : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x28, 0x01, 0x00, 0x00,
    0x48, 0x0B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x30, 0x01, 0x00, 0x00,
    0x0F, 0x95, 0xC3, 0x8B, 0x94, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0xD0, 0x00,
    0x00, 0x00, 0x4C, 0x8B, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x48, 0x8B, 0x8C,
    0x24, 0xA0, 0x00, 0x00, 0x00, 0xE8, 0xB8, 0x07, 0x00, 0x00]

theorem code_l1093fe : ∀ x ∈ codeRange 0x1093fe bytes_l1093fe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x93fe 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109448 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109448 (movR64M64Effect 0x109448 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x109448 (LoadPre 0x109448 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109448 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109448 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10944d (xorR64Imm8Effect 0x10944d 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10944d (fun s => s.RIP = 0x10944d) (xorR64Imm8Effect 0x10944d 0 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x109451 (orR64M64Effect 0x109451 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x109451 (LoadPre 0x109451 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109451 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109451 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x109459 (orR64M64Effect 0x109459 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[57, 4]
    (.letOp (n := 60) (.exec 0x109459 (LoadPre 0x109459 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x109459 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109459 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.out 0x109461 (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[59, 4]
    (.letOp (n := 62) (.out 0x109461 (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[59, 4]
    (.letOp (n := 63) (.exec 0x109461 (LoadPre 0x109461 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x109461 + BitVec.ofNat 64 8)) 8) (orR64M64Effect 0x109461 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 64) (.out 0x109469 (atFlags (condHolds 4) (setccR8Effect 0x109469 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 62]
    (.letOp (n := 65) (.exec 0x109469 (fun s => s.RIP = 0x109469) (atFlags (condHolds 4) (setccR8Effect 0x109469 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 62]
    (.letOp (n := 66) (.out 0x10946c (andR8R8Effect 0x10946c 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[64, 3]
    (.letOp (n := 67) (.exec 0x10946c (fun s => s.RIP = 0x10946c) (andR8R8Effect 0x10946c 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[64, 3]
    (.letOp (n := 68) (.exec 0x10946e (StorePre 0x10946e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x10946e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10946e 4 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[66, 14]
    (.letOp (n := 69) (.out 0x109472 (movR64R64Effect 0x109472 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 70) (.exec 0x109472 (fun s => s.RIP = 0x109472) (movR64R64Effect 0x109472 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x109475 (addR64Imm32Effect 0x109475 4 0x168) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x109475 (fun s => s.RIP = 0x109475) (addR64Imm32Effect 0x109475 4 0x168) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x10947c (popR64Effect 0x10947c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[71]
    (.letOp (n := 74) (.out 0x10947c (popR64Effect 0x10947c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x10947c (PopPre 0x10947c) (popR64Effect 0x10947c 1 3) (Reg.operands [.gpr 4] [])) #v[71]
    (.letOp (n := 76) (.out 0x10947d (popR64Effect 0x10947d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[74]
    (.letOp (n := 77) (.out 0x10947d (popR64Effect 0x10947d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[74]
    (.letOp (n := 78) (.exec 0x10947d (PopPre 0x10947d) (popR64Effect 0x10947d 2 12) (Reg.operands [.gpr 4] [])) #v[74]
    (.letOp (n := 79) (.out 0x10947f (popR64Effect 0x10947f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[77]
    (.letOp (n := 80) (.out 0x10947f (popR64Effect 0x10947f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[77]
    (.letOp (n := 81) (.exec 0x10947f (PopPre 0x10947f) (popR64Effect 0x10947f 2 13) (Reg.operands [.gpr 4] [])) #v[77]
    (.letOp (n := 82) (.out 0x109481 (popR64Effect 0x109481 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[80]
    (.letOp (n := 83) (.out 0x109481 (popR64Effect 0x109481 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x109481 (PopPre 0x109481) (popR64Effect 0x109481 2 14) (Reg.operands [.gpr 4] [])) #v[80]
    (.letOp (n := 85) (.out 0x109483 (popR64Effect 0x109483 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[83]
    (.letOp (n := 86) (.out 0x109483 (popR64Effect 0x109483 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x109483 (PopPre 0x109483) (popR64Effect 0x109483 2 15) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x109485 (popR64Effect 0x109485 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[86]
    (.letOp (n := 89) (.out 0x109485 (popR64Effect 0x109485 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x109485 (PopPre 0x109485) (popR64Effect 0x109485 1 5) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x109486 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[89]
    (.letOp (n := 92) (.out 0x109486 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x109486 (RetPre 0x109486) (retEffect) (Reg.operands [.gpr 4] [])) #v[89]
    (.terminate (.ret (RegMap.args [(0, 69), (1, 1), (2, 2), (3, 73), (4, 92), (5, 88), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 76), (13, 79), (14, 82), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 94) (some ⟨91, by decide⟩)))))))))))))))))))))))))))))))))))))))))))

def bytes_l109448 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x83, 0xF0, 0x01, 0x48, 0x0B, 0x84, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x0B, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x0B, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x0F, 0x94, 0xC0, 0x20, 0xD8, 0x41, 0x88, 0x46, 0x20, 0x4C, 0x89, 0xF0, 0x48, 0x81, 0xC4,
    0x68, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109448 : ∀ x ∈ codeRange 0x109448 bytes_l109448, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9448 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099c0_7 : Block Op Label signature Reg.count 366 :=
  .letOp (n := 366) (.out 0x109b94 (addR64R64Effect 0x109b94 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[361, 345]
    (.letOp (n := 367) (.out 0x109b94 (addR64R64Effect 0x109b94 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[361, 345]
    (.letOp (n := 368) (.exec 0x109b94 (fun s => s.RIP = 0x109b94) (addR64R64Effect 0x109b94 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[361, 345]
    (.letOp (n := 369) (.out 0x109b97 (movzxR32R8Effect 0x109b97 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[364]
    (.letOp (n := 370) (.exec 0x109b97 (fun s => s.RIP = 0x109b97) (movzxR32R8Effect 0x109b97 3 0 1) (Reg.operands [.gpr 1] [])) #v[364]
    (.letOp (n := 371) (.out 0x109b9a (atFlags StatusFlags.CF (adcR64R64Effect 0x109b9a 0 2)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[369, 356, 367]
    (.letOp (n := 372) (.exec 0x109b9a (fun s => s.RIP = 0x109b9a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b9a 0 2)) (Reg.operands [.gpr 0, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[369, 356, 367]
    (.letOp (n := 373) (.out 0x109b9d (movR64M64Effect 0x109b9d 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 374) (.exec 0x109b9d (LoadPre 0x109b9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x109b9d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b9d 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 375) (.exec 0x109ba2 (StorePre 0x109ba2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x109ba2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ba2 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[373, 65]
    (.letOp (n := 376) (.out 0x109ba7 (movR64M64Effect 0x109ba7 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 377) (.exec 0x109ba7 (LoadPre 0x109ba7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109ba7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ba7 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 378) (.exec 0x109bac (StorePre 0x109bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x109bac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bac 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[376, 65]
    (.letOp (n := 379) (.out 0x109bb1 (movR64M64Effect 0x109bb1 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 380) (.exec 0x109bb1 (LoadPre 0x109bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109bb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109bb1 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 381) (.exec 0x109bb6 (StorePre 0x109bb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x109bb6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bb6 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[379, 65]
    (.letOp (n := 382) (.out 0x109bbb (movR64M64Effect 0x109bbb 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 383) (.exec 0x109bbb (LoadPre 0x109bbb (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109bbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109bbb 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 384) (.exec 0x109bbf (StorePre 0x109bbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x109bbf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bbf 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[382, 65]
    (.letOp (n := 385) (.exec 0x109bc4 (StorePre 0x109bc4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x109bc4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc4 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[315, 65]
    (.letOp (n := 386) (.exec 0x109bc9 (StorePre 0x109bc9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x109bc9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bc9 15 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[358, 65]
    (.letOp (n := 387) (.exec 0x109bce (StorePre 0x109bce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x109bce + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109bce 11 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[366, 65]
    (.letOp (n := 388) (.exec 0x109bd3 (StorePre 0x109bd3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x109bd3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x109bd3 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[371, 65]
    (.letOp (n := 389) (.out 0x109bdb (leaR64Effect 0x109bdb 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 390) (.exec 0x109bdb (fun s => s.RIP = 0x109bdb) (leaR64Effect 0x109bdb 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 391) (.out 0x109be0 (xorR32R32Effect 0x109be0 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[356, 356]
    (.letOp (n := 392) (.exec 0x109be0 (fun s => s.RIP = 0x109be0) (xorR32R32Effect 0x109be0 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[356, 356]
    (.letOp (n := 393) (.out 0x109be2 (callEffect (fun _ => 0x11b510) 0x109be7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 394) (.exec 0x109be2 (PushPre 0x109be2 5) (callEffect (fun _ => 0x11b510) 0x109be7) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 395) (.const ⟨64, 0x109be7⟩) #v[]
    (.terminate (.call ⟨.l11b510, RegMap.args [(0, 371), (1, 382), (2, 391), (3, 199), (4, 393), (5, 323), (6, 389), (7, 7), (8, 315), (9, 339), (10, 245), (11, 366), (12, 318), (13, 341), (14, 348), (15, 358), (22, 22), (39, 39), (50, 50), (51, 51)] 396⟩ { target := .l109be7, kept := #v[], arity := rfl, guard := some (Fin.last 395) })))))))))))))))))))))))))))))))

def bytes_l1099c0_7 : List UInt8 :=
  [0x49, 0x01, 0xC3, 0x0F, 0xB6, 0xC1, 0x48, 0x11, 0xD0, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x89,
    0x4C, 0x24, 0x48, 0x48, 0x8B, 0x4C, 0x24, 0x38, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x8B, 0x4C,
    0x24, 0x30, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x48, 0x8B, 0x0C, 0x24, 0x48, 0x89, 0x4C, 0x24, 0x60,
    0x4C, 0x89, 0x44, 0x24, 0x68, 0x4C, 0x89, 0x7C, 0x24, 0x70, 0x4C, 0x89, 0x5C, 0x24, 0x78, 0x48,
    0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x48, 0x31, 0xD2, 0xE8, 0x29,
    0x19, 0x01, 0x00]

theorem code_l1099c0_7 : ∀ x ∈ codeRange 0x109b94 bytes_l1099c0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9b94 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1099c0_6 : Block Op Label signature Reg.count 318 :=
  .letOp (n := 318) (.out 0x109b56 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[311, 301, 316]
    (.letOp (n := 319) (.out 0x109b56 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[311, 301, 316]
    (.letOp (n := 320) (.exec 0x109b56 (fun s => s.RIP = 0x109b56) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b56 12 11)) (Reg.operands [.gpr 12, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[311, 301, 316]
    (.letOp (n := 321) (.out 0x109b59 (movzxR32R8Effect 0x109b59 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[304]
    (.letOp (n := 322) (.exec 0x109b59 (fun s => s.RIP = 0x109b59) (movzxR32R8Effect 0x109b59 4 5 9) (Reg.operands [.gpr 9] [])) #v[304]
    (.letOp (n := 323) (.out 0x109b5d (atFlags StatusFlags.CF (adcR64R64Effect 0x109b5d 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[321, 299, 319]
    (.letOp (n := 324) (.exec 0x109b5d (fun s => s.RIP = 0x109b5d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b5d 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[321, 299, 319]
    (.letOp (n := 325) (.out 0x109b60 (movR64R64Effect 0x109b60 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 326) (.exec 0x109b60 (fun s => s.RIP = 0x109b60) (movR64R64Effect 0x109b60 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 327) (.out 0x109b63 (mulR64Effect 0x109b63 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 325]
    (.letOp (n := 328) (.out 0x109b63 (mulR64Effect 0x109b63 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 325]
    (.letOp (n := 329) (.exec 0x109b63 (fun s => s.RIP = 0x109b63) (mulR64Effect 0x109b63 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 325]
    (.letOp (n := 330) (.out 0x109b66 (movR64R64Effect 0x109b66 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[328]
    (.letOp (n := 331) (.exec 0x109b66 (fun s => s.RIP = 0x109b66) (movR64R64Effect 0x109b66 11 2) (Reg.operands [.gpr 2] [])) #v[328]
    (.letOp (n := 332) (.out 0x109b69 (movR64R64Effect 0x109b69 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[327]
    (.letOp (n := 333) (.exec 0x109b69 (fun s => s.RIP = 0x109b69) (movR64R64Effect 0x109b69 15 0) (Reg.operands [.gpr 0] [])) #v[327]
    (.letOp (n := 334) (.out 0x109b6c (movR64R64Effect 0x109b6c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 335) (.exec 0x109b6c (fun s => s.RIP = 0x109b6c) (movR64R64Effect 0x109b6c 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 336) (.out 0x109b6f (mulR64Effect 0x109b6f 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 334]
    (.letOp (n := 337) (.out 0x109b6f (mulR64Effect 0x109b6f 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 334]
    (.letOp (n := 338) (.exec 0x109b6f (fun s => s.RIP = 0x109b6f) (mulR64Effect 0x109b6f 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 334]
    (.letOp (n := 339) (.out 0x109b72 (movR64R64Effect 0x109b72 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[337]
    (.letOp (n := 340) (.exec 0x109b72 (fun s => s.RIP = 0x109b72) (movR64R64Effect 0x109b72 9 2) (Reg.operands [.gpr 2] [])) #v[337]
    (.letOp (n := 341) (.out 0x109b75 (movR64R64Effect 0x109b75 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[336]
    (.letOp (n := 342) (.exec 0x109b75 (fun s => s.RIP = 0x109b75) (movR64R64Effect 0x109b75 13 0) (Reg.operands [.gpr 0] [])) #v[336]
    (.letOp (n := 343) (.out 0x109b78 (movR64R64Effect 0x109b78 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 344) (.exec 0x109b78 (fun s => s.RIP = 0x109b78) (movR64R64Effect 0x109b78 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 345) (.out 0x109b7b (mulR64Effect 0x109b7b 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 343]
    (.letOp (n := 346) (.out 0x109b7b (mulR64Effect 0x109b7b 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 343]
    (.letOp (n := 347) (.exec 0x109b7b (fun s => s.RIP = 0x109b7b) (mulR64Effect 0x109b7b 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 343]
    (.letOp (n := 348) (.out 0x109b7e (movR64R64Effect 0x109b7e 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 349) (.exec 0x109b7e (fun s => s.RIP = 0x109b7e) (movR64R64Effect 0x109b7e 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 350) (.out 0x109b81 (addR64R64Effect 0x109b81 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[332, 318]
    (.letOp (n := 351) (.out 0x109b81 (addR64R64Effect 0x109b81 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[332, 318]
    (.letOp (n := 352) (.exec 0x109b81 (fun s => s.RIP = 0x109b81) (addR64R64Effect 0x109b81 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[332, 318]
    (.letOp (n := 353) (.out 0x109b84 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[330, 323, 351]
    (.letOp (n := 354) (.out 0x109b84 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[330, 323, 351]
    (.letOp (n := 355) (.exec 0x109b84 (fun s => s.RIP = 0x109b84) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b84 11 5)) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[330, 323, 351]
    (.letOp (n := 356) (.out 0x109b87 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109b87 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[346, 354]
    (.letOp (n := 357) (.exec 0x109b87 (fun s => s.RIP = 0x109b87) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109b87 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[346, 354]
    (.letOp (n := 358) (.out 0x109b8b (addR64R64Effect 0x109b8b 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[350, 341]
    (.letOp (n := 359) (.out 0x109b8b (addR64R64Effect 0x109b8b 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[350, 341]
    (.letOp (n := 360) (.exec 0x109b8b (fun s => s.RIP = 0x109b8b) (addR64R64Effect 0x109b8b 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[350, 341]
    (.letOp (n := 361) (.out 0x109b8e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[353, 339, 359]
    (.letOp (n := 362) (.out 0x109b8e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[353, 339, 359]
    (.letOp (n := 363) (.exec 0x109b8e (fun s => s.RIP = 0x109b8e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b8e 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[353, 339, 359]
    (.letOp (n := 364) (.out 0x109b91 (atFlags (condHolds 2) (setccR8Effect 0x109b91 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[299, 362]
    (.letOp (n := 365) (.exec 0x109b91 (fun s => s.RIP = 0x109b91) (atFlags (condHolds 2) (setccR8Effect 0x109b91 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[299, 362]
    (b_l1099c0_7))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_6 : List UInt8 :=
  [0x4D, 0x11, 0xDC, 0x41, 0x0F, 0xB6, 0xE9, 0x48, 0x11, 0xCD, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE6,
    0x49, 0x89, 0xD3, 0x49, 0x89, 0xC7, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD1, 0x49,
    0x89, 0xC5, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xFE, 0x4D, 0x01, 0xE7, 0x49, 0x11,
    0xEB, 0x48, 0x83, 0xD2, 0x00, 0x4D, 0x01, 0xEF, 0x4D, 0x11, 0xCB, 0x0F, 0x92, 0xC1] ++ bytes_l1099c0_7

theorem code_l1099c0_6 : ∀ x ∈ codeRange 0x109b56 bytes_l1099c0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b56 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_7

@[cfg_block] def b_l1099c0_5 : Block Op Label signature Reg.count 270 :=
  .letOp (n := 270) (.out 0x109b15 (movR64R64Effect 0x109b15 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 271) (.exec 0x109b15 (fun s => s.RIP = 0x109b15) (movR64R64Effect 0x109b15 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 272) (.out 0x109b18 (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[270, 65]
    (.letOp (n := 273) (.out 0x109b18 (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[270, 65]
    (.letOp (n := 274) (.exec 0x109b18 (LoadPre 0x109b18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109b18 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x109b18 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[270, 65]
    (.letOp (n := 275) (.out 0x109b1d (movR64R64Effect 0x109b1d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[273]
    (.letOp (n := 276) (.exec 0x109b1d (fun s => s.RIP = 0x109b1d) (movR64R64Effect 0x109b1d 15 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 277) (.out 0x109b20 (movR64R64Effect 0x109b20 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[272]
    (.letOp (n := 278) (.exec 0x109b20 (fun s => s.RIP = 0x109b20) (movR64R64Effect 0x109b20 12 0) (Reg.operands [.gpr 0] [])) #v[272]
    (.letOp (n := 279) (.out 0x109b23 (addR64R64Effect 0x109b23 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[277, 263]
    (.letOp (n := 280) (.out 0x109b23 (addR64R64Effect 0x109b23 12 11) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 11] []) (.flag .CF)) #v[277, 263]
    (.letOp (n := 281) (.exec 0x109b23 (fun s => s.RIP = 0x109b23) (addR64R64Effect 0x109b23 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[277, 263]
    (.letOp (n := 282) (.out 0x109b26 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[275, 268, 280]
    (.letOp (n := 283) (.out 0x109b26 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[275, 268, 280]
    (.letOp (n := 284) (.exec 0x109b26 (fun s => s.RIP = 0x109b26) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b26 15 9)) (Reg.operands [.gpr 15, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[275, 268, 280]
    (.letOp (n := 285) (.out 0x109b29 (atFlags (condHolds 2) (setccR8Effect 0x109b29 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[146, 283]
    (.letOp (n := 286) (.exec 0x109b29 (fun s => s.RIP = 0x109b29) (atFlags (condHolds 2) (setccR8Effect 0x109b29 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[146, 283]
    (.letOp (n := 287) (.out 0x109b2c (movR64R64Effect 0x109b2c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 288) (.exec 0x109b2c (fun s => s.RIP = 0x109b2c) (movR64R64Effect 0x109b2c 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 289) (.out 0x109b2f (mulR64Effect 0x109b2f 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 287]
    (.letOp (n := 290) (.out 0x109b2f (mulR64Effect 0x109b2f 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 287]
    (.letOp (n := 291) (.exec 0x109b2f (fun s => s.RIP = 0x109b2f) (mulR64Effect 0x109b2f 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 287]
    (.letOp (n := 292) (.out 0x109b32 (movR64R64Effect 0x109b32 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[290]
    (.letOp (n := 293) (.exec 0x109b32 (fun s => s.RIP = 0x109b32) (movR64R64Effect 0x109b32 11 2) (Reg.operands [.gpr 2] [])) #v[290]
    (.letOp (n := 294) (.out 0x109b35 (movR64R64Effect 0x109b35 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[289]
    (.letOp (n := 295) (.exec 0x109b35 (fun s => s.RIP = 0x109b35) (movR64R64Effect 0x109b35 13 0) (Reg.operands [.gpr 0] [])) #v[289]
    (.letOp (n := 296) (.out 0x109b38 (addR64R64Effect 0x109b38 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[294, 279]
    (.letOp (n := 297) (.out 0x109b38 (addR64R64Effect 0x109b38 13 12) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 12] []) (.flag .CF)) #v[294, 279]
    (.letOp (n := 298) (.exec 0x109b38 (fun s => s.RIP = 0x109b38) (addR64R64Effect 0x109b38 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[294, 279]
    (.letOp (n := 299) (.out 0x109b3b (movzxR32R8Effect 0x109b3b 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 300) (.exec 0x109b3b (fun s => s.RIP = 0x109b3b) (movzxR32R8Effect 0x109b3b 3 1 1) (Reg.operands [.gpr 1] [])) #v[285]
    (.letOp (n := 301) (.out 0x109b3e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[292, 282, 297]
    (.letOp (n := 302) (.out 0x109b3e (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[292, 282, 297]
    (.letOp (n := 303) (.exec 0x109b3e (fun s => s.RIP = 0x109b3e) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b3e 11 15)) (Reg.operands [.gpr 11, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[292, 282, 297]
    (.letOp (n := 304) (.out 0x109b41 (atFlags (condHolds 2) (setccR8Effect 0x109b41 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[268, 302]
    (.letOp (n := 305) (.exec 0x109b41 (fun s => s.RIP = 0x109b41) (atFlags (condHolds 2) (setccR8Effect 0x109b41 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[268, 302]
    (.letOp (n := 306) (.out 0x109b45 (movR64M64Effect 0x109b45 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 307) (.exec 0x109b45 (LoadPre 0x109b45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109b45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109b45 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 308) (.out 0x109b4a (mulR64Effect 0x109b4a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 306]
    (.letOp (n := 309) (.out 0x109b4a (mulR64Effect 0x109b4a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 306]
    (.letOp (n := 310) (.exec 0x109b4a (fun s => s.RIP = 0x109b4a) (mulR64Effect 0x109b4a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 306]
    (.letOp (n := 311) (.out 0x109b4d (movR64R64Effect 0x109b4d 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[309]
    (.letOp (n := 312) (.exec 0x109b4d (fun s => s.RIP = 0x109b4d) (movR64R64Effect 0x109b4d 12 2) (Reg.operands [.gpr 2] [])) #v[309]
    (.letOp (n := 313) (.out 0x109b50 (movR64R64Effect 0x109b50 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[308]
    (.letOp (n := 314) (.exec 0x109b50 (fun s => s.RIP = 0x109b50) (movR64R64Effect 0x109b50 8 0) (Reg.operands [.gpr 0] [])) #v[308]
    (.letOp (n := 315) (.out 0x109b53 (addR64R64Effect 0x109b53 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[313, 296]
    (.letOp (n := 316) (.out 0x109b53 (addR64R64Effect 0x109b53 8 13) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 13] []) (.flag .CF)) #v[313, 296]
    (.letOp (n := 317) (.exec 0x109b53 (fun s => s.RIP = 0x109b53) (addR64R64Effect 0x109b53 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[313, 296]
    (b_l1099c0_6))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_5 : List UInt8 :=
  [0x48, 0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x18, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xC4, 0x4D, 0x01,
    0xDC, 0x4D, 0x11, 0xCF, 0x0F, 0x92, 0xC1, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD3,
    0x49, 0x89, 0xC5, 0x4D, 0x01, 0xE5, 0x0F, 0xB6, 0xC9, 0x4D, 0x11, 0xFB, 0x41, 0x0F, 0x92, 0xC1,
    0x48, 0x8B, 0x44, 0x24, 0x20, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC0, 0x4D, 0x01,
    0xE8] ++ bytes_l1099c0_6

theorem code_l1099c0_5 : ∀ x ∈ codeRange 0x109b15 bytes_l1099c0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9b15 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_6

@[cfg_block] def b_l1099c0_4 : Block Op Label signature Reg.count 224 :=
  .letOp (n := 224) (.out 0x109ace (addR8Imm8Effect 0x109ace 4 9 0xff) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[212]
    (.letOp (n := 225) (.out 0x109ace (addR8Imm8Effect 0x109ace 4 9 0xff) (EffectPart.reads (.flag .CF) [.gpr 9] []) (.flag .CF)) #v[212]
    (.letOp (n := 226) (.exec 0x109ace (fun s => s.RIP = 0x109ace) (addR8Imm8Effect 0x109ace 4 9 0xff) (Reg.operands [.gpr 9] [])) #v[212]
    (.letOp (n := 227) (.out 0x109ad2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109ad2 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[222, 225]
    (.letOp (n := 228) (.exec 0x109ad2 (fun s => s.RIP = 0x109ad2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109ad2 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[222, 225]
    (.letOp (n := 229) (.out 0x109ad6 (movR64R64Effect 0x109ad6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[146]
    (.letOp (n := 230) (.exec 0x109ad6 (fun s => s.RIP = 0x109ad6) (movR64R64Effect 0x109ad6 0 1) (Reg.operands [.gpr 1] [])) #v[146]
    (.letOp (n := 231) (.out 0x109ad9 (movR64M64Effect 0x109ad9 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 232) (.exec 0x109ad9 (LoadPre 0x109ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ad9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109ad9 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 233) (.out 0x109ade (mulR64Effect 0x109ade 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[231, 229]
    (.letOp (n := 234) (.out 0x109ade (mulR64Effect 0x109ade 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[231, 229]
    (.letOp (n := 235) (.exec 0x109ade (fun s => s.RIP = 0x109ade) (mulR64Effect 0x109ade 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[231, 229]
    (.letOp (n := 236) (.out 0x109ae1 (movR64R64Effect 0x109ae1 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[234]
    (.letOp (n := 237) (.exec 0x109ae1 (fun s => s.RIP = 0x109ae1) (movR64R64Effect 0x109ae1 13 2) (Reg.operands [.gpr 2] [])) #v[234]
    (.letOp (n := 238) (.out 0x109ae4 (movR64R64Effect 0x109ae4 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[233]
    (.letOp (n := 239) (.exec 0x109ae4 (fun s => s.RIP = 0x109ae4) (movR64R64Effect 0x109ae4 5 0) (Reg.operands [.gpr 0] [])) #v[233]
    (.letOp (n := 240) (.out 0x109ae7 (addR64R64Effect 0x109ae7 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[238, 214]
    (.letOp (n := 241) (.out 0x109ae7 (addR64R64Effect 0x109ae7 5 12) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 12] []) (.flag .CF)) #v[238, 214]
    (.letOp (n := 242) (.exec 0x109ae7 (fun s => s.RIP = 0x109ae7) (addR64R64Effect 0x109ae7 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[238, 214]
    (.letOp (n := 243) (.out 0x109aea (movR64M64Effect 0x109aea 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 244) (.exec 0x109aea (LoadPre 0x109aea (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109aea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aea 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 245) (.out 0x109aee (movR64M64Effect 0x109aee 10 (.base 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[243]
    (.letOp (n := 246) (.exec 0x109aee (LoadPre 0x109aee (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109aee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109aee 10 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 0] [])) #v[243]
    (.letOp (n := 247) (.out 0x109af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[236, 217, 241]
    (.letOp (n := 248) (.out 0x109af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (Reg.operands [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[236, 217, 241]
    (.letOp (n := 249) (.exec 0x109af2 (fun s => s.RIP = 0x109af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x109af2 13 15)) (Reg.operands [.gpr 13, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[236, 217, 241]
    (.letOp (n := 250) (.out 0x109af5 (atFlags (condHolds 2) (setccR8Effect 0x109af5 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[224, 248]
    (.letOp (n := 251) (.exec 0x109af5 (fun s => s.RIP = 0x109af5) (atFlags (condHolds 2) (setccR8Effect 0x109af5 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[224, 248]
    (.letOp (n := 252) (.out 0x109af9 (movR64M64Effect 0x109af9 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 253) (.exec 0x109af9 (LoadPre 0x109af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109af9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109af9 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 254) (.out 0x109afe (mulR64Effect 0x109afe 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[245, 252]
    (.letOp (n := 255) (.out 0x109afe (mulR64Effect 0x109afe 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[245, 252]
    (.letOp (n := 256) (.exec 0x109afe (fun s => s.RIP = 0x109afe) (mulR64Effect 0x109afe 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[245, 252]
    (.letOp (n := 257) (.out 0x109b01 (movR64R64Effect 0x109b01 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[255]
    (.letOp (n := 258) (.exec 0x109b01 (fun s => s.RIP = 0x109b01) (movR64R64Effect 0x109b01 11 2) (Reg.operands [.gpr 2] [])) #v[255]
    (.letOp (n := 259) (.out 0x109b04 (addR64R64Effect 0x109b04 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[254, 240]
    (.letOp (n := 260) (.out 0x109b04 (addR64R64Effect 0x109b04 0 5) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 5] []) (.flag .CF)) #v[254, 240]
    (.letOp (n := 261) (.exec 0x109b04 (fun s => s.RIP = 0x109b04) (addR64R64Effect 0x109b04 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[254, 240]
    (.letOp (n := 262) (.exec 0x109b07 (StorePre 0x109b07 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109b07 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109b07 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[259, 65]
    (.letOp (n := 263) (.out 0x109b0b (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[257, 247, 260]
    (.letOp (n := 264) (.out 0x109b0b (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[257, 247, 260]
    (.letOp (n := 265) (.exec 0x109b0b (fun s => s.RIP = 0x109b0b) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b0b 11 13)) (Reg.operands [.gpr 11, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[257, 247, 260]
    (.letOp (n := 266) (.out 0x109b0e (movzxR32R8Effect 0x109b0e 4 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[250]
    (.letOp (n := 267) (.exec 0x109b0e (fun s => s.RIP = 0x109b0e) (movzxR32R8Effect 0x109b0e 4 9 9) (Reg.operands [.gpr 9] [])) #v[250]
    (.letOp (n := 268) (.out 0x109b12 (atFlags StatusFlags.CF (adcR64R64Effect 0x109b12 9 8)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[266, 227, 264]
    (.letOp (n := 269) (.exec 0x109b12 (fun s => s.RIP = 0x109b12) (atFlags StatusFlags.CF (adcR64R64Effect 0x109b12 9 8)) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[266, 227, 264]
    (b_l1099c0_5))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_4 : List UInt8 :=
  [0x41, 0x80, 0xC1, 0xFF, 0x49, 0x83, 0xD0, 0x00, 0x48, 0x89, 0xC8, 0x4C, 0x8B, 0x74, 0x24, 0x08,
    0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD5, 0x48, 0x89, 0xC5, 0x4C, 0x01, 0xE5, 0x48, 0x8B, 0x04, 0x24,
    0x4C, 0x8B, 0x50, 0x18, 0x4D, 0x11, 0xFD, 0x41, 0x0F, 0x92, 0xC1, 0x48, 0x8B, 0x44, 0x24, 0x28,
    0x49, 0xF7, 0xE2, 0x49, 0x89, 0xD3, 0x48, 0x01, 0xE8, 0x48, 0x89, 0x04, 0x24, 0x4D, 0x11, 0xEB,
    0x45, 0x0F, 0xB6, 0xC9, 0x4D, 0x11, 0xC1] ++ bytes_l1099c0_5

theorem code_l1099c0_4 : ∀ x ∈ codeRange 0x109ace bytes_l1099c0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ace 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_5

@[cfg_block] def b_l1099c0_3 : Block Op Label signature Reg.count 177 :=
  .letOp (n := 177) (.out 0x109a8a (addR64R64Effect 0x109a8a 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[172, 157]
    (.letOp (n := 178) (.out 0x109a8a (addR64R64Effect 0x109a8a 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[172, 157]
    (.letOp (n := 179) (.exec 0x109a8a (fun s => s.RIP = 0x109a8a) (addR64R64Effect 0x109a8a 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[172, 157]
    (.letOp (n := 180) (.exec 0x109a8d (StorePre 0x109a8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x109a8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a8d 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[177, 65]
    (.letOp (n := 181) (.out 0x109a92 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[175, 165, 178]
    (.letOp (n := 182) (.out 0x109a92 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[175, 165, 178]
    (.letOp (n := 183) (.exec 0x109a92 (fun s => s.RIP = 0x109a92) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a92 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[175, 165, 178]
    (.letOp (n := 184) (.out 0x109a95 (movR64M64Effect 0x109a95 6 (.base 14 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 185) (.exec 0x109a95 (LoadPre 0x109a95 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x109a95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a95 6 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 186) (.out 0x109a99 (movzxR32R8Effect 0x109a99 4 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[168]
    (.letOp (n := 187) (.exec 0x109a99 (fun s => s.RIP = 0x109a99) (movzxR32R8Effect 0x109a99 4 10 10) (Reg.operands [.gpr 10] [])) #v[168]
    (.letOp (n := 188) (.out 0x109a9d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a9d 10 9)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[186, 142, 182]
    (.letOp (n := 189) (.exec 0x109a9d (fun s => s.RIP = 0x109a9d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a9d 10 9)) (Reg.operands [.gpr 10, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[186, 142, 182]
    (.letOp (n := 190) (.out 0x109aa0 (movR64R64Effect 0x109aa0 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 191) (.exec 0x109aa0 (fun s => s.RIP = 0x109aa0) (movR64R64Effect 0x109aa0 0 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 192) (.out 0x109aa3 (mulR64Effect 0x109aa3 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 190]
    (.letOp (n := 193) (.out 0x109aa3 (mulR64Effect 0x109aa3 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 190]
    (.letOp (n := 194) (.exec 0x109aa3 (fun s => s.RIP = 0x109aa3) (mulR64Effect 0x109aa3 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 190]
    (.letOp (n := 195) (.out 0x109aa6 (movR64R64Effect 0x109aa6 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[193]
    (.letOp (n := 196) (.exec 0x109aa6 (fun s => s.RIP = 0x109aa6) (movR64R64Effect 0x109aa6 15 2) (Reg.operands [.gpr 2] [])) #v[193]
    (.letOp (n := 197) (.out 0x109aa9 (movR64R64Effect 0x109aa9 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[192]
    (.letOp (n := 198) (.exec 0x109aa9 (fun s => s.RIP = 0x109aa9) (movR64R64Effect 0x109aa9 12 0) (Reg.operands [.gpr 0] [])) #v[192]
    (.letOp (n := 199) (.out 0x109aac (movR64M64Effect 0x109aac 3 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 200) (.exec 0x109aac (LoadPre 0x109aac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109aac + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109aac 3 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 201) (.out 0x109ab1 (movR64R64Effect 0x109ab1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[199]
    (.letOp (n := 202) (.exec 0x109ab1 (fun s => s.RIP = 0x109ab1) (movR64R64Effect 0x109ab1 0 3) (Reg.operands [.gpr 3] [])) #v[199]
    (.letOp (n := 203) (.out 0x109ab4 (mulR64Effect 0x109ab4 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 201]
    (.letOp (n := 204) (.out 0x109ab4 (mulR64Effect 0x109ab4 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 201]
    (.letOp (n := 205) (.exec 0x109ab4 (fun s => s.RIP = 0x109ab4) (mulR64Effect 0x109ab4 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 201]
    (.letOp (n := 206) (.out 0x109ab7 (addR64R64Effect 0x109ab7 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[197, 181]
    (.letOp (n := 207) (.out 0x109ab7 (addR64R64Effect 0x109ab7 12 5) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 5] []) (.flag .CF)) #v[197, 181]
    (.letOp (n := 208) (.exec 0x109ab7 (fun s => s.RIP = 0x109ab7) (addR64R64Effect 0x109ab7 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[197, 181]
    (.letOp (n := 209) (.out 0x109aba (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[195, 188, 207]
    (.letOp (n := 210) (.out 0x109aba (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[195, 188, 207]
    (.letOp (n := 211) (.exec 0x109aba (fun s => s.RIP = 0x109aba) (atFlags StatusFlags.CF (adcR64R64Effect 0x109aba 15 10)) (Reg.operands [.gpr 15, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[195, 188, 207]
    (.letOp (n := 212) (.out 0x109abd (atFlags (condHolds 2) (setccR8Effect 0x109abd 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[142, 210]
    (.letOp (n := 213) (.exec 0x109abd (fun s => s.RIP = 0x109abd) (atFlags (condHolds 2) (setccR8Effect 0x109abd 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[142, 210]
    (.letOp (n := 214) (.out 0x109ac1 (addR64R64Effect 0x109ac1 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[206, 203]
    (.letOp (n := 215) (.out 0x109ac1 (addR64R64Effect 0x109ac1 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[206, 203]
    (.letOp (n := 216) (.exec 0x109ac1 (fun s => s.RIP = 0x109ac1) (addR64R64Effect 0x109ac1 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[206, 203]
    (.letOp (n := 217) (.out 0x109ac4 (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[209, 204, 215]
    (.letOp (n := 218) (.out 0x109ac4 (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[209, 204, 215]
    (.letOp (n := 219) (.exec 0x109ac4 (fun s => s.RIP = 0x109ac4) (atFlags StatusFlags.CF (adcR64R64Effect 0x109ac4 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[209, 204, 215]
    (.letOp (n := 220) (.out 0x109ac7 (atFlags (condHolds 2) (setccR8Effect 0x109ac7 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[203, 218]
    (.letOp (n := 221) (.exec 0x109ac7 (fun s => s.RIP = 0x109ac7) (atFlags (condHolds 2) (setccR8Effect 0x109ac7 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[203, 218]
    (.letOp (n := 222) (.out 0x109aca (movzxR32R8Effect 0x109aca 4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[220]
    (.letOp (n := 223) (.exec 0x109aca (fun s => s.RIP = 0x109aca) (movzxR32R8Effect 0x109aca 4 8 0) (Reg.operands [.gpr 0] [])) #v[220]
    (b_l1099c0_4)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_3 : List UInt8 :=
  [0x4C, 0x01, 0xE8, 0x48, 0x89, 0x44, 0x24, 0x30, 0x4C, 0x11, 0xE5, 0x49, 0x8B, 0x76, 0x18, 0x45,
    0x0F, 0xB6, 0xD2, 0x4D, 0x11, 0xCA, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD7, 0x49,
    0x89, 0xC4, 0x48, 0x8B, 0x5C, 0x24, 0x10, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE3, 0x49, 0x01, 0xEC,
    0x4D, 0x11, 0xD7, 0x41, 0x0F, 0x92, 0xC1, 0x49, 0x01, 0xC4, 0x49, 0x11, 0xD7, 0x0F, 0x92, 0xC0,
    0x44, 0x0F, 0xB6, 0xC0] ++ bytes_l1099c0_4

theorem code_l1099c0_3 : ∀ x ∈ codeRange 0x109a8a bytes_l1099c0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9a8a 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_4

@[cfg_block] def b_l1099c0_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x109a44 (atFlags StatusFlags.CF (adcR64R64Effect 0x109a44 15 0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[129, 131, 134]
    (.letOp (n := 137) (.exec 0x109a44 (fun s => s.RIP = 0x109a44) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a44 15 0)) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[129, 131, 134]
    (.letOp (n := 138) (.out 0x109a47 (xorR32R32Effect 0x109a47 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[122, 122]
    (.letOp (n := 139) (.exec 0x109a47 (fun s => s.RIP = 0x109a47) (xorR32R32Effect 0x109a47 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[122, 122]
    (.letOp (n := 140) (.out 0x109a4a (cmpR64R64Effect 0x109a4a 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[136, 131]
    (.letOp (n := 141) (.exec 0x109a4a (fun s => s.RIP = 0x109a4a) (cmpR64R64Effect 0x109a4a 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[136, 131]
    (.letOp (n := 142) (.out 0x109a4d (atFlags (condHolds 2) (setccR8Effect 0x109a4d 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[138, 140]
    (.letOp (n := 143) (.exec 0x109a4d (fun s => s.RIP = 0x109a4d) (atFlags (condHolds 2) (setccR8Effect 0x109a4d 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[138, 140]
    (.letOp (n := 144) (.out 0x109a51 (movR64R64Effect 0x109a51 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 145) (.exec 0x109a51 (fun s => s.RIP = 0x109a51) (movR64R64Effect 0x109a51 0 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 146) (.out 0x109a54 (movR64R64Effect 0x109a54 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[76]
    (.letOp (n := 147) (.exec 0x109a54 (fun s => s.RIP = 0x109a54) (movR64R64Effect 0x109a54 1 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 148) (.exec 0x109a57 (StorePre 0x109a57 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109a57 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a57 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[76, 65]
    (.letOp (n := 149) (.out 0x109a5c (mulR64Effect 0x109a5c 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 144]
    (.letOp (n := 150) (.out 0x109a5c (mulR64Effect 0x109a5c 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 144]
    (.letOp (n := 151) (.exec 0x109a5c (fun s => s.RIP = 0x109a5c) (mulR64Effect 0x109a5c 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 144]
    (.letOp (n := 152) (.exec 0x109a5f (StorePre 0x109a5f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109a5f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a5f 11 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[95, 65]
    (.letOp (n := 153) (.out 0x109a64 (movR64R64Effect 0x109a64 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[150]
    (.letOp (n := 154) (.exec 0x109a64 (fun s => s.RIP = 0x109a64) (movR64R64Effect 0x109a64 12 2) (Reg.operands [.gpr 2] [])) #v[150]
    (.letOp (n := 155) (.out 0x109a67 (movR64R64Effect 0x109a67 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[149]
    (.letOp (n := 156) (.exec 0x109a67 (fun s => s.RIP = 0x109a67) (movR64R64Effect 0x109a67 13 0) (Reg.operands [.gpr 0] [])) #v[149]
    (.letOp (n := 157) (.out 0x109a6a (addR64R64Effect 0x109a6a 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[155, 133]
    (.letOp (n := 158) (.out 0x109a6a (addR64R64Effect 0x109a6a 13 10) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 10] []) (.flag .CF)) #v[155, 133]
    (.letOp (n := 159) (.exec 0x109a6a (fun s => s.RIP = 0x109a6a) (addR64R64Effect 0x109a6a 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[155, 133]
    (.letOp (n := 160) (.out 0x109a6d (movR64M64Effect 0x109a6d 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 161) (.exec 0x109a6d (LoadPre 0x109a6d (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x109a6d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a6d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 162) (.out 0x109a71 (movR64M64Effect 0x109a71 2 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[160]
    (.letOp (n := 163) (.exec 0x109a71 (LoadPre 0x109a71 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109a71 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a71 2 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[160]
    (.letOp (n := 164) (.exec 0x109a75 (StorePre 0x109a75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109a75 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a75 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[162, 65]
    (.letOp (n := 165) (.out 0x109a7a (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[153, 136, 158]
    (.letOp (n := 166) (.out 0x109a7a (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[153, 136, 158]
    (.letOp (n := 167) (.exec 0x109a7a (fun s => s.RIP = 0x109a7a) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a7a 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[153, 136, 158]
    (.letOp (n := 168) (.out 0x109a7d (atFlags (condHolds 2) (setccR8Effect 0x109a7d 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[133, 166]
    (.letOp (n := 169) (.exec 0x109a7d (fun s => s.RIP = 0x109a7d) (atFlags (condHolds 2) (setccR8Effect 0x109a7d 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[133, 166]
    (.letOp (n := 170) (.out 0x109a81 (movR64R64Effect 0x109a81 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 171) (.exec 0x109a81 (fun s => s.RIP = 0x109a81) (movR64R64Effect 0x109a81 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 172) (.out 0x109a84 (mulR64Effect 0x109a84 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[162, 170]
    (.letOp (n := 173) (.out 0x109a84 (mulR64Effect 0x109a84 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[162, 170]
    (.letOp (n := 174) (.exec 0x109a84 (fun s => s.RIP = 0x109a84) (mulR64Effect 0x109a84 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[162, 170]
    (.letOp (n := 175) (.out 0x109a87 (movR64R64Effect 0x109a87 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[173]
    (.letOp (n := 176) (.exec 0x109a87 (fun s => s.RIP = 0x109a87) (movR64R64Effect 0x109a87 5 2) (Reg.operands [.gpr 2] [])) #v[173]
    (b_l1099c0_3)))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_2 : List UInt8 :=
  [0x49, 0x11, 0xC7, 0x45, 0x31, 0xC9, 0x49, 0x39, 0xC7, 0x41, 0x0F, 0x92, 0xC1, 0x4C, 0x89, 0xE8,
    0x4C, 0x89, 0xE9, 0x4C, 0x89, 0x6C, 0x24, 0x20, 0x49, 0xF7, 0xE3, 0x4C, 0x89, 0x5C, 0x24, 0x18,
    0x49, 0x89, 0xD4, 0x49, 0x89, 0xC5, 0x4D, 0x01, 0xD5, 0x48, 0x8B, 0x04, 0x24, 0x48, 0x8B, 0x50,
    0x10, 0x48, 0x89, 0x54, 0x24, 0x08, 0x4D, 0x11, 0xFC, 0x41, 0x0F, 0x92, 0xC2, 0x48, 0x89, 0xF0,
    0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD5] ++ bytes_l1099c0_3

theorem code_l1099c0_2 : ∀ x ∈ codeRange 0x109a44 bytes_l1099c0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9a44 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_3

@[cfg_block] def b_l1099c0_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1099fc (movR64R64Effect 0x1099fc 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[89]
    (.letOp (n := 94) (.exec 0x1099fc (fun s => s.RIP = 0x1099fc) (movR64R64Effect 0x1099fc 15 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 95) (.out 0x1099ff (movR64M64Effect 0x1099ff 11 (.base 11 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[71]
    (.letOp (n := 96) (.exec 0x1099ff (LoadPre 0x1099ff (fun s => AddrMode.addr (.base 11 (.d8 0x8)) s (0x1099ff + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099ff 11 (.base 11 (.d8 0x8))) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 97) (.out 0x109a03 (leaR64Effect 0x109a03 3 (.sib 9 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9, .gpr 0] []) (.reg (.gpr 3))) #v[83, 88]
    (.letOp (n := 98) (.exec 0x109a03 (fun s => s.RIP = 0x109a03) (leaR64Effect 0x109a03 3 (.sib 9 (some 0) 0 .none)) (Reg.operands [.gpr 9, .gpr 0] [])) #v[83, 88]
    (.letOp (n := 99) (.out 0x109a07 (movR64R64Effect 0x109a07 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 100) (.exec 0x109a07 (fun s => s.RIP = 0x109a07) (movR64R64Effect 0x109a07 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 101) (.exec 0x109a0a (StorePre 0x109a0a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109a0a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a0a 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 65]
    (.letOp (n := 102) (.out 0x109a0f (mulR64Effect 0x109a0f 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[95, 99]
    (.letOp (n := 103) (.out 0x109a0f (mulR64Effect 0x109a0f 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[95, 99]
    (.letOp (n := 104) (.exec 0x109a0f (fun s => s.RIP = 0x109a0f) (mulR64Effect 0x109a0f 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[95, 99]
    (.letOp (n := 105) (.out 0x109a12 (movR64R64Effect 0x109a12 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[103]
    (.letOp (n := 106) (.exec 0x109a12 (fun s => s.RIP = 0x109a12) (movR64R64Effect 0x109a12 12 2) (Reg.operands [.gpr 2] [])) #v[103]
    (.letOp (n := 107) (.out 0x109a15 (addR64R64Effect 0x109a15 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[102, 97]
    (.letOp (n := 108) (.out 0x109a15 (addR64R64Effect 0x109a15 0 3) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 3] []) (.flag .CF)) #v[102, 97]
    (.letOp (n := 109) (.exec 0x109a15 (fun s => s.RIP = 0x109a15) (addR64R64Effect 0x109a15 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[102, 97]
    (.letOp (n := 110) (.exec 0x109a18 (StorePre 0x109a18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x109a18 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a18 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[107, 65]
    (.letOp (n := 111) (.out 0x109a1d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109a1d 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[105, 108]
    (.letOp (n := 112) (.exec 0x109a1d (fun s => s.RIP = 0x109a1d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x109a1d 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[105, 108]
    (.letOp (n := 113) (.out 0x109a21 (addR64R64Effect 0x109a21 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[83, 91]
    (.letOp (n := 114) (.out 0x109a21 (addR64R64Effect 0x109a21 9 10) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 10] []) (.flag .CF)) #v[83, 91]
    (.letOp (n := 115) (.exec 0x109a21 (fun s => s.RIP = 0x109a21) (addR64R64Effect 0x109a21 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[83, 91]
    (.letOp (n := 116) (.out 0x109a24 (movR64M64Effect 0x109a24 0 (.base 14 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 117) (.exec 0x109a24 (LoadPre 0x109a24 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x109a24 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109a24 0 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 118) (.exec 0x109a28 (StorePre 0x109a28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109a28 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109a28 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x109a2d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[111, 93, 114]
    (.letOp (n := 120) (.out 0x109a2d (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[111, 93, 114]
    (.letOp (n := 121) (.exec 0x109a2d (fun s => s.RIP = 0x109a2d) (atFlags StatusFlags.CF (adcR64R64Effect 0x109a2d 12 15)) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[111, 93, 114]
    (.letOp (n := 122) (.out 0x109a30 (atFlags (condHolds 2) (setccR8Effect 0x109a30 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[113, 120]
    (.letOp (n := 123) (.exec 0x109a30 (fun s => s.RIP = 0x109a30) (atFlags (condHolds 2) (setccR8Effect 0x109a30 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[113, 120]
    (.letOp (n := 124) (.out 0x109a34 (mulR64Effect 0x109a34 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 116]
    (.letOp (n := 125) (.out 0x109a34 (mulR64Effect 0x109a34 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 116]
    (.letOp (n := 126) (.exec 0x109a34 (fun s => s.RIP = 0x109a34) (mulR64Effect 0x109a34 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 116]
    (.letOp (n := 127) (.out 0x109a37 (movR64R64Effect 0x109a37 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[124]
    (.letOp (n := 128) (.exec 0x109a37 (fun s => s.RIP = 0x109a37) (movR64R64Effect 0x109a37 10 0) (Reg.operands [.gpr 0] [])) #v[124]
    (.letOp (n := 129) (.out 0x109a3a (movR64R64Effect 0x109a3a 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[125]
    (.letOp (n := 130) (.exec 0x109a3a (fun s => s.RIP = 0x109a3a) (movR64R64Effect 0x109a3a 15 2) (Reg.operands [.gpr 2] [])) #v[125]
    (.letOp (n := 131) (.out 0x109a3d (movzxR32R8Effect 0x109a3d 4 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[122]
    (.letOp (n := 132) (.exec 0x109a3d (fun s => s.RIP = 0x109a3d) (movzxR32R8Effect 0x109a3d 4 0 9) (Reg.operands [.gpr 9] [])) #v[122]
    (.letOp (n := 133) (.out 0x109a41 (addR64R64Effect 0x109a41 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[127, 119]
    (.letOp (n := 134) (.out 0x109a41 (addR64R64Effect 0x109a41 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[127, 119]
    (.letOp (n := 135) (.exec 0x109a41 (fun s => s.RIP = 0x109a41) (addR64R64Effect 0x109a41 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[127, 119]
    (b_l1099c0_2)))))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0_1 : List UInt8 :=
  [0x49, 0x89, 0xD7, 0x4D, 0x8B, 0x5B, 0x08, 0x49, 0x8D, 0x1C, 0x01, 0x48, 0x89, 0xF0, 0x48, 0x89,
    0x74, 0x24, 0x28, 0x49, 0xF7, 0xE3, 0x49, 0x89, 0xD4, 0x48, 0x01, 0xD8, 0x48, 0x89, 0x44, 0x24,
    0x38, 0x49, 0x83, 0xD4, 0x00, 0x4D, 0x01, 0xD1, 0x49, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x10, 0x4D, 0x11, 0xFC, 0x41, 0x0F, 0x92, 0xC1, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC2, 0x49, 0x89,
    0xD7, 0x41, 0x0F, 0xB6, 0xC1, 0x4D, 0x01, 0xE2] ++ bytes_l1099c0_2

theorem code_l1099c0_1 : ∀ x ∈ codeRange 0x1099fc bytes_l1099c0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x99fc 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_2

@[cfg_block] def b_l1099c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1099c0 (pushR64Effect 0x1099c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1099c0 (PushPre 0x1099c0 1) (pushR64Effect 0x1099c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1099c1 (pushR64Effect 0x1099c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1099c1 (PushPre 0x1099c1 2) (pushR64Effect 0x1099c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1099c3 (pushR64Effect 0x1099c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1099c3 (PushPre 0x1099c3 2) (pushR64Effect 0x1099c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1099c5 (pushR64Effect 0x1099c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1099c5 (PushPre 0x1099c5 2) (pushR64Effect 0x1099c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1099c7 (pushR64Effect 0x1099c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1099c7 (PushPre 0x1099c7 2) (pushR64Effect 0x1099c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1099c9 (pushR64Effect 0x1099c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1099c9 (PushPre 0x1099c9 1) (pushR64Effect 0x1099c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1099ca (subR64Imm32Effect 0x1099ca 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1099ca (fun s => s.RIP = 0x1099ca) (subR64Imm32Effect 0x1099ca 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1099d1 (movR64R64Effect 0x1099d1 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 68) (.exec 0x1099d1 (fun s => s.RIP = 0x1099d1) (movR64R64Effect 0x1099d1 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1099d4 (movR64M64Effect 0x1099d4 8 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x1099d4 (LoadPre 0x1099d4 (fun s => AddrMode.addr (.base 6 .none) s (0x1099d4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099d4 8 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x1099d7 (movR64R64Effect 0x1099d7 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 72) (.exec 0x1099d7 (fun s => s.RIP = 0x1099d7) (movR64R64Effect 0x1099d7 11 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.exec 0x1099da (StorePre 0x1099da 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1099da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1099da 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 74) (.out 0x1099de (movR64M64Effect 0x1099de 6 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 75) (.exec 0x1099de (LoadPre 0x1099de (fun s => AddrMode.addr (.base 2 .none) s (0x1099de + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1099de 6 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 76) (.out 0x1099e1 (movR64M64Effect 0x1099e1 13 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 77) (.exec 0x1099e1 (LoadPre 0x1099e1 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1099e1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1099e1 13 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 78) (.out 0x1099e5 (movR64R64Effect 0x1099e5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[74]
    (.letOp (n := 79) (.exec 0x1099e5 (fun s => s.RIP = 0x1099e5) (movR64R64Effect 0x1099e5 0 6) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 80) (.out 0x1099e8 (mulR64Effect 0x1099e8 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 78]
    (.letOp (n := 81) (.out 0x1099e8 (mulR64Effect 0x1099e8 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 78]
    (.letOp (n := 82) (.exec 0x1099e8 (fun s => s.RIP = 0x1099e8) (mulR64Effect 0x1099e8 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 78]
    (.letOp (n := 83) (.out 0x1099eb (movR64R64Effect 0x1099eb 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[81]
    (.letOp (n := 84) (.exec 0x1099eb (fun s => s.RIP = 0x1099eb) (movR64R64Effect 0x1099eb 9 2) (Reg.operands [.gpr 2] [])) #v[81]
    (.letOp (n := 85) (.exec 0x1099ee (StorePre 0x1099ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1099ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1099ee 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 86) (.out 0x1099f3 (movR64R64Effect 0x1099f3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 87) (.exec 0x1099f3 (fun s => s.RIP = 0x1099f3) (movR64R64Effect 0x1099f3 0 13) (Reg.operands [.gpr 13] [])) #v[76]
    (.letOp (n := 88) (.out 0x1099f6 (mulR64Effect 0x1099f6 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[69, 86]
    (.letOp (n := 89) (.out 0x1099f6 (mulR64Effect 0x1099f6 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[69, 86]
    (.letOp (n := 90) (.exec 0x1099f6 (fun s => s.RIP = 0x1099f6) (mulR64Effect 0x1099f6 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[69, 86]
    (.letOp (n := 91) (.out 0x1099f9 (movR64R64Effect 0x1099f9 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[88]
    (.letOp (n := 92) (.exec 0x1099f9 (fun s => s.RIP = 0x1099f9) (movR64R64Effect 0x1099f9 10 0) (Reg.operands [.gpr 0] [])) #v[88]
    (b_l1099c0_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1099c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD6, 0x4C, 0x8B, 0x06, 0x49, 0x89, 0xF3, 0x48, 0x89, 0x34, 0x24, 0x48, 0x8B,
    0x32, 0x4C, 0x8B, 0x6A, 0x08, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD1, 0x48, 0x89,
    0x44, 0x24, 0x40, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xC2] ++ bytes_l1099c0_1

theorem code_l1099c0 : ∀ x ∈ codeRange 0x1099c0 bytes_l1099c0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x99c0 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1099c0_1

@[cfg_block] def b_l109be7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109be7 (movR64R64Effect 0x109be7 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 54) (.exec 0x109be7 (fun s => s.RIP = 0x109be7) (movR64R64Effect 0x109be7 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x109bea (addR64Imm32Effect 0x109bea 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x109bea (fun s => s.RIP = 0x109bea) (addR64Imm32Effect 0x109bea 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109bf1 (popR64Effect 0x109bf1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x109bf1 (popR64Effect 0x109bf1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x109bf1 (PopPre 0x109bf1) (popR64Effect 0x109bf1 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x109bf2 (popR64Effect 0x109bf2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x109bf2 (popR64Effect 0x109bf2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x109bf2 (PopPre 0x109bf2) (popR64Effect 0x109bf2 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x109bf4 (popR64Effect 0x109bf4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x109bf4 (popR64Effect 0x109bf4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x109bf4 (PopPre 0x109bf4) (popR64Effect 0x109bf4 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x109bf6 (popR64Effect 0x109bf6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x109bf6 (popR64Effect 0x109bf6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x109bf6 (PopPre 0x109bf6) (popR64Effect 0x109bf6 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x109bf8 (popR64Effect 0x109bf8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x109bf8 (popR64Effect 0x109bf8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x109bf8 (PopPre 0x109bf8) (popR64Effect 0x109bf8 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x109bfa (popR64Effect 0x109bfa 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x109bfa (popR64Effect 0x109bfa 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x109bfa (PopPre 0x109bfa) (popR64Effect 0x109bfa 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x109bfb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x109bfb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x109bfb (RetPre 0x109bfb) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l109be7 : List UInt8 :=
  [0x4C, 0x89, 0xF0, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l109be7 : ∀ x ∈ codeRange 0x109be7 bytes_l109be7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9be7 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Ecdh.LIR
