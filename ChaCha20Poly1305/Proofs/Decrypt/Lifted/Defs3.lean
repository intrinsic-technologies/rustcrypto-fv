import ChaCha20Poly1305.Proofs.Decrypt.Movsd
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Labels
import ChaCha20Poly1305.Proofs.Common.CFG.EvalAttr
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Footprints

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def b_l1010d5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1010d5 (andR64Imm8Effect 0x1010d5 11 0xc0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 54) (.exec 0x1010d5 (fun s => s.RIP = 0x1010d5) (andR64Imm8Effect 0x1010d5 11 0xc0) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 55) (.exec 0x1010d9 (StorePre 0x1010d9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1010d9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d9 11 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1010de (movR32M32LowEffect 0x1010de 3 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 57) (.exec 0x1010de (LoadPre 0x1010de (fun s => AddrMode.addr (.base 7 .none) s (0x1010de + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x1010de 3 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 58) (.out 0x1010e0 (movR32M32Effect 0x1010e0 13 (.base 7 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[7]
    (.letOp (n := 59) (.exec 0x1010e0 (LoadPre 0x1010e0 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x1010e0 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010e0 13 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 60) (.out 0x1010e4 (movR32M32LowEffect 0x1010e4 6 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 61) (.exec 0x1010e4 (LoadPre 0x1010e4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1010e4 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010e4 6 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 62) (.out 0x1010e7 (movR32M32LowEffect 0x1010e7 0 (.base 7 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 63) (.exec 0x1010e7 (LoadPre 0x1010e7 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x1010e7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010e7 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 64) (.exec 0x1010ea (StorePre 0x1010ea 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1010ea + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1010ea 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1010ee (movR32M32Effect 0x1010ee 9 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 7] []) (.reg (.gpr 9))) #v[7]
    (.letOp (n := 66) (.exec 0x1010ee (LoadPre 0x1010ee (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1010ee + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010ee 9 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x1010f2 (movR32M32LowEffect 0x1010f2 5 (.base 7 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[7]
    (.letOp (n := 68) (.exec 0x1010f2 (LoadPre 0x1010f2 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x1010f2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010f2 5 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x1010f5 (movR32M32Effect 0x1010f5 15 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 70) (.exec 0x1010f5 (LoadPre 0x1010f5 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1010f5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1010f5 15 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x1010f9 (movR32M32LowEffect 0x1010f9 0 (.base 7 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 72) (.exec 0x1010f9 (LoadPre 0x1010f9 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x1010f9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1010f9 0 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.exec 0x1010fc (StorePre 0x1010fc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1010fc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1010fc 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x101100 (movR32M32LowEffect 0x101100 0 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 75) (.exec 0x101100 (LoadPre 0x101100 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x101100 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101100 0 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 76) (.out 0x101103 (movR32M32Effect 0x101103 10 (.base 7 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 77) (.exec 0x101103 (LoadPre 0x101103 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x101103 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101103 10 (.base 7 (.d8 0x24))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x101107 (movR32M32Effect 0x101107 14 (.base 7 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 79) (.exec 0x101107 (LoadPre 0x101107 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x101107 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101107 14 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 80) (.out 0x10110b (movR32M32Effect 0x10110b 12 (.base 7 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 81) (.exec 0x10110b (LoadPre 0x10110b (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x10110b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10110b 12 (.base 7 (.d8 0x2c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 82) (.out 0x10110f (movR32M32LowEffect 0x10110f 1 (.base 7 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 83) (.exec 0x10110f (LoadPre 0x10110f (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10110f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x10110f 1 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 84) (.out 0x101112 (movR32M32LowEffect 0x101112 2 (.base 7 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 85) (.exec 0x101112 (LoadPre 0x101112 (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x101112 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x101112 2 (.base 7 (.d8 0x34))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 86) (.out 0x101115 (movR32M32Effect 0x101115 8 (.base 7 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 87) (.exec 0x101115 (LoadPre 0x101115 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x101115 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101115 8 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 88) (.out 0x101119 (movR32M32Effect 0x101119 11 (.base 7 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 89) (.exec 0x101119 (LoadPre 0x101119 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x101119 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x101119 11 (.base 7 (.d8 0x3c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.terminate (.br ⟨.l10111d, RegMap.args [(0, 74), (1, 82), (2, 84), (3, 56), (4, 4), (5, 67), (6, 60), (7, 7), (8, 86), (9, 65), (10, 76), (11, 88), (12, 80), (13, 58), (14, 78), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))))))))))))))))))))))))))))))))))))))

def bytes_l1010d5 : List UInt8 :=
  [0x49, 0x83, 0xE3, 0xC0, 0x4C, 0x89, 0x5C, 0x24, 0x40, 0x8B, 0x1F, 0x44, 0x8B, 0x6F, 0x04, 0x8B,
    0x77, 0x08, 0x8B, 0x47, 0x0C, 0x89, 0x44, 0x24, 0x0C, 0x44, 0x8B, 0x4F, 0x10, 0x8B, 0x6F, 0x14,
    0x44, 0x8B, 0x7F, 0x18, 0x8B, 0x47, 0x1C, 0x89, 0x44, 0x24, 0x10, 0x8B, 0x47, 0x20, 0x44, 0x8B,
    0x57, 0x24, 0x44, 0x8B, 0x77, 0x28, 0x44, 0x8B, 0x67, 0x2C, 0x8B, 0x4F, 0x30, 0x8B, 0x57, 0x34,
    0x44, 0x8B, 0x47, 0x38, 0x44, 0x8B, 0x5F, 0x3C]

theorem code_l1010d5 : ∀ x ∈ codeRange 0x1010d5 bytes_l1010d5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10d5 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10111d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10111d (movR32Imm32Effect 0x10111d 5 7 0xa) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 54) (.exec 0x10111d (fun s => s.RIP = 0x10111d) (movR32Imm32Effect 0x10111d 5 7 0xa) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.exec 0x101122 (StorePre 0x101122 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101122 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101122 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x101127 (StorePre 0x101127 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101127 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101127 3 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 57) (.exec 0x10112b (StorePre 0x10112b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10112b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10112b 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 58) (.exec 0x10112f (StorePre 0x10112f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10112f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10112f 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 59) (.exec 0x101134 (StorePre 0x101134 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x101134 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101134 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 60) (.exec 0x101138 (StorePre 0x101138 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101138 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101138 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 61) (.exec 0x10113c (StorePre 0x10113c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10113c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10113c 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 62) (.exec 0x101140 (StorePre 0x101140 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101140 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101140 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 63) (.exec 0x101145 (StorePre 0x101145 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101145 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101145 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 64) (.exec 0x101149 (StorePre 0x101149 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101149 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101149 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 65) (.exec 0x10114d (StorePre 0x10114d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10114d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10114d 10 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 66) (.exec 0x101152 (StorePre 0x101152 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101152 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101152 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 67) (.out 0x101156 (movR32R32Effect 0x101156 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x101156 (fun s => s.RIP = 0x101156) (movR32R32Effect 0x101156 2 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x101158 (StorePre 0x101158 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x101158 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101158 15 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 70) (.exec 0x10115d (StorePre 0x10115d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10115d + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10115d 8 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 71) (.exec 0x101162 (StorePre 0x101162 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101162 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101162 14 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 72) (.out 0x101167 (movR32M32LowEffect 0x101167 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 73) (.exec 0x101167 (LoadPre 0x101167 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x101167 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101167 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x10116b (movR32M32LowEffect 0x10116b 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 75) (.exec 0x10116b (LoadPre 0x10116b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10116b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10116b 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10116f (StorePre 0x10116f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10116f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10116f 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.terminate (.br ⟨.l101174, RegMap.args [(0, 67), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 74), (7, 72), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l10111d : List UInt8 :=
  [0xBF, 0x0A, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x58, 0x89, 0x5C, 0x24, 0x38, 0x89, 0x5C,
    0x24, 0x08, 0x44, 0x89, 0x4C, 0x24, 0x50, 0x89, 0x4C, 0x24, 0x34, 0x89, 0x44, 0x24, 0x18, 0x89,
    0x44, 0x24, 0x04, 0x44, 0x89, 0x6C, 0x24, 0x60, 0x89, 0x6C, 0x24, 0x70, 0x89, 0x54, 0x24, 0x28,
    0x44, 0x89, 0x54, 0x24, 0x1C, 0x89, 0x74, 0x24, 0x68, 0x89, 0xF0, 0x44, 0x89, 0x7C, 0x24, 0x3C,
    0x44, 0x89, 0x44, 0x24, 0x2C, 0x44, 0x89, 0x74, 0x24, 0x20, 0x8B, 0x7C, 0x24, 0x0C, 0x8B, 0x74,
    0x24, 0x10, 0x44, 0x89, 0x5C, 0x24, 0x30]

theorem code_l10111d : ∀ x ∈ codeRange 0x10111d bytes_l10111d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x111d 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101174 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101174 (StorePre 0x101174 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x101174 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101174 12 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 54) (.exec 0x101179 (fun s => s.RIP = 0x101179) (fun _ => nopEffect 0x101179 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101180, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101174 : List UInt8 :=
  [0x44, 0x89, 0x64, 0x24, 0x24, 0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l101174 : ∀ x ∈ codeRange 0x101174 bytes_l101174, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1174 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101180 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101180 (StorePre 0x101180 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101180 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x101180 14 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 54) (.out 0x101185 (movR32M32Effect 0x101185 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 55) (.exec 0x101185 (LoadPre 0x101185 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101185 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101185 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10118a (addR32R32Effect 0x10118a 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[54, 9]
    (.letOp (n := 57) (.exec 0x10118a (fun s => s.RIP = 0x10118a) (addR32R32Effect 0x10118a 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[54, 9]
    (.letOp (n := 58) (.out 0x10118d (xorR32R32Effect 0x10118d 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[1, 56]
    (.letOp (n := 59) (.exec 0x10118d (fun s => s.RIP = 0x10118d) (xorR32R32Effect 0x10118d 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[1, 56]
    (.letOp (n := 60) (.out 0x101190 (rolR32Effect 0x101190 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[58]
    (.letOp (n := 61) (.exec 0x101190 (fun s => s.RIP = 0x101190) (rolR32Effect 0x101190 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x101193 (movR32M32LowEffect 0x101193 3 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 63) (.exec 0x101193 (LoadPre 0x101193 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101193 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101193 3 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x101197 (addR32R32Effect 0x101197 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x101197 (fun s => s.RIP = 0x101197) (addR32R32Effect 0x101197 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x101199 (xorR32R32Effect 0x101199 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[9, 64]
    (.letOp (n := 67) (.exec 0x101199 (fun s => s.RIP = 0x101199) (xorR32R32Effect 0x101199 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 64]
    (.letOp (n := 68) (.out 0x10119c (rolR32Effect 0x10119c 4 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[66]
    (.letOp (n := 69) (.exec 0x10119c (fun s => s.RIP = 0x10119c) (rolR32Effect 0x10119c 4 9 12) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 70) (.out 0x1011a0 (addR32R32Effect 0x1011a0 3 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[56, 68]
    (.letOp (n := 71) (.exec 0x1011a0 (fun s => s.RIP = 0x1011a0) (addR32R32Effect 0x1011a0 3 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[56, 68]
    (.letOp (n := 72) (.out 0x1011a3 (xorR32R32Effect 0x1011a3 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[60, 70]
    (.letOp (n := 73) (.exec 0x1011a3 (fun s => s.RIP = 0x1011a3) (xorR32R32Effect 0x1011a3 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[60, 70]
    (.letOp (n := 74) (.out 0x1011a6 (rolR32Effect 0x1011a6 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[72]
    (.letOp (n := 75) (.exec 0x1011a6 (fun s => s.RIP = 0x1011a6) (rolR32Effect 0x1011a6 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[72]
    (.letOp (n := 76) (.out 0x1011a9 (addR32R32Effect 0x1011a9 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[64, 74]
    (.letOp (n := 77) (.exec 0x1011a9 (fun s => s.RIP = 0x1011a9) (addR32R32Effect 0x1011a9 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[64, 74]
    (.letOp (n := 78) (.exec 0x1011ab (StorePre 0x1011ab 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1011ab + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1011ab 3 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x1011af (xorR32R32Effect 0x1011af 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[68, 76]
    (.letOp (n := 80) (.exec 0x1011af (fun s => s.RIP = 0x1011af) (xorR32R32Effect 0x1011af 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[68, 76]
    (.letOp (n := 81) (.out 0x1011b2 (movR32R32Effect 0x1011b2 3 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 14] []) (.reg (.gpr 3))) #v[70]
    (.letOp (n := 82) (.exec 0x1011b2 (fun s => s.RIP = 0x1011b2) (movR32R32Effect 0x1011b2 3 3 14) (Reg.operands [.gpr 14] [])) #v[70]
    (.letOp (n := 83) (.out 0x1011b5 (movR32M32Effect 0x1011b5 14 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 84) (.exec 0x1011b5 (LoadPre 0x1011b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1011b5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1011b5 14 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x1011ba (rolR32Effect 0x1011ba 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[79]
    (.letOp (n := 86) (.exec 0x1011ba (fun s => s.RIP = 0x1011ba) (rolR32Effect 0x1011ba 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.terminate (.br ⟨.l1011be, RegMap.args [(0, 0), (1, 74), (2, 2), (3, 81), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 85), (10, 10), (11, 11), (12, 12), (13, 13), (14, 83), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩)))))))))))))))))))))))))))))))))))

def bytes_l101180 : List UInt8 :=
  [0x44, 0x89, 0x74, 0x24, 0x78, 0x44, 0x8B, 0x74, 0x24, 0x08, 0x45, 0x01, 0xCE, 0x44, 0x31, 0xF1,
    0xC1, 0xC1, 0x10, 0x8B, 0x5C, 0x24, 0x04, 0x01, 0xCB, 0x41, 0x31, 0xD9, 0x41, 0xC1, 0xC1, 0x0C,
    0x45, 0x01, 0xCE, 0x44, 0x31, 0xF1, 0xC1, 0xC1, 0x08, 0x01, 0xCB, 0x89, 0x5C, 0x24, 0x04, 0x41,
    0x31, 0xD9, 0x44, 0x89, 0xF3, 0x44, 0x8B, 0x74, 0x24, 0x78, 0x41, 0xC1, 0xC1, 0x07]

theorem code_l101180 : ∀ x ∈ codeRange 0x101180 bytes_l101180, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1180 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011be : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011be (addR32R32Effect 0x1011be 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[13, 5]
    (.letOp (n := 54) (.exec 0x1011be (fun s => s.RIP = 0x1011be) (addR32R32Effect 0x1011be 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 55) (.out 0x1011c1 (xorR32R32Effect 0x1011c1 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x1011c1 (fun s => s.RIP = 0x1011c1) (xorR32R32Effect 0x1011c1 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x1011c4 (rolR32Effect 0x1011c4 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.exec 0x1011c4 (fun s => s.RIP = 0x1011c4) (rolR32Effect 0x1011c4 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x1011c7 (addR32R32Effect 0x1011c7 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[10, 57]
    (.letOp (n := 60) (.exec 0x1011c7 (fun s => s.RIP = 0x1011c7) (addR32R32Effect 0x1011c7 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[10, 57]
    (.letOp (n := 61) (.out 0x1011ca (xorR32R32Effect 0x1011ca 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[5, 59]
    (.letOp (n := 62) (.exec 0x1011ca (fun s => s.RIP = 0x1011ca) (xorR32R32Effect 0x1011ca 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[5, 59]
    (.letOp (n := 63) (.out 0x1011cd (rolR32Effect 0x1011cd 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.exec 0x1011cd (fun s => s.RIP = 0x1011cd) (rolR32Effect 0x1011cd 3 5 12) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x1011d0 (addR32R32Effect 0x1011d0 3 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x1011d0 (fun s => s.RIP = 0x1011d0) (addR32R32Effect 0x1011d0 3 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x1011d3 (xorR32R32Effect 0x1011d3 3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x1011d3 (fun s => s.RIP = 0x1011d3) (xorR32R32Effect 0x1011d3 3 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x1011d6 (rolR32Effect 0x1011d6 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 70) (.exec 0x1011d6 (fun s => s.RIP = 0x1011d6) (rolR32Effect 0x1011d6 3 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1011d9 (addR32R32Effect 0x1011d9 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x1011d9 (fun s => s.RIP = 0x1011d9) (addR32R32Effect 0x1011d9 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[59, 69]
    (.letOp (n := 73) (.exec 0x1011dc (StorePre 0x1011dc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1011dc + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1011dc 10 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x1011e1 (xorR32R32Effect 0x1011e1 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[63, 71]
    (.letOp (n := 75) (.exec 0x1011e1 (fun s => s.RIP = 0x1011e1) (xorR32R32Effect 0x1011e1 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[63, 71]
    (.letOp (n := 76) (.out 0x1011e4 (rolR32Effect 0x1011e4 3 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[74]
    (.letOp (n := 77) (.exec 0x1011e4 (fun s => s.RIP = 0x1011e4) (rolR32Effect 0x1011e4 3 5 7) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.terminate (.br ⟨.l1011e7, RegMap.args [(0, 0), (1, 1), (2, 69), (3, 3), (4, 4), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l1011be : List UInt8 :=
  [0x41, 0x01, 0xED, 0x44, 0x31, 0xEA, 0xC1, 0xC2, 0x10, 0x41, 0x01, 0xD2, 0x44, 0x31, 0xD5, 0xC1,
    0xC5, 0x0C, 0x41, 0x01, 0xED, 0x44, 0x31, 0xEA, 0xC1, 0xC2, 0x08, 0x41, 0x01, 0xD2, 0x44, 0x89,
    0x54, 0x24, 0x14, 0x44, 0x31, 0xD5, 0xC1, 0xC5, 0x07]

theorem code_l1011be : ∀ x ∈ codeRange 0x1011be bytes_l1011be, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11be 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1011e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1011e7 (addR32R32Effect 0x1011e7 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[0, 15]
    (.letOp (n := 54) (.exec 0x1011e7 (fun s => s.RIP = 0x1011e7) (addR32R32Effect 0x1011e7 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[0, 15]
    (.letOp (n := 55) (.out 0x1011ea (xorR32R32Effect 0x1011ea 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[8, 53]
    (.letOp (n := 56) (.exec 0x1011ea (fun s => s.RIP = 0x1011ea) (xorR32R32Effect 0x1011ea 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 53]
    (.letOp (n := 57) (.out 0x1011ed (rolR32Effect 0x1011ed 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x1011ed (fun s => s.RIP = 0x1011ed) (rolR32Effect 0x1011ed 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x1011f1 (addR32R32Effect 0x1011f1 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[14, 57]
    (.letOp (n := 60) (.exec 0x1011f1 (fun s => s.RIP = 0x1011f1) (addR32R32Effect 0x1011f1 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[14, 57]
    (.letOp (n := 61) (.out 0x1011f4 (xorR32R32Effect 0x1011f4 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[15, 59]
    (.letOp (n := 62) (.exec 0x1011f4 (fun s => s.RIP = 0x1011f4) (xorR32R32Effect 0x1011f4 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 59]
    (.letOp (n := 63) (.out 0x1011f7 (rolR32Effect 0x1011f7 4 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 64) (.exec 0x1011f7 (fun s => s.RIP = 0x1011f7) (rolR32Effect 0x1011f7 4 15 12) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x1011fb (addR32R32Effect 0x1011fb 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x1011fb (fun s => s.RIP = 0x1011fb) (addR32R32Effect 0x1011fb 3 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x1011fe (xorR32R32Effect 0x1011fe 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x1011fe (fun s => s.RIP = 0x1011fe) (xorR32R32Effect 0x1011fe 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x101201 (rolR32Effect 0x101201 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[67]
    (.letOp (n := 70) (.exec 0x101201 (fun s => s.RIP = 0x101201) (rolR32Effect 0x101201 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x101205 (addR32R32Effect 0x101205 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x101205 (fun s => s.RIP = 0x101205) (addR32R32Effect 0x101205 3 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x101208 (xorR32R32Effect 0x101208 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x101208 (fun s => s.RIP = 0x101208) (xorR32R32Effect 0x101208 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x10120b (rolR32Effect 0x10120b 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[73]
    (.letOp (n := 76) (.exec 0x10120b (fun s => s.RIP = 0x10120b) (rolR32Effect 0x10120b 4 15 7) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l10120f, RegMap.args [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 69), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1011e7 : List UInt8 :=
  [0x44, 0x01, 0xF8, 0x41, 0x31, 0xC0, 0x41, 0xC1, 0xC0, 0x10, 0x45, 0x01, 0xC6, 0x45, 0x31, 0xF7,
    0x41, 0xC1, 0xC7, 0x0C, 0x44, 0x01, 0xF8, 0x41, 0x31, 0xC0, 0x41, 0xC1, 0xC0, 0x08, 0x45, 0x01,
    0xC6, 0x45, 0x31, 0xF7, 0x41, 0xC1, 0xC7, 0x07]

theorem code_l1011e7 : ∀ x ∈ codeRange 0x1011e7 bytes_l1011e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x11e7 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10120f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10120f (addR32R32Effect 0x10120f 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[7, 6]
    (.letOp (n := 54) (.exec 0x10120f (fun s => s.RIP = 0x10120f) (addR32R32Effect 0x10120f 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[7, 6]
    (.letOp (n := 55) (.out 0x101211 (xorR32R32Effect 0x101211 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[11, 53]
    (.letOp (n := 56) (.exec 0x101211 (fun s => s.RIP = 0x101211) (xorR32R32Effect 0x101211 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[11, 53]
    (.letOp (n := 57) (.out 0x101214 (rolR32Effect 0x101214 4 11 16) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[55]
    (.letOp (n := 58) (.exec 0x101214 (fun s => s.RIP = 0x101214) (rolR32Effect 0x101214 4 11 16) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x101218 (addR32R32Effect 0x101218 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[12, 57]
    (.letOp (n := 60) (.exec 0x101218 (fun s => s.RIP = 0x101218) (addR32R32Effect 0x101218 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[12, 57]
    (.letOp (n := 61) (.out 0x10121b (xorR32R32Effect 0x10121b 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[6, 59]
    (.letOp (n := 62) (.exec 0x10121b (fun s => s.RIP = 0x10121b) (xorR32R32Effect 0x10121b 3 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[6, 59]
    (.letOp (n := 63) (.out 0x10121e (rolR32Effect 0x10121e 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[61]
    (.letOp (n := 64) (.exec 0x10121e (fun s => s.RIP = 0x10121e) (rolR32Effect 0x10121e 3 6 12) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x101221 (addR32R32Effect 0x101221 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x101221 (fun s => s.RIP = 0x101221) (addR32R32Effect 0x101221 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x101223 (xorR32R32Effect 0x101223 3 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x101223 (fun s => s.RIP = 0x101223) (xorR32R32Effect 0x101223 3 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x101226 (rolR32Effect 0x101226 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 70) (.exec 0x101226 (fun s => s.RIP = 0x101226) (rolR32Effect 0x101226 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x10122a (addR32R32Effect 0x10122a 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x10122a (fun s => s.RIP = 0x10122a) (addR32R32Effect 0x10122a 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x10122d (xorR32R32Effect 0x10122d 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x10122d (fun s => s.RIP = 0x10122d) (xorR32R32Effect 0x10122d 3 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x101230 (rolR32Effect 0x101230 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x101230 (fun s => s.RIP = 0x101230) (rolR32Effect 0x101230 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l101233, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 75), (7, 65), (8, 8), (9, 9), (11, 69), (12, 71), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l10120f : List UInt8 :=
  [0x01, 0xF7, 0x41, 0x31, 0xFB, 0x41, 0xC1, 0xC3, 0x10, 0x45, 0x01, 0xDC, 0x44, 0x31, 0xE6, 0xC1,
    0xC6, 0x0C, 0x01, 0xF7, 0x41, 0x31, 0xFB, 0x41, 0xC1, 0xC3, 0x08, 0x45, 0x01, 0xDC, 0x44, 0x31,
    0xE6, 0xC1, 0xC6, 0x07]

theorem code_l10120f : ∀ x ∈ codeRange 0x10120f bytes_l10120f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x120f 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101233 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101233 (addR32R32Effect 0x101233 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[3, 5]
    (.letOp (n := 54) (.exec 0x101233 (fun s => s.RIP = 0x101233) (addR32R32Effect 0x101233 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 55) (.out 0x101235 (xorR32R32Effect 0x101235 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[11, 53]
    (.letOp (n := 56) (.exec 0x101235 (fun s => s.RIP = 0x101235) (xorR32R32Effect 0x101235 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[11, 53]
    (.letOp (n := 57) (.out 0x101238 (rolR32Effect 0x101238 4 11 16) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[55]
    (.letOp (n := 58) (.exec 0x101238 (fun s => s.RIP = 0x101238) (rolR32Effect 0x101238 4 11 16) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x10123c (addR32R32Effect 0x10123c 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[14, 57]
    (.letOp (n := 60) (.exec 0x10123c (fun s => s.RIP = 0x10123c) (addR32R32Effect 0x10123c 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[14, 57]
    (.letOp (n := 61) (.out 0x10123f (xorR32R32Effect 0x10123f 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[5, 59]
    (.letOp (n := 62) (.exec 0x10123f (fun s => s.RIP = 0x10123f) (xorR32R32Effect 0x10123f 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[5, 59]
    (.letOp (n := 63) (.out 0x101242 (rolR32Effect 0x101242 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.exec 0x101242 (fun s => s.RIP = 0x101242) (rolR32Effect 0x101242 3 5 12) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x101245 (addR32R32Effect 0x101245 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x101245 (fun s => s.RIP = 0x101245) (addR32R32Effect 0x101245 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[53, 63]
    (.letOp (n := 67) (.exec 0x101247 (StorePre 0x101247 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101247 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x101247 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x10124b (xorR32R32Effect 0x10124b 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[57, 65]
    (.letOp (n := 69) (.exec 0x10124b (fun s => s.RIP = 0x10124b) (xorR32R32Effect 0x10124b 3 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[57, 65]
    (.letOp (n := 70) (.out 0x10124e (rolR32Effect 0x10124e 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[68]
    (.letOp (n := 71) (.exec 0x10124e (fun s => s.RIP = 0x10124e) (rolR32Effect 0x10124e 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x101252 (addR32R32Effect 0x101252 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[59, 70]
    (.letOp (n := 73) (.exec 0x101252 (fun s => s.RIP = 0x101252) (addR32R32Effect 0x101252 3 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[59, 70]
    (.letOp (n := 74) (.out 0x101255 (xorR32R32Effect 0x101255 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[63, 72]
    (.letOp (n := 75) (.exec 0x101255 (fun s => s.RIP = 0x101255) (xorR32R32Effect 0x101255 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[63, 72]
    (.letOp (n := 76) (.out 0x101258 (rolR32Effect 0x101258 3 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[74]
    (.letOp (n := 77) (.exec 0x101258 (fun s => s.RIP = 0x101258) (rolR32Effect 0x101258 3 5 7) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.terminate (.br ⟨.l10125b, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 65), (4, 4), (5, 76), (6, 6), (7, 7), (8, 8), (9, 9), (11, 70), (12, 12), (13, 13), (14, 72), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l101233 : List UInt8 :=
  [0x01, 0xEB, 0x41, 0x31, 0xDB, 0x41, 0xC1, 0xC3, 0x10, 0x45, 0x01, 0xDE, 0x44, 0x31, 0xF5, 0xC1,
    0xC5, 0x0C, 0x01, 0xEB, 0x89, 0x5C, 0x24, 0x08, 0x41, 0x31, 0xDB, 0x41, 0xC1, 0xC3, 0x08, 0x45,
    0x01, 0xDE, 0x44, 0x31, 0xF5, 0xC1, 0xC5, 0x07]

theorem code_l101233 : ∀ x ∈ codeRange 0x101233 bytes_l101233, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1233 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10125b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10125b (addR32R32Effect 0x10125b 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[13, 15]
    (.letOp (n := 54) (.exec 0x10125b (fun s => s.RIP = 0x10125b) (addR32R32Effect 0x10125b 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 15]
    (.letOp (n := 55) (.out 0x10125e (xorR32R32Effect 0x10125e 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[1, 53]
    (.letOp (n := 56) (.exec 0x10125e (fun s => s.RIP = 0x10125e) (xorR32R32Effect 0x10125e 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[1, 53]
    (.letOp (n := 57) (.out 0x101261 (rolR32Effect 0x101261 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x101261 (fun s => s.RIP = 0x101261) (rolR32Effect 0x101261 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x101264 (addR32R32Effect 0x101264 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[12, 57]
    (.letOp (n := 60) (.exec 0x101264 (fun s => s.RIP = 0x101264) (addR32R32Effect 0x101264 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[12, 57]
    (.letOp (n := 61) (.out 0x101267 (xorR32R32Effect 0x101267 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[15, 59]
    (.letOp (n := 62) (.exec 0x101267 (fun s => s.RIP = 0x101267) (xorR32R32Effect 0x101267 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[15, 59]
    (.letOp (n := 63) (.out 0x10126a (rolR32Effect 0x10126a 4 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[61]
    (.letOp (n := 64) (.exec 0x10126a (fun s => s.RIP = 0x10126a) (rolR32Effect 0x10126a 4 15 12) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x10126e (addR32R32Effect 0x10126e 3 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x10126e (fun s => s.RIP = 0x10126e) (addR32R32Effect 0x10126e 3 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x101271 (xorR32R32Effect 0x101271 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x101271 (fun s => s.RIP = 0x101271) (xorR32R32Effect 0x101271 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x101274 (rolR32Effect 0x101274 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x101274 (fun s => s.RIP = 0x101274) (rolR32Effect 0x101274 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x101277 (addR32R32Effect 0x101277 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x101277 (fun s => s.RIP = 0x101277) (addR32R32Effect 0x101277 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x10127a (xorR32R32Effect 0x10127a 3 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x10127a (fun s => s.RIP = 0x10127a) (xorR32R32Effect 0x10127a 3 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x10127d (rolR32Effect 0x10127d 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[73]
    (.letOp (n := 76) (.exec 0x10127d (fun s => s.RIP = 0x10127d) (rolR32Effect 0x10127d 4 15 7) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l101281, RegMap.args [(0, 0), (1, 69), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 71), (13, 65), (14, 14), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l10125b : List UInt8 :=
  [0x45, 0x01, 0xFD, 0x44, 0x31, 0xE9, 0xC1, 0xC1, 0x10, 0x41, 0x01, 0xCC, 0x45, 0x31, 0xE7, 0x41,
    0xC1, 0xC7, 0x0C, 0x45, 0x01, 0xFD, 0x44, 0x31, 0xE9, 0xC1, 0xC1, 0x08, 0x41, 0x01, 0xCC, 0x45,
    0x31, 0xE7, 0x41, 0xC1, 0xC7, 0x07]

theorem code_l10125b : ∀ x ∈ codeRange 0x10125b bytes_l10125b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x125b 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101281 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101281 (addR32R32Effect 0x101281 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[0, 6]
    (.letOp (n := 54) (.exec 0x101281 (fun s => s.RIP = 0x101281) (addR32R32Effect 0x101281 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[0, 6]
    (.letOp (n := 55) (.out 0x101283 (xorR32R32Effect 0x101283 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[2, 53]
    (.letOp (n := 56) (.exec 0x101283 (fun s => s.RIP = 0x101283) (xorR32R32Effect 0x101283 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[2, 53]
    (.letOp (n := 57) (.out 0x101285 (rolR32Effect 0x101285 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.exec 0x101285 (fun s => s.RIP = 0x101285) (rolR32Effect 0x101285 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x101288 (movR32M32Effect 0x101288 10 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 60) (.exec 0x101288 (LoadPre 0x101288 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101288 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101288 10 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10128d (addR32R32Effect 0x10128d 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x10128d (fun s => s.RIP = 0x10128d) (addR32R32Effect 0x10128d 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x101290 (xorR32R32Effect 0x101290 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[6, 61]
    (.letOp (n := 64) (.exec 0x101290 (fun s => s.RIP = 0x101290) (xorR32R32Effect 0x101290 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[6, 61]
    (.letOp (n := 65) (.out 0x101293 (rolR32Effect 0x101293 3 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 66) (.exec 0x101293 (fun s => s.RIP = 0x101293) (rolR32Effect 0x101293 3 6 12) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x101296 (addR32R32Effect 0x101296 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[53, 65]
    (.letOp (n := 68) (.exec 0x101296 (fun s => s.RIP = 0x101296) (addR32R32Effect 0x101296 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[53, 65]
    (.letOp (n := 69) (.out 0x101298 (xorR32R32Effect 0x101298 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[57, 67]
    (.letOp (n := 70) (.exec 0x101298 (fun s => s.RIP = 0x101298) (xorR32R32Effect 0x101298 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[57, 67]
    (.letOp (n := 71) (.out 0x10129a (rolR32Effect 0x10129a 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x10129a (fun s => s.RIP = 0x10129a) (rolR32Effect 0x10129a 3 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x10129d (addR32R32Effect 0x10129d 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[61, 71]
    (.letOp (n := 74) (.exec 0x10129d (fun s => s.RIP = 0x10129d) (addR32R32Effect 0x10129d 3 10 2) (Reg.operands [.gpr 10, .gpr 2] [])) #v[61, 71]
    (.letOp (n := 75) (.exec 0x1012a0 (StorePre 0x1012a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1012a0 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1012a0 10 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x1012a5 (xorR32R32Effect 0x1012a5 3 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[65, 73]
    (.letOp (n := 77) (.exec 0x1012a5 (fun s => s.RIP = 0x1012a5) (xorR32R32Effect 0x1012a5 3 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[65, 73]
    (.letOp (n := 78) (.out 0x1012a8 (movR32M32Effect 0x1012a8 10 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 79) (.exec 0x1012a8 (LoadPre 0x1012a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1012a8 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x1012a8 10 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x1012ad (rolR32Effect 0x1012ad 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[76]
    (.letOp (n := 81) (.exec 0x1012ad (fun s => s.RIP = 0x1012ad) (rolR32Effect 0x1012ad 3 6 7) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l1012b0, RegMap.args [(0, 67), (1, 1), (2, 71), (4, 4), (5, 5), (6, 80), (7, 7), (8, 8), (9, 9), (10, 78), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l101281 : List UInt8 :=
  [0x01, 0xF0, 0x31, 0xC2, 0xC1, 0xC2, 0x10, 0x44, 0x8B, 0x54, 0x24, 0x04, 0x41, 0x01, 0xD2, 0x44,
    0x31, 0xD6, 0xC1, 0xC6, 0x0C, 0x01, 0xF0, 0x31, 0xC2, 0xC1, 0xC2, 0x08, 0x41, 0x01, 0xD2, 0x44,
    0x89, 0x54, 0x24, 0x04, 0x44, 0x31, 0xD6, 0x44, 0x8B, 0x54, 0x24, 0x14, 0xC1, 0xC6, 0x07]

theorem code_l101281 : ∀ x ∈ codeRange 0x101281 bytes_l101281, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1281 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012b0 (addR32R32Effect 0x1012b0 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[7, 9]
    (.letOp (n := 54) (.exec 0x1012b0 (fun s => s.RIP = 0x1012b0) (addR32R32Effect 0x1012b0 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[7, 9]
    (.letOp (n := 55) (.out 0x1012b3 (xorR32R32Effect 0x1012b3 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[8, 53]
    (.letOp (n := 56) (.exec 0x1012b3 (fun s => s.RIP = 0x1012b3) (xorR32R32Effect 0x1012b3 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 53]
    (.letOp (n := 57) (.out 0x1012b6 (rolR32Effect 0x1012b6 4 8 16) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 58) (.exec 0x1012b6 (fun s => s.RIP = 0x1012b6) (rolR32Effect 0x1012b6 4 8 16) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x1012ba (addR32R32Effect 0x1012ba 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[10, 57]
    (.letOp (n := 60) (.exec 0x1012ba (fun s => s.RIP = 0x1012ba) (addR32R32Effect 0x1012ba 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[10, 57]
    (.letOp (n := 61) (.out 0x1012bd (xorR32R32Effect 0x1012bd 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[9, 59]
    (.letOp (n := 62) (.exec 0x1012bd (fun s => s.RIP = 0x1012bd) (xorR32R32Effect 0x1012bd 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 59]
    (.letOp (n := 63) (.out 0x1012c0 (rolR32Effect 0x1012c0 4 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 64) (.exec 0x1012c0 (fun s => s.RIP = 0x1012c0) (rolR32Effect 0x1012c0 4 9 12) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x1012c4 (addR32R32Effect 0x1012c4 3 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x1012c4 (fun s => s.RIP = 0x1012c4) (addR32R32Effect 0x1012c4 3 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x1012c7 (xorR32R32Effect 0x1012c7 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x1012c7 (fun s => s.RIP = 0x1012c7) (xorR32R32Effect 0x1012c7 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x1012ca (rolR32Effect 0x1012ca 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[67]
    (.letOp (n := 70) (.exec 0x1012ca (fun s => s.RIP = 0x1012ca) (rolR32Effect 0x1012ca 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1012ce (addR32R32Effect 0x1012ce 3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x1012ce (fun s => s.RIP = 0x1012ce) (addR32R32Effect 0x1012ce 3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x1012d1 (xorR32R32Effect 0x1012d1 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x1012d1 (fun s => s.RIP = 0x1012d1) (xorR32R32Effect 0x1012d1 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x1012d4 (rolR32Effect 0x1012d4 4 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[73]
    (.letOp (n := 76) (.exec 0x1012d4 (fun s => s.RIP = 0x1012d4) (rolR32Effect 0x1012d4 4 9 7) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l1012d8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 65), (8, 69), (9, 75), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l1012b0 : List UInt8 :=
  [0x44, 0x01, 0xCF, 0x41, 0x31, 0xF8, 0x41, 0xC1, 0xC0, 0x10, 0x45, 0x01, 0xC2, 0x45, 0x31, 0xD1,
    0x41, 0xC1, 0xC1, 0x0C, 0x44, 0x01, 0xCF, 0x41, 0x31, 0xF8, 0x41, 0xC1, 0xC0, 0x08, 0x45, 0x01,
    0xC2, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xC1, 0x07]

theorem code_l1012b0 : ∀ x ∈ codeRange 0x1012b0 bytes_l1012b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12b0 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012d8 (decMEffect 0x1012d8 5 64 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1012d8 (StorePre 0x1012d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1012d8 + BitVec.ofNat 64 5)) 8) (decMEffect 0x1012d8 5 64 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101180, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1012e3, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1012d8 : List UInt8 :=
  [0x48, 0xFF, 0x4C, 0x24, 0x58, 0x0F, 0x85, 0x9D, 0xFE, 0xFF, 0xFF]

theorem code_l1012d8 : ∀ x ∈ codeRange 0x1012d8 bytes_l1012d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d8 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1012e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1012e3 (movR32M32LowEffect 0x1012e3 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1012e3 (LoadPre 0x1012e3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012e3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1012e3 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1012e7 (addR32M32Effect 0x1012e7 4 3 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[53, 4]
    (.letOp (n := 56) (.exec 0x1012e7 (LoadPre 0x1012e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1012e7 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012e7 4 3 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 57) (.exec 0x1012eb (StorePre 0x1012eb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012eb + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1012eb 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1012ef (addR32M32Effect 0x1012ef 5 13 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[13, 4]
    (.letOp (n := 59) (.exec 0x1012ef (LoadPre 0x1012ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1012ef + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x1012ef 5 13 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 60) (.exec 0x1012f4 (StorePre 0x1012f4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1012f4 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1012f4 13 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x1012f9 (addR32M32Effect 0x1012f9 4 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[0, 4]
    (.letOp (n := 62) (.exec 0x1012f9 (LoadPre 0x1012f9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1012f9 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012f9 4 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 63) (.out 0x1012fd (addR32M32Effect 0x1012fd 4 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[7, 4]
    (.letOp (n := 64) (.exec 0x1012fd (LoadPre 0x1012fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1012fd + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x1012fd 4 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 65) (.out 0x101301 (addR32M32Effect 0x101301 5 9 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[9, 4]
    (.letOp (n := 66) (.exec 0x101301 (LoadPre 0x101301 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101301 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101301 5 9 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 67) (.out 0x101306 (addR32M32Effect 0x101306 4 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[5, 4]
    (.letOp (n := 68) (.exec 0x101306 (LoadPre 0x101306 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101306 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101306 4 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 69) (.out 0x10130a (addR32M32Effect 0x10130a 5 15 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[15, 4]
    (.letOp (n := 70) (.exec 0x10130a (LoadPre 0x10130a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10130a + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x10130a 5 15 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 71) (.out 0x10130f (addR32M32Effect 0x10130f 4 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[6, 4]
    (.letOp (n := 72) (.exec 0x10130f (LoadPre 0x10130f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10130f + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x10130f 4 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 73) (.out 0x101313 (movR32M32LowEffect 0x101313 3 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 74) (.exec 0x101313 (LoadPre 0x101313 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101313 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101313 3 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x101317 (addR32M32Effect 0x101317 4 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[73, 4]
    (.letOp (n := 76) (.exec 0x101317 (LoadPre 0x101317 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101317 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x101317 4 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 77) (.exec 0x10131b (StorePre 0x10131b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10131b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10131b 3 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x10131f (addR32M32Effect 0x10131f 5 10 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[10, 4]
    (.letOp (n := 79) (.exec 0x10131f (LoadPre 0x10131f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10131f + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x10131f 5 10 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 80) (.out 0x101324 (addR32M32Effect 0x101324 5 14 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[14, 4]
    (.letOp (n := 81) (.exec 0x101324 (LoadPre 0x101324 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101324 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101324 5 14 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 82) (.out 0x101329 (addR32M32Effect 0x101329 5 12 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[12, 4]
    (.letOp (n := 83) (.exec 0x101329 (LoadPre 0x101329 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x101329 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101329 5 12 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 84) (.out 0x10132e (addR32M32Effect 0x10132e 4 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[2, 4]
    (.letOp (n := 85) (.exec 0x10132e (LoadPre 0x10132e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10132e + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x10132e 4 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 86) (.out 0x101332 (addR32M32Effect 0x101332 5 8 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[8, 4]
    (.letOp (n := 87) (.exec 0x101332 (LoadPre 0x101332 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x101332 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101332 5 8 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 88) (.out 0x101337 (addR32M32Effect 0x101337 5 11 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[11, 4]
    (.letOp (n := 89) (.exec 0x101337 (LoadPre 0x101337 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x101337 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x101337 5 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.terminate (.br ⟨.l10133c, RegMap.args [(0, 61), (1, 1), (2, 84), (3, 75), (4, 4), (5, 67), (6, 71), (7, 63), (8, 86), (9, 65), (10, 78), (11, 88), (12, 82), (13, 58), (14, 80), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))))))))))))))))))))))))))))))))))))))

def bytes_l1012e3 : List UInt8 :=
  [0x8B, 0x5C, 0x24, 0x08, 0x03, 0x5C, 0x24, 0x38, 0x89, 0x5C, 0x24, 0x08, 0x44, 0x03, 0x6C, 0x24,
    0x60, 0x44, 0x89, 0x6C, 0x24, 0x14, 0x03, 0x44, 0x24, 0x68, 0x03, 0x7C, 0x24, 0x0C, 0x44, 0x03,
    0x4C, 0x24, 0x50, 0x03, 0x6C, 0x24, 0x70, 0x44, 0x03, 0x7C, 0x24, 0x3C, 0x03, 0x74, 0x24, 0x10,
    0x8B, 0x5C, 0x24, 0x04, 0x03, 0x5C, 0x24, 0x18, 0x89, 0x5C, 0x24, 0x04, 0x44, 0x03, 0x54, 0x24,
    0x1C, 0x44, 0x03, 0x74, 0x24, 0x20, 0x44, 0x03, 0x64, 0x24, 0x24, 0x03, 0x54, 0x24, 0x28, 0x44,
    0x03, 0x44, 0x24, 0x2C, 0x44, 0x03, 0x5C, 0x24, 0x30]

theorem code_l1012e3 : ∀ x ∈ codeRange 0x1012e3 bytes_l1012e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12e3 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10133c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10133c (movR32M32LowEffect 0x10133c 3 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10133c (LoadPre 0x10133c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x10133c + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10133c 3 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101340 (addR32R32Effect 0x101340 2 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[1, 53]
    (.letOp (n := 56) (.exec 0x101340 (fun s => s.RIP = 0x101340) (addR32R32Effect 0x101340 2 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 53]
    (.letOp (n := 57) (.out 0x101342 (incR32Effect 0x101342 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 58) (.exec 0x101342 (fun s => s.RIP = 0x101342) (incR32Effect 0x101342 2 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 59) (.out 0x101344 (movR32R32Effect 0x101344 3 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 60) (.exec 0x101344 (fun s => s.RIP = 0x101344) (movR32R32Effect 0x101344 3 13 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 61) (.out 0x101347 (movR64M64Effect 0x101347 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 62) (.exec 0x101347 (LoadPre 0x101347 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101347 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101347 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10134c (StorePre 0x10134c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x10134c + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10134c 13 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[59, 61]
    (.letOp (n := 64) (.out 0x101350 (movR32M32LowEffect 0x101350 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 65) (.exec 0x101350 (LoadPre 0x101350 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101350 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101350 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x101354 (movR64M64Effect 0x101354 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 67) (.exec 0x101354 (LoadPre 0x101354 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101354 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101354 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x101359 (StorePre 0x101359 4 (fun s => AddrMode.addr (.base 13 (.d8 0x40)) s (0x101359 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101359 3 (.base 13 (.d8 0x40))) (Reg.operands [.gpr 3, .gpr 13] [])) #v[64, 66]
    (.letOp (n := 69) (.out 0x10135d (movR64M64Effect 0x10135d 3 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 70) (.exec 0x10135d (LoadPre 0x10135d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10135d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10135d 3 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x101362 (movR32M32Effect 0x101362 13 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 72) (.exec 0x101362 (LoadPre 0x101362 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101362 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x101362 13 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x101367 (StorePre 0x101367 4 (fun s => AddrMode.addr (.base 3 (.d8 0x44)) s (0x101367 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101367 13 (.base 3 (.d8 0x44))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[71, 69]
    (.letOp (n := 74) (.exec 0x10136b (StorePre 0x10136b 3 (fun s => AddrMode.addr (.base 3 (.d8 0x48)) s (0x10136b + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10136b 0 (.base 3 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 69]
    (.letOp (n := 75) (.exec 0x10136e (StorePre 0x10136e 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4c)) s (0x10136e + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10136e 7 (.base 3 (.d8 0x4c))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[7, 69]
    (.letOp (n := 76) (.exec 0x101371 (StorePre 0x101371 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x101371 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101371 9 (.base 3 (.d8 0x50))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 69]
    (.letOp (n := 77) (.out 0x101375 (movR64R64Effect 0x101375 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 78) (.exec 0x101375 (fun s => s.RIP = 0x101375) (movR64R64Effect 0x101375 9 3) (Reg.operands [.gpr 3] [])) #v[69]
    (.letOp (n := 79) (.exec 0x101378 (StorePre 0x101378 3 (fun s => AddrMode.addr (.base 3 (.d8 0x54)) s (0x101378 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101378 5 (.base 3 (.d8 0x54))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 69]
    (.letOp (n := 80) (.exec 0x10137b (StorePre 0x10137b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x58)) s (0x10137b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10137b 15 (.base 3 (.d8 0x58))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 69]
    (.letOp (n := 81) (.exec 0x10137f (StorePre 0x10137f 3 (fun s => AddrMode.addr (.base 3 (.d8 0x5c)) s (0x10137f + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10137f 6 (.base 3 (.d8 0x5c))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[6, 69]
    (.letOp (n := 82) (.out 0x101382 (movR32M32LowEffect 0x101382 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 83) (.exec 0x101382 (LoadPre 0x101382 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x101382 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x101382 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l101386, RegMap.args [(0, 82), (1, 55), (2, 2), (3, 69), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 77), (10, 10), (11, 11), (12, 12), (13, 71), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l10133c : List UInt8 :=
  [0x8B, 0x5C, 0x24, 0x34, 0x01, 0xD9, 0xFF, 0xC3, 0x41, 0x89, 0xDD, 0x48, 0x8B, 0x5C, 0x24, 0x48,
    0x44, 0x89, 0x6B, 0x30, 0x8B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x6C, 0x24, 0x48, 0x41, 0x89, 0x5D,
    0x40, 0x48, 0x8B, 0x5C, 0x24, 0x48, 0x44, 0x8B, 0x6C, 0x24, 0x14, 0x44, 0x89, 0x6B, 0x44, 0x89,
    0x43, 0x48, 0x89, 0x7B, 0x4C, 0x44, 0x89, 0x4B, 0x50, 0x49, 0x89, 0xD9, 0x89, 0x6B, 0x54, 0x44,
    0x89, 0x7B, 0x58, 0x89, 0x73, 0x5C, 0x8B, 0x44, 0x24, 0x04]

theorem code_l10133c : ∀ x ∈ codeRange 0x10133c bytes_l10133c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x133c 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101386 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101386 (StorePre 0x101386 3 (fun s => AddrMode.addr (.base 3 (.d8 0x60)) s (0x101386 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101386 0 (.base 3 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.exec 0x101389 (StorePre 0x101389 4 (fun s => AddrMode.addr (.base 3 (.d8 0x64)) s (0x101389 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101389 10 (.base 3 (.d8 0x64))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[10, 3]
    (.letOp (n := 55) (.exec 0x10138d (StorePre 0x10138d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x68)) s (0x10138d + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10138d 14 (.base 3 (.d8 0x68))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 56) (.exec 0x101391 (StorePre 0x101391 4 (fun s => AddrMode.addr (.base 3 (.d8 0x6c)) s (0x101391 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x101391 12 (.base 3 (.d8 0x6c))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 57) (.exec 0x101395 (StorePre 0x101395 3 (fun s => AddrMode.addr (.base 3 (.d8 0x70)) s (0x101395 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101395 1 (.base 3 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 58) (.exec 0x101398 (StorePre 0x101398 3 (fun s => AddrMode.addr (.base 3 (.d8 0x74)) s (0x101398 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x101398 2 (.base 3 (.d8 0x74))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 59) (.exec 0x10139b (StorePre 0x10139b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x78)) s (0x10139b + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10139b 8 (.base 3 (.d8 0x78))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[8, 3]
    (.letOp (n := 60) (.exec 0x10139f (StorePre 0x10139f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x7c)) s (0x10139f + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x10139f 11 (.base 3 (.d8 0x7c))) (Reg.operands [.gpr 11, .gpr 3] [])) #v[11, 3]
    (.letOp (n := 61) (.out 0x1013a3 (movR64M64Effect 0x1013a3 10 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x1013a3 (LoadPre 0x1013a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1013a3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013a3 10 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1013ab (movR32R32Effect 0x1013ab 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x1013ab (fun s => s.RIP = 0x1013ab) (movR32R32Effect 0x1013ab 3 0 10) (Reg.operands [.gpr 10] [])) #v[61]
    (.letOp (n := 65) (.out 0x1013ae (andR32Imm8Effect 0x1013ae 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x1013ae (fun s => s.RIP = 0x1013ae) (andR32Imm8Effect 0x1013ae 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[63]
    (.letOp (n := 67) (.out 0x1013b1 (movR64M64Effect 0x1013b1 14 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 68) (.exec 0x1013b1 (LoadPre 0x1013b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1013b1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013b1 14 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1013b9 (cmpR32Imm8Effect 0x1013b9 4 14 0x4) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[67]
    (.letOp (n := 70) (.exec 0x1013b9 (fun s => s.RIP = 0x1013b9) (cmpR32Imm8Effect 0x1013b9 4 14 0x4) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 71) (.pure (condOp 3)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l1013e3, RegMap.args [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 67), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l1013bf, RegMap.args [(0, 65), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 61), (11, 11), (12, 12), (14, 67), (16, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l101386 : List UInt8 :=
  [0x89, 0x43, 0x60, 0x44, 0x89, 0x53, 0x64, 0x44, 0x89, 0x73, 0x68, 0x44, 0x89, 0x63, 0x6C, 0x89,
    0x4B, 0x70, 0x89, 0x53, 0x74, 0x44, 0x89, 0x43, 0x78, 0x44, 0x89, 0x5B, 0x7C, 0x4C, 0x8B, 0x94,
    0x24, 0xA8, 0x00, 0x00, 0x00, 0x44, 0x89, 0xD0, 0x83, 0xE0, 0x03, 0x4C, 0x8B, 0xB4, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x41, 0x83, 0xFE, 0x04, 0x73, 0x24]

theorem code_l101386 : ∀ x ∈ codeRange 0x101386 bytes_l101386, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1386 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013bf (xorR32R32Effect 0x1013bf 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 54) (.exec 0x1013bf (fun s => s.RIP = 0x1013bf) (xorR32R32Effect 0x1013bf 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.out 0x1013c1 (movR64M64Effect 0x1013c1 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x1013c1 (LoadPre 0x1013c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1013c1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013c1 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1013c9 (movR64M64Effect 0x1013c9 11 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 58) (.exec 0x1013c9 (LoadPre 0x1013c9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1013c9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013c9 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1013d1 (movR64M64Effect 0x1013d1 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 60) (.exec 0x1013d1 (LoadPre 0x1013d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1013d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013d1 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1013d9 (movR64M64Effect 0x1013d9 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 62) (.exec 0x1013d9 (LoadPre 0x1013d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1013d9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1013d9 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l10146c, RegMap.args [(0, 0), (2, 2), (3, 59), (4, 4), (6, 53), (7, 7), (8, 55), (9, 9), (11, 57), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l1013bf : List UInt8 :=
  [0x31, 0xF6, 0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24, 0x40, 0xE9,
    0x89, 0x00, 0x00, 0x00]

theorem code_l1013bf : ∀ x ∈ codeRange 0x1013bf bytes_l1013bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13bf 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013e3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013e3 (andR32Imm8Effect 0x1013e3 4 10 0x3c) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 54) (.exec 0x1013e3 (fun s => s.RIP = 0x1013e3) (andR32Imm8Effect 0x1013e3 4 10 0x3c) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x1013e7 (movR64M64Effect 0x1013e7 8 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x1013e7 (LoadPre 0x1013e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1013e7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013e7 8 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1013ef (movR64M64Effect 0x1013ef 15 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x1013ef (LoadPre 0x1013ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1013ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1013ef 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1013f4 (leaR64Effect 0x1013f4 2 (.sib 8 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 15] []) (.reg (.gpr 2))) #v[55, 57]
    (.letOp (n := 60) (.exec 0x1013f4 (fun s => s.RIP = 0x1013f4) (leaR64Effect 0x1013f4 2 (.sib 8 (some 15) 0 .none)) (Reg.operands [.gpr 8, .gpr 15] [])) #v[55, 57]
    (.letOp (n := 61) (.out 0x1013f8 (movR64M64Effect 0x1013f8 11 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 62) (.exec 0x1013f8 (LoadPre 0x1013f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1013f8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1013f8 11 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x101400 (leaR64Effect 0x101400 1 (.sib 11 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 11, .gpr 2] []) (.reg (.gpr 1))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x101400 (fun s => s.RIP = 0x101400) (leaR64Effect 0x101400 1 (.sib 11 (some 2) 0 .none)) (Reg.operands [.gpr 11, .gpr 2] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x101404 (addR64Imm8Effect 0x101404 1 0x3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x101404 (fun s => s.RIP = 0x101404) (addR64Imm8Effect 0x101404 1 0x3) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x101408 (movR64M64Effect 0x101408 3 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 68) (.exec 0x101408 (LoadPre 0x101408 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101408 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101408 3 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101410 (addR64R64Effect 0x101410 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[59, 67]
    (.letOp (n := 70) (.exec 0x101410 (fun s => s.RIP = 0x101410) (addR64R64Effect 0x101410 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 67]
    (.letOp (n := 71) (.out 0x101413 (addR64Imm8Effect 0x101413 2 0x3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x101413 (fun s => s.RIP = 0x101413) (addR64Imm8Effect 0x101413 2 0x3) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x101417 (xorR32R32Effect 0x101417 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 74) (.exec 0x101417 (fun s => s.RIP = 0x101417) (xorR32R32Effect 0x101417 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 75) (.exec 0x101419 (fun s => s.RIP = 0x101419) (fun _ => nopEffect 0x101419 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101420, RegMap.args [(0, 0), (1, 65), (2, 71), (3, 67), (4, 4), (6, 73), (8, 55), (9, 9), (10, 53), (11, 61), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l1013e3 : List UInt8 :=
  [0x41, 0x83, 0xE2, 0x3C, 0x4C, 0x8B, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x7C, 0x24,
    0x40, 0x4B, 0x8D, 0x14, 0x38, 0x4C, 0x8B, 0x9C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x8D, 0x0C,
    0x13, 0x48, 0x83, 0xC1, 0x03, 0x48, 0x8B, 0x9C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x01, 0xDA,
    0x48, 0x83, 0xC2, 0x03, 0x31, 0xF6, 0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l1013e3 : ∀ x ∈ codeRange 0x1013e3 bytes_l1013e3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13e3 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101420 (movzxR32M8Effect 0x101420 6 7 (.sib 9 (some 6) 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 6] []) (.reg (.gpr 7))) #v[9, 6]
    (.letOp (n := 54) (.exec 0x101420 (LoadPre 0x101420 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x40)) s (0x101420 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101420 6 7 (.sib 9 (some 6) 0 (.d8 0x40))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[9, 6]
    (.letOp (n := 55) (.out 0x101426 (xorR8M8Effect 0x101426 5 7 (.sib 1 (some 6) 0 (.d8 0xfd))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .gpr 6] []) (.reg (.gpr 7))) #v[53, 1, 6]
    (.letOp (n := 56) (.exec 0x101426 (LoadPre 0x101426 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfd)) s (0x101426 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101426 5 7 (.sib 1 (some 6) 0 (.d8 0xfd))) (Reg.operands [.gpr 7, .gpr 1, .gpr 6] [])) #v[53, 1, 6]
    (.letOp (n := 57) (.exec 0x10142b (StorePre 0x10142b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfd)) s (0x10142b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10142b 5 7 (.sib 2 (some 6) 0 (.d8 0xfd))) (Reg.operands [.gpr 7, .gpr 2, .gpr 6] [])) #v[55, 2, 6]
    (.letOp (n := 58) (.out 0x101430 (movzxR32M8Effect 0x101430 6 7 (.sib 9 (some 6) 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 6] []) (.reg (.gpr 7))) #v[9, 6]
    (.letOp (n := 59) (.exec 0x101430 (LoadPre 0x101430 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x41)) s (0x101430 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101430 6 7 (.sib 9 (some 6) 0 (.d8 0x41))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[9, 6]
    (.letOp (n := 60) (.out 0x101436 (xorR8M8Effect 0x101436 5 7 (.sib 1 (some 6) 0 (.d8 0xfe))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .gpr 6] []) (.reg (.gpr 7))) #v[58, 1, 6]
    (.letOp (n := 61) (.exec 0x101436 (LoadPre 0x101436 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xfe)) s (0x101436 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101436 5 7 (.sib 1 (some 6) 0 (.d8 0xfe))) (Reg.operands [.gpr 7, .gpr 1, .gpr 6] [])) #v[58, 1, 6]
    (.letOp (n := 62) (.exec 0x10143b (StorePre 0x10143b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xfe)) s (0x10143b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10143b 5 7 (.sib 2 (some 6) 0 (.d8 0xfe))) (Reg.operands [.gpr 7, .gpr 2, .gpr 6] [])) #v[60, 2, 6]
    (.letOp (n := 63) (.out 0x101440 (movzxR32M8Effect 0x101440 6 7 (.sib 9 (some 6) 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 6] []) (.reg (.gpr 7))) #v[9, 6]
    (.letOp (n := 64) (.exec 0x101440 (LoadPre 0x101440 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x42)) s (0x101440 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101440 6 7 (.sib 9 (some 6) 0 (.d8 0x42))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[9, 6]
    (.letOp (n := 65) (.out 0x101446 (xorR8M8Effect 0x101446 5 7 (.sib 1 (some 6) 0 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .gpr 6] []) (.reg (.gpr 7))) #v[63, 1, 6]
    (.letOp (n := 66) (.exec 0x101446 (LoadPre 0x101446 (fun s => AddrMode.addr (.sib 1 (some 6) 0 (.d8 0xff)) s (0x101446 + BitVec.ofNat 64 5)) 1) (xorR8M8Effect 0x101446 5 7 (.sib 1 (some 6) 0 (.d8 0xff))) (Reg.operands [.gpr 7, .gpr 1, .gpr 6] [])) #v[63, 1, 6]
    (.letOp (n := 67) (.exec 0x10144b (StorePre 0x10144b 5 (fun s => AddrMode.addr (.sib 2 (some 6) 0 (.d8 0xff)) s (0x10144b + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10144b 5 7 (.sib 2 (some 6) 0 (.d8 0xff))) (Reg.operands [.gpr 7, .gpr 2, .gpr 6] [])) #v[65, 2, 6]
    (.letOp (n := 68) (.out 0x101450 (movzxR32M8Effect 0x101450 6 7 (.sib 9 (some 6) 0 (.d8 0x43))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9, .gpr 6] []) (.reg (.gpr 7))) #v[9, 6]
    (.letOp (n := 69) (.exec 0x101450 (LoadPre 0x101450 (fun s => AddrMode.addr (.sib 9 (some 6) 0 (.d8 0x43)) s (0x101450 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101450 6 7 (.sib 9 (some 6) 0 (.d8 0x43))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[9, 6]
    (.letOp (n := 70) (.out 0x101456 (xorR8M8Effect 0x101456 4 7 (.sib 1 (some 6) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1, .gpr 6] []) (.reg (.gpr 7))) #v[68, 1, 6]
    (.letOp (n := 71) (.exec 0x101456 (LoadPre 0x101456 (fun s => AddrMode.addr (.sib 1 (some 6) 0 .none) s (0x101456 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101456 4 7 (.sib 1 (some 6) 0 .none)) (Reg.operands [.gpr 7, .gpr 1, .gpr 6] [])) #v[68, 1, 6]
    (.letOp (n := 72) (.exec 0x10145a (StorePre 0x10145a 4 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x10145a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10145a 4 7 (.sib 2 (some 6) 0 .none)) (Reg.operands [.gpr 7, .gpr 2, .gpr 6] [])) #v[70, 2, 6]
    (.letOp (n := 73) (.out 0x10145e (addR64Imm8Effect 0x10145e 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 74) (.exec 0x10145e (fun s => s.RIP = 0x10145e) (addR64Imm8Effect 0x10145e 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.out 0x101462 (cmpR64R64Effect 0x101462 10 6) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 6] []) (.flag .ZF)) #v[10, 73]
    (.letOp (n := 76) (.exec 0x101462 (fun s => s.RIP = 0x101462) (cmpR64R64Effect 0x101462 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[10, 73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l101420, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 73), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l101467, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 73), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l101420 : List UInt8 :=
  [0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x40, 0x40, 0x32, 0x7C, 0x31, 0xFD, 0x40, 0x88, 0x7C, 0x32, 0xFD,
    0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x41, 0x40, 0x32, 0x7C, 0x31, 0xFE, 0x40, 0x88, 0x7C, 0x32, 0xFE,
    0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x42, 0x40, 0x32, 0x7C, 0x31, 0xFF, 0x40, 0x88, 0x7C, 0x32, 0xFF,
    0x41, 0x0F, 0xB6, 0x7C, 0x31, 0x43, 0x40, 0x32, 0x3C, 0x31, 0x40, 0x88, 0x3C, 0x32, 0x48, 0x83,
    0xC6, 0x04, 0x49, 0x39, 0xF2, 0x75, 0xB9]

theorem code_l101420 : ∀ x ∈ codeRange 0x101420 bytes_l101420, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1420 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101467 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101467 (testR64R64Effect 0x101467 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x101467 (fun s => s.RIP = 0x101467) (testR64R64Effect 0x101467 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1014a4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10146c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101467 : List UInt8 :=
  [0x48, 0x85, 0xC0, 0x74, 0x38]

theorem code_l101467 : ∀ x ∈ codeRange 0x101467 bytes_l101467, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1467 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10146c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10146c (leaR64Effect 0x10146c 1 (.sib 6 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6, .gpr 9] []) (.reg (.gpr 1))) #v[6, 9]
    (.letOp (n := 54) (.exec 0x10146c (fun s => s.RIP = 0x10146c) (leaR64Effect 0x10146c 1 (.sib 6 (some 9) 0 .none)) (Reg.operands [.gpr 6, .gpr 9] [])) #v[6, 9]
    (.letOp (n := 55) (.out 0x101470 (addR64Imm8Effect 0x101470 1 0x40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x101470 (fun s => s.RIP = 0x101470) (addR64Imm8Effect 0x101470 1 0x40) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x101474 (addR64R64Effect 0x101474 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[8, 6]
    (.letOp (n := 58) (.exec 0x101474 (fun s => s.RIP = 0x101474) (addR64R64Effect 0x101474 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[8, 6]
    (.letOp (n := 59) (.out 0x101477 (addR64R64Effect 0x101477 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[57, 15]
    (.letOp (n := 60) (.exec 0x101477 (fun s => s.RIP = 0x101477) (addR64R64Effect 0x101477 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[57, 15]
    (.letOp (n := 61) (.out 0x10147a (addR64R64Effect 0x10147a 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[3, 59]
    (.letOp (n := 62) (.exec 0x10147a (fun s => s.RIP = 0x10147a) (addR64R64Effect 0x10147a 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[3, 59]
    (.letOp (n := 63) (.out 0x10147d (addR64R64Effect 0x10147d 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[11, 59]
    (.letOp (n := 64) (.exec 0x10147d (fun s => s.RIP = 0x10147d) (addR64R64Effect 0x10147d 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[11, 59]
    (.letOp (n := 65) (.out 0x101480 (xorR32R32Effect 0x101480 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 66) (.exec 0x101480 (fun s => s.RIP = 0x101480) (xorR32R32Effect 0x101480 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 67) (.exec 0x101482 (fun s => s.RIP = 0x101482) (fun _ => nopEffect 0x101482 14) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l101490, RegMap.args [(0, 0), (1, 55), (2, 65), (3, 61), (4, 4), (6, 6), (7, 7), (8, 59), (9, 9), (11, 63), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩))))))))))))))))

def bytes_l10146c : List UInt8 :=
  [0x4A, 0x8D, 0x0C, 0x0E, 0x48, 0x83, 0xC1, 0x40, 0x49, 0x01, 0xF0, 0x4D, 0x01, 0xF8, 0x4C, 0x01,
    0xC3, 0x4D, 0x01, 0xC3, 0x31, 0xD2, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00,
    0x00, 0x00, 0x00, 0x00]

theorem code_l10146c : ∀ x ∈ codeRange 0x10146c bytes_l10146c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x146c 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101490 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101490 (movzxR32M8Effect 0x101490 4 6 (.sib 1 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1, .gpr 2] []) (.reg (.gpr 6))) #v[1, 2]
    (.letOp (n := 54) (.exec 0x101490 (LoadPre 0x101490 (fun s => AddrMode.addr (.sib 1 (some 2) 0 .none) s (0x101490 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x101490 4 6 (.sib 1 (some 2) 0 .none)) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 2]
    (.letOp (n := 55) (.out 0x101494 (xorR8M8Effect 0x101494 4 6 (.sib 11 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11, .gpr 2] []) (.reg (.gpr 6))) #v[53, 11, 2]
    (.letOp (n := 56) (.exec 0x101494 (LoadPre 0x101494 (fun s => AddrMode.addr (.sib 11 (some 2) 0 .none) s (0x101494 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101494 4 6 (.sib 11 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 11, .gpr 2] [])) #v[53, 11, 2]
    (.letOp (n := 57) (.exec 0x101498 (StorePre 0x101498 4 (fun s => AddrMode.addr (.sib 3 (some 2) 0 .none) s (0x101498 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101498 4 6 (.sib 3 (some 2) 0 .none)) (Reg.operands [.gpr 6, .gpr 3, .gpr 2] [])) #v[55, 3, 2]
    (.letOp (n := 58) (.out 0x10149c (incR64Effect 0x10149c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 59) (.exec 0x10149c (fun s => s.RIP = 0x10149c) (incR64Effect 0x10149c 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2]
    (.letOp (n := 60) (.out 0x10149f (cmpR64R64Effect 0x10149f 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[0, 58]
    (.letOp (n := 61) (.exec 0x10149f (fun s => s.RIP = 0x10149f) (cmpR64R64Effect 0x10149f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[0, 58]
    (.letOp (n := 62) (.pure (condOp 5)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l101490, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l1014a4, RegMap.args [(0, 0), (1, 1), (2, 58), (3, 3), (4, 4), (6, 55), (7, 7), (9, 9), (11, 11), (14, 14), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l101490 : List UInt8 :=
  [0x0F, 0xB6, 0x34, 0x11, 0x41, 0x32, 0x34, 0x13, 0x40, 0x88, 0x34, 0x13, 0x48, 0xFF, 0xC2, 0x48,
    0x39, 0xD0, 0x75, 0xEC]

theorem code_l101490 : ∀ x ∈ codeRange 0x101490 bytes_l101490, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1490 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1014a4 (StorePre 0x1014a4 4 (fun s => AddrMode.addr (.base 9 (.d8 0x40)) s (0x1014a4 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1014a4 4 14 (.base 9 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 9] [])) #v[14, 9]
    (.terminate (.br ⟨.l1014a8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1014a4 : List UInt8 :=
  [0x45, 0x88, 0x71, 0x40]

theorem code_l1014a4 : ∀ x ∈ codeRange 0x1014a4 bytes_l1014a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14a4 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014a8 (xorR32R32Effect 0x1014a8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x1014a8 (fun s => s.RIP = 0x1014a8) (xorR32R32Effect 0x1014a8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l1014aa, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1014a8 : List UInt8 :=
  [0x31, 0xC0]

theorem code_l1014a8 : ∀ x ∈ codeRange 0x1014a8 bytes_l1014a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14a8 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014aa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014aa (addR64Imm32Effect 0x1014aa 4 0x170) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1014aa (fun s => s.RIP = 0x1014aa) (addR64Imm32Effect 0x1014aa 4 0x170) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1014b1 (popR64Effect 0x1014b1 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x1014b1 (popR64Effect 0x1014b1 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x1014b1 (PopPre 0x1014b1) (popR64Effect 0x1014b1 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x1014b2 (popR64Effect 0x1014b2 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x1014b2 (popR64Effect 0x1014b2 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x1014b2 (PopPre 0x1014b2) (popR64Effect 0x1014b2 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x1014b4 (popR64Effect 0x1014b4 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x1014b4 (popR64Effect 0x1014b4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x1014b4 (PopPre 0x1014b4) (popR64Effect 0x1014b4 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x1014b6 (popR64Effect 0x1014b6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x1014b6 (popR64Effect 0x1014b6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x1014b6 (PopPre 0x1014b6) (popR64Effect 0x1014b6 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x1014b8 (popR64Effect 0x1014b8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x1014b8 (popR64Effect 0x1014b8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x1014b8 (PopPre 0x1014b8) (popR64Effect 0x1014b8 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x1014ba (popR64Effect 0x1014ba 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x1014ba (popR64Effect 0x1014ba 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x1014ba (PopPre 0x1014ba) (popR64Effect 0x1014ba 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x1014bb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x1014bb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x1014bb (RetPre 0x1014bb) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (9, 9), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l1014aa : List UInt8 :=
  [0x48, 0x81, 0xC4, 0x70, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1014aa : ∀ x ∈ codeRange 0x1014aa bytes_l1014aa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14aa 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014c0_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x101513 (StorePre 0x101513 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101513 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101513 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[88, 65]
    (.letOp (n := 91) (.exec 0x101518 (StorePre 0x101518 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101518 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101518 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[86, 65]
    (.letOp (n := 92) (.out 0x10151d (testR64R64Effect 0x10151d 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[69, 69]
    (.letOp (n := 93) (.out 0x10151d (testR64R64Effect 0x10151d 14 14) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 14] []) (.flag .SF)) #v[69, 69]
    (.letOp (n := 94) (.exec 0x10151d (fun s => s.RIP = 0x10151d) (testR64R64Effect 0x10151d 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[69, 69]
    (.letOp (n := 95) (.pure (condOp 8)) #v[93]
    (.terminate (.condBr (Fin.last 95) ⟨.l101639, RegMap.args [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (19, 92), (20, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ ⟨.l101526, RegMap.args [(0, 86), (1, 88), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 72), (9, 9), (12, 12), (13, 67), (14, 69), (15, 15), (19, 92), (20, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩)))))))

def bytes_l1014c0_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x40, 0x48, 0x89, 0x44, 0x24, 0x38, 0x4D, 0x85, 0xF6, 0x0F, 0x88, 0x13,
    0x01, 0x00, 0x00]

theorem code_l1014c0_1 : ∀ x ∈ codeRange 0x101513 bytes_l1014c0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1513 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014c0 (pushR64Effect 0x1014c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1014c0 (PushPre 0x1014c0 1) (pushR64Effect 0x1014c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1014c1 (pushR64Effect 0x1014c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1014c1 (PushPre 0x1014c1 2) (pushR64Effect 0x1014c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1014c3 (pushR64Effect 0x1014c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1014c3 (PushPre 0x1014c3 2) (pushR64Effect 0x1014c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1014c5 (pushR64Effect 0x1014c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1014c5 (PushPre 0x1014c5 2) (pushR64Effect 0x1014c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1014c7 (pushR64Effect 0x1014c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1014c7 (PushPre 0x1014c7 2) (pushR64Effect 0x1014c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1014c9 (pushR64Effect 0x1014c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1014c9 (PushPre 0x1014c9 1) (pushR64Effect 0x1014c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1014ca (subR64Imm8Effect 0x1014ca 4 0x58) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1014ca (fun s => s.RIP = 0x1014ca) (subR64Imm8Effect 0x1014ca 4 0x58) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1014ce (movR64R64Effect 0x1014ce 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[1]
    (.letOp (n := 68) (.exec 0x1014ce (fun s => s.RIP = 0x1014ce) (movR64R64Effect 0x1014ce 13 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x1014d1 (movR64M64Effect 0x1014d1 14 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 70) (.exec 0x1014d1 (LoadPre 0x1014d1 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1014d1 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1014d1 14 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 71) (.exec 0x1014d9 (StorePre 0x1014d9 7 (fun s => AddrMode.addr (.rip 0x1feb20) s (0x1014d9 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x1014d9 8 (.rip 0x1feb20)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 72) (.out 0x1014e0 (addR64M64Effect 0x1014e0 8 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[8, 65]
    (.letOp (n := 73) (.out 0x1014e0 (addR64M64Effect 0x1014e0 8 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 4] []) (.flag .CF)) #v[8, 65]
    (.letOp (n := 74) (.exec 0x1014e0 (LoadPre 0x1014e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1014e0 + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x1014e0 8 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 65]
    (.letOp (n := 75) (.out 0x1014e8 (movR64Imm32Effect 0x1014e8 0 0xffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 76) (.exec 0x1014e8 (fun s => s.RIP = 0x1014e8) (movR64Imm32Effect 0x1014e8 0 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x1014ef (atFlags (condHolds 3) (cmovR64R64Effect 0x1014ef 4 0 8)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[75, 72, 73]
    (.letOp (n := 78) (.exec 0x1014ef (fun s => s.RIP = 0x1014ef) (atFlags (condHolds 3) (cmovR64R64Effect 0x1014ef 4 0 8)) (Reg.operands [.gpr 0, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[75, 72, 73]
    (.letOp (n := 79) (.exec 0x1014f3 (StorePre 0x1014f3 7 (fun s => AddrMode.addr (.rip 0x1feb0e) s (0x1014f3 + BitVec.ofNat 64 7)) 8) (movM64R64Effect 0x1014f3 0 (.rip 0x1feb0e)) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 80) (.out 0x1014fa (movR64M64Effect 0x1014fa 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 81) (.exec 0x1014fa (LoadPre 0x1014fa (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1014fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1014fa 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 82) (.exec 0x1014fe (StorePre 0x1014fe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1014fe + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014fe 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 83) (.out 0x101503 (movR64M64Effect 0x101503 0 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 84) (.exec 0x101503 (LoadPre 0x101503 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x101503 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101503 0 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 85) (.exec 0x101507 (StorePre 0x101507 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101507 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101507 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 65]
    (.letOp (n := 86) (.out 0x10150c (movR64M64Effect 0x10150c 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 87) (.exec 0x10150c (LoadPre 0x10150c (fun s => AddrMode.addr (.base 7 .none) s (0x10150c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10150c 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 88) (.out 0x10150f (movR64M64Effect 0x10150f 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 89) (.exec 0x10150f (LoadPre 0x10150f (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10150f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10150f 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (b_l1014c0_1)))))))))))))))))))))))))))))))))))))

def bytes_l1014c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x58, 0x49, 0x89,
    0xCD, 0x4C, 0x8B, 0xB4, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x05, 0x20, 0xEB, 0x1F, 0x00,
    0x4C, 0x03, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF, 0x49,
    0x0F, 0x43, 0xC0, 0x48, 0x89, 0x05, 0x0E, 0xEB, 0x1F, 0x00, 0x48, 0x8B, 0x47, 0x18, 0x48, 0x89,
    0x44, 0x24, 0x50, 0x48, 0x8B, 0x47, 0x10, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8B, 0x07, 0x48,
    0x8B, 0x4F, 0x08] ++ bytes_l1014c0_1

theorem code_l1014c0 : ∀ x ∈ codeRange 0x1014c0 bytes_l1014c0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14c0 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1014c0_1

@[cfg_block] def b_l101526 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.pure (condOp 4)) #v[19]
    (.terminate (.condBr (Fin.last 53) ⟨.l101611, RegMap.args (entryMap (live .l101526)) 54⟩ ⟨.l10152c, RegMap.args (entryMap (live .l101526)) 54⟩))

def bytes_l101526 : List UInt8 :=
  [0x0F, 0x84, 0xE5, 0x00, 0x00, 0x00]

theorem code_l101526 : ∀ x ∈ codeRange 0x101526 bytes_l101526, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1526 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10152c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10152c (movR64R64Effect 0x10152c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 54) (.exec 0x10152c (fun s => s.RIP = 0x10152c) (movR64R64Effect 0x10152c 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x10152f (movR64R64Effect 0x10152f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 56) (.exec 0x10152f (fun s => s.RIP = 0x10152f) (movR64R64Effect 0x10152f 15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x101532 (movR64R64Effect 0x101532 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 58) (.exec 0x101532 (fun s => s.RIP = 0x101532) (movR64R64Effect 0x101532 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x101535 (callEffect (fun _ => 0x101aa0) 0x10153a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101535 (PushPre 0x101535 5) (callEffect (fun _ => 0x101aa0) 0x10153a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10153a⟩) #v[]
    (.terminate (.call ⟨.l101aa0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 53), (4, 59), (5, 5), (6, 6), (7, 7), (9, 9), (12, 57), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10153a, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10152c : List UInt8 :=
  [0x4C, 0x89, 0xCB, 0x49, 0x89, 0xD7, 0x49, 0x89, 0xF4, 0xE8, 0x66, 0x05, 0x00, 0x00]

theorem code_l10152c : ∀ x ∈ codeRange 0x10152c bytes_l10152c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x152c 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
