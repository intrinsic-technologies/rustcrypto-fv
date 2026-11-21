import ChaCha20Poly1305.Proofs.Decrypt.Movsd
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Labels
import ChaCha20Poly1305.Proofs.Common.CFG.EvalAttr
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Footprints

namespace ChaCha20Poly1305.Proofs.Decrypt.Lifted

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift

@[cfg_block] def b_l100b7b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b7b (addR64R64Effect 0x100b7b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1, 2]
    (.letOp (n := 54) (.exec 0x100b7b (fun s => s.RIP = 0x100b7b) (addR64R64Effect 0x100b7b 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 2]
    (.letOp (n := 55) (.out 0x100b7e (addR64R64Effect 0x100b7e 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[53, 7]
    (.letOp (n := 56) (.exec 0x100b7e (fun s => s.RIP = 0x100b7e) (addR64R64Effect 0x100b7e 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[53, 7]
    (.letOp (n := 57) (.out 0x100b81 (addR64Imm8Effect 0x100b81 1 0x40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x100b81 (fun s => s.RIP = 0x100b81) (addR64Imm8Effect 0x100b81 1 0x40) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x100b85 (leaR64Effect 0x100b85 6 (.sib 14 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14, .gpr 2] []) (.reg (.gpr 6))) #v[14, 2]
    (.letOp (n := 60) (.exec 0x100b85 (fun s => s.RIP = 0x100b85) (leaR64Effect 0x100b85 6 (.sib 14 (some 2) 0 .none)) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 61) (.out 0x100b89 (addR64R64Effect 0x100b89 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[2, 3]
    (.letOp (n := 62) (.exec 0x100b89 (fun s => s.RIP = 0x100b89) (addR64R64Effect 0x100b89 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 63) (.out 0x100b8c (xorR32R32Effect 0x100b8c 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 64) (.exec 0x100b8c (fun s => s.RIP = 0x100b8c) (xorR32R32Effect 0x100b8c 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 65) (.exec 0x100b8f (fun s => s.RIP = 0x100b8f) (fun _ => nopEffect 0x100b8f 1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100b90, RegMap.args [(0, 0), (1, 57), (2, 61), (3, 3), (4, 4), (6, 59), (7, 7), (9, 63), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l100b7b : List UInt8 :=
  [0x48, 0x01, 0xD1, 0x48, 0x01, 0xF9, 0x48, 0x83, 0xC1, 0x40, 0x49, 0x8D, 0x34, 0x16, 0x48, 0x01,
    0xDA, 0x45, 0x31, 0xC9, 0x90]

theorem code_l100b7b : ∀ x ∈ codeRange 0x100b7b bytes_l100b7b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb7b 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100b90 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100b90 (movzxR32M8Effect 0x100b90 5 8 (.sib 1 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1, .gpr 9] []) (.reg (.gpr 8))) #v[1, 9]
    (.letOp (n := 54) (.exec 0x100b90 (LoadPre 0x100b90 (fun s => AddrMode.addr (.sib 1 (some 9) 0 .none) s (0x100b90 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b90 5 8 (.sib 1 (some 9) 0 .none)) (Reg.operands [.gpr 1, .gpr 9] [])) #v[1, 9]
    (.letOp (n := 55) (.out 0x100b95 (xorR8M8Effect 0x100b95 4 8 (.sib 2 (some 9) 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .gpr 9] []) (.reg (.gpr 8))) #v[53, 2, 9]
    (.letOp (n := 56) (.exec 0x100b95 (LoadPre 0x100b95 (fun s => AddrMode.addr (.sib 2 (some 9) 0 .none) s (0x100b95 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x100b95 4 8 (.sib 2 (some 9) 0 .none)) (Reg.operands [.gpr 8, .gpr 2, .gpr 9] [])) #v[53, 2, 9]
    (.letOp (n := 57) (.exec 0x100b99 (StorePre 0x100b99 4 (fun s => AddrMode.addr (.sib 6 (some 9) 0 .none) s (0x100b99 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b99 4 8 (.sib 6 (some 9) 0 .none)) (Reg.operands [.gpr 8, .gpr 6, .gpr 9] [])) #v[55, 6, 9]
    (.letOp (n := 58) (.out 0x100b9d (incR64Effect 0x100b9d 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 59) (.exec 0x100b9d (fun s => s.RIP = 0x100b9d) (incR64Effect 0x100b9d 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.letOp (n := 60) (.out 0x100ba0 (cmpR64R64Effect 0x100ba0 0 9) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 9] []) (.flag .ZF)) #v[0, 58]
    (.letOp (n := 61) (.exec 0x100ba0 (fun s => s.RIP = 0x100ba0) (cmpR64R64Effect 0x100ba0 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[0, 58]
    (.letOp (n := 62) (.pure (condOp 5)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l100b90, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 58), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l100ba5, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 55), (9, 58), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l100b90 : List UInt8 :=
  [0x46, 0x0F, 0xB6, 0x04, 0x09, 0x46, 0x32, 0x04, 0x0A, 0x46, 0x88, 0x04, 0x0E, 0x49, 0xFF, 0xC1,
    0x4C, 0x39, 0xC8, 0x75, 0xEB]

theorem code_l100b90 : ∀ x ∈ codeRange 0x100b90 bytes_l100b90, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb90 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ba5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ba5 (cmpMImm8Effect 0x100ba5 6 64 (.sib 4 none 0 (.d8 0x50)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x100ba5 (LoadPre 0x100ba5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100ba5 + BitVec.ofNat 64 6)) 8) (cmpMImm8Effect 0x100ba5 6 64 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100bab (StorePre 0x100bab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100bab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100bab 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 56) (.exec 0x100bb0 (StorePre 0x100bb0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100bb0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bb0 10 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 57) (.exec 0x100bb8 (StorePre 0x100bb8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100bb8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bb8 11 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 58) (.exec 0x100bc0 (StorePre 0x100bc0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100bc0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bc0 3 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 59) (.exec 0x100bc8 (StorePre 0x100bc8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100bc8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bc8 14 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 60) (.exec 0x100bd0 (StorePre 0x100bd0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100bd0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100bd0 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 61) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 61) ⟨.l1010cc, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l100bde, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l100ba5 : List UInt8 :=
  [0x48, 0x83, 0x7C, 0x24, 0x50, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x48, 0x4C, 0x89, 0x94, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x9C, 0x24, 0x90,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xBC, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x0F, 0x84, 0xEE, 0x04, 0x00, 0x00]

theorem code_l100ba5 : ∀ x ∈ codeRange 0x100ba5 bytes_l100ba5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xba5 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100bde_1 : Block Op Label signature Reg.count 84 :=
  .letOp (n := 84) (.out 0x100c28 (movR32M32LowEffect 0x100c28 0 (.base 7 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 85) (.exec 0x100c28 (LoadPre 0x100c28 (fun s => AddrMode.addr (.base 7 (.d8 0x24)) s (0x100c28 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c28 0 (.base 7 (.d8 0x24))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 86) (.exec 0x100c2b (StorePre 0x100c2b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c2b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c2b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x100c2f (movR32M32LowEffect 0x100c2f 0 (.base 7 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 88) (.exec 0x100c2f (LoadPre 0x100c2f (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x100c2f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c2f 0 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 89) (.exec 0x100c32 (StorePre 0x100c32 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100c32 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c32 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 90) (.out 0x100c36 (movR32M32LowEffect 0x100c36 0 (.base 7 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 91) (.exec 0x100c36 (LoadPre 0x100c36 (fun s => AddrMode.addr (.base 7 (.d8 0x2c)) s (0x100c36 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c36 0 (.base 7 (.d8 0x2c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 92) (.exec 0x100c39 (StorePre 0x100c39 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100c39 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c39 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x100c3d (movR32M32Effect 0x100c3d 8 (.base 7 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 94) (.exec 0x100c3d (LoadPre 0x100c3d (fun s => AddrMode.addr (.base 7 (.d8 0x34)) s (0x100c3d + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c3d 8 (.base 7 (.d8 0x34))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 95) (.out 0x100c41 (movR32M32LowEffect 0x100c41 0 (.base 7 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 96) (.exec 0x100c41 (LoadPre 0x100c41 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x100c41 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c41 0 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 97) (.exec 0x100c44 (StorePre 0x100c44 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100c44 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c44 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x100c48 (movR32M32LowEffect 0x100c48 0 (.base 7 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 99) (.exec 0x100c48 (LoadPre 0x100c48 (fun s => AddrMode.addr (.base 7 (.d8 0x3c)) s (0x100c48 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c48 0 (.base 7 (.d8 0x3c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 100) (.exec 0x100c4b (StorePre 0x100c4b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100c4b + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c4b 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[98, 4]
    (.letOp (n := 101) (.out 0x100c4f (xorR32R32Effect 0x100c4f 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 102) (.exec 0x100c4f (fun s => s.RIP = 0x100c4f) (xorR32R32Effect 0x100c4f 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 103) (.exec 0x100c51 (StorePre 0x100c51 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100c51 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c51 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 104) (.exec 0x100c56 (StorePre 0x100c56 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x100c56 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100c56 11 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 105) (.exec 0x100c5e (StorePre 0x100c5e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100c5e + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100c5e 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 106) (.exec 0x100c66 (fun s => s.RIP = 0x100c66) (fun _ => nopEffect 0x100c66 10) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100c70, RegMap.args [(0, 98), (3, 3), (4, 4), (7, 101), (8, 93), (10, 71), (11, 82), (12, 12), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 107⟩))))))))))))))))))))))))

def bytes_l100bde_1 : List UInt8 :=
  [0x8B, 0x47, 0x24, 0x89, 0x44, 0x24, 0x28, 0x8B, 0x47, 0x28, 0x89, 0x44, 0x24, 0x24, 0x8B, 0x47,
    0x2C, 0x89, 0x44, 0x24, 0x20, 0x44, 0x8B, 0x47, 0x34, 0x8B, 0x47, 0x38, 0x89, 0x44, 0x24, 0x1C,
    0x8B, 0x47, 0x3C, 0x89, 0x44, 0x24, 0x18, 0x31, 0xFF, 0x44, 0x89, 0x54, 0x24, 0x38, 0x44, 0x89,
    0x9C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x66, 0x2E,
    0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l100bde_1 : ∀ x ∈ codeRange 0x100c28 bytes_l100bde_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xc28 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100bde : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100bde (leaR64Effect 0x100bde 0 (.sib 3 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 10] []) (.reg (.gpr 0))) #v[3, 10]
    (.letOp (n := 54) (.exec 0x100bde (fun s => s.RIP = 0x100bde) (leaR64Effect 0x100bde 0 (.sib 3 (some 10) 0 .none)) (Reg.operands [.gpr 3, .gpr 10] [])) #v[3, 10]
    (.letOp (n := 55) (.exec 0x100be2 (StorePre 0x100be2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100be2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100be2 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x100be7 (leaR64Effect 0x100be7 0 (.sib 14 (some 10) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 10] []) (.reg (.gpr 0))) #v[14, 10]
    (.letOp (n := 57) (.exec 0x100be7 (fun s => s.RIP = 0x100be7) (leaR64Effect 0x100be7 0 (.sib 14 (some 10) 0 .none)) (Reg.operands [.gpr 14, .gpr 10] [])) #v[14, 10]
    (.letOp (n := 58) (.exec 0x100beb (StorePre 0x100beb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100beb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100beb 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100bf0 (movR32M32LowEffect 0x100bf0 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 60) (.exec 0x100bf0 (LoadPre 0x100bf0 (fun s => AddrMode.addr (.base 7 .none) s (0x100bf0 + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x100bf0 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 61) (.exec 0x100bf2 (StorePre 0x100bf2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100bf2 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bf2 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x100bf6 (movR32M32LowEffect 0x100bf6 0 (.base 7 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 63) (.exec 0x100bf6 (LoadPre 0x100bf6 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x100bf6 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100bf6 0 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 64) (.exec 0x100bf9 (StorePre 0x100bf9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100bf9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100bf9 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x100bfd (movR32M32LowEffect 0x100bfd 0 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 66) (.exec 0x100bfd (LoadPre 0x100bfd (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100bfd + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100bfd 0 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.exec 0x100c00 (StorePre 0x100c00 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100c00 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c00 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100c04 (movR32M32LowEffect 0x100c04 0 (.base 7 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 69) (.exec 0x100c04 (LoadPre 0x100c04 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x100c04 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c04 0 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 70) (.exec 0x100c07 (StorePre 0x100c07 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100c07 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c07 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x100c0b (movR32M32Effect 0x100c0b 10 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 72) (.exec 0x100c0b (LoadPre 0x100c0b (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100c0b + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c0b 10 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x100c0f (movR32M32LowEffect 0x100c0f 0 (.base 7 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 74) (.exec 0x100c0f (LoadPre 0x100c0f (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x100c0f + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c0f 0 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.exec 0x100c12 (StorePre 0x100c12 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100c12 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c12 0 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x100c16 (movR32M32LowEffect 0x100c16 0 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 77) (.exec 0x100c16 (LoadPre 0x100c16 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100c16 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c16 0 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.exec 0x100c19 (StorePre 0x100c19 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100c19 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c19 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x100c1d (movR32M32LowEffect 0x100c1d 0 (.base 7 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 80) (.exec 0x100c1d (LoadPre 0x100c1d (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x100c1d + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100c1d 0 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 81) (.exec 0x100c20 (StorePre 0x100c20 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100c20 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100c20 0 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.out 0x100c24 (movR32M32Effect 0x100c24 11 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 7] []) (.reg (.gpr 11))) #v[7]
    (.letOp (n := 83) (.exec 0x100c24 (LoadPre 0x100c24 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x100c24 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100c24 11 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (b_l100bde_1)))))))))))))))))))))))))))))))

def bytes_l100bde : List UInt8 :=
  [0x4A, 0x8D, 0x04, 0x13, 0x48, 0x89, 0x44, 0x24, 0x68, 0x4B, 0x8D, 0x04, 0x16, 0x48, 0x89, 0x44,
    0x24, 0x60, 0x8B, 0x07, 0x89, 0x44, 0x24, 0x58, 0x8B, 0x47, 0x04, 0x89, 0x44, 0x24, 0x10, 0x8B,
    0x47, 0x08, 0x89, 0x44, 0x24, 0x0C, 0x8B, 0x47, 0x0C, 0x89, 0x44, 0x24, 0x40, 0x44, 0x8B, 0x57,
    0x10, 0x8B, 0x47, 0x14, 0x89, 0x44, 0x24, 0x34, 0x8B, 0x47, 0x18, 0x89, 0x44, 0x24, 0x30, 0x8B,
    0x47, 0x1C, 0x89, 0x44, 0x24, 0x2C, 0x44, 0x8B, 0x5F, 0x20] ++ bytes_l100bde_1

theorem code_l100bde : ∀ x ∈ codeRange 0x100bde bytes_l100bde, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xbde 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100bde_1

@[cfg_block] def b_l100c70_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x100cc9 (fun s => s.RIP = 0x100cc9) (fun _ => nopEffect 0x100cc9 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100cd0, RegMap.args [(0, 71), (1, 67), (2, 75), (3, 57), (4, 4), (5, 59), (6, 79), (7, 69), (8, 87), (9, 62), (10, 81), (11, 83), (12, 73), (13, 65), (14, 77), (15, 85), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))

def bytes_l100c70_1 : List UInt8 :=
  [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l100c70_1 : ∀ x ∈ codeRange 0x100cc9 bytes_l100c70_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xcc9 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100c70 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100c70 (StorePre 0x100c70 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c70 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100c70 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 54) (.out 0x100c75 (movR32Imm32Effect 0x100c75 5 0 0xa) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 55) (.exec 0x100c75 (fun s => s.RIP = 0x100c75) (movR32Imm32Effect 0x100c75 5 0 0xa) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.exec 0x100c7a (StorePre 0x100c7a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c7a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100c7a 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x100c7f (movR32M32LowEffect 0x100c7f 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 58) (.exec 0x100c7f (LoadPre 0x100c7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100c7f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c7f 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100c83 (movR32R32Effect 0x100c83 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[10]
    (.letOp (n := 60) (.exec 0x100c83 (fun s => s.RIP = 0x100c83) (movR32R32Effect 0x100c83 3 5 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 61) (.exec 0x100c86 (StorePre 0x100c86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100c86 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c86 12 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 62) (.out 0x100c8b (movR32R32Effect 0x100c8b 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[12]
    (.letOp (n := 63) (.exec 0x100c8b (fun s => s.RIP = 0x100c8b) (movR32R32Effect 0x100c8b 3 9 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 64) (.exec 0x100c8e (StorePre 0x100c8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100c8e + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100c8e 11 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 65) (.out 0x100c93 (movR32M32Effect 0x100c93 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 66) (.exec 0x100c93 (LoadPre 0x100c93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c93 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100c93 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x100c98 (movR32M32LowEffect 0x100c98 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x100c98 (LoadPre 0x100c98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100c98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c98 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x100c9c (movR32R32Effect 0x100c9c 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[8]
    (.letOp (n := 70) (.exec 0x100c9c (fun s => s.RIP = 0x100c9c) (movR32R32Effect 0x100c9c 3 7 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 71) (.out 0x100c9f (movR32M32LowEffect 0x100c9f 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x100c9f (LoadPre 0x100c9f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c9f + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100c9f 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x100ca3 (movR32M32Effect 0x100ca3 12 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x100ca3 (LoadPre 0x100ca3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100ca3 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100ca3 12 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x100ca8 (movR32M32LowEffect 0x100ca8 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x100ca8 (LoadPre 0x100ca8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100ca8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100ca8 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x100cac (movR32M32Effect 0x100cac 14 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 78) (.exec 0x100cac (LoadPre 0x100cac (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100cac + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cac 14 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x100cb1 (movR32M32LowEffect 0x100cb1 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x100cb1 (LoadPre 0x100cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100cb1 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cb1 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x100cb5 (movR32M32Effect 0x100cb5 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x100cb5 (LoadPre 0x100cb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100cb5 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cb5 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x100cba (movR32M32Effect 0x100cba 11 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 84) (.exec 0x100cba (LoadPre 0x100cba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100cba + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cba 11 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x100cbf (movR32M32Effect 0x100cbf 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 86) (.exec 0x100cbf (LoadPre 0x100cbf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100cbf + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cbf 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x100cc4 (movR32M32Effect 0x100cc4 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 88) (.exec 0x100cc4 (LoadPre 0x100cc4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100cc4 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100cc4 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l100c70_1))))))))))))))))))))))))))))))))))))

def bytes_l100c70 : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x70, 0xB8, 0x0A, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x78, 0x8B,
    0x5C, 0x24, 0x58, 0x44, 0x89, 0xD5, 0x44, 0x89, 0x64, 0x24, 0x3C, 0x45, 0x89, 0xE1, 0x44, 0x89,
    0x5C, 0x24, 0x04, 0x44, 0x8B, 0x6C, 0x24, 0x10, 0x8B, 0x4C, 0x24, 0x34, 0x44, 0x89, 0xC7, 0x8B,
    0x44, 0x24, 0x28, 0x44, 0x8B, 0x64, 0x24, 0x0C, 0x8B, 0x54, 0x24, 0x30, 0x44, 0x8B, 0x74, 0x24,
    0x1C, 0x8B, 0x74, 0x24, 0x24, 0x44, 0x8B, 0x54, 0x24, 0x40, 0x44, 0x8B, 0x5C, 0x24, 0x2C, 0x44,
    0x8B, 0x7C, 0x24, 0x18, 0x44, 0x8B, 0x44, 0x24, 0x20] ++ bytes_l100c70_1

theorem code_l100c70 : ∀ x ∈ codeRange 0x100c70 bytes_l100c70, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xc70 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100c70_1

@[cfg_block] def b_l100cd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100cd0 (StorePre 0x100cd0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100cd0 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100cd0 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.out 0x100cd4 (addR32R32Effect 0x100cd4 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[3, 5]
    (.letOp (n := 55) (.exec 0x100cd4 (fun s => s.RIP = 0x100cd4) (addR32R32Effect 0x100cd4 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 56) (.out 0x100cd6 (xorR32R32Effect 0x100cd6 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[9, 54]
    (.letOp (n := 57) (.exec 0x100cd6 (fun s => s.RIP = 0x100cd6) (xorR32R32Effect 0x100cd6 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 54]
    (.letOp (n := 58) (.out 0x100cd9 (rolR32Effect 0x100cd9 4 9 16) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 59) (.exec 0x100cd9 (fun s => s.RIP = 0x100cd9) (rolR32Effect 0x100cd9 4 9 16) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[56]
    (.letOp (n := 60) (.out 0x100cdd (movR32M32LowEffect 0x100cdd 6 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x100cdd (LoadPre 0x100cdd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100cdd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cdd 6 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x100ce1 (addR32R32Effect 0x100ce1 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[60, 58]
    (.letOp (n := 63) (.exec 0x100ce1 (fun s => s.RIP = 0x100ce1) (addR32R32Effect 0x100ce1 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[60, 58]
    (.letOp (n := 64) (.out 0x100ce4 (xorR32R32Effect 0x100ce4 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[5, 62]
    (.letOp (n := 65) (.exec 0x100ce4 (fun s => s.RIP = 0x100ce4) (xorR32R32Effect 0x100ce4 2 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[5, 62]
    (.letOp (n := 66) (.out 0x100ce6 (rolR32Effect 0x100ce6 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[64]
    (.letOp (n := 67) (.exec 0x100ce6 (fun s => s.RIP = 0x100ce6) (rolR32Effect 0x100ce6 3 5 12) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 68) (.out 0x100ce9 (addR32R32Effect 0x100ce9 2 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[54, 66]
    (.letOp (n := 69) (.exec 0x100ce9 (fun s => s.RIP = 0x100ce9) (addR32R32Effect 0x100ce9 2 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[54, 66]
    (.letOp (n := 70) (.out 0x100ceb (xorR32R32Effect 0x100ceb 3 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[58, 68]
    (.letOp (n := 71) (.exec 0x100ceb (fun s => s.RIP = 0x100ceb) (xorR32R32Effect 0x100ceb 3 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[58, 68]
    (.letOp (n := 72) (.out 0x100cee (rolR32Effect 0x100cee 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[70]
    (.letOp (n := 73) (.exec 0x100cee (fun s => s.RIP = 0x100cee) (rolR32Effect 0x100cee 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[70]
    (.letOp (n := 74) (.out 0x100cf2 (addR32R32Effect 0x100cf2 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[62, 72]
    (.letOp (n := 75) (.exec 0x100cf2 (fun s => s.RIP = 0x100cf2) (addR32R32Effect 0x100cf2 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[62, 72]
    (.letOp (n := 76) (.exec 0x100cf5 (StorePre 0x100cf5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100cf5 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100cf5 6 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x100cf9 (xorR32R32Effect 0x100cf9 2 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[66, 74]
    (.letOp (n := 78) (.exec 0x100cf9 (fun s => s.RIP = 0x100cf9) (xorR32R32Effect 0x100cf9 2 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[66, 74]
    (.letOp (n := 79) (.out 0x100cfb (movR32M32LowEffect 0x100cfb 6 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 80) (.exec 0x100cfb (LoadPre 0x100cfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100cfb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100cfb 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x100cff (rolR32Effect 0x100cff 3 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[77]
    (.letOp (n := 82) (.exec 0x100cff (fun s => s.RIP = 0x100cff) (rolR32Effect 0x100cff 3 5 7) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.terminate (.br ⟨.l100d02, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 68), (4, 4), (5, 81), (6, 79), (7, 7), (8, 8), (9, 72), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l100cd0 : List UInt8 :=
  [0x89, 0x74, 0x24, 0x14, 0x01, 0xEB, 0x41, 0x31, 0xD9, 0x41, 0xC1, 0xC1, 0x10, 0x8B, 0x74, 0x24,
    0x04, 0x44, 0x01, 0xCE, 0x31, 0xF5, 0xC1, 0xC5, 0x0C, 0x01, 0xEB, 0x41, 0x31, 0xD9, 0x41, 0xC1,
    0xC1, 0x08, 0x44, 0x01, 0xCE, 0x89, 0x74, 0x24, 0x04, 0x31, 0xF5, 0x8B, 0x74, 0x24, 0x14, 0xC1,
    0xC5, 0x07]

theorem code_l100cd0 : ∀ x ∈ codeRange 0x100cd0 bytes_l100cd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xcd0 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100d02 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100d02 (addR32R32Effect 0x100d02 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[13, 1]
    (.letOp (n := 54) (.exec 0x100d02 (fun s => s.RIP = 0x100d02) (addR32R32Effect 0x100d02 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[13, 1]
    (.letOp (n := 55) (.out 0x100d05 (xorR32R32Effect 0x100d05 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[7, 53]
    (.letOp (n := 56) (.exec 0x100d05 (fun s => s.RIP = 0x100d05) (xorR32R32Effect 0x100d05 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[7, 53]
    (.letOp (n := 57) (.out 0x100d08 (rolR32Effect 0x100d08 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x100d08 (fun s => s.RIP = 0x100d08) (rolR32Effect 0x100d08 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100d0b (addR32R32Effect 0x100d0b 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[0, 57]
    (.letOp (n := 60) (.exec 0x100d0b (fun s => s.RIP = 0x100d0b) (addR32R32Effect 0x100d0b 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 57]
    (.letOp (n := 61) (.out 0x100d0d (xorR32R32Effect 0x100d0d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1, 59]
    (.letOp (n := 62) (.exec 0x100d0d (fun s => s.RIP = 0x100d0d) (xorR32R32Effect 0x100d0d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1, 59]
    (.letOp (n := 63) (.out 0x100d0f (rolR32Effect 0x100d0f 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x100d0f (fun s => s.RIP = 0x100d0f) (rolR32Effect 0x100d0f 3 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100d12 (addR32R32Effect 0x100d12 3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100d12 (fun s => s.RIP = 0x100d12) (addR32R32Effect 0x100d12 3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100d15 (xorR32R32Effect 0x100d15 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100d15 (fun s => s.RIP = 0x100d15) (xorR32R32Effect 0x100d15 3 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100d18 (rolR32Effect 0x100d18 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[67]
    (.letOp (n := 70) (.exec 0x100d18 (fun s => s.RIP = 0x100d18) (rolR32Effect 0x100d18 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100d1b (addR32R32Effect 0x100d1b 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100d1b (fun s => s.RIP = 0x100d1b) (addR32R32Effect 0x100d1b 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[59, 69]
    (.letOp (n := 73) (.exec 0x100d1d (StorePre 0x100d1d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d1d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100d1d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x100d21 (xorR32R32Effect 0x100d21 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[63, 71]
    (.letOp (n := 75) (.exec 0x100d21 (fun s => s.RIP = 0x100d21) (xorR32R32Effect 0x100d21 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[63, 71]
    (.letOp (n := 76) (.out 0x100d23 (rolR32Effect 0x100d23 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[74]
    (.letOp (n := 77) (.exec 0x100d23 (fun s => s.RIP = 0x100d23) (rolR32Effect 0x100d23 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.terminate (.br ⟨.l100d26, RegMap.args [(0, 71), (1, 76), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 69), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l100d02 : List UInt8 :=
  [0x41, 0x01, 0xCD, 0x44, 0x31, 0xEF, 0xC1, 0xC7, 0x10, 0x01, 0xF8, 0x31, 0xC1, 0xC1, 0xC1, 0x0C,
    0x41, 0x01, 0xCD, 0x44, 0x31, 0xEF, 0xC1, 0xC7, 0x08, 0x01, 0xF8, 0x89, 0x44, 0x24, 0x08, 0x31,
    0xC1, 0xC1, 0xC1, 0x07]

theorem code_l100d02 : ∀ x ∈ codeRange 0x100d02 bytes_l100d02, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd02 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100d26 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100d26 (addR32R32Effect 0x100d26 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[12, 2]
    (.letOp (n := 54) (.exec 0x100d26 (fun s => s.RIP = 0x100d26) (addR32R32Effect 0x100d26 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[12, 2]
    (.letOp (n := 55) (.out 0x100d29 (xorR32R32Effect 0x100d29 3 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[14, 53]
    (.letOp (n := 56) (.exec 0x100d29 (fun s => s.RIP = 0x100d29) (xorR32R32Effect 0x100d29 3 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[14, 53]
    (.letOp (n := 57) (.out 0x100d2c (rolR32Effect 0x100d2c 4 14 16) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 58) (.exec 0x100d2c (fun s => s.RIP = 0x100d2c) (rolR32Effect 0x100d2c 4 14 16) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100d30 (addR32R32Effect 0x100d30 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 60) (.exec 0x100d30 (fun s => s.RIP = 0x100d30) (addR32R32Effect 0x100d30 3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[6, 57]
    (.letOp (n := 61) (.out 0x100d33 (xorR32R32Effect 0x100d33 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 59]
    (.letOp (n := 62) (.exec 0x100d33 (fun s => s.RIP = 0x100d33) (xorR32R32Effect 0x100d33 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 59]
    (.letOp (n := 63) (.out 0x100d35 (rolR32Effect 0x100d35 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x100d35 (fun s => s.RIP = 0x100d35) (rolR32Effect 0x100d35 3 2 12) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100d38 (addR32R32Effect 0x100d38 3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100d38 (fun s => s.RIP = 0x100d38) (addR32R32Effect 0x100d38 3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100d3b (xorR32R32Effect 0x100d3b 3 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100d3b (fun s => s.RIP = 0x100d3b) (xorR32R32Effect 0x100d3b 3 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100d3e (rolR32Effect 0x100d3e 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 70) (.exec 0x100d3e (fun s => s.RIP = 0x100d3e) (rolR32Effect 0x100d3e 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100d42 (addR32R32Effect 0x100d42 3 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100d42 (fun s => s.RIP = 0x100d42) (addR32R32Effect 0x100d42 3 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x100d45 (xorR32R32Effect 0x100d45 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x100d45 (fun s => s.RIP = 0x100d45) (xorR32R32Effect 0x100d45 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x100d47 (rolR32Effect 0x100d47 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 76) (.exec 0x100d47 (fun s => s.RIP = 0x100d47) (rolR32Effect 0x100d47 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l100d4a, RegMap.args [(1, 1), (2, 75), (3, 3), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l100d26 : List UInt8 :=
  [0x41, 0x01, 0xD4, 0x45, 0x31, 0xE6, 0x41, 0xC1, 0xC6, 0x10, 0x44, 0x01, 0xF6, 0x31, 0xF2, 0xC1,
    0xC2, 0x0C, 0x41, 0x01, 0xD4, 0x45, 0x31, 0xE6, 0x41, 0xC1, 0xC6, 0x08, 0x44, 0x01, 0xF6, 0x31,
    0xF2, 0xC1, 0xC2, 0x07]

theorem code_l100d26 : ∀ x ∈ codeRange 0x100d26 bytes_l100d26, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd26 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100d4a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100d4a (addR32R32Effect 0x100d4a 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[10, 11]
    (.letOp (n := 54) (.exec 0x100d4a (fun s => s.RIP = 0x100d4a) (addR32R32Effect 0x100d4a 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 11]
    (.letOp (n := 55) (.out 0x100d4d (xorR32R32Effect 0x100d4d 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[15, 53]
    (.letOp (n := 56) (.exec 0x100d4d (fun s => s.RIP = 0x100d4d) (xorR32R32Effect 0x100d4d 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[15, 53]
    (.letOp (n := 57) (.out 0x100d50 (rolR32Effect 0x100d50 4 15 16) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 58) (.exec 0x100d50 (fun s => s.RIP = 0x100d50) (rolR32Effect 0x100d50 4 15 16) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100d54 (addR32R32Effect 0x100d54 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[8, 57]
    (.letOp (n := 60) (.exec 0x100d54 (fun s => s.RIP = 0x100d54) (addR32R32Effect 0x100d54 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[8, 57]
    (.letOp (n := 61) (.out 0x100d57 (xorR32R32Effect 0x100d57 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[11, 59]
    (.letOp (n := 62) (.exec 0x100d57 (fun s => s.RIP = 0x100d57) (xorR32R32Effect 0x100d57 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[11, 59]
    (.letOp (n := 63) (.out 0x100d5a (rolR32Effect 0x100d5a 4 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 64) (.exec 0x100d5a (fun s => s.RIP = 0x100d5a) (rolR32Effect 0x100d5a 4 11 12) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100d5e (addR32R32Effect 0x100d5e 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100d5e (fun s => s.RIP = 0x100d5e) (addR32R32Effect 0x100d5e 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100d61 (xorR32R32Effect 0x100d61 3 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100d61 (fun s => s.RIP = 0x100d61) (xorR32R32Effect 0x100d61 3 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100d64 (rolR32Effect 0x100d64 4 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.exec 0x100d64 (fun s => s.RIP = 0x100d64) (rolR32Effect 0x100d64 4 15 8) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100d68 (addR32R32Effect 0x100d68 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100d68 (fun s => s.RIP = 0x100d68) (addR32R32Effect 0x100d68 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x100d6b (xorR32R32Effect 0x100d6b 3 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x100d6b (fun s => s.RIP = 0x100d6b) (xorR32R32Effect 0x100d6b 3 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x100d6e (rolR32Effect 0x100d6e 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x100d6e (fun s => s.RIP = 0x100d6e) (rolR32Effect 0x100d6e 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l100d72, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 9), (10, 65), (11, 75), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l100d4a : List UInt8 :=
  [0x45, 0x01, 0xDA, 0x45, 0x31, 0xD7, 0x41, 0xC1, 0xC7, 0x10, 0x45, 0x01, 0xF8, 0x45, 0x31, 0xC3,
    0x41, 0xC1, 0xC3, 0x0C, 0x45, 0x01, 0xDA, 0x45, 0x31, 0xD7, 0x41, 0xC1, 0xC7, 0x08, 0x45, 0x01,
    0xF8, 0x45, 0x31, 0xC3, 0x41, 0xC1, 0xC3, 0x07]

theorem code_l100d4a : ∀ x ∈ codeRange 0x100d4a bytes_l100d4a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd4a 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100d72 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100d72 (addR32R32Effect 0x100d72 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[3, 1]
    (.letOp (n := 54) (.exec 0x100d72 (fun s => s.RIP = 0x100d72) (addR32R32Effect 0x100d72 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[3, 1]
    (.letOp (n := 55) (.out 0x100d74 (xorR32R32Effect 0x100d74 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[15, 53]
    (.letOp (n := 56) (.exec 0x100d74 (fun s => s.RIP = 0x100d74) (xorR32R32Effect 0x100d74 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 53]
    (.letOp (n := 57) (.out 0x100d77 (rolR32Effect 0x100d77 4 15 16) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 58) (.exec 0x100d77 (fun s => s.RIP = 0x100d77) (rolR32Effect 0x100d77 4 15 16) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100d7b (addR32R32Effect 0x100d7b 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[6, 57]
    (.letOp (n := 60) (.exec 0x100d7b (fun s => s.RIP = 0x100d7b) (addR32R32Effect 0x100d7b 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[6, 57]
    (.letOp (n := 61) (.out 0x100d7e (xorR32R32Effect 0x100d7e 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1, 59]
    (.letOp (n := 62) (.exec 0x100d7e (fun s => s.RIP = 0x100d7e) (xorR32R32Effect 0x100d7e 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1, 59]
    (.letOp (n := 63) (.out 0x100d80 (rolR32Effect 0x100d80 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x100d80 (fun s => s.RIP = 0x100d80) (rolR32Effect 0x100d80 3 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100d83 (addR32R32Effect 0x100d83 2 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100d83 (fun s => s.RIP = 0x100d83) (addR32R32Effect 0x100d83 2 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100d85 (xorR32R32Effect 0x100d85 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100d85 (fun s => s.RIP = 0x100d85) (xorR32R32Effect 0x100d85 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100d88 (rolR32Effect 0x100d88 4 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.exec 0x100d88 (fun s => s.RIP = 0x100d88) (rolR32Effect 0x100d88 4 15 8) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100d8c (addR32R32Effect 0x100d8c 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100d8c (fun s => s.RIP = 0x100d8c) (addR32R32Effect 0x100d8c 3 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x100d8f (xorR32R32Effect 0x100d8f 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x100d8f (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x100d91 (rolR32Effect 0x100d91 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[73]
    (.letOp (n := 76) (.exec 0x100d91 (fun s => s.RIP = 0x100d91) (rolR32Effect 0x100d91 3 1 7) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l100d94, RegMap.args [(1, 75), (2, 2), (3, 65), (4, 4), (5, 5), (6, 71), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l100d72 : List UInt8 :=
  [0x01, 0xCB, 0x41, 0x31, 0xDF, 0x41, 0xC1, 0xC7, 0x10, 0x44, 0x01, 0xFE, 0x31, 0xF1, 0xC1, 0xC1,
    0x0C, 0x01, 0xCB, 0x41, 0x31, 0xDF, 0x41, 0xC1, 0xC7, 0x08, 0x44, 0x01, 0xFE, 0x31, 0xF1, 0xC1,
    0xC1, 0x07]

theorem code_l100d72 : ∀ x ∈ codeRange 0x100d72 bytes_l100d72, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd72 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100d94 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100d94 (addR32R32Effect 0x100d94 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[13, 2]
    (.letOp (n := 54) (.exec 0x100d94 (fun s => s.RIP = 0x100d94) (addR32R32Effect 0x100d94 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[13, 2]
    (.letOp (n := 55) (.out 0x100d97 (xorR32R32Effect 0x100d97 3 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[9, 53]
    (.letOp (n := 56) (.exec 0x100d97 (fun s => s.RIP = 0x100d97) (xorR32R32Effect 0x100d97 3 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[9, 53]
    (.letOp (n := 57) (.out 0x100d9a (rolR32Effect 0x100d9a 4 9 16) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x100d9a (fun s => s.RIP = 0x100d9a) (rolR32Effect 0x100d9a 4 9 16) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100d9e (addR32R32Effect 0x100d9e 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[8, 57]
    (.letOp (n := 60) (.exec 0x100d9e (fun s => s.RIP = 0x100d9e) (addR32R32Effect 0x100d9e 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[8, 57]
    (.letOp (n := 61) (.out 0x100da1 (xorR32R32Effect 0x100da1 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[2, 59]
    (.letOp (n := 62) (.exec 0x100da1 (fun s => s.RIP = 0x100da1) (xorR32R32Effect 0x100da1 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[2, 59]
    (.letOp (n := 63) (.out 0x100da4 (rolR32Effect 0x100da4 3 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x100da4 (fun s => s.RIP = 0x100da4) (rolR32Effect 0x100da4 3 2 12) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100da7 (addR32R32Effect 0x100da7 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100da7 (fun s => s.RIP = 0x100da7) (addR32R32Effect 0x100da7 3 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100daa (xorR32R32Effect 0x100daa 3 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100daa (fun s => s.RIP = 0x100daa) (xorR32R32Effect 0x100daa 3 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100dad (rolR32Effect 0x100dad 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x100dad (fun s => s.RIP = 0x100dad) (rolR32Effect 0x100dad 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100db1 (addR32R32Effect 0x100db1 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100db1 (fun s => s.RIP = 0x100db1) (addR32R32Effect 0x100db1 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x100db4 (xorR32R32Effect 0x100db4 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x100db4 (fun s => s.RIP = 0x100db4) (xorR32R32Effect 0x100db4 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x100db7 (rolR32Effect 0x100db7 3 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[73]
    (.letOp (n := 76) (.exec 0x100db7 (fun s => s.RIP = 0x100db7) (rolR32Effect 0x100db7 3 2 7) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l100dba, RegMap.args [(1, 1), (2, 75), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 71), (9, 69), (10, 10), (11, 11), (12, 12), (13, 65), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l100d94 : List UInt8 :=
  [0x41, 0x01, 0xD5, 0x45, 0x31, 0xE9, 0x41, 0xC1, 0xC1, 0x10, 0x45, 0x01, 0xC8, 0x44, 0x31, 0xC2,
    0xC1, 0xC2, 0x0C, 0x41, 0x01, 0xD5, 0x45, 0x31, 0xE9, 0x41, 0xC1, 0xC1, 0x08, 0x45, 0x01, 0xC8,
    0x44, 0x31, 0xC2, 0xC1, 0xC2, 0x07]

theorem code_l100d94 : ∀ x ∈ codeRange 0x100d94 bytes_l100d94, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd94 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100dba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100dba (addR32R32Effect 0x100dba 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[12, 11]
    (.letOp (n := 54) (.exec 0x100dba (fun s => s.RIP = 0x100dba) (addR32R32Effect 0x100dba 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[12, 11]
    (.letOp (n := 55) (.out 0x100dbd (xorR32R32Effect 0x100dbd 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[7, 53]
    (.letOp (n := 56) (.exec 0x100dbd (fun s => s.RIP = 0x100dbd) (xorR32R32Effect 0x100dbd 3 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[7, 53]
    (.letOp (n := 57) (.out 0x100dc0 (rolR32Effect 0x100dc0 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x100dc0 (fun s => s.RIP = 0x100dc0) (rolR32Effect 0x100dc0 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100dc3 (movR32M32LowEffect 0x100dc3 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x100dc3 (LoadPre 0x100dc3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100dc3 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100dc3 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x100dc7 (addR32R32Effect 0x100dc7 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x100dc7 (fun s => s.RIP = 0x100dc7) (addR32R32Effect 0x100dc7 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x100dc9 (xorR32R32Effect 0x100dc9 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[11, 61]
    (.letOp (n := 64) (.exec 0x100dc9 (fun s => s.RIP = 0x100dc9) (xorR32R32Effect 0x100dc9 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[11, 61]
    (.letOp (n := 65) (.out 0x100dcc (rolR32Effect 0x100dcc 4 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[63]
    (.letOp (n := 66) (.exec 0x100dcc (fun s => s.RIP = 0x100dcc) (rolR32Effect 0x100dcc 4 11 12) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x100dd0 (addR32R32Effect 0x100dd0 3 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[53, 65]
    (.letOp (n := 68) (.exec 0x100dd0 (fun s => s.RIP = 0x100dd0) (addR32R32Effect 0x100dd0 3 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[53, 65]
    (.letOp (n := 69) (.out 0x100dd3 (xorR32R32Effect 0x100dd3 3 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[57, 67]
    (.letOp (n := 70) (.exec 0x100dd3 (fun s => s.RIP = 0x100dd3) (xorR32R32Effect 0x100dd3 3 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[57, 67]
    (.letOp (n := 71) (.out 0x100dd6 (rolR32Effect 0x100dd6 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x100dd6 (fun s => s.RIP = 0x100dd6) (rolR32Effect 0x100dd6 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x100dd9 (addR32R32Effect 0x100dd9 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[61, 71]
    (.letOp (n := 74) (.exec 0x100dd9 (fun s => s.RIP = 0x100dd9) (addR32R32Effect 0x100dd9 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[61, 71]
    (.letOp (n := 75) (.exec 0x100ddb (StorePre 0x100ddb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100ddb + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100ddb 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x100ddf (xorR32R32Effect 0x100ddf 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[65, 73]
    (.letOp (n := 77) (.exec 0x100ddf (fun s => s.RIP = 0x100ddf) (xorR32R32Effect 0x100ddf 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[65, 73]
    (.letOp (n := 78) (.out 0x100de2 (movR32M32LowEffect 0x100de2 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x100de2 (LoadPre 0x100de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100de2 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100de2 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x100de6 (rolR32Effect 0x100de6 4 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[76]
    (.letOp (n := 81) (.exec 0x100de6 (fun s => s.RIP = 0x100de6) (rolR32Effect 0x100de6 4 11 7) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76]
    (.terminate (.br ⟨.l100dea, RegMap.args [(0, 78), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 80), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l100dba : List UInt8 :=
  [0x45, 0x01, 0xDC, 0x44, 0x31, 0xE7, 0xC1, 0xC7, 0x10, 0x8B, 0x44, 0x24, 0x04, 0x01, 0xF8, 0x41,
    0x31, 0xC3, 0x41, 0xC1, 0xC3, 0x0C, 0x45, 0x01, 0xDC, 0x44, 0x31, 0xE7, 0xC1, 0xC7, 0x08, 0x01,
    0xF8, 0x89, 0x44, 0x24, 0x04, 0x41, 0x31, 0xC3, 0x8B, 0x44, 0x24, 0x08, 0x41, 0xC1, 0xC3, 0x07]

theorem code_l100dba : ∀ x ∈ codeRange 0x100dba bytes_l100dba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdba 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100dea : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100dea (addR32R32Effect 0x100dea 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[10, 5]
    (.letOp (n := 54) (.exec 0x100dea (fun s => s.RIP = 0x100dea) (addR32R32Effect 0x100dea 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[10, 5]
    (.letOp (n := 55) (.out 0x100ded (xorR32R32Effect 0x100ded 3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[14, 53]
    (.letOp (n := 56) (.exec 0x100ded (fun s => s.RIP = 0x100ded) (xorR32R32Effect 0x100ded 3 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[14, 53]
    (.letOp (n := 57) (.out 0x100df0 (rolR32Effect 0x100df0 4 14 16) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 58) (.exec 0x100df0 (fun s => s.RIP = 0x100df0) (rolR32Effect 0x100df0 4 14 16) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x100df4 (addR32R32Effect 0x100df4 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[0, 57]
    (.letOp (n := 60) (.exec 0x100df4 (fun s => s.RIP = 0x100df4) (addR32R32Effect 0x100df4 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 57]
    (.letOp (n := 61) (.out 0x100df7 (xorR32R32Effect 0x100df7 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[5, 59]
    (.letOp (n := 62) (.exec 0x100df7 (fun s => s.RIP = 0x100df7) (xorR32R32Effect 0x100df7 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 59]
    (.letOp (n := 63) (.out 0x100df9 (rolR32Effect 0x100df9 3 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[61]
    (.letOp (n := 64) (.exec 0x100df9 (fun s => s.RIP = 0x100df9) (rolR32Effect 0x100df9 3 5 12) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100dfc (addR32R32Effect 0x100dfc 3 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[53, 63]
    (.letOp (n := 66) (.exec 0x100dfc (fun s => s.RIP = 0x100dfc) (addR32R32Effect 0x100dfc 3 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[53, 63]
    (.letOp (n := 67) (.out 0x100dff (xorR32R32Effect 0x100dff 3 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10] []) (.reg (.gpr 14))) #v[57, 65]
    (.letOp (n := 68) (.exec 0x100dff (fun s => s.RIP = 0x100dff) (xorR32R32Effect 0x100dff 3 14 10) (Reg.operands [.gpr 14, .gpr 10] [])) #v[57, 65]
    (.letOp (n := 69) (.out 0x100e02 (rolR32Effect 0x100e02 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 70) (.exec 0x100e02 (fun s => s.RIP = 0x100e02) (rolR32Effect 0x100e02 4 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x100e06 (addR32R32Effect 0x100e06 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[59, 69]
    (.letOp (n := 72) (.exec 0x100e06 (fun s => s.RIP = 0x100e06) (addR32R32Effect 0x100e06 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[59, 69]
    (.letOp (n := 73) (.out 0x100e09 (xorR32R32Effect 0x100e09 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[63, 71]
    (.letOp (n := 74) (.exec 0x100e09 (fun s => s.RIP = 0x100e09) (xorR32R32Effect 0x100e09 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[63, 71]
    (.letOp (n := 75) (.out 0x100e0b (rolR32Effect 0x100e0b 3 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[73]
    (.letOp (n := 76) (.exec 0x100e0b (fun s => s.RIP = 0x100e0b) (rolR32Effect 0x100e0b 3 5 7) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.terminate (.br ⟨.l100e0e, RegMap.args [(0, 71), (1, 1), (2, 2), (3, 3), (4, 4), (5, 75), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 11), (12, 12), (13, 13), (14, 69), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l100dea : List UInt8 :=
  [0x41, 0x01, 0xEA, 0x45, 0x31, 0xD6, 0x41, 0xC1, 0xC6, 0x10, 0x44, 0x01, 0xF0, 0x31, 0xC5, 0xC1,
    0xC5, 0x0C, 0x41, 0x01, 0xEA, 0x45, 0x31, 0xD6, 0x41, 0xC1, 0xC6, 0x08, 0x44, 0x01, 0xF0, 0x31,
    0xC5, 0xC1, 0xC5, 0x07]

theorem code_l100dea : ∀ x ∈ codeRange 0x100dea bytes_l100dea, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdea 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e0e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e0e (decMEffect 0x100e0e 5 64 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x100e0e (StorePre 0x100e0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100e0e + BitVec.ofNat 64 5)) 8) (decMEffect 0x100e0e 5 64 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100cd0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100e19, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100e0e : List UInt8 :=
  [0x48, 0xFF, 0x4C, 0x24, 0x78, 0x0F, 0x85, 0xB7, 0xFE, 0xFF, 0xFF]

theorem code_l100e0e : ∀ x ∈ codeRange 0x100e0e bytes_l100e0e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe0e 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e19 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e19 (addR32M32Effect 0x100e19 4 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[3, 4]
    (.letOp (n := 54) (.exec 0x100e19 (LoadPre 0x100e19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100e19 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e19 4 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 55) (.exec 0x100e1d (StorePre 0x100e1d 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x100e1d + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e1d 3 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x100e24 (addR32M32Effect 0x100e24 5 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[13, 4]
    (.letOp (n := 57) (.exec 0x100e24 (LoadPre 0x100e24 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100e24 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e24 5 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 58) (.exec 0x100e29 (StorePre 0x100e29 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf4)) s (0x100e29 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e29 13 (.sib 4 none 0 (.d32 0xf4))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100e31 (addR32M32Effect 0x100e31 5 12 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[12, 4]
    (.letOp (n := 60) (.exec 0x100e31 (LoadPre 0x100e31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100e31 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e31 5 12 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 61) (.exec 0x100e36 (StorePre 0x100e36 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x100e36 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e36 12 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x100e3e (addR32M32Effect 0x100e3e 5 10 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[10, 4]
    (.letOp (n := 63) (.exec 0x100e3e (LoadPre 0x100e3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100e3e + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e3e 5 10 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 64) (.exec 0x100e43 (StorePre 0x100e43 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x100e43 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e43 10 (.sib 4 none 0 (.d32 0xfc))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x100e4b (movR32M32Effect 0x100e4b 10 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 66) (.exec 0x100e4b (LoadPre 0x100e4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100e4b + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100e4b 10 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x100e50 (addR32R32Effect 0x100e50 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[5, 65]
    (.letOp (n := 68) (.exec 0x100e50 (fun s => s.RIP = 0x100e50) (addR32R32Effect 0x100e50 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[5, 65]
    (.letOp (n := 69) (.exec 0x100e53 (StorePre 0x100e53 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x100e53 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e53 5 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x100e5a (addR32M32Effect 0x100e5a 4 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[1, 4]
    (.letOp (n := 71) (.exec 0x100e5a (LoadPre 0x100e5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x100e5a + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e5a 4 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 72) (.exec 0x100e5e (StorePre 0x100e5e 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x100e5e + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e5e 1 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x100e65 (addR32M32Effect 0x100e65 4 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[2, 4]
    (.letOp (n := 74) (.exec 0x100e65 (LoadPre 0x100e65 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100e65 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e65 4 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 75) (.exec 0x100e69 (StorePre 0x100e69 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x100e69 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e69 2 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x100e70 (addR32M32Effect 0x100e70 5 11 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[11, 4]
    (.letOp (n := 77) (.exec 0x100e70 (LoadPre 0x100e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x100e70 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100e70 5 11 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 78) (.exec 0x100e75 (StorePre 0x100e75 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x100e75 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100e75 11 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x100e7d (movR32M32Effect 0x100e7d 11 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 80) (.exec 0x100e7d (LoadPre 0x100e7d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x100e7d + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x100e7d 11 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x100e85 (movR32M32LowEffect 0x100e85 1 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 82) (.exec 0x100e85 (LoadPre 0x100e85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x100e85 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100e85 1 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x100e89 (addR32R32Effect 0x100e89 3 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[81, 79]
    (.letOp (n := 84) (.exec 0x100e89 (fun s => s.RIP = 0x100e89) (addR32R32Effect 0x100e89 3 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[81, 79]
    (.terminate (.br ⟨.l100e8c, RegMap.args [(0, 0), (1, 83), (2, 73), (3, 53), (4, 4), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (10, 65), (11, 79), (12, 59), (13, 56), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l100e19 : List UInt8 :=
  [0x03, 0x5C, 0x24, 0x58, 0x89, 0x9C, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x44, 0x03, 0x6C, 0x24, 0x10,
    0x44, 0x89, 0xAC, 0x24, 0xF4, 0x00, 0x00, 0x00, 0x44, 0x03, 0x64, 0x24, 0x0C, 0x44, 0x89, 0xA4,
    0x24, 0xF8, 0x00, 0x00, 0x00, 0x44, 0x03, 0x54, 0x24, 0x40, 0x44, 0x89, 0x94, 0x24, 0xFC, 0x00,
    0x00, 0x00, 0x44, 0x8B, 0x54, 0x24, 0x38, 0x44, 0x01, 0xD5, 0x89, 0xAC, 0x24, 0x00, 0x01, 0x00,
    0x00, 0x03, 0x4C, 0x24, 0x34, 0x89, 0x8C, 0x24, 0x04, 0x01, 0x00, 0x00, 0x03, 0x54, 0x24, 0x30,
    0x89, 0x94, 0x24, 0x08, 0x01, 0x00, 0x00, 0x44, 0x03, 0x5C, 0x24, 0x2C, 0x44, 0x89, 0x9C, 0x24,
    0x0C, 0x01, 0x00, 0x00, 0x44, 0x8B, 0x9C, 0x24, 0x84, 0x00, 0x00, 0x00, 0x8B, 0x4C, 0x24, 0x04,
    0x44, 0x01, 0xD9]

theorem code_l100e19 : ∀ x ∈ codeRange 0x100e19 bytes_l100e19, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe19 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e8c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100e8c (StorePre 0x100e8c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x100e8c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e8c 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.out 0x100e93 (addR32M32Effect 0x100e93 4 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[0, 4]
    (.letOp (n := 55) (.exec 0x100e93 (LoadPre 0x100e93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100e93 + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e93 4 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 56) (.exec 0x100e97 (StorePre 0x100e97 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x100e97 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100e97 0 (.sib 4 none 0 (.d32 0x114))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[54, 4]
    (.letOp (n := 57) (.out 0x100e9e (addR32M32Effect 0x100e9e 4 6 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[6, 4]
    (.letOp (n := 58) (.exec 0x100e9e (LoadPre 0x100e9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100e9e + BitVec.ofNat 64 4)) 4) (addR32M32Effect 0x100e9e 4 6 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 59) (.exec 0x100ea2 (StorePre 0x100ea2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x100ea2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100ea2 6 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x100ea9 (addR32M32Effect 0x100ea9 5 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[8, 4]
    (.letOp (n := 61) (.exec 0x100ea9 (LoadPre 0x100ea9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100ea9 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ea9 5 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 62) (.exec 0x100eae (StorePre 0x100eae 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x100eae + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100eae 8 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x100eb6 (movR32M32Effect 0x100eb6 12 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 64) (.exec 0x100eb6 (LoadPre 0x100eb6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100eb6 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100eb6 12 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x100ebb (addR32R32Effect 0x100ebb 3 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[9, 63]
    (.letOp (n := 66) (.exec 0x100ebb (fun s => s.RIP = 0x100ebb) (addR32R32Effect 0x100ebb 3 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[9, 63]
    (.letOp (n := 67) (.exec 0x100ebe (StorePre 0x100ebe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x100ebe + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100ebe 9 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100ec6 (movR32M32Effect 0x100ec6 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 69) (.exec 0x100ec6 (LoadPre 0x100ec6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100ec6 + BitVec.ofNat 64 8)) 4) (movR32M32Effect 0x100ec6 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x100ece (addR32R32Effect 0x100ece 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[7, 68]
    (.letOp (n := 71) (.exec 0x100ece (fun s => s.RIP = 0x100ece) (addR32R32Effect 0x100ece 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 68]
    (.letOp (n := 72) (.out 0x100ed1 (addR32M32Effect 0x100ed1 5 14 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[14, 4]
    (.letOp (n := 73) (.exec 0x100ed1 (LoadPre 0x100ed1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100ed1 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ed1 5 14 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 74) (.out 0x100ed6 (addR32M32Effect 0x100ed6 5 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[15, 4]
    (.letOp (n := 75) (.exec 0x100ed6 (LoadPre 0x100ed6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100ed6 + BitVec.ofNat 64 5)) 4) (addR32M32Effect 0x100ed6 5 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 76) (.exec 0x100edb (StorePre 0x100edb 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x124)) s (0x100edb + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x100edb 7 (.sib 4 none 0 (.d32 0x124))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 77) (.exec 0x100ee2 (StorePre 0x100ee2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x100ee2 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100ee2 14 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 78) (.exec 0x100eea (StorePre 0x100eea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x12c)) s (0x100eea + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100eea 15 (.sib 4 none 0 (.d32 0x12c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 79) (.out 0x100ef2 (movR64M64Effect 0x100ef2 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 80) (.exec 0x100ef2 (LoadPre 0x100ef2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100ef2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ef2 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x100ef7 (movR64R64Effect 0x100ef7 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 82) (.exec 0x100ef7 (fun s => s.RIP = 0x100ef7) (movR64R64Effect 0x100ef7 0 7) (Reg.operands [.gpr 7] [])) #v[79]
    (.letOp (n := 83) (.out 0x100efa (shlR64Effect 0x100efa 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[81]
    (.letOp (n := 84) (.exec 0x100efa (fun s => s.RIP = 0x100efa) (shlR64Effect 0x100efa 4 0 6) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.terminate (.br ⟨.l100efe, RegMap.args [(0, 83), (1, 1), (4, 4), (6, 57), (7, 79), (8, 68), (9, 65), (10, 10), (11, 11), (12, 63), (14, 72), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l100e8c : List UInt8 :=
  [0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x03, 0x44, 0x24, 0x28, 0x89, 0x84, 0x24, 0x14, 0x01,
    0x00, 0x00, 0x03, 0x74, 0x24, 0x24, 0x89, 0xB4, 0x24, 0x18, 0x01, 0x00, 0x00, 0x44, 0x03, 0x44,
    0x24, 0x20, 0x44, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00, 0x44, 0x8B, 0x64, 0x24, 0x3C, 0x45,
    0x01, 0xE1, 0x44, 0x89, 0x8C, 0x24, 0x20, 0x01, 0x00, 0x00, 0x44, 0x8B, 0x84, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x44, 0x01, 0xC7, 0x44, 0x03, 0x74, 0x24, 0x1C, 0x44, 0x03, 0x7C, 0x24, 0x18, 0x89,
    0xBC, 0x24, 0x24, 0x01, 0x00, 0x00, 0x44, 0x89, 0xB4, 0x24, 0x28, 0x01, 0x00, 0x00, 0x44, 0x89,
    0xBC, 0x24, 0x2C, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0xF8, 0x48, 0xC1,
    0xE0, 0x06]

theorem code_l100e8c : ∀ x ∈ codeRange 0x100e8c bytes_l100e8c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe8c 114 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100efe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100efe (movR64M64Effect 0x100efe 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x100efe (LoadPre 0x100efe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100efe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100efe 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100f03 (movR64M64Effect 0x100f03 1 (.sib 2 (some 0) 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 56) (.exec 0x100f03 (LoadPre 0x100f03 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x38)) s (0x100f03 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f03 1 (.sib 2 (some 0) 0 (.d8 0x38))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 57) (.exec 0x100f08 (StorePre 0x100f08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x168)) s (0x100f08 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f08 1 (.sib 4 none 0 (.d32 0x168))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x100f10 (movR64M64Effect 0x100f10 1 (.sib 2 (some 0) 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 59) (.exec 0x100f10 (LoadPre 0x100f10 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x30)) s (0x100f10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f10 1 (.sib 2 (some 0) 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 60) (.exec 0x100f15 (StorePre 0x100f15 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x160)) s (0x100f15 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f15 1 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x100f1d (movR64M64Effect 0x100f1d 1 (.sib 2 (some 0) 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 62) (.exec 0x100f1d (LoadPre 0x100f1d (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x28)) s (0x100f1d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f1d 1 (.sib 2 (some 0) 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 63) (.exec 0x100f22 (StorePre 0x100f22 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x100f22 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f22 1 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x100f2a (movR64M64Effect 0x100f2a 1 (.sib 2 (some 0) 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 65) (.exec 0x100f2a (LoadPre 0x100f2a (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x20)) s (0x100f2a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f2a 1 (.sib 2 (some 0) 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 66) (.exec 0x100f2f (StorePre 0x100f2f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x100f2f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f2f 1 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x100f37 (movR64M64Effect 0x100f37 1 (.sib 2 (some 0) 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 68) (.exec 0x100f37 (LoadPre 0x100f37 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x18)) s (0x100f37 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f37 1 (.sib 2 (some 0) 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 69) (.exec 0x100f3c (StorePre 0x100f3c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x100f3c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f3c 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x100f44 (movR64M64Effect 0x100f44 1 (.sib 2 (some 0) 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 71) (.exec 0x100f44 (LoadPre 0x100f44 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x10)) s (0x100f44 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f44 1 (.sib 2 (some 0) 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 72) (.exec 0x100f49 (StorePre 0x100f49 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x100f49 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f49 1 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x100f51 (movR64M64Effect 0x100f51 1 (.sib 2 (some 0) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2, .gpr 0] []) (.reg (.gpr 1))) #v[53, 0]
    (.letOp (n := 74) (.exec 0x100f51 (LoadPre 0x100f51 (fun s => AddrMode.addr (.sib 2 (some 0) 0 .none) s (0x100f51 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100f51 1 (.sib 2 (some 0) 0 .none)) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 75) (.out 0x100f55 (movR64M64Effect 0x100f55 2 (.sib 2 (some 0) 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 0]
    (.letOp (n := 76) (.exec 0x100f55 (LoadPre 0x100f55 (fun s => AddrMode.addr (.sib 2 (some 0) 0 (.d8 0x8)) s (0x100f55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100f55 2 (.sib 2 (some 0) 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 77) (.exec 0x100f5a (StorePre 0x100f5a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x138)) s (0x100f5a + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f5a 2 (.sib 4 none 0 (.d32 0x138))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.exec 0x100f62 (StorePre 0x100f62 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x100f62 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f62 1 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 79) (.exec 0x100f6a (StorePre 0x100f6a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x100f6a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f6a (.sib 4 none 0 (.d32 0xe8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x100f76 (StorePre 0x100f76 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100f76 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f76 (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x100f82 (StorePre 0x100f82 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100f82 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f82 (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l100f8e, RegMap.args [(0, 0), (1, 73), (2, 75), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l100efe : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x68, 0x48, 0x8B, 0x4C, 0x02, 0x38, 0x48, 0x89, 0x8C, 0x24, 0x68, 0x01,
    0x00, 0x00, 0x48, 0x8B, 0x4C, 0x02, 0x30, 0x48, 0x89, 0x8C, 0x24, 0x60, 0x01, 0x00, 0x00, 0x48,
    0x8B, 0x4C, 0x02, 0x28, 0x48, 0x89, 0x8C, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x02,
    0x20, 0x48, 0x89, 0x8C, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x02, 0x18, 0x48, 0x89,
    0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x02, 0x10, 0x48, 0x89, 0x8C, 0x24, 0x40,
    0x01, 0x00, 0x00, 0x48, 0x8B, 0x0C, 0x02, 0x48, 0x8B, 0x54, 0x02, 0x08, 0x48, 0x89, 0x94, 0x24,
    0x38, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xE8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l100efe : ∀ x ∈ codeRange 0x100efe bytes_l100efe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xefe 144 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100f8e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100f8e (StorePre 0x100f8e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100f8e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f8e (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x100f9a (StorePre 0x100f9a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100f9a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100f9a (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100fa6 (StorePre 0x100fa6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100fa6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fa6 (.sib 4 none 0 (.d32 0xc0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x100fb2 (StorePre 0x100fb2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x100fb2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fb2 (.sib 4 none 0 (.d32 0xb8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100fbe (StorePre 0x100fbe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100fbe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100fbe (.sib 4 none 0 (.d32 0xb0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x100fca (movR32Imm32Effect 0x100fca 5 1 0x3) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x100fca (fun s => s.RIP = 0x100fca) (movR32Imm32Effect 0x100fca 5 1 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.exec 0x100fcf (fun s => s.RIP = 0x100fcf) (fun _ => nopEffect 0x100fcf 1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100fd0, RegMap.args [(0, 0), (1, 58), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l100f8e : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xB9, 0x03, 0x00, 0x00,
    0x00, 0x90]

theorem code_l100f8e : ∀ x ∈ codeRange 0x100f8e bytes_l100f8e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf8e 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100fd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100fd0 (movzxR32M8Effect 0x100fd0 8 2 (.sib 4 (some 1) 0 (.d32 0xed))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4, .gpr 1] []) (.reg (.gpr 2))) #v[4, 1]
    (.letOp (n := 54) (.exec 0x100fd0 (LoadPre 0x100fd0 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xed)) s (0x100fd0 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100fd0 8 2 (.sib 4 (some 1) 0 (.d32 0xed))) (Reg.operands [.gpr 4, .gpr 1] [])) #v[4, 1]
    (.letOp (n := 55) (.out 0x100fd8 (movzxR32M8Effect 0x100fd8 8 6 (.sib 4 (some 1) 0 (.d32 0xee))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4, .gpr 1] []) (.reg (.gpr 6))) #v[4, 1]
    (.letOp (n := 56) (.exec 0x100fd8 (LoadPre 0x100fd8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xee)) s (0x100fd8 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100fd8 8 6 (.sib 4 (some 1) 0 (.d32 0xee))) (Reg.operands [.gpr 4, .gpr 1] [])) #v[4, 1]
    (.letOp (n := 57) (.out 0x100fe0 (xorR8M8Effect 0x100fe0 7 2 (.sib 4 (some 1) 0 (.d32 0x12d))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4, .gpr 1] []) (.reg (.gpr 2))) #v[53, 4, 1]
    (.letOp (n := 58) (.exec 0x100fe0 (LoadPre 0x100fe0 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12d)) s (0x100fe0 + BitVec.ofNat 64 7)) 1) (xorR8M8Effect 0x100fe0 7 2 (.sib 4 (some 1) 0 (.d32 0x12d))) (Reg.operands [.gpr 2, .gpr 4, .gpr 1] [])) #v[53, 4, 1]
    (.letOp (n := 59) (.out 0x100fe7 (xorR8M8Effect 0x100fe7 8 6 (.sib 4 (some 1) 0 (.d32 0x12e))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 1] []) (.reg (.gpr 6))) #v[55, 4, 1]
    (.letOp (n := 60) (.exec 0x100fe7 (LoadPre 0x100fe7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12e)) s (0x100fe7 + BitVec.ofNat 64 8)) 1) (xorR8M8Effect 0x100fe7 8 6 (.sib 4 (some 1) 0 (.d32 0x12e))) (Reg.operands [.gpr 6, .gpr 4, .gpr 1] [])) #v[55, 4, 1]
    (.letOp (n := 61) (.exec 0x100fef (StorePre 0x100fef 7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xad)) s (0x100fef + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x100fef 7 2 (.sib 4 (some 1) 0 (.d32 0xad))) (Reg.operands [.gpr 2, .gpr 4, .gpr 1] [])) #v[57, 4, 1]
    (.letOp (n := 62) (.out 0x100ff6 (movzxR32M8Effect 0x100ff6 8 2 (.sib 4 (some 1) 0 (.d32 0xef))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4, .gpr 1] []) (.reg (.gpr 2))) #v[4, 1]
    (.letOp (n := 63) (.exec 0x100ff6 (LoadPre 0x100ff6 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xef)) s (0x100ff6 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100ff6 8 2 (.sib 4 (some 1) 0 (.d32 0xef))) (Reg.operands [.gpr 4, .gpr 1] [])) #v[4, 1]
    (.letOp (n := 64) (.out 0x100ffe (xorR8M8Effect 0x100ffe 7 2 (.sib 4 (some 1) 0 (.d32 0x12f))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4, .gpr 1] []) (.reg (.gpr 2))) #v[62, 4, 1]
    (.letOp (n := 65) (.exec 0x100ffe (LoadPre 0x100ffe (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x12f)) s (0x100ffe + BitVec.ofNat 64 7)) 1) (xorR8M8Effect 0x100ffe 7 2 (.sib 4 (some 1) 0 (.d32 0x12f))) (Reg.operands [.gpr 2, .gpr 4, .gpr 1] [])) #v[62, 4, 1]
    (.letOp (n := 66) (.exec 0x101005 (StorePre 0x101005 8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xae)) s (0x101005 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x101005 8 6 (.sib 4 (some 1) 0 (.d32 0xae))) (Reg.operands [.gpr 6, .gpr 4, .gpr 1] [])) #v[59, 4, 1]
    (.letOp (n := 67) (.out 0x10100d (movzxR32M8Effect 0x10100d 8 6 (.sib 4 (some 1) 0 (.d32 0xf0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4, .gpr 1] []) (.reg (.gpr 6))) #v[4, 1]
    (.letOp (n := 68) (.exec 0x10100d (LoadPre 0x10100d (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xf0)) s (0x10100d + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x10100d 8 6 (.sib 4 (some 1) 0 (.d32 0xf0))) (Reg.operands [.gpr 4, .gpr 1] [])) #v[4, 1]
    (.letOp (n := 69) (.out 0x101015 (xorR8M8Effect 0x101015 8 6 (.sib 4 (some 1) 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 1] []) (.reg (.gpr 6))) #v[67, 4, 1]
    (.letOp (n := 70) (.exec 0x101015 (LoadPre 0x101015 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0x130)) s (0x101015 + BitVec.ofNat 64 8)) 1) (xorR8M8Effect 0x101015 8 6 (.sib 4 (some 1) 0 (.d32 0x130))) (Reg.operands [.gpr 6, .gpr 4, .gpr 1] [])) #v[67, 4, 1]
    (.letOp (n := 71) (.exec 0x10101d (StorePre 0x10101d 7 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xaf)) s (0x10101d + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10101d 7 2 (.sib 4 (some 1) 0 (.d32 0xaf))) (Reg.operands [.gpr 2, .gpr 4, .gpr 1] [])) #v[64, 4, 1]
    (.letOp (n := 72) (.exec 0x101024 (StorePre 0x101024 8 (fun s => AddrMode.addr (.sib 4 (some 1) 0 (.d32 0xb0)) s (0x101024 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x101024 8 6 (.sib 4 (some 1) 0 (.d32 0xb0))) (Reg.operands [.gpr 6, .gpr 4, .gpr 1] [])) #v[69, 4, 1]
    (.letOp (n := 73) (.out 0x10102c (addR64Imm8Effect 0x10102c 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 74) (.exec 0x10102c (fun s => s.RIP = 0x10102c) (addR64Imm8Effect 0x10102c 1 0x4) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 75) (.out 0x101030 (cmpR64Imm8Effect 0x101030 1 0x43) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[73]
    (.letOp (n := 76) (.exec 0x101030 (fun s => s.RIP = 0x101030) (cmpR64Imm8Effect 0x101030 1 0x43) (Reg.operands [.gpr 1] [])) #v[73]
    (.letOp (n := 77) (.pure (condOp 5)) #v[75]
    (.terminate (.condBr (Fin.last 77) ⟨.l100fd0, RegMap.args [(0, 0), (1, 73), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ ⟨.l101036, RegMap.args [(0, 0), (1, 73), (2, 64), (4, 4), (6, 69), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩))))))))))))))))))))))))))

def bytes_l100fd0 : List UInt8 :=
  [0x0F, 0xB6, 0x94, 0x0C, 0xED, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4, 0x0C, 0xEE, 0x00, 0x00, 0x00,
    0x32, 0x94, 0x0C, 0x2D, 0x01, 0x00, 0x00, 0x40, 0x32, 0xB4, 0x0C, 0x2E, 0x01, 0x00, 0x00, 0x88,
    0x94, 0x0C, 0xAD, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x94, 0x0C, 0xEF, 0x00, 0x00, 0x00, 0x32, 0x94,
    0x0C, 0x2F, 0x01, 0x00, 0x00, 0x40, 0x88, 0xB4, 0x0C, 0xAE, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xB4,
    0x0C, 0xF0, 0x00, 0x00, 0x00, 0x40, 0x32, 0xB4, 0x0C, 0x30, 0x01, 0x00, 0x00, 0x88, 0x94, 0x0C,
    0xAF, 0x00, 0x00, 0x00, 0x40, 0x88, 0xB4, 0x0C, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x83, 0xC1, 0x04,
    0x48, 0x83, 0xF9, 0x43, 0x75, 0x9A]

theorem code_l100fd0 : ∀ x ∈ codeRange 0x100fd0 bytes_l100fd0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfd0 102 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101036_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.pure (condOp 5)) #v[83]
    (.terminate (.condBr (Fin.last 85) ⟨.l100c70, RegMap.args [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ ⟨.l1010b3, RegMap.args [(0, 0), (1, 77), (2, 79), (4, 4), (6, 59), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (19, 83), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩))

def bytes_l101036_1 : List UInt8 :=
  [0x0F, 0x85, 0xBD, 0xFB, 0xFF, 0xFF]

theorem code_l101036_1 : ∀ x ∈ codeRange 0x1010ad bytes_l101036_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10ad 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101036 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101036 (incR32Effect 0x101036 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 54) (.exec 0x101036 (fun s => s.RIP = 0x101036) (incR32Effect 0x101036 3 12) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[12]
    (.letOp (n := 55) (.out 0x101039 (incR64Effect 0x101039 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x101039 (fun s => s.RIP = 0x101039) (incR64Effect 0x101039 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7]
    (.letOp (n := 57) (.out 0x10103c (movR64M64Effect 0x10103c 1 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10103c (LoadPre 0x10103c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x10103c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10103c 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x101044 (movR64M64Effect 0x101044 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x101044 (LoadPre 0x101044 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101044 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101044 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101049 (StorePre 0x101049 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x38)) s (0x101049 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101049 1 (.sib 6 (some 0) 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[57, 59, 0]
    (.letOp (n := 62) (.out 0x10104e (movR64M64Effect 0x10104e 1 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x10104e (LoadPre 0x10104e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10104e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10104e 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x101056 (StorePre 0x101056 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x30)) s (0x101056 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101056 1 (.sib 6 (some 0) 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[62, 59, 0]
    (.letOp (n := 65) (.out 0x10105b (movR64M64Effect 0x10105b 1 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 66) (.exec 0x10105b (LoadPre 0x10105b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10105b + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10105b 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x101063 (StorePre 0x101063 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x28)) s (0x101063 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101063 1 (.sib 6 (some 0) 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[65, 59, 0]
    (.letOp (n := 68) (.out 0x101068 (movR64M64Effect 0x101068 1 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 69) (.exec 0x101068 (LoadPre 0x101068 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x101068 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101068 1 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x101070 (StorePre 0x101070 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x20)) s (0x101070 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101070 1 (.sib 6 (some 0) 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[68, 59, 0]
    (.letOp (n := 71) (.out 0x101075 (movR64M64Effect 0x101075 1 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 72) (.exec 0x101075 (LoadPre 0x101075 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x101075 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101075 1 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x10107d (StorePre 0x10107d 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x18)) s (0x10107d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10107d 1 (.sib 6 (some 0) 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[71, 59, 0]
    (.letOp (n := 74) (.out 0x101082 (movR64M64Effect 0x101082 1 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 75) (.exec 0x101082 (LoadPre 0x101082 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101082 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101082 1 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10108a (StorePre 0x10108a 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x10)) s (0x10108a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10108a 1 (.sib 6 (some 0) 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[74, 59, 0]
    (.letOp (n := 77) (.out 0x10108f (movR64M64Effect 0x10108f 1 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 78) (.exec 0x10108f (LoadPre 0x10108f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10108f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10108f 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101097 (movR64M64Effect 0x101097 2 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 80) (.exec 0x101097 (LoadPre 0x101097 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x101097 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101097 2 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x10109f (StorePre 0x10109f 5 (fun s => AddrMode.addr (.sib 6 (some 0) 0 (.d8 0x8)) s (0x10109f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10109f 2 (.sib 6 (some 0) 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 6, .gpr 0] [])) #v[79, 59, 0]
    (.letOp (n := 82) (.exec 0x1010a4 (StorePre 0x1010a4 4 (fun s => AddrMode.addr (.sib 6 (some 0) 0 .none) s (0x1010a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1010a4 1 (.sib 6 (some 0) 0 .none)) (Reg.operands [.gpr 1, .gpr 6, .gpr 0] [])) #v[77, 59, 0]
    (.letOp (n := 83) (.out 0x1010a8 (cmpMREffect 0x1010a8 5 64 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 4] []) (.flag .ZF)) #v[55, 4]
    (.letOp (n := 84) (.exec 0x1010a8 (LoadPre 0x1010a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1010a8 + BitVec.ofNat 64 5)) 8) (cmpMREffect 0x1010a8 5 64 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[55, 4]
    (b_l101036_1))))))))))))))))))))))))))))))))

def bytes_l101036 : List UInt8 :=
  [0x41, 0xFF, 0xC4, 0x48, 0xFF, 0xC7, 0x48, 0x8B, 0x8C, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x74, 0x24, 0x60, 0x48, 0x89, 0x4C, 0x06, 0x38, 0x48, 0x8B, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x4C, 0x06, 0x30, 0x48, 0x8B, 0x8C, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C,
    0x06, 0x28, 0x48, 0x8B, 0x8C, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x06, 0x20, 0x48,
    0x8B, 0x8C, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x06, 0x18, 0x48, 0x8B, 0x8C, 0x24,
    0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4C, 0x06, 0x10, 0x48, 0x8B, 0x8C, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x94, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x54, 0x06, 0x08, 0x48, 0x89,
    0x0C, 0x06, 0x48, 0x39, 0x7C, 0x24, 0x50] ++ bytes_l101036_1

theorem code_l101036 : ∀ x ∈ codeRange 0x101036 bytes_l101036, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1036 119 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101036_1

@[cfg_block] def b_l1010b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1010b3 (movR64M64Effect 0x1010b3 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1010b3 (LoadPre 0x1010b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010b3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010b3 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1010b8 (StorePre 0x1010b8 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x1010b8 + BitVec.ofNat 64 4)) 4) (movM32R32Effect 0x1010b8 12 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 12, .gpr 7] [])) #v[12, 53]
    (.letOp (n := 56) (.out 0x1010bc (movR64M64Effect 0x1010bc 11 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 57) (.exec 0x1010bc (LoadPre 0x1010bc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1010bc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1010bc 11 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1010c4 (movR64M64Effect 0x1010c4 15 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 59) (.exec 0x1010c4 (LoadPre 0x1010c4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1010c4 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1010c4 15 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1010cc, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 53), (9, 9), (11, 56), (12, 12), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1010b3 : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x48, 0x44, 0x89, 0x67, 0x30, 0x4C, 0x8B, 0x9C, 0x24, 0xA8, 0x00, 0x00,
    0x00, 0x4C, 0x8B, 0xBC, 0x24, 0xA0, 0x00, 0x00, 0x00]

theorem code_l1010b3 : ∀ x ∈ codeRange 0x1010b3 bytes_l1010b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10b3 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1010cc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1010cc (testR64R64Effect 0x1010cc 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 54) (.exec 0x1010cc (fun s => s.RIP = 0x1010cc) (testR64R64Effect 0x1010cc 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1014a8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1010d5, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (9, 9), (11, 11), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1010cc : List UInt8 :=
  [0x4D, 0x85, 0xFF, 0x0F, 0x84, 0xD3, 0x03, 0x00, 0x00]

theorem code_l1010cc : ∀ x ∈ codeRange 0x1010cc bytes_l1010cc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10cc 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end ChaCha20Poly1305.Proofs.Decrypt.Lifted
