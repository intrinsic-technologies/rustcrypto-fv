import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_block] def b_l101c20_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x101c6d (StorePre 0x101c6d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101c6d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c6d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 65]
    (.letOp (n := 89) (.out 0x101c72 (movR64R64Effect 0x101c72 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 90) (.exec 0x101c72 (fun s => s.RIP = 0x101c72) (movR64R64Effect 0x101c72 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 91) (.out 0x101c75 (shrR64Effect 0x101c75 4 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x101c75 (fun s => s.RIP = 0x101c75) (shrR64Effect 0x101c75 4 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 93) (.out 0x101c79 (leaR64Effect 0x101c79 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 94) (.exec 0x101c79 (fun s => s.RIP = 0x101c79) (leaR64Effect 0x101c79 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 95) (.out 0x101c7e (movR64R64Effect 0x101c7e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 96) (.exec 0x101c7e (fun s => s.RIP = 0x101c7e) (movR64R64Effect 0x101c7e 6 12) (Reg.operands [.gpr 12] [])) #v[67]
    (.letOp (n := 97) (.out 0x101c81 (callEffect (fun _ => 0x109980) 0x101c86) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 98) (.exec 0x101c81 (PushPre 0x101c81 5) (callEffect (fun _ => 0x109980) 0x101c86) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 99) (.const ⟨64, 0x101c86⟩) #v[]
    (.terminate (.call ⟨.l109980, RegMap.args [(0, 83), (1, 85), (2, 91), (3, 72), (4, 97), (5, 5), (6, 95), (7, 93), (8, 8), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 75), (22, 22), (39, 39), (50, 50), (51, 51)] 100⟩ { target := .l101c86, kept := #v[], arity := rfl, guard := some (Fin.last 99) })))))))))))))

def bytes_l101c20_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x50, 0x4C, 0x89, 0xC2, 0x48, 0xC1, 0xEA, 0x04, 0x48, 0x8D, 0x7C, 0x24,
    0x50, 0x4C, 0x89, 0xE6, 0xE8, 0xFA, 0x7C, 0x00, 0x00]

theorem code_l101c20_1 : ∀ x ∈ codeRange 0x101c6d bytes_l101c20_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c6d 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101c20 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101c20 (pushR64Effect 0x101c20 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x101c20 (PushPre 0x101c20 1) (pushR64Effect 0x101c20 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x101c21 (pushR64Effect 0x101c21 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101c21 (PushPre 0x101c21 2) (pushR64Effect 0x101c21 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101c23 (pushR64Effect 0x101c23 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x101c23 (PushPre 0x101c23 2) (pushR64Effect 0x101c23 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x101c25 (pushR64Effect 0x101c25 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x101c25 (PushPre 0x101c25 2) (pushR64Effect 0x101c25 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x101c27 (pushR64Effect 0x101c27 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101c27 (PushPre 0x101c27 2) (pushR64Effect 0x101c27 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101c29 (pushR64Effect 0x101c29 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x101c29 (PushPre 0x101c29 1) (pushR64Effect 0x101c29 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x101c2a (subR64Imm32Effect 0x101c2a 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x101c2a (fun s => s.RIP = 0x101c2a) (subR64Imm32Effect 0x101c2a 4 0x88) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x101c31 (movR64R64Effect 0x101c31 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[1]
    (.letOp (n := 68) (.exec 0x101c31 (fun s => s.RIP = 0x101c31) (movR64R64Effect 0x101c31 12 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.exec 0x101c34 (StorePre 0x101c34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101c34 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c34 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 65]
    (.letOp (n := 70) (.out 0x101c39 (movR64R64Effect 0x101c39 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[9]
    (.letOp (n := 71) (.exec 0x101c39 (fun s => s.RIP = 0x101c39) (movR64R64Effect 0x101c39 14 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 72) (.out 0x101c3c (movR64R64Effect 0x101c3c 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 8] []) (.reg (.gpr 3))) #v[8]
    (.letOp (n := 73) (.exec 0x101c3c (fun s => s.RIP = 0x101c3c) (movR64R64Effect 0x101c3c 3 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 74) (.exec 0x101c3f (StorePre 0x101c3f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101c3f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x101c3f 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 75) (.out 0x101c47 (movR64M64Effect 0x101c47 15 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 76) (.exec 0x101c47 (LoadPre 0x101c47 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101c47 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101c47 15 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.out 0x101c4f (movR64M64Effect 0x101c4f 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 78) (.exec 0x101c4f (LoadPre 0x101c4f (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101c4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c4f 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.exec 0x101c53 (StorePre 0x101c53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101c53 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c53 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 80) (.out 0x101c58 (movR64M64Effect 0x101c58 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 81) (.exec 0x101c58 (LoadPre 0x101c58 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x101c58 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c58 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 82) (.exec 0x101c5c (StorePre 0x101c5c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101c5c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c5c 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 83) (.out 0x101c61 (movR64M64Effect 0x101c61 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 84) (.exec 0x101c61 (LoadPre 0x101c61 (fun s => AddrMode.addr (.base 6 .none) s (0x101c61 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101c61 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 85) (.out 0x101c64 (movR64M64Effect 0x101c64 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 86) (.exec 0x101c64 (LoadPre 0x101c64 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x101c64 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101c64 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 87) (.exec 0x101c68 (StorePre 0x101c68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101c68 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101c68 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 65]
    (b_l101c20_1)))))))))))))))))))))))))))))))))))

def bytes_l101c20 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x88, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xCC, 0x48, 0x89, 0x54, 0x24, 0x78, 0x4D, 0x89, 0xCE, 0x4C, 0x89, 0xC3, 0x48,
    0x89, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24,
    0x60, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x58] ++ bytes_l101c20_1

theorem code_l101c20 : ∀ x ∈ codeRange 0x101c20 bytes_l101c20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c20 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101c20_1

@[cfg_block] def b_l101c86 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101c86 (movR64R64Effect 0x101c86 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 3] []) (.reg (.gpr 13))) #v[3]
    (.letOp (n := 54) (.exec 0x101c86 (fun s => s.RIP = 0x101c86) (movR64R64Effect 0x101c86 13 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101c89 (andR64Imm8Effect 0x101c89 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 56) (.out 0x101c89 (andR64Imm8Effect 0x101c89 13 0xf) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x101c89 (fun s => s.RIP = 0x101c89) (andR64Imm8Effect 0x101c89 13 0xf) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101d5e, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101c93, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101c86 : List UInt8 :=
  [0x49, 0x89, 0xDD, 0x49, 0x83, 0xE5, 0x0F, 0x0F, 0x84, 0xCB, 0x00, 0x00, 0x00]

theorem code_l101c86 : ∀ x ∈ codeRange 0x101c86 bytes_l101c86, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c86 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101c93 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101c93 (movR64Imm64Effect 0x101c93 0 0x1ffffffffffffff0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101c93 (fun s => s.RIP = 0x101c93) (movR64Imm64Effect 0x101c93 0 0x1ffffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101c9d (andR64R64Effect 0x101c9d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x101c9d (fun s => s.RIP = 0x101c9d) (andR64R64Effect 0x101c9d 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x101ca0 (addR64R64Effect 0x101ca0 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[12, 55]
    (.letOp (n := 58) (.exec 0x101ca0 (fun s => s.RIP = 0x101ca0) (addR64R64Effect 0x101ca0 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[12, 55]
    (.letOp (n := 59) (.out 0x101ca3 (movR32Imm32Effect 0x101ca3 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x101ca3 (fun s => s.RIP = 0x101ca3) (movR32Imm32Effect 0x101ca3 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x101ca8 (subR64R64Effect 0x101ca8 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13] []) (.reg (.gpr 2))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x101ca8 (fun s => s.RIP = 0x101ca8) (subR64R64Effect 0x101ca8 2 13) (Reg.operands [.gpr 2, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x101cab (leaR64Effect 0x101cab 7 (.sib 4 (some 13) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 13] []) (.reg (.gpr 7))) #v[4, 13]
    (.letOp (n := 64) (.exec 0x101cab (fun s => s.RIP = 0x101cab) (leaR64Effect 0x101cab 7 (.sib 4 (some 13) 0 .none)) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 65) (.out 0x101caf (addR64Imm8Effect 0x101caf 7 0x40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x101caf (fun s => s.RIP = 0x101caf) (addR64Imm8Effect 0x101caf 7 0x40) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x101cb3 (xorR32R32Effect 0x101cb3 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x101cb3 (fun s => s.RIP = 0x101cb3) (xorR32R32Effect 0x101cb3 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x101cb5 (callEffect (callMemPtr 0x101cb5 (.rip 0xff56d)) (0x101cb5 + BitVec.ofNat 64 (callMemLen (.rip 0xff56d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101cb5 (GoesTo (CallMemPre 0x101cb5 (.rip 0xff56d)) (callEffect (callMemPtr 0x101cb5 (.rip 0xff56d)) (0x101cb5 + BitVec.ofNat 64 (callMemLen (.rip 0xff56d)))) 0x103eb0) (callEffect (callMemPtr 0x101cb5 (.rip 0xff56d)) (0x101cb5 + BitVec.ofNat 64 (callMemLen (.rip 0xff56d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101cbb⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101cbb, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101c93 : List UInt8 :=
  [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x1F, 0x48, 0x21, 0xD8, 0x49, 0x01, 0xC4,
    0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xEA, 0x4A, 0x8D, 0x3C, 0x2C, 0x48, 0x83, 0xC7, 0x40,
    0x31, 0xF6, 0xFF, 0x15, 0x6D, 0xF5, 0x0F, 0x00]

theorem code_l101c93 : ∀ x ∈ codeRange 0x101c93 bytes_l101c93, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c93 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101cbb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101cbb (leaR64Effect 0x101cbb 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101cbb (fun s => s.RIP = 0x101cbb) (leaR64Effect 0x101cbb 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101cc0 (movR64R64Effect 0x101cc0 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x101cc0 (fun s => s.RIP = 0x101cc0) (movR64R64Effect 0x101cc0 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x101cc3 (movR64R64Effect 0x101cc3 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 58) (.exec 0x101cc3 (fun s => s.RIP = 0x101cc3) (movR64R64Effect 0x101cc3 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x101cc6 (callEffect (callMemPtr 0x101cc6 (.rip 0xff53c)) (0x101cc6 + BitVec.ofNat 64 (callMemLen (.rip 0xff53c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101cc6 (GoesTo (CallMemPre 0x101cc6 (.rip 0xff53c)) (callEffect (callMemPtr 0x101cc6 (.rip 0xff53c)) (0x101cc6 + BitVec.ofNat 64 (callMemLen (.rip 0xff53c)))) 0x103f00) (callEffect (callMemPtr 0x101cc6 (.rip 0xff53c)) (0x101cc6 + BitVec.ofNat 64 (callMemLen (.rip 0xff53c)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101ccc⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101ccc, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101cbb : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xEA, 0xFF, 0x15, 0x3C, 0xF5, 0x0F,
    0x00]

theorem code_l101cbb : ∀ x ∈ codeRange 0x101cbb bytes_l101cbb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1cbb 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101ccc_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x101d2a (movzxR32M8Effect 0x101d2a 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x101d2a (LoadPre 0x101d2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101d2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d2a 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x101d2f (StorePre 0x101d2f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101d2f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d2f 4 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.exec 0x101d33 (StorePre 0x101d33 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101d33 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d33 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 89) (.out 0x101d37 (movzxR32M8Effect 0x101d37 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x101d37 (LoadPre 0x101d37 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101d37 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d37 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x101d3c (movzxR32M8Effect 0x101d3c 5 1 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 92) (.exec 0x101d3c (LoadPre 0x101d3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101d3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d3c 5 1 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x101d41 (StorePre 0x101d41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101d41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d41 4 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.exec 0x101d45 (StorePre 0x101d45 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101d45 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101d45 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 95) (.exec 0x101d49 (StorePre 0x101d49 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101d49 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101d49 6 16 (.sib 4 none 0 (.d8 0x17)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x101d4f (leaR64Effect 0x101d4f 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 97) (.exec 0x101d4f (fun s => s.RIP = 0x101d4f) (leaR64Effect 0x101d4f 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x101d54 (leaR64Effect 0x101d54 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 99) (.exec 0x101d54 (fun s => s.RIP = 0x101d54) (leaR64Effect 0x101d54 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x101d59 (callEffect (fun _ => 0x1034c0) 0x101d5e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 101) (.exec 0x101d59 (PushPre 0x101d59 5) (callEffect (fun _ => 0x1034c0) 0x101d5e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.const ⟨64, 0x101d5e⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 103⟩ { target := .l101d5e, kept := #v[], arity := rfl, guard := some (Fin.last 102) })))))))))))))))))))

def bytes_l101ccc_1 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1A, 0x88, 0x4C, 0x24, 0x15, 0x88, 0x44, 0x24, 0x1A, 0x0F, 0xB6, 0x44,
    0x24, 0x16, 0x0F, 0xB6, 0x4C, 0x24, 0x19, 0x88, 0x4C, 0x24, 0x16, 0x88, 0x44, 0x24, 0x19, 0x66,
    0xC1, 0x44, 0x24, 0x17, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8,
    0x62, 0x17, 0x00, 0x00]

theorem code_l101ccc_1 : ∀ x ∈ codeRange 0x101d2a bytes_l101ccc_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d2a 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101ccc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101ccc (movR64M64Effect 0x101ccc 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101ccc (LoadPre 0x101ccc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101ccc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ccc 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101cd1 (movR64M64Effect 0x101cd1 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101cd1 (LoadPre 0x101cd1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101cd1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101cd1 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101cd6 (StorePre 0x101cd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101cd6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101cd6 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x101cdb (StorePre 0x101cdb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101cdb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101cdb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x101ce0 (movzxR32M8Effect 0x101ce0 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x101ce0 (LoadPre 0x101ce0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101ce0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101ce0 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101ce5 (StorePre 0x101ce5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101ce5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ce5 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x101ce9 (StorePre 0x101ce9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101ce9 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ce9 4 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.out 0x101ced (movzxR32M16Effect 0x101ced 5 0 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x101ced (LoadPre 0x101ced (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101ced + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101ced 5 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x101cf2 (rolR16Effect 0x101cf2 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x101cf2 (fun s => s.RIP = 0x101cf2) (rolR16Effect 0x101cf2 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x101cf6 (movzxR32M16Effect 0x101cf6 5 1 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x101cf6 (LoadPre 0x101cf6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101cf6 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101cf6 5 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101cfb (rolR16Effect 0x101cfb 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x101cfb (fun s => s.RIP = 0x101cfb) (rolR16Effect 0x101cfb 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x101cff (movzxR32M16Effect 0x101cff 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x101cff (LoadPre 0x101cff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101cff + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101cff 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x101d04 (StorePre 0x101d04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101d04 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d04 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 74) (.out 0x101d09 (rolR16Effect 0x101d09 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 75) (.exec 0x101d09 (fun s => s.RIP = 0x101d09) (rolR16Effect 0x101d09 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 76) (.exec 0x101d0d (StorePre 0x101d0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101d0d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d0d 5 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 77) (.out 0x101d12 (movzxR32M16Effect 0x101d12 5 0 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x101d12 (LoadPre 0x101d12 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101d12 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101d12 5 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101d17 (rolR16Effect 0x101d17 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x101d17 (fun s => s.RIP = 0x101d17) (rolR16Effect 0x101d17 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x101d1b (StorePre 0x101d1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101d1b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d1b 5 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x101d20 (StorePre 0x101d20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101d20 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101d20 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 83) (.out 0x101d25 (movzxR32M8Effect 0x101d25 5 0 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x101d25 (LoadPre 0x101d25 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101d25 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101d25 5 0 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101ccc_1))))))))))))))))))))))))))))))))

def bytes_l101ccc : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0x88, 0x4C, 0x24, 0x10, 0x88, 0x44, 0x24,
    0x1F, 0x0F, 0xB7, 0x44, 0x24, 0x11, 0x66, 0xC1, 0xC0, 0x08, 0x0F, 0xB7, 0x4C, 0x24, 0x1D, 0x66,
    0xC1, 0xC1, 0x08, 0x0F, 0xB7, 0x54, 0x24, 0x13, 0x66, 0x89, 0x4C, 0x24, 0x11, 0x66, 0xC1, 0xC2,
    0x08, 0x66, 0x89, 0x44, 0x24, 0x1D, 0x0F, 0xB7, 0x44, 0x24, 0x1B, 0x66, 0xC1, 0xC0, 0x08, 0x66,
    0x89, 0x44, 0x24, 0x13, 0x66, 0x89, 0x54, 0x24, 0x1B, 0x0F, 0xB6, 0x44, 0x24, 0x15] ++ bytes_l101ccc_1

theorem code_l101ccc : ∀ x ∈ codeRange 0x101ccc bytes_l101ccc, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ccc 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101ccc_1

@[cfg_block] def b_l101d5e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d5e (movR64R64Effect 0x101d5e 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 54) (.exec 0x101d5e (fun s => s.RIP = 0x101d5e) (movR64R64Effect 0x101d5e 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x101d61 (shrR64Effect 0x101d61 4 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x101d61 (fun s => s.RIP = 0x101d61) (shrR64Effect 0x101d61 4 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x101d65 (leaR64Effect 0x101d65 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x101d65 (fun s => s.RIP = 0x101d65) (leaR64Effect 0x101d65 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x101d6a (movR64R64Effect 0x101d6a 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x101d6a (fun s => s.RIP = 0x101d6a) (movR64R64Effect 0x101d6a 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x101d6d (callEffect (fun _ => 0x109980) 0x101d72) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x101d6d (PushPre 0x101d6d 5) (callEffect (fun _ => 0x109980) 0x101d72) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x101d72⟩) #v[]
    (.terminate (.call ⟨.l109980, RegMap.args [(0, 0), (1, 1), (2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l101d72, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l101d5e : List UInt8 :=
  [0x4C, 0x89, 0xFA, 0x48, 0xC1, 0xEA, 0x04, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x4C, 0x89, 0xF6, 0xE8,
    0x0E, 0x7C, 0x00, 0x00]

theorem code_l101d5e : ∀ x ∈ codeRange 0x101d5e bytes_l101d5e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d5e 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d72 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d72 (movR64R64Effect 0x101d72 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[15]
    (.letOp (n := 54) (.exec 0x101d72 (fun s => s.RIP = 0x101d72) (movR64R64Effect 0x101d72 12 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x101d75 (andR64Imm8Effect 0x101d75 12 0xf) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[53]
    (.letOp (n := 56) (.out 0x101d75 (andR64Imm8Effect 0x101d75 12 0xf) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x101d75 (fun s => s.RIP = 0x101d75) (andR64Imm8Effect 0x101d75 12 0xf) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101e4a, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101d7f, RegMap.args [(3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101d72 : List UInt8 :=
  [0x4D, 0x89, 0xFC, 0x49, 0x83, 0xE4, 0x0F, 0x0F, 0x84, 0xCB, 0x00, 0x00, 0x00]

theorem code_l101d72 : ∀ x ∈ codeRange 0x101d72 bytes_l101d72, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d72 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101d7f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101d7f (movR64Imm64Effect 0x101d7f 0 0xffffffff0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x101d7f (fun s => s.RIP = 0x101d7f) (movR64Imm64Effect 0x101d7f 0 0xffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x101d89 (andR64R64Effect 0x101d89 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x101d89 (fun s => s.RIP = 0x101d89) (andR64R64Effect 0x101d89 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x101d8c (addR64R64Effect 0x101d8c 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 55]
    (.letOp (n := 58) (.exec 0x101d8c (fun s => s.RIP = 0x101d8c) (addR64R64Effect 0x101d8c 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 55]
    (.letOp (n := 59) (.out 0x101d8f (movR32Imm32Effect 0x101d8f 5 2 0x10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x101d8f (fun s => s.RIP = 0x101d8f) (movR32Imm32Effect 0x101d8f 5 2 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x101d94 (subR64R64Effect 0x101d94 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x101d94 (fun s => s.RIP = 0x101d94) (subR64R64Effect 0x101d94 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x101d97 (leaR64Effect 0x101d97 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 64) (.exec 0x101d97 (fun s => s.RIP = 0x101d97) (leaR64Effect 0x101d97 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 65) (.out 0x101d9b (addR64Imm8Effect 0x101d9b 7 0x40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x101d9b (fun s => s.RIP = 0x101d9b) (addR64Imm8Effect 0x101d9b 7 0x40) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x101d9f (xorR32R32Effect 0x101d9f 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x101d9f (fun s => s.RIP = 0x101d9f) (xorR32R32Effect 0x101d9f 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x101da1 (callEffect (callMemPtr 0x101da1 (.rip 0xff481)) (0x101da1 + BitVec.ofNat 64 (callMemLen (.rip 0xff481)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101da1 (GoesTo (CallMemPre 0x101da1 (.rip 0xff481)) (callEffect (callMemPtr 0x101da1 (.rip 0xff481)) (0x101da1 + BitVec.ofNat 64 (callMemLen (.rip 0xff481)))) 0x103eb0) (callEffect (callMemPtr 0x101da1 (.rip 0xff481)) (0x101da1 + BitVec.ofNat 64 (callMemLen (.rip 0xff481)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101da7⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 57), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101da7, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101d7f : List UInt8 :=
  [0x48, 0xB8, 0xF0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x21, 0xF8, 0x49, 0x01, 0xC6,
    0xBA, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xE2, 0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x83, 0xC7, 0x40,
    0x31, 0xF6, 0xFF, 0x15, 0x81, 0xF4, 0x0F, 0x00]

theorem code_l101d7f : ∀ x ∈ codeRange 0x101d7f bytes_l101d7f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1d7f 40 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101da7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101da7 (leaR64Effect 0x101da7 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x101da7 (fun s => s.RIP = 0x101da7) (leaR64Effect 0x101da7 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101dac (movR64R64Effect 0x101dac 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x101dac (fun s => s.RIP = 0x101dac) (movR64R64Effect 0x101dac 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x101daf (movR64R64Effect 0x101daf 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 58) (.exec 0x101daf (fun s => s.RIP = 0x101daf) (movR64R64Effect 0x101daf 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.out 0x101db2 (callEffect (callMemPtr 0x101db2 (.rip 0xff450)) (0x101db2 + BitVec.ofNat 64 (callMemLen (.rip 0xff450)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x101db2 (GoesTo (CallMemPre 0x101db2 (.rip 0xff450)) (callEffect (callMemPtr 0x101db2 (.rip 0xff450)) (0x101db2 + BitVec.ofNat 64 (callMemLen (.rip 0xff450)))) 0x103f00) (callEffect (callMemPtr 0x101db2 (.rip 0xff450)) (0x101db2 + BitVec.ofNat 64 (callMemLen (.rip 0xff450)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101db8⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101db8, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l101da7 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x40, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xE2, 0xFF, 0x15, 0x50, 0xF4, 0x0F,
    0x00]

theorem code_l101da7 : ∀ x ∈ codeRange 0x101da7 bytes_l101da7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1da7 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101db8_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x101e16 (movzxR32M8Effect 0x101e16 5 1 (.sib 4 none 0 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 86) (.exec 0x101e16 (LoadPre 0x101e16 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101e16 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e16 5 1 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.exec 0x101e1b (StorePre 0x101e1b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101e1b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e1b 4 1 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.exec 0x101e1f (StorePre 0x101e1f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101e1f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e1f 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[83, 4]
    (.letOp (n := 89) (.out 0x101e23 (movzxR32M8Effect 0x101e23 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 90) (.exec 0x101e23 (LoadPre 0x101e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101e23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e23 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 91) (.out 0x101e28 (movzxR32M8Effect 0x101e28 5 1 (.sib 4 none 0 (.d8 0x19))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 92) (.exec 0x101e28 (LoadPre 0x101e28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101e28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e28 5 1 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 93) (.exec 0x101e2d (StorePre 0x101e2d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101e2d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e2d 4 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.exec 0x101e31 (StorePre 0x101e31 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101e31 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e31 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 95) (.exec 0x101e35 (StorePre 0x101e35 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x101e35 + BitVec.ofNat 64 6)) 2) (rolMEffect 0x101e35 6 16 (.sib 4 none 0 (.d8 0x17)) 8) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [])) #v[4]
    (.letOp (n := 96) (.out 0x101e3b (leaR64Effect 0x101e3b 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 97) (.exec 0x101e3b (fun s => s.RIP = 0x101e3b) (leaR64Effect 0x101e3b 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 98) (.out 0x101e40 (leaR64Effect 0x101e40 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 99) (.exec 0x101e40 (fun s => s.RIP = 0x101e40) (leaR64Effect 0x101e40 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 100) (.out 0x101e45 (callEffect (fun _ => 0x1034c0) 0x101e4a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 101) (.exec 0x101e45 (PushPre 0x101e45 5) (callEffect (fun _ => 0x1034c0) 0x101e4a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 102) (.const ⟨64, 0x101e4a⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 89), (1, 91), (2, 74), (3, 3), (4, 100), (5, 5), (6, 98), (7, 96), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 103⟩ { target := .l101e4a, kept := #v[], arity := rfl, guard := some (Fin.last 102) })))))))))))))))))))

def bytes_l101db8_1 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1A, 0x88, 0x4C, 0x24, 0x15, 0x88, 0x44, 0x24, 0x1A, 0x0F, 0xB6, 0x44,
    0x24, 0x16, 0x0F, 0xB6, 0x4C, 0x24, 0x19, 0x88, 0x4C, 0x24, 0x16, 0x88, 0x44, 0x24, 0x19, 0x66,
    0xC1, 0x44, 0x24, 0x17, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x50, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8,
    0x76, 0x16, 0x00, 0x00]

theorem code_l101db8_1 : ∀ x ∈ codeRange 0x101e16 bytes_l101db8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1e16 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101db8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101db8 (movR64M64Effect 0x101db8 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101db8 (LoadPre 0x101db8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101db8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101db8 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101dbd (movR64M64Effect 0x101dbd 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101dbd (LoadPre 0x101dbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101dbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101dbd 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101dc2 (StorePre 0x101dc2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101dc2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101dc2 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x101dc7 (StorePre 0x101dc7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101dc7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101dc7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x101dcc (movzxR32M8Effect 0x101dcc 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x101dcc (LoadPre 0x101dcc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101dcc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101dcc 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101dd1 (StorePre 0x101dd1 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101dd1 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101dd1 4 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.exec 0x101dd5 (StorePre 0x101dd5 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101dd5 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101dd5 4 0 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.out 0x101dd9 (movzxR32M16Effect 0x101dd9 5 0 (.sib 4 none 0 (.d8 0x11))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x101dd9 (LoadPre 0x101dd9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101dd9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101dd9 5 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x101dde (rolR16Effect 0x101dde 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 66) (.exec 0x101dde (fun s => s.RIP = 0x101dde) (rolR16Effect 0x101dde 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x101de2 (movzxR32M16Effect 0x101de2 5 1 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x101de2 (LoadPre 0x101de2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101de2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101de2 5 1 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101de7 (rolR16Effect 0x101de7 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 70) (.exec 0x101de7 (fun s => s.RIP = 0x101de7) (rolR16Effect 0x101de7 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x101deb (movzxR32M16Effect 0x101deb 5 2 (.sib 4 none 0 (.d8 0x13))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x101deb (LoadPre 0x101deb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101deb + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101deb 5 2 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x101df0 (StorePre 0x101df0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101df0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101df0 5 1 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 74) (.out 0x101df5 (rolR16Effect 0x101df5 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 75) (.exec 0x101df5 (fun s => s.RIP = 0x101df5) (rolR16Effect 0x101df5 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 76) (.exec 0x101df9 (StorePre 0x101df9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101df9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101df9 5 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 77) (.out 0x101dfe (movzxR32M16Effect 0x101dfe 5 0 (.sib 4 none 0 (.d8 0x1b))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x101dfe (LoadPre 0x101dfe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101dfe + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x101dfe 5 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101e03 (rolR16Effect 0x101e03 4 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x101e03 (fun s => s.RIP = 0x101e03) (rolR16Effect 0x101e03 4 0 8) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x101e07 (StorePre 0x101e07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101e07 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101e07 5 0 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x101e0c (StorePre 0x101e0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101e0c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x101e0c 5 2 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 83) (.out 0x101e11 (movzxR32M8Effect 0x101e11 5 0 (.sib 4 none 0 (.d8 0x15))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 84) (.exec 0x101e11 (LoadPre 0x101e11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101e11 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101e11 5 0 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101db8_1))))))))))))))))))))))))))))))))

def bytes_l101db8 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0x88, 0x4C, 0x24, 0x10, 0x88, 0x44, 0x24,
    0x1F, 0x0F, 0xB7, 0x44, 0x24, 0x11, 0x66, 0xC1, 0xC0, 0x08, 0x0F, 0xB7, 0x4C, 0x24, 0x1D, 0x66,
    0xC1, 0xC1, 0x08, 0x0F, 0xB7, 0x54, 0x24, 0x13, 0x66, 0x89, 0x4C, 0x24, 0x11, 0x66, 0xC1, 0xC2,
    0x08, 0x66, 0x89, 0x44, 0x24, 0x1D, 0x0F, 0xB7, 0x44, 0x24, 0x1B, 0x66, 0xC1, 0xC0, 0x08, 0x66,
    0x89, 0x44, 0x24, 0x13, 0x66, 0x89, 0x54, 0x24, 0x1B, 0x0F, 0xB6, 0x44, 0x24, 0x15] ++ bytes_l101db8_1

theorem code_l101db8 : ∀ x ∈ codeRange 0x101db8 bytes_l101db8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1db8 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101db8_1

@[cfg_block] def b_l101e4a_2 : Block Op Label signature Reg.count 118 :=
  .letOp (n := 118) (.out 0x101ee1 (leaR64Effect 0x101ee1 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 119) (.exec 0x101ee1 (fun s => s.RIP = 0x101ee1) (leaR64Effect 0x101ee1 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 120) (.out 0x101ee6 (callEffect (fun _ => 0x1034c0) 0x101eeb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 121) (.exec 0x101ee6 (PushPre 0x101ee6 5) (callEffect (fun _ => 0x1034c0) 0x101eeb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.const ⟨64, 0x101eeb⟩) #v[]
    (.terminate (.call ⟨.l1034c0, RegMap.args [(0, 109), (1, 89), (3, 113), (4, 120), (5, 5), (6, 118), (7, 116), (12, 12), (13, 13), (14, 14), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 123⟩ { target := .l101eeb, kept := #v[], arity := rfl, guard := some (Fin.last 122) }))))))

def bytes_l101e4a_2 : List UInt8 :=
  [0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8, 0xD5, 0x15, 0x00, 0x00]

theorem code_l101e4a_2 : ∀ x ∈ codeRange 0x101ee1 bytes_l101e4a_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ee1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101e4a_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x101e8f (movR64R64Effect 0x101e8f 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 88) (.exec 0x101e8f (fun s => s.RIP = 0x101e8f) (movR64R64Effect 0x101e8f 1 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 89) (.out 0x101e92 (shrR64Effect 0x101e92 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x101e92 (fun s => s.RIP = 0x101e92) (shrR64Effect 0x101e92 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.exec 0x101e96 (StorePre 0x101e96 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x101e96 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e96 4 1 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 92) (.exec 0x101e9a (StorePre 0x101e9a 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x101e9a + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e9a 4 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 93) (.out 0x101e9e (movR64R64Effect 0x101e9e 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 94) (.exec 0x101e9e (fun s => s.RIP = 0x101e9e) (movR64R64Effect 0x101e9e 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 95) (.out 0x101ea1 (shrR64Effect 0x101ea1 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[93]
    (.letOp (n := 96) (.exec 0x101ea1 (fun s => s.RIP = 0x101ea1) (shrR64Effect 0x101ea1 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x101ea5 (shrR32Effect 0x101ea5 4 15 24) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[59]
    (.letOp (n := 98) (.exec 0x101ea5 (fun s => s.RIP = 0x101ea5) (shrR32Effect 0x101ea5 4 15 24) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 99) (.exec 0x101ea9 (StorePre 0x101ea9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x101ea9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x101ea9 5 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[97, 4]
    (.letOp (n := 100) (.exec 0x101eae (StorePre 0x101eae 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x101eae + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101eae 4 0 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 101) (.out 0x101eb2 (movR64R64Effect 0x101eb2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 102) (.exec 0x101eb2 (fun s => s.RIP = 0x101eb2) (movR64R64Effect 0x101eb2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 103) (.out 0x101eb5 (shrR64Effect 0x101eb5 4 0 40) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 104) (.exec 0x101eb5 (fun s => s.RIP = 0x101eb5) (shrR64Effect 0x101eb5 4 0 40) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.exec 0x101eb9 (StorePre 0x101eb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x101eb9 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x101eb9 (.sib 4 none 0 (.d8 0x15)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.exec 0x101ebe (StorePre 0x101ebe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x101ebe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ebe 4 0 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[103, 4]
    (.letOp (n := 107) (.out 0x101ec2 (movR64R64Effect 0x101ec2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 108) (.exec 0x101ec2 (fun s => s.RIP = 0x101ec2) (movR64R64Effect 0x101ec2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 109) (.out 0x101ec5 (shrR64Effect 0x101ec5 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[107]
    (.letOp (n := 110) (.exec 0x101ec5 (fun s => s.RIP = 0x101ec5) (shrR64Effect 0x101ec5 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 111) (.exec 0x101ec9 (StorePre 0x101ec9 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x101ec9 + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x101ec9 (.sib 4 none 0 (.d8 0x16)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.exec 0x101ed0 (StorePre 0x101ed0 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x101ed0 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ed0 4 0 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[109, 4]
    (.letOp (n := 113) (.out 0x101ed4 (shrR64Effect 0x101ed4 4 3 56) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 114) (.exec 0x101ed4 (fun s => s.RIP = 0x101ed4) (shrR64Effect 0x101ed4 4 3 56) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 115) (.exec 0x101ed8 (StorePre 0x101ed8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101ed8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ed8 4 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x101edc (leaR64Effect 0x101edc 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 117) (.exec 0x101edc (fun s => s.RIP = 0x101edc) (leaR64Effect 0x101edc 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101e4a_2)))))))))))))))))))))))))))))))

def bytes_l101e4a_1 : List UInt8 :=
  [0x4C, 0x89, 0xF9, 0x48, 0xC1, 0xE9, 0x20, 0x88, 0x4C, 0x24, 0x13, 0x88, 0x44, 0x24, 0x1C, 0x48,
    0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x20, 0x41, 0xC1, 0xEF, 0x18, 0x44, 0x88, 0x7C, 0x24, 0x14, 0x88,
    0x44, 0x24, 0x1B, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x28, 0xC6, 0x44, 0x24, 0x15, 0x00, 0x88,
    0x44, 0x24, 0x1A, 0x48, 0x89, 0xD8, 0x48, 0xC1, 0xE8, 0x30, 0x66, 0xC7, 0x44, 0x24, 0x16, 0x00,
    0x00, 0x88, 0x44, 0x24, 0x19, 0x48, 0xC1, 0xEB, 0x38, 0x88, 0x5C, 0x24, 0x18, 0x48, 0x8D, 0x7C,
    0x24, 0x50] ++ bytes_l101e4a_2

theorem code_l101e4a_1 : ∀ x ∈ codeRange 0x101e8f bytes_l101e4a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e8f 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101e4a_2

@[cfg_block] def b_l101e4a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101e4a (shlR64Effect 0x101e4a 4 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 54) (.exec 0x101e4a (fun s => s.RIP = 0x101e4a) (shlR64Effect 0x101e4a 4 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 55) (.out 0x101e4e (shlR64Effect 0x101e4e 4 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x101e4e (fun s => s.RIP = 0x101e4e) (shlR64Effect 0x101e4e 4 15 3) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 57) (.out 0x101e52 (bswapR64Effect 0x101e52 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 58) (.exec 0x101e52 (fun s => s.RIP = 0x101e52) (bswapR64Effect 0x101e52 3 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x101e55 (bswapR64Effect 0x101e55 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 60) (.exec 0x101e55 (fun s => s.RIP = 0x101e55) (bswapR64Effect 0x101e55 3 15) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 61) (.out 0x101e58 (movR64R64Effect 0x101e58 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x101e58 (fun s => s.RIP = 0x101e58) (movR64R64Effect 0x101e58 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 63) (.out 0x101e5b (shrR64Effect 0x101e5b 4 0 56) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x101e5b (fun s => s.RIP = 0x101e5b) (shrR64Effect 0x101e5b 4 0 56) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x101e5f (StorePre 0x101e5f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101e5f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e5f 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x101e63 (StorePre 0x101e63 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x101e63 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e63 4 3 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 67) (.out 0x101e67 (movR64R64Effect 0x101e67 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 68) (.exec 0x101e67 (fun s => s.RIP = 0x101e67) (movR64R64Effect 0x101e67 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 69) (.out 0x101e6a (shrR64Effect 0x101e6a 4 0 48) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x101e6a (fun s => s.RIP = 0x101e6a) (shrR64Effect 0x101e6a 4 0 48) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.exec 0x101e6e (StorePre 0x101e6e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x101e6e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e6e 4 0 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.exec 0x101e72 (StorePre 0x101e72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x101e72 + BitVec.ofNat 64 4)) 1) (movM8R8NoRexEffect 0x101e72 4 7 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 73) (.out 0x101e76 (movR32R32Effect 0x101e76 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 74) (.exec 0x101e76 (fun s => s.RIP = 0x101e76) (movR32R32Effect 0x101e76 2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 75) (.out 0x101e78 (shrR32Effect 0x101e78 3 0 16) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x101e78 (fun s => s.RIP = 0x101e78) (shrR32Effect 0x101e78 3 0 16) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x101e7b (movR64R64Effect 0x101e7b 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 78) (.exec 0x101e7b (fun s => s.RIP = 0x101e7b) (movR64R64Effect 0x101e7b 1 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 79) (.out 0x101e7e (shrR64Effect 0x101e7e 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 80) (.exec 0x101e7e (fun s => s.RIP = 0x101e7e) (shrR64Effect 0x101e7e 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.exec 0x101e82 (StorePre 0x101e82 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x101e82 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e82 4 1 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[79, 4]
    (.letOp (n := 82) (.exec 0x101e86 (StorePre 0x101e86 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x101e86 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101e86 4 0 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 83) (.out 0x101e8a (movR32R32Effect 0x101e8a 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 84) (.exec 0x101e8a (fun s => s.RIP = 0x101e8a) (movR32R32Effect 0x101e8a 2 0 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 85) (.out 0x101e8c (shrR32Effect 0x101e8c 3 0 24) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x101e8c (fun s => s.RIP = 0x101e8c) (shrR32Effect 0x101e8c 3 0 24) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (b_l101e4a_1))))))))))))))))))))))))))))))))))

def bytes_l101e4a : List UInt8 :=
  [0x48, 0xC1, 0xE3, 0x03, 0x49, 0xC1, 0xE7, 0x03, 0x48, 0x0F, 0xCB, 0x49, 0x0F, 0xCF, 0x4C, 0x89,
    0xF8, 0x48, 0xC1, 0xE8, 0x38, 0x88, 0x44, 0x24, 0x10, 0x88, 0x5C, 0x24, 0x1F, 0x4C, 0x89, 0xF8,
    0x48, 0xC1, 0xE8, 0x30, 0x88, 0x44, 0x24, 0x11, 0x88, 0x7C, 0x24, 0x1E, 0x89, 0xD8, 0xC1, 0xE8,
    0x10, 0x4C, 0x89, 0xF9, 0x48, 0xC1, 0xE9, 0x28, 0x88, 0x4C, 0x24, 0x12, 0x88, 0x44, 0x24, 0x1D,
    0x89, 0xD8, 0xC1, 0xE8, 0x18] ++ bytes_l101e4a_1

theorem code_l101e4a : ∀ x ∈ codeRange 0x101e4a bytes_l101e4a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1e4a 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101e4a_1

@[cfg_block] def b_l101eeb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101eeb (movR64M64Effect 0x101eeb 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101eeb (LoadPre 0x101eeb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101eeb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101eeb 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x101ef0 (StorePre 0x101ef0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101ef0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101ef0 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x101ef5 (movR64M64Effect 0x101ef5 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x101ef5 (LoadPre 0x101ef5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x101ef5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101ef5 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101efa (StorePre 0x101efa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101efa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101efa 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x101eff (movR64M64Effect 0x101eff 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101eff (LoadPre 0x101eff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101eff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101eff 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x101f04 (movR64M64Effect 0x101f04 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x101f04 (LoadPre 0x101f04 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101f04 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101f04 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x101f09 (StorePre 0x101f09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101f09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101f09 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x101f0e (StorePre 0x101f0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101f0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101f0e 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x101f13 (leaR64Effect 0x101f13 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x101f13 (fun s => s.RIP = 0x101f13) (leaR64Effect 0x101f13 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x101f18 (leaR64Effect 0x101f18 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x101f18 (fun s => s.RIP = 0x101f18) (leaR64Effect 0x101f18 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101f1d (callEffect (fun _ => 0x1034a0) 0x101f22) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x101f1d (PushPre 0x101f1d 5) (callEffect (fun _ => 0x1034a0) 0x101f22) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x101f22⟩) #v[]
    (.terminate (.call ⟨.l1034a0, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l101f22, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l101eeb : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x60, 0x48,
    0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x48, 0x89,
    0x4C, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8D, 0x7C, 0x24, 0x40, 0x48, 0x8D, 0x74,
    0x24, 0x10, 0xE8, 0x7E, 0x15, 0x00, 0x00]

theorem code_l101eeb : ∀ x ∈ codeRange 0x101eeb bytes_l101eeb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1eeb 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101f22_3 : Block Op Label signature Reg.count 154 :=
  .letOp (n := 154) (.out 0x102028 (popR64Effect 0x102028 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[152]
    (.letOp (n := 155) (.out 0x102028 (popR64Effect 0x102028 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[152]
    (.letOp (n := 156) (.exec 0x102028 (PopPre 0x102028) (popR64Effect 0x102028 2 12) (Reg.operands [.gpr 4] [])) #v[152]
    (.letOp (n := 157) (.out 0x10202a (popR64Effect 0x10202a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[155]
    (.letOp (n := 158) (.out 0x10202a (popR64Effect 0x10202a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[155]
    (.letOp (n := 159) (.exec 0x10202a (PopPre 0x10202a) (popR64Effect 0x10202a 2 13) (Reg.operands [.gpr 4] [])) #v[155]
    (.letOp (n := 160) (.out 0x10202c (popR64Effect 0x10202c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[158]
    (.letOp (n := 161) (.out 0x10202c (popR64Effect 0x10202c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[158]
    (.letOp (n := 162) (.exec 0x10202c (PopPre 0x10202c) (popR64Effect 0x10202c 2 14) (Reg.operands [.gpr 4] [])) #v[158]
    (.letOp (n := 163) (.out 0x10202e (popR64Effect 0x10202e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[161]
    (.letOp (n := 164) (.out 0x10202e (popR64Effect 0x10202e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[161]
    (.letOp (n := 165) (.exec 0x10202e (PopPre 0x10202e) (popR64Effect 0x10202e 2 15) (Reg.operands [.gpr 4] [])) #v[161]
    (.letOp (n := 166) (.out 0x102030 (popR64Effect 0x102030 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[164]
    (.letOp (n := 167) (.out 0x102030 (popR64Effect 0x102030 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[164]
    (.letOp (n := 168) (.exec 0x102030 (PopPre 0x102030) (popR64Effect 0x102030 1 5) (Reg.operands [.gpr 4] [])) #v[164]
    (.letOp (n := 169) (.out 0x102031 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[167]
    (.letOp (n := 170) (.out 0x102031 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[167]
    (.letOp (n := 171) (.exec 0x102031 (RetPre 0x102031) (retEffect) (Reg.operands [.gpr 4] [])) #v[167]
    (.terminate (.ret (RegMap.args [(0, 127), (1, 125), (2, 145), (3, 151), (4, 170), (5, 166), (6, 141), (7, 111), (8, 89), (9, 109), (10, 91), (11, 93), (12, 154), (13, 157), (14, 160), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)] 172) (some ⟨169, by decide⟩))))))))))))))))))))

def bytes_l101f22_3 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101f22_3 : ∀ x ∈ codeRange 0x102028 bytes_l101f22_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2028 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101f22_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.exec 0x101fdb (StorePre 0x101fdb 3 (fun s => AddrMode.addr (.base 0 .none) s (0x101fdb + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101fdb 3 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[89, 127]
    (.letOp (n := 130) (.exec 0x101fde (StorePre 0x101fde 4 (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101fde + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fde 4 10 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[91, 127]
    (.letOp (n := 131) (.exec 0x101fe2 (StorePre 0x101fe2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101fe2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fe2 4 11 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[93, 127]
    (.letOp (n := 132) (.exec 0x101fe6 (StorePre 0x101fe6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101fe6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fe6 4 15 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[95, 127]
    (.letOp (n := 133) (.exec 0x101fea (StorePre 0x101fea 4 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101fea + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fea 4 12 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[97, 127]
    (.letOp (n := 134) (.exec 0x101fee (StorePre 0x101fee 4 (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101fee + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fee 4 13 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[99, 127]
    (.letOp (n := 135) (.exec 0x101ff2 (StorePre 0x101ff2 4 (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101ff2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ff2 4 5 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[101, 127]
    (.letOp (n := 136) (.exec 0x101ff6 (StorePre 0x101ff6 4 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101ff6 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ff6 4 14 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[103, 127]
    (.letOp (n := 137) (.exec 0x101ffa (StorePre 0x101ffa 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101ffa + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101ffa 4 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[105, 127]
    (.letOp (n := 138) (.exec 0x101ffe (StorePre 0x101ffe 3 (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101ffe + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x101ffe 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[107, 127]
    (.letOp (n := 139) (.exec 0x102001 (StorePre 0x102001 4 (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x102001 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102001 4 9 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[109, 127]
    (.letOp (n := 140) (.exec 0x102005 (StorePre 0x102005 4 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x102005 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102005 4 7 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[111, 127]
    (.letOp (n := 141) (.out 0x102009 (movzxR32M8Effect 0x102009 5 6 (.sib 4 none 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 142) (.exec 0x102009 (LoadPre 0x102009 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x102009 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102009 5 6 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.exec 0x10200e (StorePre 0x10200e 4 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x10200e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10200e 4 6 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[141, 127]
    (.letOp (n := 144) (.exec 0x102012 (StorePre 0x102012 3 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x102012 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x102012 3 2 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[118, 127]
    (.letOp (n := 145) (.out 0x102015 (movzxR32M8Effect 0x102015 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 146) (.exec 0x102015 (LoadPre 0x102015 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x102015 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102015 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 147) (.exec 0x10201a (StorePre 0x10201a 3 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x10201a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10201a 3 2 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[145, 127]
    (.letOp (n := 148) (.exec 0x10201d (StorePre 0x10201d 3 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x10201d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10201d 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[125, 127]
    (.letOp (n := 149) (.out 0x102020 (addR64Imm32Effect 0x102020 4 0x88) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 150) (.exec 0x102020 (fun s => s.RIP = 0x102020) (addR64Imm32Effect 0x102020 4 0x88) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 151) (.out 0x102027 (popR64Effect 0x102027 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[149]
    (.letOp (n := 152) (.out 0x102027 (popR64Effect 0x102027 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[149]
    (.letOp (n := 153) (.exec 0x102027 (PopPre 0x102027) (popR64Effect 0x102027 1 3) (Reg.operands [.gpr 4] [])) #v[149]
    (b_l101f22_3)))))))))))))))))))))))))

def bytes_l101f22_2 : List UInt8 :=
  [0x44, 0x88, 0x00, 0x44, 0x88, 0x50, 0x01, 0x44, 0x88, 0x58, 0x02, 0x44, 0x88, 0x78, 0x03, 0x44,
    0x88, 0x60, 0x04, 0x44, 0x88, 0x68, 0x05, 0x40, 0x88, 0x68, 0x06, 0x44, 0x88, 0x70, 0x07, 0x40,
    0x88, 0x70, 0x08, 0x88, 0x58, 0x09, 0x44, 0x88, 0x48, 0x0A, 0x40, 0x88, 0x78, 0x0B, 0x0F, 0xB6,
    0x74, 0x24, 0x3E, 0x40, 0x88, 0x70, 0x0C, 0x88, 0x50, 0x0D, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x88,
    0x50, 0x0E, 0x88, 0x48, 0x0F, 0x48, 0x81, 0xC4, 0x88, 0x00, 0x00, 0x00, 0x5B] ++ bytes_l101f22_3

theorem code_l101f22_2 : ∀ x ∈ codeRange 0x101fdb bytes_l101f22_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1fdb 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101f22_3

@[cfg_block] def b_l101f22_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x101f8a (xorR8M8Effect 0x101f8a 4 10 (.base 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[60, 87]
    (.letOp (n := 92) (.exec 0x101f8a (LoadPre 0x101f8a (fun s => AddrMode.addr (.base 0 (.d8 0x1)) s (0x101f8a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f8a 4 10 (.base 0 (.d8 0x1))) (Reg.operands [.gpr 10, .gpr 0] [])) #v[60, 87]
    (.letOp (n := 93) (.out 0x101f8e (xorR8M8Effect 0x101f8e 4 11 (.base 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[65, 87]
    (.letOp (n := 94) (.exec 0x101f8e (LoadPre 0x101f8e (fun s => AddrMode.addr (.base 0 (.d8 0x2)) s (0x101f8e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f8e 4 11 (.base 0 (.d8 0x2))) (Reg.operands [.gpr 11, .gpr 0] [])) #v[65, 87]
    (.letOp (n := 95) (.out 0x101f92 (xorR8M8Effect 0x101f92 4 15 (.base 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[69, 87]
    (.letOp (n := 96) (.exec 0x101f92 (LoadPre 0x101f92 (fun s => AddrMode.addr (.base 0 (.d8 0x3)) s (0x101f92 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f92 4 15 (.base 0 (.d8 0x3))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[69, 87]
    (.letOp (n := 97) (.out 0x101f96 (xorR8M8Effect 0x101f96 4 12 (.base 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[73, 87]
    (.letOp (n := 98) (.exec 0x101f96 (LoadPre 0x101f96 (fun s => AddrMode.addr (.base 0 (.d8 0x4)) s (0x101f96 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f96 4 12 (.base 0 (.d8 0x4))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[73, 87]
    (.letOp (n := 99) (.out 0x101f9a (xorR8M8Effect 0x101f9a 4 13 (.base 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[77, 87]
    (.letOp (n := 100) (.exec 0x101f9a (LoadPre 0x101f9a (fun s => AddrMode.addr (.base 0 (.d8 0x5)) s (0x101f9a + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f9a 4 13 (.base 0 (.d8 0x5))) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 87]
    (.letOp (n := 101) (.out 0x101f9e (xorR8M8Effect 0x101f9e 4 5 (.base 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[81, 87]
    (.letOp (n := 102) (.exec 0x101f9e (LoadPre 0x101f9e (fun s => AddrMode.addr (.base 0 (.d8 0x6)) s (0x101f9e + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101f9e 4 5 (.base 0 (.d8 0x6))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[81, 87]
    (.letOp (n := 103) (.out 0x101fa2 (xorR8M8Effect 0x101fa2 4 14 (.base 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[85, 87]
    (.letOp (n := 104) (.exec 0x101fa2 (LoadPre 0x101fa2 (fun s => AddrMode.addr (.base 0 (.d8 0x7)) s (0x101fa2 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fa2 4 14 (.base 0 (.d8 0x7))) (Reg.operands [.gpr 14, .gpr 0] [])) #v[85, 87]
    (.letOp (n := 105) (.out 0x101fa6 (xorR8M8Effect 0x101fa6 4 6 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[83, 87]
    (.letOp (n := 106) (.exec 0x101fa6 (LoadPre 0x101fa6 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x101fa6 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fa6 4 6 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[83, 87]
    (.letOp (n := 107) (.out 0x101faa (xorR8M8Effect 0x101faa 3 3 (.base 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[79, 87]
    (.letOp (n := 108) (.exec 0x101faa (LoadPre 0x101faa (fun s => AddrMode.addr (.base 0 (.d8 0x9)) s (0x101faa + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101faa 3 3 (.base 0 (.d8 0x9))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[79, 87]
    (.letOp (n := 109) (.out 0x101fad (xorR8M8Effect 0x101fad 4 9 (.base 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[75, 87]
    (.letOp (n := 110) (.exec 0x101fad (LoadPre 0x101fad (fun s => AddrMode.addr (.base 0 (.d8 0xa)) s (0x101fad + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fad 4 9 (.base 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[75, 87]
    (.letOp (n := 111) (.out 0x101fb1 (xorR8M8Effect 0x101fb1 4 7 (.base 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[71, 87]
    (.letOp (n := 112) (.exec 0x101fb1 (LoadPre 0x101fb1 (fun s => AddrMode.addr (.base 0 (.d8 0xb)) s (0x101fb1 + BitVec.ofNat 64 4)) 1) (xorR8M8Effect 0x101fb1 4 7 (.base 0 (.d8 0xb))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[71, 87]
    (.letOp (n := 113) (.out 0x101fb5 (xorR8M8Effect 0x101fb5 3 2 (.base 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[67, 87]
    (.letOp (n := 114) (.exec 0x101fb5 (LoadPre 0x101fb5 (fun s => AddrMode.addr (.base 0 (.d8 0xc)) s (0x101fb5 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fb5 3 2 (.base 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[67, 87]
    (.letOp (n := 115) (.exec 0x101fb8 (StorePre 0x101fb8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x101fb8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fb8 4 2 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x101fbc (movzxR32M8Effect 0x101fbc 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 117) (.exec 0x101fbc (LoadPre 0x101fbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101fbc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101fbc 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x101fc1 (xorR8M8Effect 0x101fc1 3 2 (.base 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[116, 87]
    (.letOp (n := 119) (.exec 0x101fc1 (LoadPre 0x101fc1 (fun s => AddrMode.addr (.base 0 (.d8 0xd)) s (0x101fc1 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fc1 3 2 (.base 0 (.d8 0xd))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[116, 87]
    (.letOp (n := 120) (.out 0x101fc4 (xorR8M8Effect 0x101fc4 3 1 (.base 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[58, 87]
    (.letOp (n := 121) (.exec 0x101fc4 (LoadPre 0x101fc4 (fun s => AddrMode.addr (.base 0 (.d8 0xe)) s (0x101fc4 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fc4 3 1 (.base 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[58, 87]
    (.letOp (n := 122) (.exec 0x101fc7 (StorePre 0x101fc7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101fc7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101fc7 4 1 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[120, 4]
    (.letOp (n := 123) (.out 0x101fcb (movzxR32M8Effect 0x101fcb 5 1 (.sib 4 none 0 (.d8 0x3f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 124) (.exec 0x101fcb (LoadPre 0x101fcb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101fcb + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101fcb 5 1 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 125) (.out 0x101fd0 (xorR8M8Effect 0x101fd0 3 1 (.base 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[123, 87]
    (.letOp (n := 126) (.exec 0x101fd0 (LoadPre 0x101fd0 (fun s => AddrMode.addr (.base 0 (.d8 0xf)) s (0x101fd0 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101fd0 3 1 (.base 0 (.d8 0xf))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[123, 87]
    (.letOp (n := 127) (.out 0x101fd3 (movR64M64Effect 0x101fd3 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 128) (.exec 0x101fd3 (LoadPre 0x101fd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101fd3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101fd3 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101f22_2))))))))))))))))))))))))))))))))))))))

def bytes_l101f22_1 : List UInt8 :=
  [0x44, 0x32, 0x50, 0x01, 0x44, 0x32, 0x58, 0x02, 0x44, 0x32, 0x78, 0x03, 0x44, 0x32, 0x60, 0x04,
    0x44, 0x32, 0x68, 0x05, 0x40, 0x32, 0x68, 0x06, 0x44, 0x32, 0x70, 0x07, 0x40, 0x32, 0x70, 0x08,
    0x32, 0x58, 0x09, 0x44, 0x32, 0x48, 0x0A, 0x40, 0x32, 0x78, 0x0B, 0x32, 0x50, 0x0C, 0x88, 0x54,
    0x24, 0x3E, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0x32, 0x50, 0x0D, 0x32, 0x48, 0x0E, 0x88, 0x4C, 0x24,
    0x0F, 0x0F, 0xB6, 0x4C, 0x24, 0x3F, 0x32, 0x48, 0x0F, 0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00,
    0x00] ++ bytes_l101f22_2

theorem code_l101f22_1 : ∀ x ∈ codeRange 0x101f8a bytes_l101f22_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f8a 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101f22_2

@[cfg_block] def b_l101f22 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101f22 (movzxR32M8Effect 0x101f22 6 8 (.sib 4 none 0 (.d8 0x4f))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 54) (.exec 0x101f22 (LoadPre 0x101f22 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4f)) s (0x101f22 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f22 6 8 (.sib 4 none 0 (.d8 0x4f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101f28 (movzxR32M8Effect 0x101f28 5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x101f28 (LoadPre 0x101f28 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101f28 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f28 5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x101f2d (StorePre 0x101f2d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3f)) s (0x101f2d + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101f2d 4 0 (.sib 4 none 0 (.d8 0x3f))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x101f31 (movzxR32M8Effect 0x101f31 5 1 (.sib 4 none 0 (.d8 0x41))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x101f31 (LoadPre 0x101f31 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x41)) s (0x101f31 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f31 5 1 (.sib 4 none 0 (.d8 0x41))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x101f36 (movzxR32M8Effect 0x101f36 6 10 (.sib 4 none 0 (.d8 0x4e))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x101f36 (LoadPre 0x101f36 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x101f36 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f36 6 10 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x101f3c (movzxR32M8Effect 0x101f3c 5 0 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x101f3c (LoadPre 0x101f3c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x101f3c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f3c 5 0 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x101f41 (StorePre 0x101f41 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x101f41 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x101f41 4 0 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x101f45 (movzxR32M8Effect 0x101f45 6 11 (.sib 4 none 0 (.d8 0x4d))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 66) (.exec 0x101f45 (LoadPre 0x101f45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4d)) s (0x101f45 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f45 6 11 (.sib 4 none 0 (.d8 0x4d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x101f4b (movzxR32M8Effect 0x101f4b 5 2 (.sib 4 none 0 (.d8 0x43))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x101f4b (LoadPre 0x101f4b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x43)) s (0x101f4b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f4b 5 2 (.sib 4 none 0 (.d8 0x43))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x101f50 (movzxR32M8Effect 0x101f50 6 15 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 70) (.exec 0x101f50 (LoadPre 0x101f50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x101f50 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f50 6 15 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x101f56 (movzxR32M8Effect 0x101f56 5 7 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 72) (.exec 0x101f56 (LoadPre 0x101f56 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x101f56 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f56 5 7 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x101f5b (movzxR32M8Effect 0x101f5b 6 12 (.sib 4 none 0 (.d8 0x4b))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 74) (.exec 0x101f5b (LoadPre 0x101f5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4b)) s (0x101f5b + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f5b 6 12 (.sib 4 none 0 (.d8 0x4b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x101f61 (movzxR32M8Effect 0x101f61 6 9 (.sib 4 none 0 (.d8 0x45))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 76) (.exec 0x101f61 (LoadPre 0x101f61 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x45)) s (0x101f61 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f61 6 9 (.sib 4 none 0 (.d8 0x45))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x101f67 (movzxR32M8Effect 0x101f67 6 13 (.sib 4 none 0 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 78) (.exec 0x101f67 (LoadPre 0x101f67 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x101f67 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f67 6 13 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x101f6d (movzxR32M8Effect 0x101f6d 5 3 (.sib 4 none 0 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 80) (.exec 0x101f6d (LoadPre 0x101f6d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x101f6d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f6d 5 3 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x101f72 (movzxR32M8Effect 0x101f72 5 5 (.sib 4 none 0 (.d8 0x49))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 82) (.exec 0x101f72 (LoadPre 0x101f72 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x49)) s (0x101f72 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f72 5 5 (.sib 4 none 0 (.d8 0x49))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x101f77 (movzxR32M8Effect 0x101f77 5 6 (.sib 4 none 0 (.d8 0x47))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x101f77 (LoadPre 0x101f77 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x47)) s (0x101f77 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101f77 5 6 (.sib 4 none 0 (.d8 0x47))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x101f7c (movzxR32M8Effect 0x101f7c 6 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 86) (.exec 0x101f7c (LoadPre 0x101f7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101f7c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x101f7c 6 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x101f82 (movR64M64Effect 0x101f82 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x101f82 (LoadPre 0x101f82 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101f82 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101f82 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x101f87 (xorR8M8Effect 0x101f87 3 8 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[53, 87]
    (.letOp (n := 90) (.exec 0x101f87 (LoadPre 0x101f87 (fun s => AddrMode.addr (.base 0 .none) s (0x101f87 + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x101f87 3 8 (.base 0 .none)) (Reg.operands [.gpr 8, .gpr 0] [])) #v[53, 87]
    (b_l101f22_1))))))))))))))))))))))))))))))))))))))

def bytes_l101f22 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0x44, 0x24, 0x4F, 0x0F, 0xB6, 0x44, 0x24, 0x40, 0x88, 0x44, 0x24, 0x3F, 0x0F,
    0xB6, 0x4C, 0x24, 0x41, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x4E, 0x0F, 0xB6, 0x44, 0x24, 0x42, 0x88,
    0x44, 0x24, 0x0F, 0x44, 0x0F, 0xB6, 0x5C, 0x24, 0x4D, 0x0F, 0xB6, 0x54, 0x24, 0x43, 0x44, 0x0F,
    0xB6, 0x7C, 0x24, 0x4C, 0x0F, 0xB6, 0x7C, 0x24, 0x44, 0x44, 0x0F, 0xB6, 0x64, 0x24, 0x4B, 0x44,
    0x0F, 0xB6, 0x4C, 0x24, 0x45, 0x44, 0x0F, 0xB6, 0x6C, 0x24, 0x4A, 0x0F, 0xB6, 0x5C, 0x24, 0x46,
    0x0F, 0xB6, 0x6C, 0x24, 0x49, 0x0F, 0xB6, 0x74, 0x24, 0x47, 0x44, 0x0F, 0xB6, 0x74, 0x24, 0x48,
    0x48, 0x8B, 0x44, 0x24, 0x78, 0x44, 0x32, 0x00] ++ bytes_l101f22_1

theorem code_l101f22 : ∀ x ∈ codeRange 0x101f22 bytes_l101f22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1f22 104 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101f22_1

@[cfg_block] def b_l102040 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102040 (pushR64Effect 0x102040 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x102040 (PushPre 0x102040 2) (pushR64Effect 0x102040 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x102042 (pushR64Effect 0x102042 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x102042 (PushPre 0x102042 1) (pushR64Effect 0x102042 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x102043 (subR64Imm8Effect 0x102043 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x102043 (fun s => s.RIP = 0x102043) (subR64Imm8Effect 0x102043 4 0x28) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x102047 (movR64R64Effect 0x102047 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 60) (.exec 0x102047 (fun s => s.RIP = 0x102047) (movR64R64Effect 0x102047 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x10204a (movR64R64Effect 0x10204a 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x10204a (fun s => s.RIP = 0x10204a) (movR64R64Effect 0x10204a 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.exec 0x10204d (StorePre 0x10204d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10204d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10204d (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 64) (.exec 0x102056 (StorePre 0x102056 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102056 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102056 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 65) (.out 0x10205f (movR64R64Effect 0x10205f 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 66) (.exec 0x10205f (fun s => s.RIP = 0x10205f) (movR64R64Effect 0x10205f 7 4) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 67) (.out 0x102062 (leaR64Effect 0x102062 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 68) (.exec 0x102062 (fun s => s.RIP = 0x102062) (leaR64Effect 0x102062 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 69) (.out 0x102067 (callEffect (fun _ => 0x105100) 0x10206c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 70) (.exec 0x102067 (PushPre 0x102067 5) (callEffect (fun _ => 0x105100) 0x10206c) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 71) (.const ⟨64, 0x10206c⟩) #v[]
    (.terminate (.call ⟨.l105100, RegMap.args [(2, 67), (3, 61), (4, 69), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l10206c, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l102040 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0xC7, 0x44,
    0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xE7, 0x48, 0x8D, 0x54, 0x24, 0x18, 0xE8, 0x94, 0x30, 0x00, 0x00]

theorem code_l102040 : ∀ x ∈ codeRange 0x102040 bytes_l102040, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2040 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10206c_3 : Block Op Label signature Reg.count 171 :=
  .letOp (n := 171) (.out 0x102157 (callEffect (fun _ => 0x102b80) 0x10215c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 172) (.exec 0x102157 (PushPre 0x102157 5) (callEffect (fun _ => 0x102b80) 0x10215c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 173) (.const ⟨64, 0x10215c⟩) #v[]
    (.terminate (.call ⟨.l102b80, RegMap.args [(0, 163), (1, 143), (2, 157), (3, 3), (4, 171), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 174⟩ { target := .l10215c, kept := #v[], arity := rfl, guard := some (Fin.last 173) }))))

def bytes_l10206c_3 : List UInt8 :=
  [0xE8, 0x24, 0x0A, 0x00, 0x00]

theorem code_l10206c_3 : ∀ x ∈ codeRange 0x102157 bytes_l10206c_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2157 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10206c_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x10210b (shlR32Effect 0x10210b 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 134) (.exec 0x10210b (fun s => s.RIP = 0x10210b) (shlR32Effect 0x10210b 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.out 0x10210e (orR64R64Effect 0x10210e 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[129, 133]
    (.letOp (n := 136) (.exec 0x10210e (fun s => s.RIP = 0x10210e) (orR64R64Effect 0x10210e 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[129, 133]
    (.letOp (n := 137) (.out 0x102111 (movR64R64Effect 0x102111 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 138) (.exec 0x102111 (fun s => s.RIP = 0x102111) (movR64R64Effect 0x102111 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 139) (.out 0x102114 (shlR64Effect 0x102114 4 7 56) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[137]
    (.letOp (n := 140) (.exec 0x102114 (fun s => s.RIP = 0x102114) (shlR64Effect 0x102114 4 7 56) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 141) (.out 0x102118 (orR64R64Effect 0x102118 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[95, 139]
    (.letOp (n := 142) (.exec 0x102118 (fun s => s.RIP = 0x102118) (orR64R64Effect 0x102118 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[95, 139]
    (.letOp (n := 143) (.out 0x10211b (shldR64R64Effect 0x10211b 5 1 6 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[141, 99]
    (.letOp (n := 144) (.exec 0x10211b (fun s => s.RIP = 0x10211b) (shldR64R64Effect 0x10211b 5 1 6 1) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141, 99]
    (.letOp (n := 145) (.out 0x102120 (shrR32Effect 0x102120 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 146) (.exec 0x102120 (fun s => s.RIP = 0x102120) (shrR32Effect 0x102120 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 147) (.out 0x102123 (movR64Imm64Effect 0x102123 6 0x8000000000000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 148) (.exec 0x102123 (fun s => s.RIP = 0x102123) (movR64Imm64Effect 0x102123 6 0x8000000000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 149) (.out 0x10212d (andR64R64Effect 0x10212d 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[147, 139]
    (.letOp (n := 150) (.exec 0x10212d (fun s => s.RIP = 0x10212d) (andR64R64Effect 0x10212d 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[147, 139]
    (.letOp (n := 151) (.out 0x102130 (movR64R64Effect 0x102130 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[145]
    (.letOp (n := 152) (.exec 0x102130 (fun s => s.RIP = 0x102130) (movR64R64Effect 0x102130 7 0) (Reg.operands [.gpr 0] [])) #v[145]
    (.letOp (n := 153) (.out 0x102133 (shlR64Effect 0x102133 4 7 62) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x102133 (fun s => s.RIP = 0x102133) (shlR64Effect 0x102133 4 7 62) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.out 0x102137 (orR64R64Effect 0x102137 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[153, 149]
    (.letOp (n := 156) (.exec 0x102137 (fun s => s.RIP = 0x102137) (orR64R64Effect 0x102137 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[153, 149]
    (.letOp (n := 157) (.out 0x10213a (leaR64Effect 0x10213a 2 (.sib 0 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 2] []) (.reg (.gpr 2))) #v[145, 135]
    (.letOp (n := 158) (.exec 0x10213a (fun s => s.RIP = 0x10213a) (leaR64Effect 0x10213a 2 (.sib 0 (some 2) 1 .none)) (Reg.operands [.gpr 0, .gpr 2] [])) #v[145, 135]
    (.letOp (n := 159) (.out 0x10213e (shlR64Effect 0x10213e 4 0 57) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 160) (.exec 0x10213e (fun s => s.RIP = 0x10213e) (shlR64Effect 0x10213e 4 0 57) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 161) (.out 0x102142 (orR64R64Effect 0x102142 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[159, 155]
    (.letOp (n := 162) (.exec 0x102142 (fun s => s.RIP = 0x102142) (orR64R64Effect 0x102142 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[159, 155]
    (.letOp (n := 163) (.out 0x102145 (xorR64R64Effect 0x102145 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[161, 143]
    (.letOp (n := 164) (.exec 0x102145 (fun s => s.RIP = 0x102145) (xorR64R64Effect 0x102145 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[161, 143]
    (.letOp (n := 165) (.exec 0x102148 (StorePre 0x102148 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102148 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102148 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[157, 4]
    (.letOp (n := 166) (.exec 0x10214c (StorePre 0x10214c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10214c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10214c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[163, 4]
    (.letOp (n := 167) (.out 0x102151 (movR64R64Effect 0x102151 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 168) (.exec 0x102151 (fun s => s.RIP = 0x102151) (movR64R64Effect 0x102151 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x102154 (movR64R64Effect 0x102154 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 170) (.exec 0x102154 (fun s => s.RIP = 0x102154) (movR64R64Effect 0x102154 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (b_l10206c_3))))))))))))))))))))))))))))))))))))))

def bytes_l10206c_2 : List UInt8 :=
  [0xC1, 0xE7, 0x08, 0x48, 0x09, 0xFA, 0x48, 0x89, 0xC7, 0x48, 0xC1, 0xE7, 0x38, 0x48, 0x09, 0xF9,
    0x48, 0x0F, 0xA4, 0xF1, 0x01, 0xC1, 0xE8, 0x07, 0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x48, 0x21, 0xFE, 0x48, 0x89, 0xC7, 0x48, 0xC1, 0xE7, 0x3E, 0x48, 0x09, 0xF7, 0x48,
    0x8D, 0x14, 0x50, 0x48, 0xC1, 0xE0, 0x39, 0x48, 0x09, 0xF8, 0x48, 0x31, 0xC8, 0x48, 0x89, 0x14,
    0x24, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xE6, 0x48, 0x89, 0xDF] ++ bytes_l10206c_3

theorem code_l10206c_2 : ∀ x ∈ codeRange 0x10210b bytes_l10206c_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x210b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10206c_3

@[cfg_block] def b_l10206c_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1020bd (movzxR32M8Effect 0x1020bd 5 2 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 94) (.exec 0x1020bd (LoadPre 0x1020bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x1020bd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020bd 5 2 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x1020c2 (orR64R64Effect 0x1020c2 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[91, 81]
    (.letOp (n := 96) (.exec 0x1020c2 (fun s => s.RIP = 0x1020c2) (orR64R64Effect 0x1020c2 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[91, 81]
    (.letOp (n := 97) (.out 0x1020c5 (movzxR32M8Effect 0x1020c5 5 7 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 98) (.exec 0x1020c5 (LoadPre 0x1020c5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1020c5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020c5 5 7 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x1020ca (shlR64Effect 0x1020ca 4 6 56) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 100) (.exec 0x1020ca (fun s => s.RIP = 0x1020ca) (shlR64Effect 0x1020ca 4 6 56) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 101) (.out 0x1020ce (shlR64Effect 0x1020ce 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 102) (.exec 0x1020ce (fun s => s.RIP = 0x1020ce) (shlR64Effect 0x1020ce 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 103) (.out 0x1020d2 (shlR64Effect 0x1020d2 4 7 40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[97]
    (.letOp (n := 104) (.exec 0x1020d2 (fun s => s.RIP = 0x1020d2) (shlR64Effect 0x1020d2 4 7 40) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 105) (.out 0x1020d6 (orR64R64Effect 0x1020d6 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[101, 99]
    (.letOp (n := 106) (.exec 0x1020d6 (fun s => s.RIP = 0x1020d6) (orR64R64Effect 0x1020d6 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[101, 99]
    (.letOp (n := 107) (.out 0x1020d9 (orR64R64Effect 0x1020d9 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x1020d9 (fun s => s.RIP = 0x1020d9) (orR64R64Effect 0x1020d9 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x1020dc (movzxR32M8Effect 0x1020dc 5 7 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 110) (.exec 0x1020dc (LoadPre 0x1020dc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x1020dc + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020dc 5 7 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x1020e1 (shlR64Effect 0x1020e1 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[109]
    (.letOp (n := 112) (.exec 0x1020e1 (fun s => s.RIP = 0x1020e1) (shlR64Effect 0x1020e1 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x1020e5 (orR64R64Effect 0x1020e5 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[107, 111]
    (.letOp (n := 114) (.exec 0x1020e5 (fun s => s.RIP = 0x1020e5) (orR64R64Effect 0x1020e5 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[107, 111]
    (.letOp (n := 115) (.out 0x1020e8 (movzxR32M8Effect 0x1020e8 5 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 116) (.exec 0x1020e8 (LoadPre 0x1020e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1020e8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020e8 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x1020ed (shlR32Effect 0x1020ed 3 7 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[115]
    (.letOp (n := 118) (.exec 0x1020ed (fun s => s.RIP = 0x1020ed) (shlR32Effect 0x1020ed 3 7 24) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x1020f0 (orR64R64Effect 0x1020f0 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[113, 117]
    (.letOp (n := 120) (.exec 0x1020f0 (fun s => s.RIP = 0x1020f0) (orR64R64Effect 0x1020f0 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[113, 117]
    (.letOp (n := 121) (.out 0x1020f3 (movzxR32M8Effect 0x1020f3 5 7 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 122) (.exec 0x1020f3 (LoadPre 0x1020f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x1020f3 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020f3 5 7 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x1020f8 (shlR32Effect 0x1020f8 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[121]
    (.letOp (n := 124) (.exec 0x1020f8 (fun s => s.RIP = 0x1020f8) (shlR32Effect 0x1020f8 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.out 0x1020fb (orR64R64Effect 0x1020fb 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[119, 123]
    (.letOp (n := 126) (.exec 0x1020fb (fun s => s.RIP = 0x1020fb) (orR64R64Effect 0x1020fb 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[119, 123]
    (.letOp (n := 127) (.out 0x1020fe (movzxR32M8Effect 0x1020fe 5 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 128) (.exec 0x1020fe (LoadPre 0x1020fe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1020fe + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020fe 5 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 129) (.out 0x102103 (orR64R64Effect 0x102103 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[125, 127]
    (.letOp (n := 130) (.exec 0x102103 (fun s => s.RIP = 0x102103) (orR64R64Effect 0x102103 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[125, 127]
    (.letOp (n := 131) (.out 0x102106 (movzxR32M8Effect 0x102106 5 7 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 132) (.exec 0x102106 (LoadPre 0x102106 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x102106 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102106 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l10206c_2))))))))))))))))))))))))))))))))))))))))

def bytes_l10206c_1 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x09, 0x4C, 0x09, 0xC1, 0x0F, 0xB6, 0x7C, 0x24, 0x0A, 0x48, 0xC1, 0xE6,
    0x38, 0x48, 0xC1, 0xE2, 0x30, 0x48, 0xC1, 0xE7, 0x28, 0x48, 0x09, 0xF2, 0x48, 0x09, 0xFA, 0x0F,
    0xB6, 0x7C, 0x24, 0x0B, 0x48, 0xC1, 0xE7, 0x20, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0C,
    0xC1, 0xE7, 0x18, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0D, 0xC1, 0xE7, 0x10, 0x48, 0x09,
    0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0F, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0E] ++ bytes_l10206c_2

theorem code_l10206c_1 : ∀ x ∈ codeRange 0x1020bd bytes_l10206c_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x20bd 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10206c_2

@[cfg_block] def b_l10206c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10206c (movzxR32M8Effect 0x10206c 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10206c (LoadPre 0x10206c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10206c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10206c 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102070 (movzxR32M8Effect 0x102070 5 7 (.sib 4 none 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x102070 (LoadPre 0x102070 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x102070 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102070 5 7 (.sib 4 none 0 (.d8 0x1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102075 (movzxR32M8Effect 0x102075 5 1 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x102075 (LoadPre 0x102075 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x102075 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102075 5 1 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10207a (movzxR32M8Effect 0x10207a 5 6 (.sib 4 none 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x10207a (LoadPre 0x10207a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x10207a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10207a 5 6 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10207f (movzxR32M8Effect 0x10207f 5 2 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x10207f (LoadPre 0x10207f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x10207f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10207f 5 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x102084 (shlR64Effect 0x102084 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 64) (.exec 0x102084 (fun s => s.RIP = 0x102084) (shlR64Effect 0x102084 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 65) (.out 0x102088 (shlR64Effect 0x102088 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 66) (.exec 0x102088 (fun s => s.RIP = 0x102088) (shlR64Effect 0x102088 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x10208c (orR64R64Effect 0x10208c 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x10208c (fun s => s.RIP = 0x10208c) (orR64R64Effect 0x10208c 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x10208f (movzxR32M8Effect 0x10208f 5 7 (.sib 4 none 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x10208f (LoadPre 0x10208f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x10208f + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10208f 5 7 (.sib 4 none 0 (.d8 0x5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x102094 (shlR64Effect 0x102094 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 72) (.exec 0x102094 (fun s => s.RIP = 0x102094) (shlR64Effect 0x102094 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 73) (.out 0x102098 (orR64R64Effect 0x102098 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x102098 (fun s => s.RIP = 0x102098) (orR64R64Effect 0x102098 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x10209b (movzxR32M8Effect 0x10209b 5 1 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x10209b (LoadPre 0x10209b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x10209b + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10209b 5 1 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1020a0 (shlR32Effect 0x1020a0 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 78) (.exec 0x1020a0 (fun s => s.RIP = 0x1020a0) (shlR32Effect 0x1020a0 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 79) (.out 0x1020a3 (orR64R64Effect 0x1020a3 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x1020a3 (fun s => s.RIP = 0x1020a3) (orR64R64Effect 0x1020a3 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x1020a6 (movzxR32M8Effect 0x1020a6 6 8 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 82) (.exec 0x1020a6 (LoadPre 0x1020a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1020a6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1020a6 6 8 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1020ac (shlR32Effect 0x1020ac 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 84) (.exec 0x1020ac (fun s => s.RIP = 0x1020ac) (shlR32Effect 0x1020ac 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 85) (.out 0x1020af (orR64R64Effect 0x1020af 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[83, 79]
    (.letOp (n := 86) (.exec 0x1020af (fun s => s.RIP = 0x1020af) (orR64R64Effect 0x1020af 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[83, 79]
    (.letOp (n := 87) (.out 0x1020b2 (movzxR32M8Effect 0x1020b2 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 88) (.exec 0x1020b2 (LoadPre 0x1020b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1020b2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1020b2 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x1020b7 (shlR32Effect 0x1020b7 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[75]
    (.letOp (n := 90) (.exec 0x1020b7 (fun s => s.RIP = 0x1020b7) (shlR32Effect 0x1020b7 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 91) (.out 0x1020ba (orR64R64Effect 0x1020ba 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x1020ba (fun s => s.RIP = 0x1020ba) (orR64R64Effect 0x1020ba 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[89, 85]
    (b_l10206c_1))))))))))))))))))))))))))))))))))))))))

def bytes_l10206c : List UInt8 :=
  [0x0F, 0xB6, 0x04, 0x24, 0x0F, 0xB6, 0x7C, 0x24, 0x01, 0x0F, 0xB6, 0x4C, 0x24, 0x02, 0x0F, 0xB6,
    0x74, 0x24, 0x03, 0x0F, 0xB6, 0x54, 0x24, 0x04, 0x48, 0xC1, 0xE7, 0x30, 0x48, 0xC1, 0xE1, 0x28,
    0x48, 0x09, 0xF9, 0x0F, 0xB6, 0x7C, 0x24, 0x05, 0x48, 0xC1, 0xE6, 0x20, 0x48, 0x09, 0xCE, 0x0F,
    0xB6, 0x4C, 0x24, 0x06, 0xC1, 0xE2, 0x18, 0x48, 0x09, 0xF2, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07,
    0xC1, 0xE7, 0x10, 0x48, 0x09, 0xD7, 0x0F, 0xB6, 0x74, 0x24, 0x08, 0xC1, 0xE1, 0x08, 0x48, 0x09,
    0xF9] ++ bytes_l10206c_1

theorem code_l10206c : ∀ x ∈ codeRange 0x10206c bytes_l10206c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x206c 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10206c_1

@[cfg_block] def b_l10215c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10215c (movR64R64Effect 0x10215c 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10215c (fun s => s.RIP = 0x10215c) (movR64R64Effect 0x10215c 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10215f (addR64Imm8Effect 0x10215f 7 0x20) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10215f (fun s => s.RIP = 0x10215f) (addR64Imm8Effect 0x10215f 7 0x20) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x102163 (movR32Imm32Effect 0x102163 5 2 0xb0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x102163 (fun s => s.RIP = 0x102163) (movR32Imm32Effect 0x102163 5 2 0xb0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x102168 (movR64R64Effect 0x102168 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x102168 (fun s => s.RIP = 0x102168) (movR64R64Effect 0x102168 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10216b (callEffect (callMemPtr 0x10216b (.rip 0xff097)) (0x10216b + BitVec.ofNat 64 (callMemLen (.rip 0xff097)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10216b (GoesTo (CallMemPre 0x10216b (.rip 0xff097)) (callEffect (callMemPtr 0x10216b (.rip 0xff097)) (0x10216b + BitVec.ofNat 64 (callMemLen (.rip 0xff097)))) 0x103f00) (callEffect (callMemPtr 0x10216b (.rip 0xff097)) (0x10216b + BitVec.ofNat 64 (callMemLen (.rip 0xff097)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x102171⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l102171, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10215c : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x48, 0x83, 0xC7, 0x20, 0xBA, 0xB0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xFF,
    0x15, 0x97, 0xF0, 0x0F, 0x00]

theorem code_l10215c : ∀ x ∈ codeRange 0x10215c bytes_l10215c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x215c 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102171 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102171 (movR64R64Effect 0x102171 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x102171 (fun s => s.RIP = 0x102171) (movR64R64Effect 0x102171 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x102174 (addR64Imm8Effect 0x102174 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x102174 (fun s => s.RIP = 0x102174) (addR64Imm8Effect 0x102174 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102178 (popR64Effect 0x102178 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x102178 (popR64Effect 0x102178 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x102178 (PopPre 0x102178) (popR64Effect 0x102178 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x102179 (popR64Effect 0x102179 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x102179 (popR64Effect 0x102179 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x102179 (PopPre 0x102179) (popR64Effect 0x102179 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10217b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x10217b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10217b (RetPre 0x10217b) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l102171 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x28, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l102171 : ∀ x ∈ codeRange 0x102171 bytes_l102171, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2171 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102180 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102180 (pushR64Effect 0x102180 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x102180 (PushPre 0x102180 2) (pushR64Effect 0x102180 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x102182 (pushR64Effect 0x102182 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x102182 (PushPre 0x102182 1) (pushR64Effect 0x102182 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x102183 (subR64Imm8Effect 0x102183 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 58) (.exec 0x102183 (fun s => s.RIP = 0x102183) (subR64Imm8Effect 0x102183 4 0x28) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 59) (.out 0x102187 (movR64R64Effect 0x102187 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 60) (.exec 0x102187 (fun s => s.RIP = 0x102187) (movR64R64Effect 0x102187 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x10218a (movR64R64Effect 0x10218a 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 62) (.exec 0x10218a (fun s => s.RIP = 0x10218a) (movR64R64Effect 0x10218a 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.exec 0x10218d (StorePre 0x10218d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10218d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10218d (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 64) (.exec 0x102196 (StorePre 0x102196 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102196 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102196 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 65) (.out 0x10219f (movR64R64Effect 0x10219f 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 66) (.exec 0x10219f (fun s => s.RIP = 0x10219f) (movR64R64Effect 0x10219f 7 4) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 67) (.out 0x1021a2 (leaR64Effect 0x1021a2 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 68) (.exec 0x1021a2 (fun s => s.RIP = 0x1021a2) (leaR64Effect 0x1021a2 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 69) (.out 0x1021a7 (callEffect (fun _ => 0x106960) 0x1021ac) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 70) (.exec 0x1021a7 (PushPre 0x1021a7 5) (callEffect (fun _ => 0x106960) 0x1021ac) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 71) (.const ⟨64, 0x1021ac⟩) #v[]
    (.terminate (.call ⟨.l106960, RegMap.args [(2, 67), (3, 61), (4, 69), (5, 5), (6, 6), (7, 65), (12, 12), (13, 13), (14, 59), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l1021ac, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l102180 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0xC7, 0x44,
    0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xE7, 0x48, 0x8D, 0x54, 0x24, 0x18, 0xE8, 0xB4, 0x47, 0x00, 0x00]

theorem code_l102180 : ∀ x ∈ codeRange 0x102180 bytes_l102180, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2180 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1021ac_3 : Block Op Label signature Reg.count 171 :=
  .letOp (n := 171) (.out 0x102297 (callEffect (fun _ => 0x102b80) 0x10229c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 172) (.exec 0x102297 (PushPre 0x102297 5) (callEffect (fun _ => 0x102b80) 0x10229c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 173) (.const ⟨64, 0x10229c⟩) #v[]
    (.terminate (.call ⟨.l102b80, RegMap.args [(0, 163), (1, 143), (2, 157), (3, 3), (4, 171), (5, 5), (6, 167), (7, 169), (8, 81), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 174⟩ { target := .l10229c, kept := #v[], arity := rfl, guard := some (Fin.last 173) }))))

def bytes_l1021ac_3 : List UInt8 :=
  [0xE8, 0xE4, 0x08, 0x00, 0x00]

theorem code_l1021ac_3 : ∀ x ∈ codeRange 0x102297 bytes_l1021ac_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2297 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1021ac_2 : Block Op Label signature Reg.count 133 :=
  .letOp (n := 133) (.out 0x10224b (shlR32Effect 0x10224b 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[131]
    (.letOp (n := 134) (.exec 0x10224b (fun s => s.RIP = 0x10224b) (shlR32Effect 0x10224b 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.out 0x10224e (orR64R64Effect 0x10224e 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[129, 133]
    (.letOp (n := 136) (.exec 0x10224e (fun s => s.RIP = 0x10224e) (orR64R64Effect 0x10224e 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[129, 133]
    (.letOp (n := 137) (.out 0x102251 (movR64R64Effect 0x102251 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 138) (.exec 0x102251 (fun s => s.RIP = 0x102251) (movR64R64Effect 0x102251 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 139) (.out 0x102254 (shlR64Effect 0x102254 4 7 56) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[137]
    (.letOp (n := 140) (.exec 0x102254 (fun s => s.RIP = 0x102254) (shlR64Effect 0x102254 4 7 56) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 141) (.out 0x102258 (orR64R64Effect 0x102258 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[95, 139]
    (.letOp (n := 142) (.exec 0x102258 (fun s => s.RIP = 0x102258) (orR64R64Effect 0x102258 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[95, 139]
    (.letOp (n := 143) (.out 0x10225b (shldR64R64Effect 0x10225b 5 1 6 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[141, 99]
    (.letOp (n := 144) (.exec 0x10225b (fun s => s.RIP = 0x10225b) (shldR64R64Effect 0x10225b 5 1 6 1) (Reg.operands [.gpr 1, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141, 99]
    (.letOp (n := 145) (.out 0x102260 (shrR32Effect 0x102260 3 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 146) (.exec 0x102260 (fun s => s.RIP = 0x102260) (shrR32Effect 0x102260 3 0 7) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 147) (.out 0x102263 (movR64Imm64Effect 0x102263 6 0x8000000000000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 148) (.exec 0x102263 (fun s => s.RIP = 0x102263) (movR64Imm64Effect 0x102263 6 0x8000000000000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 149) (.out 0x10226d (andR64R64Effect 0x10226d 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[147, 139]
    (.letOp (n := 150) (.exec 0x10226d (fun s => s.RIP = 0x10226d) (andR64R64Effect 0x10226d 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[147, 139]
    (.letOp (n := 151) (.out 0x102270 (movR64R64Effect 0x102270 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[145]
    (.letOp (n := 152) (.exec 0x102270 (fun s => s.RIP = 0x102270) (movR64R64Effect 0x102270 7 0) (Reg.operands [.gpr 0] [])) #v[145]
    (.letOp (n := 153) (.out 0x102273 (shlR64Effect 0x102273 4 7 62) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x102273 (fun s => s.RIP = 0x102273) (shlR64Effect 0x102273 4 7 62) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.out 0x102277 (orR64R64Effect 0x102277 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[153, 149]
    (.letOp (n := 156) (.exec 0x102277 (fun s => s.RIP = 0x102277) (orR64R64Effect 0x102277 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[153, 149]
    (.letOp (n := 157) (.out 0x10227a (leaR64Effect 0x10227a 2 (.sib 0 (some 2) 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 2] []) (.reg (.gpr 2))) #v[145, 135]
    (.letOp (n := 158) (.exec 0x10227a (fun s => s.RIP = 0x10227a) (leaR64Effect 0x10227a 2 (.sib 0 (some 2) 1 .none)) (Reg.operands [.gpr 0, .gpr 2] [])) #v[145, 135]
    (.letOp (n := 159) (.out 0x10227e (shlR64Effect 0x10227e 4 0 57) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[145]
    (.letOp (n := 160) (.exec 0x10227e (fun s => s.RIP = 0x10227e) (shlR64Effect 0x10227e 4 0 57) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 161) (.out 0x102282 (orR64R64Effect 0x102282 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[159, 155]
    (.letOp (n := 162) (.exec 0x102282 (fun s => s.RIP = 0x102282) (orR64R64Effect 0x102282 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[159, 155]
    (.letOp (n := 163) (.out 0x102285 (xorR64R64Effect 0x102285 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[161, 143]
    (.letOp (n := 164) (.exec 0x102285 (fun s => s.RIP = 0x102285) (xorR64R64Effect 0x102285 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[161, 143]
    (.letOp (n := 165) (.exec 0x102288 (StorePre 0x102288 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102288 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102288 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[157, 4]
    (.letOp (n := 166) (.exec 0x10228c (StorePre 0x10228c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10228c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10228c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[163, 4]
    (.letOp (n := 167) (.out 0x102291 (movR64R64Effect 0x102291 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 168) (.exec 0x102291 (fun s => s.RIP = 0x102291) (movR64R64Effect 0x102291 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 169) (.out 0x102294 (movR64R64Effect 0x102294 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 170) (.exec 0x102294 (fun s => s.RIP = 0x102294) (movR64R64Effect 0x102294 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (b_l1021ac_3))))))))))))))))))))))))))))))))))))))

def bytes_l1021ac_2 : List UInt8 :=
  [0xC1, 0xE7, 0x08, 0x48, 0x09, 0xFA, 0x48, 0x89, 0xC7, 0x48, 0xC1, 0xE7, 0x38, 0x48, 0x09, 0xF9,
    0x48, 0x0F, 0xA4, 0xF1, 0x01, 0xC1, 0xE8, 0x07, 0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x48, 0x21, 0xFE, 0x48, 0x89, 0xC7, 0x48, 0xC1, 0xE7, 0x3E, 0x48, 0x09, 0xF7, 0x48,
    0x8D, 0x14, 0x50, 0x48, 0xC1, 0xE0, 0x39, 0x48, 0x09, 0xF8, 0x48, 0x31, 0xC8, 0x48, 0x89, 0x14,
    0x24, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xE6, 0x48, 0x89, 0xDF] ++ bytes_l1021ac_3

theorem code_l1021ac_2 : ∀ x ∈ codeRange 0x10224b bytes_l1021ac_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x224b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1021ac_3

@[cfg_block] def b_l1021ac_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1021fd (movzxR32M8Effect 0x1021fd 5 2 (.sib 4 none 0 (.d8 0x9))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 94) (.exec 0x1021fd (LoadPre 0x1021fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x1021fd + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021fd 5 2 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x102202 (orR64R64Effect 0x102202 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[91, 81]
    (.letOp (n := 96) (.exec 0x102202 (fun s => s.RIP = 0x102202) (orR64R64Effect 0x102202 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[91, 81]
    (.letOp (n := 97) (.out 0x102205 (movzxR32M8Effect 0x102205 5 7 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 98) (.exec 0x102205 (LoadPre 0x102205 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x102205 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102205 5 7 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x10220a (shlR64Effect 0x10220a 4 6 56) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 100) (.exec 0x10220a (fun s => s.RIP = 0x10220a) (shlR64Effect 0x10220a 4 6 56) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 101) (.out 0x10220e (shlR64Effect 0x10220e 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 102) (.exec 0x10220e (fun s => s.RIP = 0x10220e) (shlR64Effect 0x10220e 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 103) (.out 0x102212 (shlR64Effect 0x102212 4 7 40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[97]
    (.letOp (n := 104) (.exec 0x102212 (fun s => s.RIP = 0x102212) (shlR64Effect 0x102212 4 7 40) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 105) (.out 0x102216 (orR64R64Effect 0x102216 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[101, 99]
    (.letOp (n := 106) (.exec 0x102216 (fun s => s.RIP = 0x102216) (orR64R64Effect 0x102216 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[101, 99]
    (.letOp (n := 107) (.out 0x102219 (orR64R64Effect 0x102219 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x102219 (fun s => s.RIP = 0x102219) (orR64R64Effect 0x102219 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x10221c (movzxR32M8Effect 0x10221c 5 7 (.sib 4 none 0 (.d8 0xb))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 110) (.exec 0x10221c (LoadPre 0x10221c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x10221c + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10221c 5 7 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.out 0x102221 (shlR64Effect 0x102221 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[109]
    (.letOp (n := 112) (.exec 0x102221 (fun s => s.RIP = 0x102221) (shlR64Effect 0x102221 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x102225 (orR64R64Effect 0x102225 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[107, 111]
    (.letOp (n := 114) (.exec 0x102225 (fun s => s.RIP = 0x102225) (orR64R64Effect 0x102225 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[107, 111]
    (.letOp (n := 115) (.out 0x102228 (movzxR32M8Effect 0x102228 5 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 116) (.exec 0x102228 (LoadPre 0x102228 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x102228 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102228 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 117) (.out 0x10222d (shlR32Effect 0x10222d 3 7 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[115]
    (.letOp (n := 118) (.exec 0x10222d (fun s => s.RIP = 0x10222d) (shlR32Effect 0x10222d 3 7 24) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x102230 (orR64R64Effect 0x102230 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[113, 117]
    (.letOp (n := 120) (.exec 0x102230 (fun s => s.RIP = 0x102230) (orR64R64Effect 0x102230 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[113, 117]
    (.letOp (n := 121) (.out 0x102233 (movzxR32M8Effect 0x102233 5 7 (.sib 4 none 0 (.d8 0xd))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 122) (.exec 0x102233 (LoadPre 0x102233 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x102233 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102233 5 7 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 123) (.out 0x102238 (shlR32Effect 0x102238 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[121]
    (.letOp (n := 124) (.exec 0x102238 (fun s => s.RIP = 0x102238) (shlR32Effect 0x102238 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.out 0x10223b (orR64R64Effect 0x10223b 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[119, 123]
    (.letOp (n := 126) (.exec 0x10223b (fun s => s.RIP = 0x10223b) (orR64R64Effect 0x10223b 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[119, 123]
    (.letOp (n := 127) (.out 0x10223e (movzxR32M8Effect 0x10223e 5 7 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 128) (.exec 0x10223e (LoadPre 0x10223e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10223e + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10223e 5 7 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 129) (.out 0x102243 (orR64R64Effect 0x102243 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[125, 127]
    (.letOp (n := 130) (.exec 0x102243 (fun s => s.RIP = 0x102243) (orR64R64Effect 0x102243 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[125, 127]
    (.letOp (n := 131) (.out 0x102246 (movzxR32M8Effect 0x102246 5 7 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 132) (.exec 0x102246 (LoadPre 0x102246 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x102246 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x102246 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l1021ac_2))))))))))))))))))))))))))))))))))))))))

def bytes_l1021ac_1 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x09, 0x4C, 0x09, 0xC1, 0x0F, 0xB6, 0x7C, 0x24, 0x0A, 0x48, 0xC1, 0xE6,
    0x38, 0x48, 0xC1, 0xE2, 0x30, 0x48, 0xC1, 0xE7, 0x28, 0x48, 0x09, 0xF2, 0x48, 0x09, 0xFA, 0x0F,
    0xB6, 0x7C, 0x24, 0x0B, 0x48, 0xC1, 0xE7, 0x20, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0C,
    0xC1, 0xE7, 0x18, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0D, 0xC1, 0xE7, 0x10, 0x48, 0x09,
    0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0F, 0x48, 0x09, 0xFA, 0x0F, 0xB6, 0x7C, 0x24, 0x0E] ++ bytes_l1021ac_2

theorem code_l1021ac_1 : ∀ x ∈ codeRange 0x1021fd bytes_l1021ac_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21fd 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1021ac_2

@[cfg_block] def b_l1021ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1021ac (movzxR32M8Effect 0x1021ac 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1021ac (LoadPre 0x1021ac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1021ac + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x1021ac 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1021b0 (movzxR32M8Effect 0x1021b0 5 7 (.sib 4 none 0 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x1021b0 (LoadPre 0x1021b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x1021b0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021b0 5 7 (.sib 4 none 0 (.d8 0x1))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1021b5 (movzxR32M8Effect 0x1021b5 5 1 (.sib 4 none 0 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x1021b5 (LoadPre 0x1021b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x1021b5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021b5 5 1 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1021ba (movzxR32M8Effect 0x1021ba 5 6 (.sib 4 none 0 (.d8 0x3))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1021ba (LoadPre 0x1021ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x1021ba + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021ba 5 6 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1021bf (movzxR32M8Effect 0x1021bf 5 2 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1021bf (LoadPre 0x1021bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1021bf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021bf 5 2 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1021c4 (shlR64Effect 0x1021c4 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 64) (.exec 0x1021c4 (fun s => s.RIP = 0x1021c4) (shlR64Effect 0x1021c4 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 65) (.out 0x1021c8 (shlR64Effect 0x1021c8 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 66) (.exec 0x1021c8 (fun s => s.RIP = 0x1021c8) (shlR64Effect 0x1021c8 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x1021cc (orR64R64Effect 0x1021cc 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x1021cc (fun s => s.RIP = 0x1021cc) (orR64R64Effect 0x1021cc 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x1021cf (movzxR32M8Effect 0x1021cf 5 7 (.sib 4 none 0 (.d8 0x5))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1021cf (LoadPre 0x1021cf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x1021cf + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021cf 5 7 (.sib 4 none 0 (.d8 0x5))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1021d4 (shlR64Effect 0x1021d4 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 72) (.exec 0x1021d4 (fun s => s.RIP = 0x1021d4) (shlR64Effect 0x1021d4 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 73) (.out 0x1021d8 (orR64R64Effect 0x1021d8 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x1021d8 (fun s => s.RIP = 0x1021d8) (orR64R64Effect 0x1021d8 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x1021db (movzxR32M8Effect 0x1021db 5 1 (.sib 4 none 0 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x1021db (LoadPre 0x1021db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1021db + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021db 5 1 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1021e0 (shlR32Effect 0x1021e0 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 78) (.exec 0x1021e0 (fun s => s.RIP = 0x1021e0) (shlR32Effect 0x1021e0 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 79) (.out 0x1021e3 (orR64R64Effect 0x1021e3 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x1021e3 (fun s => s.RIP = 0x1021e3) (orR64R64Effect 0x1021e3 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x1021e6 (movzxR32M8Effect 0x1021e6 6 8 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 82) (.exec 0x1021e6 (LoadPre 0x1021e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x1021e6 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x1021e6 6 8 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1021ec (shlR32Effect 0x1021ec 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 84) (.exec 0x1021ec (fun s => s.RIP = 0x1021ec) (shlR32Effect 0x1021ec 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 85) (.out 0x1021ef (orR64R64Effect 0x1021ef 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[83, 79]
    (.letOp (n := 86) (.exec 0x1021ef (fun s => s.RIP = 0x1021ef) (orR64R64Effect 0x1021ef 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[83, 79]
    (.letOp (n := 87) (.out 0x1021f2 (movzxR32M8Effect 0x1021f2 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 88) (.exec 0x1021f2 (LoadPre 0x1021f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1021f2 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1021f2 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x1021f7 (shlR32Effect 0x1021f7 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[75]
    (.letOp (n := 90) (.exec 0x1021f7 (fun s => s.RIP = 0x1021f7) (shlR32Effect 0x1021f7 3 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[75]
    (.letOp (n := 91) (.out 0x1021fa (orR64R64Effect 0x1021fa 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x1021fa (fun s => s.RIP = 0x1021fa) (orR64R64Effect 0x1021fa 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[89, 85]
    (b_l1021ac_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1021ac : List UInt8 :=
  [0x0F, 0xB6, 0x04, 0x24, 0x0F, 0xB6, 0x7C, 0x24, 0x01, 0x0F, 0xB6, 0x4C, 0x24, 0x02, 0x0F, 0xB6,
    0x74, 0x24, 0x03, 0x0F, 0xB6, 0x54, 0x24, 0x04, 0x48, 0xC1, 0xE7, 0x30, 0x48, 0xC1, 0xE1, 0x28,
    0x48, 0x09, 0xF9, 0x0F, 0xB6, 0x7C, 0x24, 0x05, 0x48, 0xC1, 0xE6, 0x20, 0x48, 0x09, 0xCE, 0x0F,
    0xB6, 0x4C, 0x24, 0x06, 0xC1, 0xE2, 0x18, 0x48, 0x09, 0xF2, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x07,
    0xC1, 0xE7, 0x10, 0x48, 0x09, 0xD7, 0x0F, 0xB6, 0x74, 0x24, 0x08, 0xC1, 0xE1, 0x08, 0x48, 0x09,
    0xF9] ++ bytes_l1021ac_1

theorem code_l1021ac : ∀ x ∈ codeRange 0x1021ac bytes_l1021ac, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x21ac 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1021ac_1

@[cfg_block] def b_l10229c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10229c (movR64R64Effect 0x10229c 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10229c (fun s => s.RIP = 0x10229c) (movR64R64Effect 0x10229c 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10229f (addR64Imm8Effect 0x10229f 7 0x20) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10229f (fun s => s.RIP = 0x10229f) (addR64Imm8Effect 0x10229f 7 0x20) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x1022a3 (movR32Imm32Effect 0x1022a3 5 2 0xf0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1022a3 (fun s => s.RIP = 0x1022a3) (movR32Imm32Effect 0x1022a3 5 2 0xf0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1022a8 (movR64R64Effect 0x1022a8 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x1022a8 (fun s => s.RIP = 0x1022a8) (movR64R64Effect 0x1022a8 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1022ab (callEffect (callMemPtr 0x1022ab (.rip 0xfef57)) (0x1022ab + BitVec.ofNat 64 (callMemLen (.rip 0xfef57)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1022ab (GoesTo (CallMemPre 0x1022ab (.rip 0xfef57)) (callEffect (callMemPtr 0x1022ab (.rip 0xfef57)) (0x1022ab + BitVec.ofNat 64 (callMemLen (.rip 0xfef57)))) 0x103f00) (callEffect (callMemPtr 0x1022ab (.rip 0xfef57)) (0x1022ab + BitVec.ofNat 64 (callMemLen (.rip 0xfef57)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1022b1⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 57), (3, 3), (4, 61), (5, 5), (6, 59), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1022b1, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10229c : List UInt8 :=
  [0x48, 0x89, 0xDF, 0x48, 0x83, 0xC7, 0x20, 0xBA, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6, 0xFF,
    0x15, 0x57, 0xEF, 0x0F, 0x00]

theorem code_l10229c : ∀ x ∈ codeRange 0x10229c bytes_l10229c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x229c 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1022b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1022b1 (movR64R64Effect 0x1022b1 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1022b1 (fun s => s.RIP = 0x1022b1) (movR64R64Effect 0x1022b1 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1022b4 (addR64Imm8Effect 0x1022b4 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1022b4 (fun s => s.RIP = 0x1022b4) (addR64Imm8Effect 0x1022b4 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1022b8 (popR64Effect 0x1022b8 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1022b8 (popR64Effect 0x1022b8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1022b8 (PopPre 0x1022b8) (popR64Effect 0x1022b8 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1022b9 (popR64Effect 0x1022b9 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[58]
    (.letOp (n := 61) (.out 0x1022b9 (popR64Effect 0x1022b9 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1022b9 (PopPre 0x1022b9) (popR64Effect 0x1022b9 2 14) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1022bb (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[61]
    (.letOp (n := 64) (.out 0x1022bb (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1022bb (RetPre 0x1022bb) (retEffect) (Reg.operands [.gpr 4] [])) #v[61]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 64), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66) (some ⟨63, by decide⟩)))))))))))))))

def bytes_l1022b1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x28, 0x5B, 0x41, 0x5E, 0xC3]

theorem code_l1022b1 : ∀ x ∈ codeRange 0x1022b1 bytes_l1022b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x22b1 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1022c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1022c0 (pushR64Effect 0x1022c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1022c0 (PushPre 0x1022c0 1) (pushR64Effect 0x1022c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1022c1 (pushR64Effect 0x1022c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1022c1 (PushPre 0x1022c1 2) (pushR64Effect 0x1022c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1022c3 (pushR64Effect 0x1022c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1022c3 (PushPre 0x1022c3 2) (pushR64Effect 0x1022c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1022c5 (pushR64Effect 0x1022c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1022c5 (PushPre 0x1022c5 2) (pushR64Effect 0x1022c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1022c7 (pushR64Effect 0x1022c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1022c7 (PushPre 0x1022c7 2) (pushR64Effect 0x1022c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1022c9 (pushR64Effect 0x1022c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1022c9 (PushPre 0x1022c9 1) (pushR64Effect 0x1022c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1022ca (subR64Imm32Effect 0x1022ca 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1022ca (fun s => s.RIP = 0x1022ca) (subR64Imm32Effect 0x1022ca 4 0xa8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1022d1 (movR64R64Effect 0x1022d1 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 68) (.exec 0x1022d1 (fun s => s.RIP = 0x1022d1) (movR64R64Effect 0x1022d1 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x1022d4 (movR64Imm64Effect 0x1022d4 3 0xfffffffe0) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 70) (.exec 0x1022d4 (fun s => s.RIP = 0x1022d4) (movR64Imm64Effect 0x1022d4 3 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x1022de (movR64M64Effect 0x1022de 14 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 72) (.exec 0x1022de (LoadPre 0x1022de (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x1022de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1022de 14 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 73) (.out 0x1022e2 (cmpR64R64Effect 0x1022e2 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 74) (.out 0x1022e2 (cmpR64R64Effect 0x1022e2 14 3) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 3] []) (.flag .ZF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x1022e2 (fun s => s.RIP = 0x1022e2) (cmpR64R64Effect 0x1022e2 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[71, 69]
    (.letOp (n := 76) (.out 0x1022e5 (atFlags (condHolds 7) (setccR8Effect 0x1022e5 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 73, 74]
    (.letOp (n := 77) (.exec 0x1022e5 (fun s => s.RIP = 0x1022e5) (atFlags (condHolds 7) (setccR8Effect 0x1022e5 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 73, 74]
    (.letOp (n := 78) (.out 0x1022e8 (shrR64Effect 0x1022e8 4 1 61) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 79) (.out 0x1022e8 (shrR64Effect 0x1022e8 4 1 61) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[1]
    (.letOp (n := 80) (.exec 0x1022e8 (fun s => s.RIP = 0x1022e8) (shrR64Effect 0x1022e8 4 1 61) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 81) (.out 0x1022ec (atFlags (condHolds 5) (setccR8Effect 0x1022ec 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[78, 79]
    (.letOp (n := 82) (.exec 0x1022ec (fun s => s.RIP = 0x1022ec) (atFlags (condHolds 5) (setccR8Effect 0x1022ec 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[78, 79]
    (.letOp (n := 83) (.out 0x1022ef (orR8R8Effect 0x1022ef 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[81, 76]
    (.letOp (n := 84) (.out 0x1022ef (orR8R8Effect 0x1022ef 2 1 0) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 0] []) (.flag .ZF)) #v[81, 76]
    (.letOp (n := 85) (.exec 0x1022ef (fun s => s.RIP = 0x1022ef) (orR8R8Effect 0x1022ef 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[81, 76]
    (.letOp (n := 86) (.out 0x1022f1 (movR8Imm8Effect 0x1022f1 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 87) (.exec 0x1022f1 (fun s => s.RIP = 0x1022f1) (movR8Imm8Effect 0x1022f1 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[76]
    (.letOp (n := 88) (.pure (condOp 5)) #v[84]
    (.terminate (.condBr (Fin.last 88) ⟨.l102501, RegMap.args [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ ⟨.l1022f9, RegMap.args [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l1022c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xCD, 0x48, 0xBB, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4D, 0x8B,
    0x70, 0x10, 0x49, 0x39, 0xDE, 0x0F, 0x97, 0xC0, 0x48, 0xC1, 0xE9, 0x3D, 0x0F, 0x95, 0xC1, 0x08,
    0xC1, 0xB0, 0x01, 0x0F, 0x85, 0x08, 0x02, 0x00, 0x00]

theorem code_l1022c0 : ∀ x ∈ codeRange 0x1022c0 bytes_l1022c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x22c0 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1022f9_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.out 0x102357 (callEffect (fun _ => 0x105100) 0x10235c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 83) (.exec 0x102357 (PushPre 0x102357 5) (callEffect (fun _ => 0x105100) 0x10235c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.const ⟨64, 0x10235c⟩) #v[]
    (.terminate (.call ⟨.l105100, RegMap.args [(0, 57), (1, 59), (2, 77), (3, 3), (4, 82), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l10235c, kept := #v[], arity := rfl, guard := some (Fin.last 84) }))))

def bytes_l1022f9_1 : List UInt8 :=
  [0xE8, 0xA4, 0x2D, 0x00, 0x00]

theorem code_l1022f9_1 : ∀ x ∈ codeRange 0x102357 bytes_l1022f9_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2357 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1022f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1022f9 (movR64R64Effect 0x1022f9 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 54) (.exec 0x1022f9 (fun s => s.RIP = 0x1022f9) (movR64R64Effect 0x1022f9 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x1022fc (movR64R64Effect 0x1022fc 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 56) (.exec 0x1022fc (fun s => s.RIP = 0x1022fc) (movR64R64Effect 0x1022fc 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x1022ff (movR32M32LowEffect 0x1022ff 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 58) (.exec 0x1022ff (LoadPre 0x1022ff (fun s => AddrMode.addr (.base 6 .none) s (0x1022ff + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x1022ff 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x102301 (movR32M32LowEffect 0x102301 1 (.base 6 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 60) (.exec 0x102301 (LoadPre 0x102301 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x102301 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102301 1 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.exec 0x102304 (StorePre 0x102304 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102304 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102304 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 62) (.out 0x102309 (movR32M32LowEffect 0x102309 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 63) (.exec 0x102309 (LoadPre 0x102309 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102309 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102309 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.exec 0x10230c (StorePre 0x10230c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10230c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10230c (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x102318 (StorePre 0x102318 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102318 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102318 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x102321 (leaR64Effect 0x102321 6 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 67) (.exec 0x102321 (fun s => s.RIP = 0x102321) (leaR64Effect 0x102321 6 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 68) (.exec 0x102325 (StorePre 0x102325 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102325 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102325 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 69) (.exec 0x102329 (StorePre 0x102329 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102329 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102329 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x10232d (StorePre 0x10232d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10232d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10232d 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 71) (.exec 0x102331 (StorePre 0x102331 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x102331 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102331 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 72) (.exec 0x102335 (StorePre 0x102335 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102335 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102335 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 73) (.exec 0x102339 (StorePre 0x102339 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102339 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102339 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 74) (.exec 0x10233d (StorePre 0x10233d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10233d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x10233d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x102345 (leaR64Effect 0x102345 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x102345 (fun s => s.RIP = 0x102345) (leaR64Effect 0x102345 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x10234a (leaR64Effect 0x10234a 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 78) (.exec 0x10234a (fun s => s.RIP = 0x10234a) (leaR64Effect 0x10234a 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10234f (StorePre 0x10234f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10234f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10234f 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 80) (.out 0x102354 (movR64R64Effect 0x102354 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[8]
    (.letOp (n := 81) (.exec 0x102354 (fun s => s.RIP = 0x102354) (movR64R64Effect 0x102354 15 8) (Reg.operands [.gpr 8] [])) #v[8]
    (b_l1022f9_1)))))))))))))))))))))))))))))

def bytes_l1022f9 : List UInt8 :=
  [0x4D, 0x89, 0xCD, 0x49, 0x89, 0xFC, 0x8B, 0x06, 0x8B, 0x4E, 0x04, 0x48, 0x89, 0x54, 0x24, 0x50,
    0x8B, 0x56, 0x08, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x77, 0x20, 0x89, 0x44, 0x24, 0x3C,
    0x89, 0x44, 0x24, 0x10, 0x89, 0x4C, 0x24, 0x38, 0x89, 0x4C, 0x24, 0x14, 0x89, 0x54, 0x24, 0x34,
    0x89, 0x54, 0x24, 0x18, 0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01, 0x48, 0x8D, 0x7C, 0x24,
    0x78, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0x74, 0x24, 0x48, 0x4D, 0x89, 0xC7] ++ bytes_l1022f9_1

theorem code_l1022f9 : ∀ x ∈ codeRange 0x1022f9 bytes_l1022f9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x22f9 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1022f9_1

@[cfg_block] def b_l10235c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10235c (StorePre 0x10235c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10235c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10235c 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.out 0x102361 (movR64M64Effect 0x102361 9 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 55) (.exec 0x102361 (LoadPre 0x102361 (fun s => AddrMode.addr (.base 15 .none) s (0x102361 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102361 9 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.exec 0x102364 (StorePre 0x102364 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102364 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102364 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 57) (.out 0x102368 (leaR64Effect 0x102368 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x102368 (fun s => s.RIP = 0x102368) (leaR64Effect 0x102368 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102370 (movR64R64Effect 0x102370 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 60) (.exec 0x102370 (fun s => s.RIP = 0x102370) (movR64R64Effect 0x102370 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x102373 (leaR64Effect 0x102373 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x102373 (fun s => s.RIP = 0x102373) (leaR64Effect 0x102373 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x102378 (movR64M64Effect 0x102378 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x102378 (LoadPre 0x102378 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102378 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102378 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10237d (movR64R64Effect 0x10237d 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 66) (.exec 0x10237d (fun s => s.RIP = 0x10237d) (movR64R64Effect 0x10237d 8 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.out 0x102380 (movR64R64Effect 0x102380 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 68) (.exec 0x102380 (fun s => s.RIP = 0x102380) (movR64R64Effect 0x102380 12 9) (Reg.operands [.gpr 9] [])) #v[54]
    (.letOp (n := 69) (.out 0x102383 (callEffect (fun _ => 0x101800) 0x102388) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x102383 (PushPre 0x102383 5) (callEffect (fun _ => 0x101800) 0x102388) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x102388⟩) #v[]
    (.terminate (.call ⟨.l101800, RegMap.args [(1, 63), (2, 61), (3, 3), (4, 69), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l102388, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l10235c : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x40, 0x4D, 0x8B, 0x0F, 0x4C, 0x89, 0x34, 0x24, 0x48, 0x8D, 0xBC, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0x48, 0x8D, 0x54, 0x24, 0x78, 0x48, 0x8B, 0x4C, 0x24,
    0x50, 0x49, 0x89, 0xE8, 0x4D, 0x89, 0xCC, 0xE8, 0x78, 0xF4, 0xFF, 0xFF]

theorem code_l10235c : ∀ x ∈ codeRange 0x10235c bytes_l10235c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x235c 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102388_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x1023d6 (leaR64Effect 0x1023d6 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 96) (.exec 0x1023d6 (fun s => s.RIP = 0x1023d6) (leaR64Effect 0x1023d6 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x1023db (cmpM8Imm8Effect 0x1023db 5 (.sib 4 none 0 (.d8 0x10)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 98) (.exec 0x1023db (LoadPre 0x1023db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1023db + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x1023db 5 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x1023e0 (atFlags (condHolds 4) (setccR8Effect 0x1023e0 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[95, 97]
    (.letOp (n := 100) (.exec 0x1023e0 (fun s => s.RIP = 0x1023e0) (atFlags (condHolds 4) (setccR8Effect 0x1023e0 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[95, 97]
    (.letOp (n := 101) (.pure (condOp 4)) #v[97]
    (.terminate (.condBr (Fin.last 101) ⟨.l102501, RegMap.args [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 102⟩ ⟨.l1023e9, RegMap.args [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 102⟩))))))))

def bytes_l102388_1 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x10, 0x80, 0x7C, 0x24, 0x10, 0x00, 0x0F, 0x94, 0xC0, 0x0F, 0x84, 0x18,
    0x01, 0x00, 0x00]

theorem code_l102388_1 : ∀ x ∈ codeRange 0x1023d6 bytes_l102388_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x23d6 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102388 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102388 (movR64M64Effect 0x102388 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x102388 (LoadPre 0x102388 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x102388 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102388 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102390 (movR64M64Effect 0x102390 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x102390 (LoadPre 0x102390 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x102390 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102390 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102398 (movR64M64Effect 0x102398 7 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 58) (.exec 0x102398 (LoadPre 0x102398 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x102398 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102398 7 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10239c (movR64M64Effect 0x10239c 8 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 60) (.exec 0x10239c (LoadPre 0x10239c (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x10239c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10239c 8 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x1023a0 (xorR32R32Effect 0x1023a0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 62) (.exec 0x1023a0 (fun s => s.RIP = 0x1023a0) (xorR32R32Effect 0x1023a0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 63) (.out 0x1023a2 (movR16Imm16Effect 0x1023a2 4 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 64) (.exec 0x1023a2 (fun s => s.RIP = 0x1023a2) (movR16Imm16Effect 0x1023a2 4 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x1023a6 (movR16Imm16Effect 0x1023a6 5 9 0x1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 66) (.exec 0x1023a6 (fun s => s.RIP = 0x1023a6) (movR16Imm16Effect 0x1023a6 5 9 0x1) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 67) (.out 0x1023ab (xorR64R64Effect 0x1023ab 2 7) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 7] []) (.flag .ZF)) #v[53, 57]
    (.letOp (n := 68) (.exec 0x1023ab (fun s => s.RIP = 0x1023ab) (xorR64R64Effect 0x1023ab 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[53, 57]
    (.letOp (n := 69) (.out 0x1023ae (atFlags (condHolds 5) (cmovR64R64Effect 0x1023ae 4 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[65, 61, 67]
    (.letOp (n := 70) (.exec 0x1023ae (fun s => s.RIP = 0x1023ae) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023ae 4 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 61, 67]
    (.letOp (n := 71) (.out 0x1023b2 (movzxR32R8Effect 0x1023b2 4 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x1023b2 (fun s => s.RIP = 0x1023b2) (movzxR32R8Effect 0x1023b2 4 2 9) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x1023b6 (xorR64R64Effect 0x1023b6 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 59]
    (.letOp (n := 74) (.out 0x1023b6 (xorR64R64Effect 0x1023b6 6 8) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 8] []) (.flag .ZF)) #v[55, 59]
    (.letOp (n := 75) (.exec 0x1023b6 (fun s => s.RIP = 0x1023b6) (xorR64R64Effect 0x1023b6 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 59]
    (.letOp (n := 76) (.out 0x1023b9 (atFlags (condHolds 5) (cmovR64R64Effect 0x1023b9 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[71, 61, 74]
    (.letOp (n := 77) (.exec 0x1023b9 (fun s => s.RIP = 0x1023b9) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023b9 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 61, 74]
    (.letOp (n := 78) (.out 0x1023bd (movzxR32R8Effect 0x1023bd 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[76]
    (.letOp (n := 79) (.exec 0x1023bd (fun s => s.RIP = 0x1023bd) (movzxR32R8Effect 0x1023bd 3 2 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 80) (.out 0x1023c0 (xorR32R32Effect 0x1023c0 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[73, 73]
    (.letOp (n := 81) (.exec 0x1023c0 (fun s => s.RIP = 0x1023c0) (xorR32R32Effect 0x1023c0 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[73, 73]
    (.letOp (n := 82) (.out 0x1023c2 (xorR64R64Effect 0x1023c2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[80, 61]
    (.letOp (n := 83) (.out 0x1023c2 (xorR64R64Effect 0x1023c2 6 0) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 0] []) (.flag .ZF)) #v[80, 61]
    (.letOp (n := 84) (.exec 0x1023c2 (fun s => s.RIP = 0x1023c2) (xorR64R64Effect 0x1023c2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[80, 61]
    (.letOp (n := 85) (.out 0x1023c5 (atFlags (condHolds 5) (cmovR64R64Effect 0x1023c5 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[78, 61, 83]
    (.letOp (n := 86) (.exec 0x1023c5 (fun s => s.RIP = 0x1023c5) (atFlags (condHolds 5) (cmovR64R64Effect 0x1023c5 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[78, 61, 83]
    (.letOp (n := 87) (.out 0x1023c9 (movzxR32R8Effect 0x1023c9 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[85]
    (.letOp (n := 88) (.exec 0x1023c9 (fun s => s.RIP = 0x1023c9) (movzxR32R8Effect 0x1023c9 3 2 2) (Reg.operands [.gpr 2] [])) #v[85]
    (.letOp (n := 89) (.out 0x1023cc (xorR16R16Effect 0x1023cc 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[87, 63]
    (.letOp (n := 90) (.out 0x1023cc (xorR16R16Effect 0x1023cc 3 2 1) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[87, 63]
    (.letOp (n := 91) (.exec 0x1023cc (fun s => s.RIP = 0x1023cc) (xorR16R16Effect 0x1023cc 3 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[87, 63]
    (.letOp (n := 92) (.out 0x1023cf (atFlags (condHolds 4) (cmovR32R32Effect 0x1023cf 3 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 63, 90]
    (.letOp (n := 93) (.exec 0x1023cf (fun s => s.RIP = 0x1023cf) (atFlags (condHolds 4) (cmovR32R32Effect 0x1023cf 3 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 63, 90]
    (.letOp (n := 94) (.exec 0x1023d2 (StorePre 0x1023d2 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1023d2 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1023d2 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (b_l102388_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l102388 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x49, 0x8B, 0x7D, 0x00, 0x4D, 0x8B, 0x45, 0x08, 0x31, 0xC0, 0x66, 0xB9, 0x01, 0x00, 0x66, 0x41,
    0xB9, 0x01, 0x00, 0x48, 0x31, 0xFA, 0x4C, 0x0F, 0x45, 0xC8, 0x41, 0x0F, 0xB6, 0xD1, 0x4C, 0x31,
    0xC6, 0x48, 0x0F, 0x45, 0xD0, 0x0F, 0xB6, 0xD2, 0x31, 0xF6, 0x48, 0x31, 0xC6, 0x48, 0x0F, 0x45,
    0xD0, 0x0F, 0xB6, 0xD2, 0x66, 0x31, 0xCA, 0x0F, 0x44, 0xC1, 0x88, 0x44, 0x24, 0x10] ++ bytes_l102388_1

theorem code_l102388 : ∀ x ∈ codeRange 0x102388 bytes_l102388, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2388 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102388_1

@[cfg_block] def b_l1023e9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1023e9 (movR64M64Effect 0x1023e9 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1023e9 (LoadPre 0x1023e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1023e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1023e9 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1023ee (StorePre 0x1023ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1023ee + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1023ee 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1023f3 (leaR64Effect 0x1023f3 15 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 57) (.exec 0x1023f3 (fun s => s.RIP = 0x1023f3) (leaR64Effect 0x1023f3 15 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1023f8 (movR32M32LowEffect 0x1023f8 1 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x1023f8 (LoadPre 0x1023f8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1023f8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1023f8 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1023fc (StorePre 0x1023fc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1023fc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1023fc 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x102400 (movR32M32LowEffect 0x102400 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x102400 (LoadPre 0x102400 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102400 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102400 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x102404 (StorePre 0x102404 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x102404 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102404 1 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x102408 (movR32M32LowEffect 0x102408 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x102408 (LoadPre 0x102408 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102408 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102408 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10240c (StorePre 0x10240c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10240c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10240c 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x102410 (movR64Imm64Effect 0x102410 1 0x100000001) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 68) (.exec 0x102410 (fun s => s.RIP = 0x102410) (movR64Imm64Effect 0x102410 1 0x100000001) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.exec 0x10241a (StorePre 0x10241a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10241a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10241a 1 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x10241f (cmpR64Imm8Effect 0x10241f 14 0x11) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 71) (.exec 0x10241f (fun s => s.RIP = 0x10241f) (cmpR64Imm8Effect 0x10241f 14 0x11) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.pure (condOp 2)) #v[70]
    (.terminate (.condBr (Fin.last 72) ⟨.l10247c, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l102425, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l1023e9 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x4C, 0x8D, 0x7C, 0x24, 0x60, 0x8B,
    0x4C, 0x24, 0x3C, 0x89, 0x4C, 0x24, 0x60, 0x8B, 0x4C, 0x24, 0x38, 0x89, 0x4C, 0x24, 0x64, 0x8B,
    0x4C, 0x24, 0x34, 0x89, 0x4C, 0x24, 0x68, 0x48, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x4C, 0x24, 0x6C, 0x49, 0x83, 0xFE, 0x11, 0x72, 0x57]

theorem code_l1023e9 : ∀ x ∈ codeRange 0x1023e9 bytes_l1023e9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x23e9 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102425 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102425 (movR64R64Effect 0x102425 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 54) (.exec 0x102425 (fun s => s.RIP = 0x102425) (movR64R64Effect 0x102425 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x102428 (shrR64Effect 0x102428 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x102428 (fun s => s.RIP = 0x102428) (shrR64Effect 0x102428 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10242c (movR64M64Effect 0x10242c 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10242c (LoadPre 0x10242c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10242c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10242c 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102431 (movR64M64Effect 0x102431 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x102431 (LoadPre 0x102431 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102431 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102431 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x102435 (addR64Imm8Effect 0x102435 3 0x10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 62) (.exec 0x102435 (fun s => s.RIP = 0x102435) (addR64Imm8Effect 0x102435 3 0x10) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x102439 (andR64R64Effect 0x102439 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[61, 14]
    (.letOp (n := 64) (.exec 0x102439 (fun s => s.RIP = 0x102439) (andR64R64Effect 0x102439 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[61, 14]
    (.letOp (n := 65) (.out 0x10243c (andR32Imm8Effect 0x10243c 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x10243c (fun s => s.RIP = 0x10243c) (andR32Imm8Effect 0x10243c 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x102440 (leaR64Effect 0x102440 13 (.sib 12 (some 3) 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12, .gpr 3] []) (.reg (.gpr 13))) #v[12, 63]
    (.letOp (n := 68) (.exec 0x102440 (fun s => s.RIP = 0x102440) (leaR64Effect 0x102440 13 (.sib 12 (some 3) 0 .none)) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 63]
    (.letOp (n := 69) (.out 0x102444 (addR64R64Effect 0x102444 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[63, 59]
    (.letOp (n := 70) (.exec 0x102444 (fun s => s.RIP = 0x102444) (addR64R64Effect 0x102444 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[63, 59]
    (.letOp (n := 71) (.exec 0x102447 (StorePre 0x102447 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102447 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102447 3 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 6] [])) #v[69, 57]
    (.letOp (n := 72) (.exec 0x10244b (StorePre 0x10244b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10244b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10244b 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 73) (.exec 0x102450 (StorePre 0x102450 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102450 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102450 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 74) (.exec 0x102455 (StorePre 0x102455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102455 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102455 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 75) (.exec 0x10245a (StorePre 0x10245a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10245a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10245a 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 76) (.out 0x10245f (leaR64Effect 0x10245f 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 77) (.exec 0x10245f (fun s => s.RIP = 0x10245f) (leaR64Effect 0x10245f 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x102464 (leaR64Effect 0x102464 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 79) (.exec 0x102464 (fun s => s.RIP = 0x102464) (leaR64Effect 0x102464 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x102469 (movR32R32Effect 0x102469 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[0]
    (.letOp (n := 81) (.exec 0x102469 (fun s => s.RIP = 0x102469) (movR32R32Effect 0x102469 2 3 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 82) (.out 0x10246b (callEffect (fun _ => 0x107050) 0x102470) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 83) (.exec 0x10246b (PushPre 0x10246b 5) (callEffect (fun _ => 0x107050) 0x102470) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.const ⟨64, 0x102470⟩) #v[]
    (.terminate (.call ⟨.l107050, RegMap.args [(0, 0), (1, 55), (2, 59), (3, 80), (4, 82), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l102470, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l102425 : List UInt8 :=
  [0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x8B, 0x56, 0x08,
    0x48, 0x83, 0xC3, 0x10, 0x4C, 0x21, 0xF3, 0x41, 0x83, 0xE6, 0x0F, 0x4D, 0x8D, 0x2C, 0x1C, 0x48,
    0x01, 0xD3, 0x48, 0x89, 0x5E, 0x08, 0x4C, 0x89, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0x64, 0x24, 0x18,
    0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x58, 0x48,
    0x8D, 0x74, 0x24, 0x10, 0x89, 0xC3, 0xE8, 0xE0, 0x4B, 0x00, 0x00]

theorem code_l102425 : ∀ x ∈ codeRange 0x102425 bytes_l102425, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2425 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102470 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102470 (movR32R32Effect 0x102470 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x102470 (fun s => s.RIP = 0x102470) (movR32R32Effect 0x102470 2 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x102472 (testR64R64Effect 0x102472 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x102472 (fun s => s.RIP = 0x102472) (testR64R64Effect 0x102472 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l102484, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l102477, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l102470 : List UInt8 :=
  [0x89, 0xD8, 0x4D, 0x85, 0xF6, 0x75, 0x0D]

theorem code_l102470 : ∀ x ∈ codeRange 0x102470 bytes_l102470, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2470 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102477 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l102501, RegMap.args (entryMap (live .l102477)) 53⟩)

def bytes_l102477 : List UInt8 :=
  [0xE9, 0x85, 0x00, 0x00, 0x00]

theorem code_l102477 : ∀ x ∈ codeRange 0x102477 bytes_l102477, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2477 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10247c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10247c (movR64R64Effect 0x10247c 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 54) (.exec 0x10247c (fun s => s.RIP = 0x10247c) (movR64R64Effect 0x10247c 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x10247f (testR64R64Effect 0x10247f 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x10247f (fun s => s.RIP = 0x10247f) (testR64R64Effect 0x10247f 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l102501, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l102484, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10247c : List UInt8 :=
  [0x4D, 0x89, 0xE5, 0x4D, 0x85, 0xF6, 0x74, 0x7D]

theorem code_l10247c : ∀ x ∈ codeRange 0x10247c bytes_l10247c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x247c 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102484 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102484 (movR32Imm32Effect 0x102484 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x102484 (fun s => s.RIP = 0x102484) (movR32Imm32Effect 0x102484 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x102489 (subR64R64Effect 0x102489 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x102489 (fun s => s.RIP = 0x102489) (subR64R64Effect 0x102489 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x10248c (xorR32R32Effect 0x10248c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x10248c (fun s => s.RIP = 0x10248c) (xorR32R32Effect 0x10248c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x10248e (cmpR64Imm8Effect 0x10248e 14 0x10) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 60) (.exec 0x10248e (fun s => s.RIP = 0x10248e) (cmpR64Imm8Effect 0x10248e 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x102492 (atFlags (condHolds 2) (cmovR64R64Effect 0x102492 4 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[57, 55, 59]
    (.letOp (n := 62) (.exec 0x102492 (fun s => s.RIP = 0x102492) (atFlags (condHolds 2) (cmovR64R64Effect 0x102492 4 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 55, 59]
    (.letOp (n := 63) (.out 0x102496 (leaR64Effect 0x102496 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 64) (.exec 0x102496 (fun s => s.RIP = 0x102496) (leaR64Effect 0x102496 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 65) (.out 0x10249a (addR64Imm32Effect 0x10249a 7 0x98) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x10249a (fun s => s.RIP = 0x10249a) (addR64Imm32Effect 0x10249a 7 0x98) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x1024a1 (xorR32R32Effect 0x1024a1 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x1024a1 (fun s => s.RIP = 0x1024a1) (xorR32R32Effect 0x1024a1 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x1024a3 (movR32R32Effect 0x1024a3 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[0]
    (.letOp (n := 70) (.exec 0x1024a3 (fun s => s.RIP = 0x1024a3) (movR32R32Effect 0x1024a3 2 5 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 71) (.out 0x1024a5 (callEffect (callMemPtr 0x1024a5 (.rip 0xfed7d)) (0x1024a5 + BitVec.ofNat 64 (callMemLen (.rip 0xfed7d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x1024a5 (GoesTo (CallMemPre 0x1024a5 (.rip 0xfed7d)) (callEffect (callMemPtr 0x1024a5 (.rip 0xfed7d)) (0x1024a5 + BitVec.ofNat 64 (callMemLen (.rip 0xfed7d)))) 0x103eb0) (callEffect (callMemPtr 0x1024a5 (.rip 0xfed7d)) (0x1024a5 + BitVec.ofNat 64 (callMemLen (.rip 0xfed7d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x1024ab⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 0), (1, 55), (2, 61), (3, 3), (4, 71), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l1024ab, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l102484 : List UInt8 :=
  [0xB9, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF1, 0x31, 0xD2, 0x49, 0x83, 0xFE, 0x10, 0x48, 0x0F,
    0x42, 0xD1, 0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x81, 0xC7, 0x98, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x89,
    0xC5, 0xFF, 0x15, 0x7D, 0xED, 0x0F, 0x00]

theorem code_l102484 : ∀ x ∈ codeRange 0x102484 bytes_l102484, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2484 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1024ab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1024ab (leaR64Effect 0x1024ab 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1024ab (fun s => s.RIP = 0x1024ab) (leaR64Effect 0x1024ab 3 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1024b3 (leaR64Effect 0x1024b3 12 (.rip 0x1a46)) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 56) (.exec 0x1024b3 (fun s => s.RIP = 0x1024b3) (leaR64Effect 0x1024b3 12 (.rip 0x1a46)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1024ba (movR64R64Effect 0x1024ba 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x1024ba (fun s => s.RIP = 0x1024ba) (movR64R64Effect 0x1024ba 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x1024bd (movR64R64Effect 0x1024bd 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 60) (.exec 0x1024bd (fun s => s.RIP = 0x1024bd) (movR64R64Effect 0x1024bd 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x1024c0 (movR64R64Effect 0x1024c0 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 62) (.exec 0x1024c0 (fun s => s.RIP = 0x1024c0) (movR64R64Effect 0x1024c0 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x1024c3 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024c6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 55]
    (.letOp (n := 64) (.exec 0x1024c3 (GoesTo (CallPre 0x1024c3 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024c6) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024c6) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 55]
    (.letOp (n := 65) (.const ⟨64, 0x1024c6⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 61), (3, 53), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1024c6, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1024ab : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x25, 0x46, 0x1A, 0x00, 0x00, 0x48,
    0x89, 0xDF, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xF2, 0x41, 0xFF, 0xD4]

theorem code_l1024ab : ∀ x ∈ codeRange 0x1024ab bytes_l1024ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ab 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1024c6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1024c6 (StorePre 0x1024c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1024c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024c6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.exec 0x1024cb (StorePre 0x1024cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1024cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024cb 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 55) (.exec 0x1024d0 (StorePre 0x1024d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1024d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1024d0 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.exec 0x1024d5 (StorePre 0x1024d5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1024d5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1024d5 (.sib 4 none 0 (.d8 0x28)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1024de (leaR64Effect 0x1024de 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1024de (fun s => s.RIP = 0x1024de) (leaR64Effect 0x1024de 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1024e3 (leaR64Effect 0x1024e3 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1024e3 (fun s => s.RIP = 0x1024e3) (leaR64Effect 0x1024e3 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1024e8 (callEffect (fun _ => 0x107050) 0x1024ed) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1024e8 (PushPre 0x1024e8 5) (callEffect (fun _ => 0x107050) 0x1024ed) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1024ed⟩) #v[]
    (.terminate (.call ⟨.l107050, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1024ed, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1024c6 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0x5C, 0x24, 0x20, 0x48,
    0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x58, 0x48, 0x8D, 0x74,
    0x24, 0x10, 0xE8, 0x63, 0x4B, 0x00, 0x00]

theorem code_l1024c6 : ∀ x ∈ codeRange 0x1024c6 bytes_l1024c6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24c6 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1024ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1024ed (movR64M64Effect 0x1024ed 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1024ed (LoadPre 0x1024ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1024ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1024ed 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1024f2 (movR64M64Effect 0x1024f2 7 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1024f2 (LoadPre 0x1024f2 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x1024f2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1024f2 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1024f6 (movR64R64Effect 0x1024f6 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x1024f6 (fun s => s.RIP = 0x1024f6) (movR64R64Effect 0x1024f6 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x1024f9 (movR64R64Effect 0x1024f9 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x1024f9 (fun s => s.RIP = 0x1024f9) (movR64R64Effect 0x1024f9 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1024fc (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024ff) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 62) (.exec 0x1024fc (GoesTo (CallPre 0x1024fc 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024ff) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x1024ff) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 63) (.const ⟨64, 0x1024ff⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 53), (2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1024ff, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1024ed : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x78, 0x08, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xF2, 0x41,
    0xFF, 0xD4]

theorem code_l1024ed : ∀ x ∈ codeRange 0x1024ed bytes_l1024ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ed 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1024ff : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1024ff (movR32R32Effect 0x1024ff 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x1024ff (fun s => s.RIP = 0x1024ff) (movR32R32Effect 0x1024ff 2 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l102501, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1024ff : List UInt8 :=
  [0x89, 0xE8]

theorem code_l1024ff : ∀ x ∈ codeRange 0x1024ff bytes_l1024ff, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x24ff 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102501 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102501 (addR64Imm32Effect 0x102501 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x102501 (fun s => s.RIP = 0x102501) (addR64Imm32Effect 0x102501 4 0xa8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102508 (popR64Effect 0x102508 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x102508 (popR64Effect 0x102508 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x102508 (PopPre 0x102508) (popR64Effect 0x102508 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x102509 (popR64Effect 0x102509 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x102509 (popR64Effect 0x102509 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x102509 (PopPre 0x102509) (popR64Effect 0x102509 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10250b (popR64Effect 0x10250b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10250b (popR64Effect 0x10250b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10250b (PopPre 0x10250b) (popR64Effect 0x10250b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10250d (popR64Effect 0x10250d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10250d (popR64Effect 0x10250d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10250d (PopPre 0x10250d) (popR64Effect 0x10250d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x10250f (popR64Effect 0x10250f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x10250f (popR64Effect 0x10250f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10250f (PopPre 0x10250f) (popR64Effect 0x10250f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x102511 (popR64Effect 0x102511 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x102511 (popR64Effect 0x102511 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x102511 (PopPre 0x102511) (popR64Effect 0x102511 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x102512 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x102512 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x102512 (RetPre 0x102512) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l102501 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l102501 : ∀ x ∈ codeRange 0x102501 bytes_l102501, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2501 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102520 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102520 (pushR64Effect 0x102520 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x102520 (PushPre 0x102520 1) (pushR64Effect 0x102520 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x102521 (pushR64Effect 0x102521 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x102521 (PushPre 0x102521 2) (pushR64Effect 0x102521 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x102523 (pushR64Effect 0x102523 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x102523 (PushPre 0x102523 2) (pushR64Effect 0x102523 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x102525 (pushR64Effect 0x102525 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x102525 (PushPre 0x102525 2) (pushR64Effect 0x102525 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x102527 (pushR64Effect 0x102527 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x102527 (PushPre 0x102527 2) (pushR64Effect 0x102527 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x102529 (pushR64Effect 0x102529 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x102529 (PushPre 0x102529 1) (pushR64Effect 0x102529 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10252a (subR64Imm32Effect 0x10252a 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10252a (fun s => s.RIP = 0x10252a) (subR64Imm32Effect 0x10252a 4 0x98) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x102531 (movR64R64Effect 0x102531 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x102531 (fun s => s.RIP = 0x102531) (movR64R64Effect 0x102531 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x102534 (movR64Imm64Effect 0x102534 0 0xfffffffe0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 70) (.exec 0x102534 (fun s => s.RIP = 0x102534) (movR64Imm64Effect 0x102534 0 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10253e (movR64M64Effect 0x10253e 12 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[9]
    (.letOp (n := 72) (.exec 0x10253e (LoadPre 0x10253e (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10253e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10253e 12 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 73) (.out 0x102542 (cmpR64R64Effect 0x102542 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 74) (.out 0x102542 (cmpR64R64Effect 0x102542 12 0) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 0] []) (.flag .ZF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x102542 (fun s => s.RIP = 0x102542) (cmpR64R64Effect 0x102542 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[71, 69]
    (.letOp (n := 76) (.out 0x102545 (atFlags (condHolds 7) (setccR8Effect 0x102545 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[69, 73, 74]
    (.letOp (n := 77) (.exec 0x102545 (fun s => s.RIP = 0x102545) (atFlags (condHolds 7) (setccR8Effect 0x102545 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[69, 73, 74]
    (.letOp (n := 78) (.out 0x102548 (movR64R64Effect 0x102548 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[8]
    (.letOp (n := 79) (.exec 0x102548 (fun s => s.RIP = 0x102548) (movR64R64Effect 0x102548 7 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 80) (.out 0x10254b (shrR64Effect 0x10254b 4 7 61) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.out 0x10254b (shrR64Effect 0x10254b 4 7 61) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[78]
    (.letOp (n := 82) (.exec 0x10254b (fun s => s.RIP = 0x10254b) (shrR64Effect 0x10254b 4 7 61) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 83) (.out 0x10254f (atFlags (condHolds 5) (setccR8Effect 0x10254f 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[80, 81]
    (.letOp (n := 84) (.exec 0x10254f (fun s => s.RIP = 0x10254f) (atFlags (condHolds 5) (setccR8Effect 0x10254f 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[80, 81]
    (.letOp (n := 85) (.out 0x102553 (orR8R8Effect 0x102553 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[83, 76]
    (.letOp (n := 86) (.out 0x102553 (orR8R8Effect 0x102553 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[83, 76]
    (.letOp (n := 87) (.exec 0x102553 (fun s => s.RIP = 0x102553) (orR8R8Effect 0x102553 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[83, 76]
    (.letOp (n := 88) (.pure (condOp 4)) #v[86]
    (.terminate (.condBr (Fin.last 88) ⟨.l102560, RegMap.args [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ ⟨.l102558, RegMap.args [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l102520 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x48, 0xB8, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4D, 0x8B,
    0x61, 0x10, 0x49, 0x39, 0xC4, 0x0F, 0x97, 0xC0, 0x4C, 0x89, 0xC7, 0x48, 0xC1, 0xEF, 0x3D, 0x40,
    0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x08]

theorem code_l102520 : ∀ x ∈ codeRange 0x102520 bytes_l102520, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2520 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102558 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102558 (StorePre 0x102558 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102558 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102558 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10270a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l102558 : List UInt8 :=
  [0xC6, 0x03, 0x01, 0xE9, 0xAA, 0x01, 0x00, 0x00]

theorem code_l102558 : ∀ x ∈ codeRange 0x102558 bytes_l102558, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2558 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102560 (movR64R64Effect 0x102560 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[9]
    (.letOp (n := 54) (.exec 0x102560 (fun s => s.RIP = 0x102560) (movR64R64Effect 0x102560 14 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.exec 0x102563 (StorePre 0x102563 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x102563 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102563 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.exec 0x102568 (StorePre 0x102568 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x102568 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102568 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 57) (.exec 0x10256d (StorePre 0x10256d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10256d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10256d 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 58) (.out 0x102572 (movR32M32Effect 0x102572 13 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 59) (.exec 0x102572 (LoadPre 0x102572 (fun s => AddrMode.addr (.base 2 .none) s (0x102572 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x102572 13 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 60) (.out 0x102575 (movR32M32Effect 0x102575 15 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 61) (.exec 0x102575 (LoadPre 0x102575 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x102575 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x102575 15 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 62) (.out 0x102579 (movR32M32LowEffect 0x102579 3 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 63) (.exec 0x102579 (LoadPre 0x102579 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x102579 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102579 3 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 64) (.exec 0x10257c (StorePre 0x10257c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10257c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10257c (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x102588 (StorePre 0x102588 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102588 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102588 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x102591 (StorePre 0x102591 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102591 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102591 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 67) (.out 0x102596 (leaR64Effect 0x102596 5 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 68) (.exec 0x102596 (fun s => s.RIP = 0x102596) (leaR64Effect 0x102596 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x10259a (StorePre 0x10259a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10259a + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10259a 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 70) (.exec 0x10259f (StorePre 0x10259f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x10259f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x10259f 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 71) (.exec 0x1025a4 (StorePre 0x1025a4 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1025a4 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1025a4 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 72) (.exec 0x1025a8 (StorePre 0x1025a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1025a8 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x1025a8 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x1025b0 (leaR64Effect 0x1025b0 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x1025b0 (fun s => s.RIP = 0x1025b0) (leaR64Effect 0x1025b0 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1025b5 (leaR64Effect 0x1025b5 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x1025b5 (fun s => s.RIP = 0x1025b5) (leaR64Effect 0x1025b5 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1025ba (movR64R64Effect 0x1025ba 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 78) (.exec 0x1025ba (fun s => s.RIP = 0x1025ba) (movR64R64Effect 0x1025ba 6 5) (Reg.operands [.gpr 5] [])) #v[67]
    (.letOp (n := 79) (.out 0x1025bd (callEffect (fun _ => 0x105100) 0x1025c2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x1025bd (PushPre 0x1025bd 5) (callEffect (fun _ => 0x105100) 0x1025c2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x1025c2⟩) #v[]
    (.terminate (.call ⟨.l105100, RegMap.args [(1, 1), (2, 75), (3, 62), (4, 79), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l1025c2, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l102560 : List UInt8 :=
  [0x4D, 0x89, 0xCE, 0x48, 0x89, 0x5C, 0x24, 0x58, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x4C, 0x89, 0x44,
    0x24, 0x70, 0x44, 0x8B, 0x2A, 0x44, 0x8B, 0x7A, 0x04, 0x8B, 0x5A, 0x08, 0x48, 0xC7, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x74, 0x24, 0x60, 0x48, 0x8D, 0x6E, 0x20, 0x44, 0x89, 0x6C, 0x24, 0x10, 0x44,
    0x89, 0x7C, 0x24, 0x14, 0x89, 0x5C, 0x24, 0x18, 0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01,
    0x48, 0x8D, 0x7C, 0x24, 0x78, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0xEE, 0xE8, 0x3E, 0x2B,
    0x00, 0x00]

theorem code_l102560 : ∀ x ∈ codeRange 0x102560 bytes_l102560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2560 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1025c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1025c2 (StorePre 0x1025c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1025c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1025c2 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 54) (.out 0x1025c7 (movR64R64Effect 0x1025c7 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[12]
    (.letOp (n := 55) (.exec 0x1025c7 (fun s => s.RIP = 0x1025c7) (movR64R64Effect 0x1025c7 5 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 56) (.out 0x1025ca (leaR64Effect 0x1025ca 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x1025ca (fun s => s.RIP = 0x1025ca) (leaR64Effect 0x1025ca 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1025cf (StorePre 0x1025cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1025cf + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1025cf 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 59) (.exec 0x1025d4 (StorePre 0x1025d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1025d4 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1025d4 15 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 60) (.exec 0x1025d9 (StorePre 0x1025d9 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1025d9 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1025d9 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 61) (.out 0x1025dd (movR64Imm64Effect 0x1025dd 0 0x100000001) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x1025dd (fun s => s.RIP = 0x1025dd) (movR64Imm64Effect 0x1025dd 0 0x100000001) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x1025e7 (StorePre 0x1025e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1025e7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1025e7 0 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1025ec (movR64M64Effect 0x1025ec 15 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 65) (.exec 0x1025ec (LoadPre 0x1025ec (fun s => AddrMode.addr (.base 14 .none) s (0x1025ec + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1025ec 15 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x1025ef (movR64M64Effect 0x1025ef 13 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 67) (.exec 0x1025ef (LoadPre 0x1025ef (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x1025ef + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1025ef 13 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.out 0x1025f3 (cmpR64Imm8Effect 0x1025f3 12 0x11) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[12]
    (.letOp (n := 69) (.exec 0x1025f3 (fun s => s.RIP = 0x1025f3) (cmpR64Imm8Effect 0x1025f3 12 0x11) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.pure (condOp 2)) #v[68]
    (.terminate (.condBr (Fin.last 70) ⟨.l10264f, RegMap.args [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l1025f9, RegMap.args [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l1025c2 : List UInt8 :=
  [0x48, 0x89, 0x6C, 0x24, 0x30, 0x4C, 0x89, 0xE5, 0x48, 0x8D, 0x4C, 0x24, 0x38, 0x44, 0x89, 0x6C,
    0x24, 0x38, 0x44, 0x89, 0x7C, 0x24, 0x3C, 0x89, 0x5C, 0x24, 0x40, 0x48, 0xB8, 0x01, 0x00, 0x00,
    0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x44, 0x4D, 0x8B, 0x3E, 0x4D, 0x8B, 0x6E,
    0x08, 0x49, 0x83, 0xFC, 0x11, 0x72, 0x56]

theorem code_l1025c2 : ∀ x ∈ codeRange 0x1025c2 bytes_l1025c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25c2 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1025f9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1025f9 (movR64R64Effect 0x1025f9 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x1025f9 (fun s => s.RIP = 0x1025f9) (movR64R64Effect 0x1025f9 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x1025fc (shrR64Effect 0x1025fc 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1025fc (fun s => s.RIP = 0x1025fc) (shrR64Effect 0x1025fc 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x102600 (movR64Imm64Effect 0x102600 12 0xfffffffe0) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 58) (.exec 0x102600 (fun s => s.RIP = 0x102600) (movR64Imm64Effect 0x102600 12 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10260a (addR64Imm8Effect 0x10260a 12 0x10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x10260a (fun s => s.RIP = 0x10260a) (addR64Imm8Effect 0x10260a 12 0x10) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.out 0x10260e (andR64R64Effect 0x10260e 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[59, 5]
    (.letOp (n := 62) (.exec 0x10260e (fun s => s.RIP = 0x10260e) (andR64R64Effect 0x10260e 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[59, 5]
    (.letOp (n := 63) (.out 0x102611 (movR32R32Effect 0x102611 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[5]
    (.letOp (n := 64) (.exec 0x102611 (fun s => s.RIP = 0x102611) (movR32R32Effect 0x102611 3 14 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 65) (.out 0x102614 (andR32Imm8Effect 0x102614 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.exec 0x102614 (fun s => s.RIP = 0x102614) (andR32Imm8Effect 0x102614 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[63]
    (.letOp (n := 67) (.out 0x102618 (leaR64Effect 0x102618 3 (.sib 15 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15, .gpr 12] []) (.reg (.gpr 3))) #v[15, 61]
    (.letOp (n := 68) (.exec 0x102618 (fun s => s.RIP = 0x102618) (leaR64Effect 0x102618 3 (.sib 15 (some 12) 0 .none)) (Reg.operands [.gpr 15, .gpr 12] [])) #v[15, 61]
    (.letOp (n := 69) (.out 0x10261c (addR64R64Effect 0x10261c 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[61, 13]
    (.letOp (n := 70) (.exec 0x10261c (fun s => s.RIP = 0x10261c) (addR64R64Effect 0x10261c 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[61, 13]
    (.letOp (n := 71) (.exec 0x10261f (StorePre 0x10261f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10261f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10261f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 72) (.exec 0x102624 (StorePre 0x102624 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102624 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102624 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 73) (.exec 0x102629 (StorePre 0x102629 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102629 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102629 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 74) (.exec 0x10262e (StorePre 0x10262e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10262e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10262e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 75) (.out 0x102633 (leaR64Effect 0x102633 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x102633 (fun s => s.RIP = 0x102633) (leaR64Effect 0x102633 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x102638 (leaR64Effect 0x102638 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x102638 (fun s => s.RIP = 0x102638) (leaR64Effect 0x102638 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x10263d (callEffect (fun _ => 0x107050) 0x102642) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x10263d (PushPre 0x10263d 5) (callEffect (fun _ => 0x107050) 0x102642) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x102642⟩) #v[]
    (.terminate (.call ⟨.l107050, RegMap.args [(0, 55), (1, 1), (3, 67), (4, 79), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l102642, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1025f9 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x04, 0x49, 0xBC, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00,
    0x00, 0x49, 0x83, 0xC4, 0x10, 0x49, 0x21, 0xEC, 0x41, 0x89, 0xEE, 0x41, 0x83, 0xE6, 0x0F, 0x4B,
    0x8D, 0x1C, 0x27, 0x4D, 0x01, 0xEC, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x4C, 0x89, 0x7C, 0x24, 0x18,
    0x4C, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x30, 0x48,
    0x8D, 0x74, 0x24, 0x10, 0xE8, 0x0E, 0x4A, 0x00, 0x00]

theorem code_l1025f9 : ∀ x ∈ codeRange 0x1025f9 bytes_l1025f9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25f9 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102642 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102642 (movR64R64Effect 0x102642 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 54) (.exec 0x102642 (fun s => s.RIP = 0x102642) (movR64R64Effect 0x102642 15 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x102645 (testR64R64Effect 0x102645 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x102645 (fun s => s.RIP = 0x102645) (testR64R64Effect 0x102645 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10265e, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10264a, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l102642 : List UInt8 :=
  [0x49, 0x89, 0xDF, 0x4D, 0x85, 0xF6, 0x75, 0x14]

theorem code_l102642 : ∀ x ∈ codeRange 0x102642 bytes_l102642, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2642 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10264a : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1026de, RegMap.args (entryMap (live .l10264a)) 53⟩)

def bytes_l10264a : List UInt8 :=
  [0xE9, 0x8F, 0x00, 0x00, 0x00]

theorem code_l10264a : ∀ x ∈ codeRange 0x10264a bytes_l10264a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x264a 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10264f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10264f (movR64R64Effect 0x10264f 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[13]
    (.letOp (n := 54) (.exec 0x10264f (fun s => s.RIP = 0x10264f) (movR64R64Effect 0x10264f 12 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x102652 (movR64R64Effect 0x102652 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[5]
    (.letOp (n := 56) (.exec 0x102652 (fun s => s.RIP = 0x102652) (movR64R64Effect 0x102652 14 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x102655 (testR64R64Effect 0x102655 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x102655 (fun s => s.RIP = 0x102655) (testR64R64Effect 0x102655 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1026de, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10265e, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l10264f : List UInt8 :=
  [0x4D, 0x89, 0xEC, 0x49, 0x89, 0xEE, 0x4D, 0x85, 0xF6, 0x0F, 0x84, 0x80, 0x00, 0x00, 0x00]

theorem code_l10264f : ∀ x ∈ codeRange 0x10264f bytes_l10264f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x264f 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10265e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10265e (movR32Imm32Effect 0x10265e 5 0 0x10) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x10265e (fun s => s.RIP = 0x10265e) (movR32Imm32Effect 0x10265e 5 0 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x102663 (subR64R64Effect 0x102663 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x102663 (fun s => s.RIP = 0x102663) (subR64R64Effect 0x102663 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x102666 (xorR32R32Effect 0x102666 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x102666 (fun s => s.RIP = 0x102666) (xorR32R32Effect 0x102666 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x102668 (cmpR64Imm8Effect 0x102668 14 0x10) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 60) (.exec 0x102668 (fun s => s.RIP = 0x102668) (cmpR64Imm8Effect 0x102668 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10266c (atFlags (condHolds 2) (cmovR64R64Effect 0x10266c 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[57, 55, 59]
    (.letOp (n := 62) (.exec 0x10266c (fun s => s.RIP = 0x10266c) (atFlags (condHolds 2) (cmovR64R64Effect 0x10266c 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 55, 59]
    (.letOp (n := 63) (.out 0x102670 (leaR64Effect 0x102670 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 64) (.exec 0x102670 (fun s => s.RIP = 0x102670) (leaR64Effect 0x102670 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 65) (.out 0x102674 (addR64Imm32Effect 0x102674 7 0x88) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x102674 (fun s => s.RIP = 0x102674) (addR64Imm32Effect 0x102674 7 0x88) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x10267b (xorR32R32Effect 0x10267b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x10267b (fun s => s.RIP = 0x10267b) (xorR32R32Effect 0x10267b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x10267d (callEffect (callMemPtr 0x10267d (.rip 0xfeba5)) (0x10267d + BitVec.ofNat 64 (callMemLen (.rip 0xfeba5)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x10267d (GoesTo (CallMemPre 0x10267d (.rip 0xfeba5)) (callEffect (callMemPtr 0x10267d (.rip 0xfeba5)) (0x10267d + BitVec.ofNat 64 (callMemLen (.rip 0xfeba5)))) 0x103eb0) (callEffect (callMemPtr 0x10267d (.rip 0xfeba5)) (0x10267d + BitVec.ofNat 64 (callMemLen (.rip 0xfeba5)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x102683⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l102683, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l10265e : List UInt8 :=
  [0xB8, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF0, 0x31, 0xD2, 0x49, 0x83, 0xFE, 0x10, 0x48, 0x0F,
    0x42, 0xD0, 0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00, 0x31, 0xF6, 0xFF,
    0x15, 0xA5, 0xEB, 0x0F, 0x00]

theorem code_l10265e : ∀ x ∈ codeRange 0x10265e bytes_l10265e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265e 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102683 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102683 (StorePre 0x102683 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102683 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102683 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 54) (.out 0x102688 (leaR64Effect 0x102688 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 55) (.exec 0x102688 (fun s => s.RIP = 0x102688) (leaR64Effect 0x102688 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x102690 (leaR64Effect 0x102690 3 (.rip 0x1869)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 57) (.exec 0x102690 (fun s => s.RIP = 0x102690) (leaR64Effect 0x102690 3 (.rip 0x1869)) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x102697 (movR64R64Effect 0x102697 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[54]
    (.letOp (n := 59) (.exec 0x102697 (fun s => s.RIP = 0x102697) (movR64R64Effect 0x102697 7 13) (Reg.operands [.gpr 13] [])) #v[54]
    (.letOp (n := 60) (.out 0x10269a (movR64R64Effect 0x10269a 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 61) (.exec 0x10269a (fun s => s.RIP = 0x10269a) (movR64R64Effect 0x10269a 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 62) (.out 0x10269d (movR64R64Effect 0x10269d 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 63) (.exec 0x10269d (fun s => s.RIP = 0x10269d) (movR64R64Effect 0x10269d 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 64) (.out 0x1026a0 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026a2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 56]
    (.letOp (n := 65) (.exec 0x1026a0 (GoesTo (CallPre 0x1026a0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026a2) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026a2) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 56]
    (.letOp (n := 66) (.const ⟨64, 0x1026a2⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 62), (3, 56), (4, 64), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l1026a2, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l102683 : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x50, 0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x1D,
    0x69, 0x18, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0xFF, 0xD3]

theorem code_l102683 : ∀ x ∈ codeRange 0x102683 bytes_l102683, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2683 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1026a2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1026a2 (leaR64Effect 0x1026a2 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1026a2 (fun s => s.RIP = 0x1026a2) (leaR64Effect 0x1026a2 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1026a7 (StorePre 0x1026a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1026a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026a7 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x1026ac (StorePre 0x1026ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1026ac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026ac 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 57) (.exec 0x1026b1 (StorePre 0x1026b1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1026b1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1026b1 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 58) (.exec 0x1026b6 (StorePre 0x1026b6 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1026b6 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1026b6 (.sib 4 none 0 (.d8 0x28)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1026bf (leaR64Effect 0x1026bf 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x1026bf (fun s => s.RIP = 0x1026bf) (leaR64Effect 0x1026bf 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1026c4 (leaR64Effect 0x1026c4 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1026c4 (fun s => s.RIP = 0x1026c4) (leaR64Effect 0x1026c4 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1026c9 (callEffect (fun _ => 0x107050) 0x1026ce) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x1026c9 (PushPre 0x1026c9 5) (callEffect (fun _ => 0x107050) 0x1026ce) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x1026ce⟩) #v[]
    (.terminate (.call ⟨.l107050, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1026ce, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1026a2 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x6C, 0x24, 0x18, 0x4C,
    0x89, 0x6C, 0x24, 0x20, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C,
    0x24, 0x30, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8, 0x82, 0x49, 0x00, 0x00]

theorem code_l1026a2 : ∀ x ∈ codeRange 0x1026a2 bytes_l1026a2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26a2 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1026ce : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1026ce (movR64R64Effect 0x1026ce 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x1026ce (fun s => s.RIP = 0x1026ce) (movR64R64Effect 0x1026ce 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1026d1 (movR64R64Effect 0x1026d1 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 56) (.exec 0x1026d1 (fun s => s.RIP = 0x1026d1) (movR64R64Effect 0x1026d1 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x1026d4 (movR64M64Effect 0x1026d4 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x1026d4 (LoadPre 0x1026d4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1026d4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026d4 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1026d9 (movR64R64Effect 0x1026d9 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x1026d9 (fun s => s.RIP = 0x1026d9) (movR64R64Effect 0x1026d9 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1026dc (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026de) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 62) (.exec 0x1026dc (GoesTo (CallPre 0x1026dc 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026de) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x1026de) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 63) (.const ⟨64, 0x1026de⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1026de, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l1026ce : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xEE, 0x4C, 0x8B, 0x6C, 0x24, 0x50, 0x4C, 0x89, 0xF2, 0xFF, 0xD3]

theorem code_l1026ce : ∀ x ∈ codeRange 0x1026ce bytes_l1026ce, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26ce 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1026de : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1026de (movR64M64Effect 0x1026de 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1026de (LoadPre 0x1026de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1026de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026de 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1026e3 (leaR64Effect 0x1026e3 7 (.base 3 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1026e3 (fun s => s.RIP = 0x1026e3) (leaR64Effect 0x1026e3 7 (.base 3 (.d8 0x1))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1026e7 (StorePre 0x1026e7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1026e7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1026e7 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 58) (.out 0x1026eb (leaR64Effect 0x1026eb 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1026eb (fun s => s.RIP = 0x1026eb) (leaR64Effect 0x1026eb 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x1026f0 (movR64M64Effect 0x1026f0 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x1026f0 (LoadPre 0x1026f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1026f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026f0 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1026f5 (movR64M64Effect 0x1026f5 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x1026f5 (LoadPre 0x1026f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1026f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026f5 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1026fa (movR64M64Effect 0x1026fa 8 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x1026fa (LoadPre 0x1026fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1026fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026fa 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x1026ff (movR64R64Effect 0x1026ff 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[13]
    (.letOp (n := 67) (.exec 0x1026ff (fun s => s.RIP = 0x1026ff) (movR64R64Effect 0x1026ff 9 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.out 0x102702 (callEffect (fun _ => 0x101800) 0x102707) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x102702 (PushPre 0x102702 5) (callEffect (fun _ => 0x101800) 0x102707) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x102707⟩) #v[]
    (.terminate (.call ⟨.l101800, RegMap.args [(1, 62), (2, 58), (3, 53), (4, 68), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l102707, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l1026de : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x58, 0x48, 0x8D, 0x7B, 0x01, 0x48, 0x89, 0x2C, 0x24, 0x48, 0x8D, 0x54,
    0x24, 0x78, 0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x8B, 0x44, 0x24,
    0x70, 0x4D, 0x89, 0xE9, 0xE8, 0xF9, 0xF0, 0xFF, 0xFF]

theorem code_l1026de : ∀ x ∈ codeRange 0x1026de bytes_l1026de, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x26de 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102707 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102707 (StorePre 0x102707 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102707 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102707 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10270a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l102707 : List UInt8 :=
  [0xC6, 0x03, 0x00]

theorem code_l102707 : ∀ x ∈ codeRange 0x102707 bytes_l102707, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2707 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10270a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10270a (movR64R64Effect 0x10270a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10270a (fun s => s.RIP = 0x10270a) (movR64R64Effect 0x10270a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10270d (addR64Imm32Effect 0x10270d 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10270d (fun s => s.RIP = 0x10270d) (addR64Imm32Effect 0x10270d 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102714 (popR64Effect 0x102714 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x102714 (popR64Effect 0x102714 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x102714 (PopPre 0x102714) (popR64Effect 0x102714 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x102715 (popR64Effect 0x102715 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x102715 (popR64Effect 0x102715 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x102715 (PopPre 0x102715) (popR64Effect 0x102715 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x102717 (popR64Effect 0x102717 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x102717 (popR64Effect 0x102717 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x102717 (PopPre 0x102717) (popR64Effect 0x102717 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x102719 (popR64Effect 0x102719 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x102719 (popR64Effect 0x102719 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x102719 (PopPre 0x102719) (popR64Effect 0x102719 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10271b (popR64Effect 0x10271b 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10271b (popR64Effect 0x10271b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10271b (PopPre 0x10271b) (popR64Effect 0x10271b 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10271d (popR64Effect 0x10271d 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10271d (popR64Effect 0x10271d 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10271d (PopPre 0x10271d) (popR64Effect 0x10271d 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10271e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10271e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10271e (RetPre 0x10271e) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10270a : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10270a : ∀ x ∈ codeRange 0x10270a bytes_l10270a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x270a 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102720 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102720 (pushR64Effect 0x102720 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x102720 (PushPre 0x102720 1) (pushR64Effect 0x102720 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x102721 (pushR64Effect 0x102721 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x102721 (PushPre 0x102721 2) (pushR64Effect 0x102721 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x102723 (pushR64Effect 0x102723 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x102723 (PushPre 0x102723 2) (pushR64Effect 0x102723 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x102725 (pushR64Effect 0x102725 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x102725 (PushPre 0x102725 2) (pushR64Effect 0x102725 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x102727 (pushR64Effect 0x102727 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x102727 (PushPre 0x102727 2) (pushR64Effect 0x102727 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x102729 (pushR64Effect 0x102729 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x102729 (PushPre 0x102729 1) (pushR64Effect 0x102729 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10272a (subR64Imm32Effect 0x10272a 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10272a (fun s => s.RIP = 0x10272a) (subR64Imm32Effect 0x10272a 4 0xa8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x102731 (movR64R64Effect 0x102731 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 68) (.exec 0x102731 (fun s => s.RIP = 0x102731) (movR64R64Effect 0x102731 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x102734 (movR64Imm64Effect 0x102734 3 0xfffffffe0) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 70) (.exec 0x102734 (fun s => s.RIP = 0x102734) (movR64Imm64Effect 0x102734 3 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10273e (movR64M64Effect 0x10273e 14 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[8]
    (.letOp (n := 72) (.exec 0x10273e (LoadPre 0x10273e (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x10273e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10273e 14 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 73) (.out 0x102742 (cmpR64R64Effect 0x102742 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 74) (.out 0x102742 (cmpR64R64Effect 0x102742 14 3) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 3] []) (.flag .ZF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x102742 (fun s => s.RIP = 0x102742) (cmpR64R64Effect 0x102742 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[71, 69]
    (.letOp (n := 76) (.out 0x102745 (atFlags (condHolds 7) (setccR8Effect 0x102745 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[0, 73, 74]
    (.letOp (n := 77) (.exec 0x102745 (fun s => s.RIP = 0x102745) (atFlags (condHolds 7) (setccR8Effect 0x102745 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[0, 73, 74]
    (.letOp (n := 78) (.out 0x102748 (shrR64Effect 0x102748 4 1 61) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 79) (.out 0x102748 (shrR64Effect 0x102748 4 1 61) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[1]
    (.letOp (n := 80) (.exec 0x102748 (fun s => s.RIP = 0x102748) (shrR64Effect 0x102748 4 1 61) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 81) (.out 0x10274c (atFlags (condHolds 5) (setccR8Effect 0x10274c 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[78, 79]
    (.letOp (n := 82) (.exec 0x10274c (fun s => s.RIP = 0x10274c) (atFlags (condHolds 5) (setccR8Effect 0x10274c 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[78, 79]
    (.letOp (n := 83) (.out 0x10274f (orR8R8Effect 0x10274f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[81, 76]
    (.letOp (n := 84) (.out 0x10274f (orR8R8Effect 0x10274f 2 1 0) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 0] []) (.flag .ZF)) #v[81, 76]
    (.letOp (n := 85) (.exec 0x10274f (fun s => s.RIP = 0x10274f) (orR8R8Effect 0x10274f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[81, 76]
    (.letOp (n := 86) (.out 0x102751 (movR8Imm8Effect 0x102751 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 87) (.exec 0x102751 (fun s => s.RIP = 0x102751) (movR8Imm8Effect 0x102751 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[76]
    (.letOp (n := 88) (.pure (condOp 5)) #v[84]
    (.terminate (.condBr (Fin.last 88) ⟨.l102961, RegMap.args [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ ⟨.l102759, RegMap.args [(0, 86), (1, 83), (2, 2), (3, 69), (4, 65), (5, 67), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 71), (15, 15), (19, 84), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l102720 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xA8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xCD, 0x48, 0xBB, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4D, 0x8B,
    0x70, 0x10, 0x49, 0x39, 0xDE, 0x0F, 0x97, 0xC0, 0x48, 0xC1, 0xE9, 0x3D, 0x0F, 0x95, 0xC1, 0x08,
    0xC1, 0xB0, 0x01, 0x0F, 0x85, 0x08, 0x02, 0x00, 0x00]

theorem code_l102720 : ∀ x ∈ codeRange 0x102720 bytes_l102720, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2720 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102759_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.out 0x1027b7 (callEffect (fun _ => 0x106960) 0x1027bc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 83) (.exec 0x1027b7 (PushPre 0x1027b7 5) (callEffect (fun _ => 0x106960) 0x1027bc) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.const ⟨64, 0x1027bc⟩) #v[]
    (.terminate (.call ⟨.l106960, RegMap.args [(0, 57), (1, 59), (2, 77), (3, 3), (4, 82), (5, 5), (6, 66), (7, 75), (8, 8), (9, 9), (12, 55), (13, 53), (14, 14), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l1027bc, kept := #v[], arity := rfl, guard := some (Fin.last 84) }))))

def bytes_l102759_1 : List UInt8 :=
  [0xE8, 0xA4, 0x41, 0x00, 0x00]

theorem code_l102759_1 : ∀ x ∈ codeRange 0x1027b7 bytes_l102759_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b7 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102759 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102759 (movR64R64Effect 0x102759 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 54) (.exec 0x102759 (fun s => s.RIP = 0x102759) (movR64R64Effect 0x102759 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.out 0x10275c (movR64R64Effect 0x10275c 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 56) (.exec 0x10275c (fun s => s.RIP = 0x10275c) (movR64R64Effect 0x10275c 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10275f (movR32M32LowEffect 0x10275f 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 58) (.exec 0x10275f (LoadPre 0x10275f (fun s => AddrMode.addr (.base 6 .none) s (0x10275f + BitVec.ofNat 64 2)) 4) (movR32M32LowEffect 0x10275f 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x102761 (movR32M32LowEffect 0x102761 1 (.base 6 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 60) (.exec 0x102761 (LoadPre 0x102761 (fun s => AddrMode.addr (.base 6 (.d8 0x4)) s (0x102761 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102761 1 (.base 6 (.d8 0x4))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.exec 0x102764 (StorePre 0x102764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102764 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102764 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 62) (.out 0x102769 (movR32M32LowEffect 0x102769 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 63) (.exec 0x102769 (LoadPre 0x102769 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102769 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x102769 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.exec 0x10276c (StorePre 0x10276c 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10276c + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10276c (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x102778 (StorePre 0x102778 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x102778 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102778 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x102781 (leaR64Effect 0x102781 6 (.base 7 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 67) (.exec 0x102781 (fun s => s.RIP = 0x102781) (leaR64Effect 0x102781 6 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 68) (.exec 0x102785 (StorePre 0x102785 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102785 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102785 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 69) (.exec 0x102789 (StorePre 0x102789 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102789 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102789 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 70) (.exec 0x10278d (StorePre 0x10278d 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10278d + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10278d 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 71) (.exec 0x102791 (StorePre 0x102791 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x102791 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102791 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 72) (.exec 0x102795 (StorePre 0x102795 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102795 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102795 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 73) (.exec 0x102799 (StorePre 0x102799 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102799 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102799 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 74) (.exec 0x10279d (StorePre 0x10279d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10279d + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x10279d 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1027a5 (leaR64Effect 0x1027a5 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x1027a5 (fun s => s.RIP = 0x1027a5) (leaR64Effect 0x1027a5 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x1027aa (leaR64Effect 0x1027aa 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 78) (.exec 0x1027aa (fun s => s.RIP = 0x1027aa) (leaR64Effect 0x1027aa 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x1027af (StorePre 0x1027af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1027af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1027af 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 80) (.out 0x1027b4 (movR64R64Effect 0x1027b4 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[8]
    (.letOp (n := 81) (.exec 0x1027b4 (fun s => s.RIP = 0x1027b4) (movR64R64Effect 0x1027b4 15 8) (Reg.operands [.gpr 8] [])) #v[8]
    (b_l102759_1)))))))))))))))))))))))))))))

def bytes_l102759 : List UInt8 :=
  [0x4D, 0x89, 0xCD, 0x49, 0x89, 0xFC, 0x8B, 0x06, 0x8B, 0x4E, 0x04, 0x48, 0x89, 0x54, 0x24, 0x50,
    0x8B, 0x56, 0x08, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x77, 0x20, 0x89, 0x44, 0x24, 0x3C,
    0x89, 0x44, 0x24, 0x10, 0x89, 0x4C, 0x24, 0x38, 0x89, 0x4C, 0x24, 0x14, 0x89, 0x54, 0x24, 0x34,
    0x89, 0x54, 0x24, 0x18, 0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01, 0x48, 0x8D, 0x7C, 0x24,
    0x78, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0x74, 0x24, 0x48, 0x4D, 0x89, 0xC7] ++ bytes_l102759_1

theorem code_l102759 : ∀ x ∈ codeRange 0x102759 bytes_l102759, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2759 94 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102759_1

@[cfg_block] def b_l1027bc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1027bc (StorePre 0x1027bc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1027bc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1027bc 15 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.out 0x1027c1 (movR64M64Effect 0x1027c1 9 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 15] []) (.reg (.gpr 9))) #v[15]
    (.letOp (n := 55) (.exec 0x1027c1 (LoadPre 0x1027c1 (fun s => AddrMode.addr (.base 15 .none) s (0x1027c1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1027c1 9 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 56) (.exec 0x1027c4 (StorePre 0x1027c4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1027c4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1027c4 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 57) (.out 0x1027c8 (leaR64Effect 0x1027c8 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1027c8 (fun s => s.RIP = 0x1027c8) (leaR64Effect 0x1027c8 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1027d0 (movR64R64Effect 0x1027d0 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 60) (.exec 0x1027d0 (fun s => s.RIP = 0x1027d0) (movR64R64Effect 0x1027d0 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x1027d3 (leaR64Effect 0x1027d3 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1027d3 (fun s => s.RIP = 0x1027d3) (leaR64Effect 0x1027d3 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1027d8 (movR64M64Effect 0x1027d8 1 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x1027d8 (LoadPre 0x1027d8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1027d8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027d8 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1027dd (movR64R64Effect 0x1027dd 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 66) (.exec 0x1027dd (fun s => s.RIP = 0x1027dd) (movR64R64Effect 0x1027dd 8 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.out 0x1027e0 (movR64R64Effect 0x1027e0 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[54]
    (.letOp (n := 68) (.exec 0x1027e0 (fun s => s.RIP = 0x1027e0) (movR64R64Effect 0x1027e0 12 9) (Reg.operands [.gpr 9] [])) #v[54]
    (.letOp (n := 69) (.out 0x1027e3 (callEffect (fun _ => 0x101c20) 0x1027e8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x1027e3 (PushPre 0x1027e3 5) (callEffect (fun _ => 0x101c20) 0x1027e8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x1027e8⟩) #v[]
    (.terminate (.call ⟨.l101c20, RegMap.args [(1, 63), (2, 61), (3, 3), (4, 69), (5, 5), (6, 59), (7, 57), (8, 65), (9, 54), (11, 11), (12, 67), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l1027e8, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1027bc : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x40, 0x4D, 0x8B, 0x0F, 0x4C, 0x89, 0x34, 0x24, 0x48, 0x8D, 0xBC, 0x24,
    0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0x48, 0x8D, 0x54, 0x24, 0x78, 0x48, 0x8B, 0x4C, 0x24,
    0x50, 0x49, 0x89, 0xE8, 0x4D, 0x89, 0xCC, 0xE8, 0x38, 0xF4, 0xFF, 0xFF]

theorem code_l1027bc : ∀ x ∈ codeRange 0x1027bc bytes_l1027bc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27bc 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027e8_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x102836 (leaR64Effect 0x102836 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 96) (.exec 0x102836 (fun s => s.RIP = 0x102836) (leaR64Effect 0x102836 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x10283b (cmpM8Imm8Effect 0x10283b 5 (.sib 4 none 0 (.d8 0x10)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 98) (.exec 0x10283b (LoadPre 0x10283b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10283b + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x10283b 5 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x102840 (atFlags (condHolds 4) (setccR8Effect 0x102840 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[95, 97]
    (.letOp (n := 100) (.exec 0x102840 (fun s => s.RIP = 0x102840) (atFlags (condHolds 4) (setccR8Effect 0x102840 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[95, 97]
    (.letOp (n := 101) (.pure (condOp 4)) #v[97]
    (.terminate (.condBr (Fin.last 101) ⟨.l102961, RegMap.args [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 102⟩ ⟨.l102849, RegMap.args [(0, 99), (1, 63), (2, 89), (3, 3), (4, 4), (5, 5), (6, 82), (7, 57), (8, 59), (9, 69), (11, 11), (12, 12), (13, 13), (14, 14), (19, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 102⟩))))))))

def bytes_l1027e8_1 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x10, 0x80, 0x7C, 0x24, 0x10, 0x00, 0x0F, 0x94, 0xC0, 0x0F, 0x84, 0x18,
    0x01, 0x00, 0x00]

theorem code_l1027e8_1 : ∀ x ∈ codeRange 0x102836 bytes_l1027e8_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2836 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1027e8 (movR64M64Effect 0x1027e8 2 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1027e8 (LoadPre 0x1027e8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1027e8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027e8 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1027f0 (movR64M64Effect 0x1027f0 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1027f0 (LoadPre 0x1027f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1027f0 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027f0 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1027f8 (movR64M64Effect 0x1027f8 7 (.base 13 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 58) (.exec 0x1027f8 (LoadPre 0x1027f8 (fun s => AddrMode.addr (.base 13 (.d8 0x0)) s (0x1027f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1027f8 7 (.base 13 (.d8 0x0))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x1027fc (movR64M64Effect 0x1027fc 8 (.base 13 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 60) (.exec 0x1027fc (LoadPre 0x1027fc (fun s => AddrMode.addr (.base 13 (.d8 0x8)) s (0x1027fc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1027fc 8 (.base 13 (.d8 0x8))) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x102800 (xorR32R32Effect 0x102800 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 62) (.exec 0x102800 (fun s => s.RIP = 0x102800) (xorR32R32Effect 0x102800 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 63) (.out 0x102802 (movR16Imm16Effect 0x102802 4 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 64) (.exec 0x102802 (fun s => s.RIP = 0x102802) (movR16Imm16Effect 0x102802 4 1 0x1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x102806 (movR16Imm16Effect 0x102806 5 9 0x1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 66) (.exec 0x102806 (fun s => s.RIP = 0x102806) (movR16Imm16Effect 0x102806 5 9 0x1) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 67) (.out 0x10280b (xorR64R64Effect 0x10280b 2 7) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 7] []) (.flag .ZF)) #v[53, 57]
    (.letOp (n := 68) (.exec 0x10280b (fun s => s.RIP = 0x10280b) (xorR64R64Effect 0x10280b 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[53, 57]
    (.letOp (n := 69) (.out 0x10280e (atFlags (condHolds 5) (cmovR64R64Effect 0x10280e 4 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[65, 61, 67]
    (.letOp (n := 70) (.exec 0x10280e (fun s => s.RIP = 0x10280e) (atFlags (condHolds 5) (cmovR64R64Effect 0x10280e 4 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 61, 67]
    (.letOp (n := 71) (.out 0x102812 (movzxR32R8Effect 0x102812 4 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x102812 (fun s => s.RIP = 0x102812) (movzxR32R8Effect 0x102812 4 2 9) (Reg.operands [.gpr 9] [])) #v[69]
    (.letOp (n := 73) (.out 0x102816 (xorR64R64Effect 0x102816 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 59]
    (.letOp (n := 74) (.out 0x102816 (xorR64R64Effect 0x102816 6 8) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 8] []) (.flag .ZF)) #v[55, 59]
    (.letOp (n := 75) (.exec 0x102816 (fun s => s.RIP = 0x102816) (xorR64R64Effect 0x102816 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 59]
    (.letOp (n := 76) (.out 0x102819 (atFlags (condHolds 5) (cmovR64R64Effect 0x102819 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[71, 61, 74]
    (.letOp (n := 77) (.exec 0x102819 (fun s => s.RIP = 0x102819) (atFlags (condHolds 5) (cmovR64R64Effect 0x102819 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 61, 74]
    (.letOp (n := 78) (.out 0x10281d (movzxR32R8Effect 0x10281d 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[76]
    (.letOp (n := 79) (.exec 0x10281d (fun s => s.RIP = 0x10281d) (movzxR32R8Effect 0x10281d 3 2 2) (Reg.operands [.gpr 2] [])) #v[76]
    (.letOp (n := 80) (.out 0x102820 (xorR32R32Effect 0x102820 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[73, 73]
    (.letOp (n := 81) (.exec 0x102820 (fun s => s.RIP = 0x102820) (xorR32R32Effect 0x102820 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[73, 73]
    (.letOp (n := 82) (.out 0x102822 (xorR64R64Effect 0x102822 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[80, 61]
    (.letOp (n := 83) (.out 0x102822 (xorR64R64Effect 0x102822 6 0) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 0] []) (.flag .ZF)) #v[80, 61]
    (.letOp (n := 84) (.exec 0x102822 (fun s => s.RIP = 0x102822) (xorR64R64Effect 0x102822 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[80, 61]
    (.letOp (n := 85) (.out 0x102825 (atFlags (condHolds 5) (cmovR64R64Effect 0x102825 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[78, 61, 83]
    (.letOp (n := 86) (.exec 0x102825 (fun s => s.RIP = 0x102825) (atFlags (condHolds 5) (cmovR64R64Effect 0x102825 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[78, 61, 83]
    (.letOp (n := 87) (.out 0x102829 (movzxR32R8Effect 0x102829 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[85]
    (.letOp (n := 88) (.exec 0x102829 (fun s => s.RIP = 0x102829) (movzxR32R8Effect 0x102829 3 2 2) (Reg.operands [.gpr 2] [])) #v[85]
    (.letOp (n := 89) (.out 0x10282c (xorR16R16Effect 0x10282c 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[87, 63]
    (.letOp (n := 90) (.out 0x10282c (xorR16R16Effect 0x10282c 3 2 1) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[87, 63]
    (.letOp (n := 91) (.exec 0x10282c (fun s => s.RIP = 0x10282c) (xorR16R16Effect 0x10282c 3 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[87, 63]
    (.letOp (n := 92) (.out 0x10282f (atFlags (condHolds 4) (cmovR32R32Effect 0x10282f 3 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[61, 63, 90]
    (.letOp (n := 93) (.exec 0x10282f (fun s => s.RIP = 0x10282f) (atFlags (condHolds 4) (cmovR32R32Effect 0x10282f 3 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 63, 90]
    (.letOp (n := 94) (.exec 0x102832 (StorePre 0x102832 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102832 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x102832 4 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[92, 4]
    (b_l1027e8_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l1027e8 : List UInt8 :=
  [0x48, 0x8B, 0x94, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00,
    0x49, 0x8B, 0x7D, 0x00, 0x4D, 0x8B, 0x45, 0x08, 0x31, 0xC0, 0x66, 0xB9, 0x01, 0x00, 0x66, 0x41,
    0xB9, 0x01, 0x00, 0x48, 0x31, 0xFA, 0x4C, 0x0F, 0x45, 0xC8, 0x41, 0x0F, 0xB6, 0xD1, 0x4C, 0x31,
    0xC6, 0x48, 0x0F, 0x45, 0xD0, 0x0F, 0xB6, 0xD2, 0x31, 0xF6, 0x48, 0x31, 0xC6, 0x48, 0x0F, 0x45,
    0xD0, 0x0F, 0xB6, 0xD2, 0x66, 0x31, 0xCA, 0x0F, 0x44, 0xC1, 0x88, 0x44, 0x24, 0x10] ++ bytes_l1027e8_1

theorem code_l1027e8 : ∀ x ∈ codeRange 0x1027e8 bytes_l1027e8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x27e8 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1027e8_1

@[cfg_block] def b_l102849 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102849 (movR64M64Effect 0x102849 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x102849 (LoadPre 0x102849 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102849 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102849 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10284e (StorePre 0x10284e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10284e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10284e 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x102853 (leaR64Effect 0x102853 15 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 57) (.exec 0x102853 (fun s => s.RIP = 0x102853) (leaR64Effect 0x102853 15 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x102858 (movR32M32LowEffect 0x102858 1 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 59) (.exec 0x102858 (LoadPre 0x102858 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102858 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102858 1 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x10285c (StorePre 0x10285c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10285c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10285c 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x102860 (movR32M32LowEffect 0x102860 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x102860 (LoadPre 0x102860 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102860 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102860 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x102864 (StorePre 0x102864 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x102864 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102864 1 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x102868 (movR32M32LowEffect 0x102868 1 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 65) (.exec 0x102868 (LoadPre 0x102868 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x102868 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x102868 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x10286c (StorePre 0x10286c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10286c + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x10286c 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x102870 (movR64Imm64Effect 0x102870 1 0x100000001) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 68) (.exec 0x102870 (fun s => s.RIP = 0x102870) (movR64Imm64Effect 0x102870 1 0x100000001) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.exec 0x10287a (StorePre 0x10287a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10287a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10287a 1 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x10287f (cmpR64Imm8Effect 0x10287f 14 0x11) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 71) (.exec 0x10287f (fun s => s.RIP = 0x10287f) (cmpR64Imm8Effect 0x10287f 14 0x11) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 72) (.pure (condOp 2)) #v[70]
    (.terminate (.condBr (Fin.last 72) ⟨.l1028dc, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ ⟨.l102885, RegMap.args [(0, 0), (1, 67), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (14, 14), (15, 56), (16, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l102849 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x4C, 0x24, 0x58, 0x4C, 0x8D, 0x7C, 0x24, 0x60, 0x8B,
    0x4C, 0x24, 0x3C, 0x89, 0x4C, 0x24, 0x60, 0x8B, 0x4C, 0x24, 0x38, 0x89, 0x4C, 0x24, 0x64, 0x8B,
    0x4C, 0x24, 0x34, 0x89, 0x4C, 0x24, 0x68, 0x48, 0xB9, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x4C, 0x24, 0x6C, 0x49, 0x83, 0xFE, 0x11, 0x72, 0x57]

theorem code_l102849 : ∀ x ∈ codeRange 0x102849 bytes_l102849, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2849 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102885 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102885 (movR64R64Effect 0x102885 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 54) (.exec 0x102885 (fun s => s.RIP = 0x102885) (movR64R64Effect 0x102885 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x102888 (shrR64Effect 0x102888 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x102888 (fun s => s.RIP = 0x102888) (shrR64Effect 0x102888 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10288c (movR64M64Effect 0x10288c 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10288c (LoadPre 0x10288c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10288c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10288c 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102891 (movR64M64Effect 0x102891 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x102891 (LoadPre 0x102891 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102891 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102891 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[57]
    (.letOp (n := 61) (.out 0x102895 (addR64Imm8Effect 0x102895 3 0x10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 62) (.exec 0x102895 (fun s => s.RIP = 0x102895) (addR64Imm8Effect 0x102895 3 0x10) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 63) (.out 0x102899 (andR64R64Effect 0x102899 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[61, 14]
    (.letOp (n := 64) (.exec 0x102899 (fun s => s.RIP = 0x102899) (andR64R64Effect 0x102899 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[61, 14]
    (.letOp (n := 65) (.out 0x10289c (andR32Imm8Effect 0x10289c 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 66) (.exec 0x10289c (fun s => s.RIP = 0x10289c) (andR32Imm8Effect 0x10289c 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x1028a0 (leaR64Effect 0x1028a0 13 (.sib 12 (some 3) 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12, .gpr 3] []) (.reg (.gpr 13))) #v[12, 63]
    (.letOp (n := 68) (.exec 0x1028a0 (fun s => s.RIP = 0x1028a0) (leaR64Effect 0x1028a0 13 (.sib 12 (some 3) 0 .none)) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 63]
    (.letOp (n := 69) (.out 0x1028a4 (addR64R64Effect 0x1028a4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[63, 59]
    (.letOp (n := 70) (.exec 0x1028a4 (fun s => s.RIP = 0x1028a4) (addR64R64Effect 0x1028a4 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[63, 59]
    (.letOp (n := 71) (.exec 0x1028a7 (StorePre 0x1028a7 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1028a7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1028a7 3 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 6] [])) #v[69, 57]
    (.letOp (n := 72) (.exec 0x1028ab (StorePre 0x1028ab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1028ab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028ab 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 73) (.exec 0x1028b0 (StorePre 0x1028b0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1028b0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028b0 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 74) (.exec 0x1028b5 (StorePre 0x1028b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1028b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028b5 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 75) (.exec 0x1028ba (StorePre 0x1028ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1028ba + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1028ba 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 76) (.out 0x1028bf (leaR64Effect 0x1028bf 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 77) (.exec 0x1028bf (fun s => s.RIP = 0x1028bf) (leaR64Effect 0x1028bf 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x1028c4 (leaR64Effect 0x1028c4 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 79) (.exec 0x1028c4 (fun s => s.RIP = 0x1028c4) (leaR64Effect 0x1028c4 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x1028c9 (movR32R32Effect 0x1028c9 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[0]
    (.letOp (n := 81) (.exec 0x1028c9 (fun s => s.RIP = 0x1028c9) (movR32R32Effect 0x1028c9 2 3 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 82) (.out 0x1028cb (callEffect (fun _ => 0x1084e0) 0x1028d0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 83) (.exec 0x1028cb (PushPre 0x1028cb 5) (callEffect (fun _ => 0x1084e0) 0x1028d0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.const ⟨64, 0x1028d0⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(0, 0), (1, 55), (2, 59), (3, 80), (4, 82), (5, 5), (6, 78), (7, 76), (11, 11), (12, 12), (13, 67), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l1028d0, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l102885 : List UInt8 :=
  [0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x8B, 0x56, 0x08,
    0x48, 0x83, 0xC3, 0x10, 0x4C, 0x21, 0xF3, 0x41, 0x83, 0xE6, 0x0F, 0x4D, 0x8D, 0x2C, 0x1C, 0x48,
    0x01, 0xD3, 0x48, 0x89, 0x5E, 0x08, 0x4C, 0x89, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0x64, 0x24, 0x18,
    0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89, 0x4C, 0x24, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x58, 0x48,
    0x8D, 0x74, 0x24, 0x10, 0x89, 0xC3, 0xE8, 0x10, 0x5C, 0x00, 0x00]

theorem code_l102885 : ∀ x ∈ codeRange 0x102885 bytes_l102885, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2885 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1028d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1028d0 (movR32R32Effect 0x1028d0 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1028d0 (fun s => s.RIP = 0x1028d0) (movR32R32Effect 0x1028d0 2 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1028d2 (testR64R64Effect 0x1028d2 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x1028d2 (fun s => s.RIP = 0x1028d2) (testR64R64Effect 0x1028d2 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1028e4, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1028d7, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1028d0 : List UInt8 :=
  [0x89, 0xD8, 0x4D, 0x85, 0xF6, 0x75, 0x0D]

theorem code_l1028d0 : ∀ x ∈ codeRange 0x1028d0 bytes_l1028d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d0 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1028d7 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l102961, RegMap.args (entryMap (live .l1028d7)) 53⟩)

def bytes_l1028d7 : List UInt8 :=
  [0xE9, 0x85, 0x00, 0x00, 0x00]

theorem code_l1028d7 : ∀ x ∈ codeRange 0x1028d7 bytes_l1028d7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28d7 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1028dc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1028dc (movR64R64Effect 0x1028dc 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 54) (.exec 0x1028dc (fun s => s.RIP = 0x1028dc) (movR64R64Effect 0x1028dc 13 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1028df (testR64R64Effect 0x1028df 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x1028df (fun s => s.RIP = 0x1028df) (testR64R64Effect 0x1028df 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l102961, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1028e4, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1028dc : List UInt8 :=
  [0x4D, 0x89, 0xE5, 0x4D, 0x85, 0xF6, 0x74, 0x7D]

theorem code_l1028dc : ∀ x ∈ codeRange 0x1028dc bytes_l1028dc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28dc 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1028e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1028e4 (movR32Imm32Effect 0x1028e4 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x1028e4 (fun s => s.RIP = 0x1028e4) (movR32Imm32Effect 0x1028e4 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1028e9 (subR64R64Effect 0x1028e9 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1028e9 (fun s => s.RIP = 0x1028e9) (subR64R64Effect 0x1028e9 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1028ec (xorR32R32Effect 0x1028ec 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x1028ec (fun s => s.RIP = 0x1028ec) (xorR32R32Effect 0x1028ec 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x1028ee (cmpR64Imm8Effect 0x1028ee 14 0x10) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 60) (.exec 0x1028ee (fun s => s.RIP = 0x1028ee) (cmpR64Imm8Effect 0x1028ee 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1028f2 (atFlags (condHolds 2) (cmovR64R64Effect 0x1028f2 4 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[57, 55, 59]
    (.letOp (n := 62) (.exec 0x1028f2 (fun s => s.RIP = 0x1028f2) (atFlags (condHolds 2) (cmovR64R64Effect 0x1028f2 4 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 55, 59]
    (.letOp (n := 63) (.out 0x1028f6 (leaR64Effect 0x1028f6 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 64) (.exec 0x1028f6 (fun s => s.RIP = 0x1028f6) (leaR64Effect 0x1028f6 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 65) (.out 0x1028fa (addR64Imm32Effect 0x1028fa 7 0x98) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x1028fa (fun s => s.RIP = 0x1028fa) (addR64Imm32Effect 0x1028fa 7 0x98) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x102901 (xorR32R32Effect 0x102901 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x102901 (fun s => s.RIP = 0x102901) (xorR32R32Effect 0x102901 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x102903 (movR32R32Effect 0x102903 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[0]
    (.letOp (n := 70) (.exec 0x102903 (fun s => s.RIP = 0x102903) (movR32R32Effect 0x102903 2 5 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 71) (.out 0x102905 (callEffect (callMemPtr 0x102905 (.rip 0xfe91d)) (0x102905 + BitVec.ofNat 64 (callMemLen (.rip 0xfe91d)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x102905 (GoesTo (CallMemPre 0x102905 (.rip 0xfe91d)) (callEffect (callMemPtr 0x102905 (.rip 0xfe91d)) (0x102905 + BitVec.ofNat 64 (callMemLen (.rip 0xfe91d)))) 0x103eb0) (callEffect (callMemPtr 0x102905 (.rip 0xfe91d)) (0x102905 + BitVec.ofNat 64 (callMemLen (.rip 0xfe91d)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x10290b⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 0), (1, 55), (2, 61), (3, 3), (4, 71), (5, 69), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l10290b, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l1028e4 : List UInt8 :=
  [0xB9, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF1, 0x31, 0xD2, 0x49, 0x83, 0xFE, 0x10, 0x48, 0x0F,
    0x42, 0xD1, 0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x81, 0xC7, 0x98, 0x00, 0x00, 0x00, 0x31, 0xF6, 0x89,
    0xC5, 0xFF, 0x15, 0x1D, 0xE9, 0x0F, 0x00]

theorem code_l1028e4 : ∀ x ∈ codeRange 0x1028e4 bytes_l1028e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28e4 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10290b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10290b (leaR64Effect 0x10290b 3 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x10290b (fun s => s.RIP = 0x10290b) (leaR64Effect 0x10290b 3 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102913 (leaR64Effect 0x102913 12 (.rip 0x15e6)) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 56) (.exec 0x102913 (fun s => s.RIP = 0x102913) (leaR64Effect 0x102913 12 (.rip 0x15e6)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10291a (movR64R64Effect 0x10291a 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10291a (fun s => s.RIP = 0x10291a) (movR64R64Effect 0x10291a 7 3) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 59) (.out 0x10291d (movR64R64Effect 0x10291d 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 60) (.exec 0x10291d (fun s => s.RIP = 0x10291d) (movR64R64Effect 0x10291d 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x102920 (movR64R64Effect 0x102920 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 62) (.exec 0x102920 (fun s => s.RIP = 0x102920) (movR64R64Effect 0x102920 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 63) (.out 0x102923 (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x102926) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 55]
    (.letOp (n := 64) (.exec 0x102923 (GoesTo (CallPre 0x102923 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x102926) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x102926) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 55]
    (.letOp (n := 65) (.const ⟨64, 0x102926⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 61), (3, 53), (4, 63), (5, 5), (6, 59), (7, 57), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l102926, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10290b : List UInt8 :=
  [0x48, 0x8D, 0x9C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x25, 0xE6, 0x15, 0x00, 0x00, 0x48,
    0x89, 0xDF, 0x4C, 0x89, 0xEE, 0x4C, 0x89, 0xF2, 0x41, 0xFF, 0xD4]

theorem code_l10290b : ∀ x ∈ codeRange 0x10290b bytes_l10290b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x290b 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102926 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102926 (StorePre 0x102926 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102926 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102926 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.exec 0x10292b (StorePre 0x10292b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10292b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10292b 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 55) (.exec 0x102930 (StorePre 0x102930 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102930 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102930 3 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.exec 0x102935 (StorePre 0x102935 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102935 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102935 (.sib 4 none 0 (.d8 0x28)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10293e (leaR64Effect 0x10293e 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10293e (fun s => s.RIP = 0x10293e) (leaR64Effect 0x10293e 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102943 (leaR64Effect 0x102943 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x102943 (fun s => s.RIP = 0x102943) (leaR64Effect 0x102943 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x102948 (callEffect (fun _ => 0x1084e0) 0x10294d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x102948 (PushPre 0x102948 5) (callEffect (fun _ => 0x1084e0) 0x10294d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10294d⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(1, 1), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10294d, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l102926 : List UInt8 :=
  [0x4C, 0x89, 0x7C, 0x24, 0x10, 0x48, 0x89, 0x5C, 0x24, 0x18, 0x48, 0x89, 0x5C, 0x24, 0x20, 0x48,
    0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x58, 0x48, 0x8D, 0x74,
    0x24, 0x10, 0xE8, 0x93, 0x5B, 0x00, 0x00]

theorem code_l102926 : ∀ x ∈ codeRange 0x102926 bytes_l102926, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2926 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10294d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10294d (movR64M64Effect 0x10294d 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10294d (LoadPre 0x10294d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10294d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10294d 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102952 (movR64M64Effect 0x102952 7 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x102952 (LoadPre 0x102952 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x102952 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102952 7 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x102956 (movR64R64Effect 0x102956 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 58) (.exec 0x102956 (fun s => s.RIP = 0x102956) (movR64R64Effect 0x102956 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.out 0x102959 (movR64R64Effect 0x102959 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x102959 (fun s => s.RIP = 0x102959) (movR64R64Effect 0x102959 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10295c (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10295f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[4, 12]
    (.letOp (n := 62) (.exec 0x10295c (GoesTo (CallPre 0x10295c 3 (fun s => (Operand.reg 12 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10295f) 0x103f00) (callEffect (fun s => (Operand.reg 12 : Operand 64).read s) 0x10295f) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 63) (.const ⟨64, 0x10295f⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 53), (2, 59), (3, 3), (4, 61), (5, 5), (6, 57), (7, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10295f, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10294d : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x78, 0x08, 0x48, 0x89, 0xDE, 0x4C, 0x89, 0xF2, 0x41,
    0xFF, 0xD4]

theorem code_l10294d : ∀ x ∈ codeRange 0x10294d bytes_l10294d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x294d 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10295f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10295f (movR32R32Effect 0x10295f 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x10295f (fun s => s.RIP = 0x10295f) (movR32R32Effect 0x10295f 2 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.terminate (.br ⟨.l102961, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10295f : List UInt8 :=
  [0x89, 0xE8]

theorem code_l10295f : ∀ x ∈ codeRange 0x10295f bytes_l10295f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x295f 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102961 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102961 (addR64Imm32Effect 0x102961 4 0xa8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x102961 (fun s => s.RIP = 0x102961) (addR64Imm32Effect 0x102961 4 0xa8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102968 (popR64Effect 0x102968 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x102968 (popR64Effect 0x102968 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x102968 (PopPre 0x102968) (popR64Effect 0x102968 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x102969 (popR64Effect 0x102969 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x102969 (popR64Effect 0x102969 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x102969 (PopPre 0x102969) (popR64Effect 0x102969 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10296b (popR64Effect 0x10296b 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10296b (popR64Effect 0x10296b 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10296b (PopPre 0x10296b) (popR64Effect 0x10296b 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10296d (popR64Effect 0x10296d 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10296d (popR64Effect 0x10296d 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10296d (PopPre 0x10296d) (popR64Effect 0x10296d 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x10296f (popR64Effect 0x10296f 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x10296f (popR64Effect 0x10296f 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10296f (PopPre 0x10296f) (popR64Effect 0x10296f 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x102971 (popR64Effect 0x102971 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x102971 (popR64Effect 0x102971 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x102971 (PopPre 0x102971) (popR64Effect 0x102971 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x102972 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x102972 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x102972 (RetPre 0x102972) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l102961 : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l102961 : ∀ x ∈ codeRange 0x102961 bytes_l102961, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2961 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102980 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102980 (pushR64Effect 0x102980 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x102980 (PushPre 0x102980 1) (pushR64Effect 0x102980 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x102981 (pushR64Effect 0x102981 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x102981 (PushPre 0x102981 2) (pushR64Effect 0x102981 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x102983 (pushR64Effect 0x102983 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x102983 (PushPre 0x102983 2) (pushR64Effect 0x102983 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x102985 (pushR64Effect 0x102985 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x102985 (PushPre 0x102985 2) (pushR64Effect 0x102985 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x102987 (pushR64Effect 0x102987 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x102987 (PushPre 0x102987 2) (pushR64Effect 0x102987 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x102989 (pushR64Effect 0x102989 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x102989 (PushPre 0x102989 1) (pushR64Effect 0x102989 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10298a (subR64Imm32Effect 0x10298a 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10298a (fun s => s.RIP = 0x10298a) (subR64Imm32Effect 0x10298a 4 0x98) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x102991 (movR64R64Effect 0x102991 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x102991 (fun s => s.RIP = 0x102991) (movR64R64Effect 0x102991 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x102994 (movR64Imm64Effect 0x102994 0 0xfffffffe0) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 70) (.exec 0x102994 (fun s => s.RIP = 0x102994) (movR64Imm64Effect 0x102994 0 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10299e (movR64M64Effect 0x10299e 12 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[9]
    (.letOp (n := 72) (.exec 0x10299e (LoadPre 0x10299e (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10299e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10299e 12 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 73) (.out 0x1029a2 (cmpR64R64Effect 0x1029a2 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[71, 69]
    (.letOp (n := 74) (.out 0x1029a2 (cmpR64R64Effect 0x1029a2 12 0) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 0] []) (.flag .ZF)) #v[71, 69]
    (.letOp (n := 75) (.exec 0x1029a2 (fun s => s.RIP = 0x1029a2) (cmpR64R64Effect 0x1029a2 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[71, 69]
    (.letOp (n := 76) (.out 0x1029a5 (atFlags (condHolds 7) (setccR8Effect 0x1029a5 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 0))) #v[69, 73, 74]
    (.letOp (n := 77) (.exec 0x1029a5 (fun s => s.RIP = 0x1029a5) (atFlags (condHolds 7) (setccR8Effect 0x1029a5 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[69, 73, 74]
    (.letOp (n := 78) (.out 0x1029a8 (movR64R64Effect 0x1029a8 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[8]
    (.letOp (n := 79) (.exec 0x1029a8 (fun s => s.RIP = 0x1029a8) (movR64R64Effect 0x1029a8 7 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 80) (.out 0x1029ab (shrR64Effect 0x1029ab 4 7 61) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.out 0x1029ab (shrR64Effect 0x1029ab 4 7 61) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[78]
    (.letOp (n := 82) (.exec 0x1029ab (fun s => s.RIP = 0x1029ab) (shrR64Effect 0x1029ab 4 7 61) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 83) (.out 0x1029af (atFlags (condHolds 5) (setccR8Effect 0x1029af 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[80, 81]
    (.letOp (n := 84) (.exec 0x1029af (fun s => s.RIP = 0x1029af) (atFlags (condHolds 5) (setccR8Effect 0x1029af 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[80, 81]
    (.letOp (n := 85) (.out 0x1029b3 (orR8R8Effect 0x1029b3 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[83, 76]
    (.letOp (n := 86) (.out 0x1029b3 (orR8R8Effect 0x1029b3 3 7 0) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 0] []) (.flag .ZF)) #v[83, 76]
    (.letOp (n := 87) (.exec 0x1029b3 (fun s => s.RIP = 0x1029b3) (orR8R8Effect 0x1029b3 3 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[83, 76]
    (.letOp (n := 88) (.pure (condOp 4)) #v[86]
    (.terminate (.condBr (Fin.last 88) ⟨.l1029c0, RegMap.args [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩ ⟨.l1029b8, RegMap.args [(0, 76), (1, 1), (2, 2), (3, 67), (4, 65), (5, 5), (6, 6), (7, 85), (8, 8), (9, 9), (11, 11), (12, 71), (13, 13), (14, 14), (15, 15), (19, 86), (22, 22), (39, 39), (50, 50), (51, 51)] 89⟩)))))))))))))))))))))))))))))))))))))

def bytes_l102980 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x98, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xFB, 0x48, 0xB8, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00, 0x00, 0x4D, 0x8B,
    0x61, 0x10, 0x49, 0x39, 0xC4, 0x0F, 0x97, 0xC0, 0x4C, 0x89, 0xC7, 0x48, 0xC1, 0xEF, 0x3D, 0x40,
    0x0F, 0x95, 0xC7, 0x40, 0x08, 0xC7, 0x74, 0x08]

theorem code_l102980 : ∀ x ∈ codeRange 0x102980 bytes_l102980, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2980 56 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1029b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1029b8 (StorePre 0x1029b8 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1029b8 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x1029b8 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l102b6a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1029b8 : List UInt8 :=
  [0xC6, 0x03, 0x01, 0xE9, 0xAA, 0x01, 0x00, 0x00]

theorem code_l1029b8 : ∀ x ∈ codeRange 0x1029b8 bytes_l1029b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29b8 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1029c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1029c0 (movR64R64Effect 0x1029c0 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[9]
    (.letOp (n := 54) (.exec 0x1029c0 (fun s => s.RIP = 0x1029c0) (movR64R64Effect 0x1029c0 14 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 55) (.exec 0x1029c3 (StorePre 0x1029c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1029c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029c3 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 56) (.exec 0x1029c8 (StorePre 0x1029c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1029c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029c8 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 57) (.exec 0x1029cd (StorePre 0x1029cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1029cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029cd 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 58) (.out 0x1029d2 (movR32M32Effect 0x1029d2 13 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 59) (.exec 0x1029d2 (LoadPre 0x1029d2 (fun s => AddrMode.addr (.base 2 .none) s (0x1029d2 + BitVec.ofNat 64 3)) 4) (movR32M32Effect 0x1029d2 13 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 60) (.out 0x1029d5 (movR32M32Effect 0x1029d5 15 (.base 2 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 61) (.exec 0x1029d5 (LoadPre 0x1029d5 (fun s => AddrMode.addr (.base 2 (.d8 0x4)) s (0x1029d5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1029d5 15 (.base 2 (.d8 0x4))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 62) (.out 0x1029d9 (movR32M32LowEffect 0x1029d9 3 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 63) (.exec 0x1029d9 (LoadPre 0x1029d9 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1029d9 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1029d9 3 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 64) (.exec 0x1029dc (StorePre 0x1029dc 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1029dc + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1029dc (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1029e8 (StorePre 0x1029e8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1029e8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1029e8 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1029f1 (StorePre 0x1029f1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1029f1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1029f1 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 67) (.out 0x1029f6 (leaR64Effect 0x1029f6 5 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 68) (.exec 0x1029f6 (fun s => s.RIP = 0x1029f6) (leaR64Effect 0x1029f6 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x1029fa (StorePre 0x1029fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1029fa + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1029fa 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 70) (.exec 0x1029ff (StorePre 0x1029ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1029ff + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1029ff 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 71) (.exec 0x102a04 (StorePre 0x102a04 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102a04 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102a04 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 72) (.exec 0x102a08 (StorePre 0x102a08 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x102a08 + BitVec.ofNat 64 8)) 4) (movM32Imm32Effect 0x102a08 8 (.sib 4 none 0 (.d8 0x1c)) 0x1000000) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x102a10 (leaR64Effect 0x102a10 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 74) (.exec 0x102a10 (fun s => s.RIP = 0x102a10) (leaR64Effect 0x102a10 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x102a15 (leaR64Effect 0x102a15 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 76) (.exec 0x102a15 (fun s => s.RIP = 0x102a15) (leaR64Effect 0x102a15 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x102a1a (movR64R64Effect 0x102a1a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 78) (.exec 0x102a1a (fun s => s.RIP = 0x102a1a) (movR64R64Effect 0x102a1a 6 5) (Reg.operands [.gpr 5] [])) #v[67]
    (.letOp (n := 79) (.out 0x102a1d (callEffect (fun _ => 0x106960) 0x102a22) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x102a1d (PushPre 0x102a1d 5) (callEffect (fun _ => 0x106960) 0x102a22) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x102a22⟩) #v[]
    (.terminate (.call ⟨.l106960, RegMap.args [(1, 1), (2, 75), (3, 62), (4, 79), (5, 67), (6, 77), (7, 73), (8, 8), (9, 9), (12, 12), (13, 58), (14, 53), (15, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l102a22, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1029c0 : List UInt8 :=
  [0x4D, 0x89, 0xCE, 0x48, 0x89, 0x5C, 0x24, 0x58, 0x48, 0x89, 0x4C, 0x24, 0x68, 0x4C, 0x89, 0x44,
    0x24, 0x70, 0x44, 0x8B, 0x2A, 0x44, 0x8B, 0x7A, 0x04, 0x8B, 0x5A, 0x08, 0x48, 0xC7, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x74, 0x24, 0x60, 0x48, 0x8D, 0x6E, 0x20, 0x44, 0x89, 0x6C, 0x24, 0x10, 0x44,
    0x89, 0x7C, 0x24, 0x14, 0x89, 0x5C, 0x24, 0x18, 0xC7, 0x44, 0x24, 0x1C, 0x00, 0x00, 0x00, 0x01,
    0x48, 0x8D, 0x7C, 0x24, 0x78, 0x48, 0x8D, 0x54, 0x24, 0x10, 0x48, 0x89, 0xEE, 0xE8, 0x3E, 0x3F,
    0x00, 0x00]

theorem code_l1029c0 : ∀ x ∈ codeRange 0x1029c0 bytes_l1029c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x29c0 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102a22 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102a22 (StorePre 0x102a22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102a22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a22 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 54) (.out 0x102a27 (movR64R64Effect 0x102a27 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[12]
    (.letOp (n := 55) (.exec 0x102a27 (fun s => s.RIP = 0x102a27) (movR64R64Effect 0x102a27 5 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 56) (.out 0x102a2a (leaR64Effect 0x102a2a 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x102a2a (fun s => s.RIP = 0x102a2a) (leaR64Effect 0x102a2a 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x102a2f (StorePre 0x102a2f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102a2f + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x102a2f 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 59) (.exec 0x102a34 (StorePre 0x102a34 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x102a34 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x102a34 15 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 60) (.exec 0x102a39 (StorePre 0x102a39 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x102a39 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x102a39 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 61) (.out 0x102a3d (movR64Imm64Effect 0x102a3d 0 0x100000001) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x102a3d (fun s => s.RIP = 0x102a3d) (movR64Imm64Effect 0x102a3d 0 0x100000001) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.exec 0x102a47 (StorePre 0x102a47 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x102a47 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a47 0 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x102a4c (movR64M64Effect 0x102a4c 15 (.base 14 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 14] []) (.reg (.gpr 15))) #v[14]
    (.letOp (n := 65) (.exec 0x102a4c (LoadPre 0x102a4c (fun s => AddrMode.addr (.base 14 .none) s (0x102a4c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102a4c 15 (.base 14 .none)) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x102a4f (movR64M64Effect 0x102a4f 13 (.base 14 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[14]
    (.letOp (n := 67) (.exec 0x102a4f (LoadPre 0x102a4f (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x102a4f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102a4f 13 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 68) (.out 0x102a53 (cmpR64Imm8Effect 0x102a53 12 0x11) (EffectPart.reads (.flag .CF) [.gpr 12] []) (.flag .CF)) #v[12]
    (.letOp (n := 69) (.exec 0x102a53 (fun s => s.RIP = 0x102a53) (cmpR64Imm8Effect 0x102a53 12 0x11) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 70) (.pure (condOp 2)) #v[68]
    (.terminate (.condBr (Fin.last 70) ⟨.l102aaf, RegMap.args [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l102a59, RegMap.args [(0, 61), (1, 56), (2, 2), (3, 3), (4, 4), (5, 54), (6, 6), (9, 9), (11, 11), (12, 12), (13, 66), (14, 14), (15, 64), (16, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l102a22 : List UInt8 :=
  [0x48, 0x89, 0x6C, 0x24, 0x30, 0x4C, 0x89, 0xE5, 0x48, 0x8D, 0x4C, 0x24, 0x38, 0x44, 0x89, 0x6C,
    0x24, 0x38, 0x44, 0x89, 0x7C, 0x24, 0x3C, 0x89, 0x5C, 0x24, 0x40, 0x48, 0xB8, 0x01, 0x00, 0x00,
    0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x44, 0x4D, 0x8B, 0x3E, 0x4D, 0x8B, 0x6E,
    0x08, 0x49, 0x83, 0xFC, 0x11, 0x72, 0x56]

theorem code_l102a22 : ∀ x ∈ codeRange 0x102a22 bytes_l102a22, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a22 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102a59 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102a59 (movR64R64Effect 0x102a59 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x102a59 (fun s => s.RIP = 0x102a59) (movR64R64Effect 0x102a59 0 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x102a5c (shrR64Effect 0x102a5c 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x102a5c (fun s => s.RIP = 0x102a5c) (shrR64Effect 0x102a5c 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x102a60 (movR64Imm64Effect 0x102a60 12 0xfffffffe0) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 58) (.exec 0x102a60 (fun s => s.RIP = 0x102a60) (movR64Imm64Effect 0x102a60 12 0xfffffffe0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x102a6a (addR64Imm8Effect 0x102a6a 12 0x10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.exec 0x102a6a (fun s => s.RIP = 0x102a6a) (addR64Imm8Effect 0x102a6a 12 0x10) (Reg.operands [.gpr 12] [])) #v[57]
    (.letOp (n := 61) (.out 0x102a6e (andR64R64Effect 0x102a6e 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5] []) (.reg (.gpr 12))) #v[59, 5]
    (.letOp (n := 62) (.exec 0x102a6e (fun s => s.RIP = 0x102a6e) (andR64R64Effect 0x102a6e 12 5) (Reg.operands [.gpr 12, .gpr 5] [])) #v[59, 5]
    (.letOp (n := 63) (.out 0x102a71 (movR32R32Effect 0x102a71 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[5]
    (.letOp (n := 64) (.exec 0x102a71 (fun s => s.RIP = 0x102a71) (movR32R32Effect 0x102a71 3 14 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 65) (.out 0x102a74 (andR32Imm8Effect 0x102a74 4 14 0xf) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.exec 0x102a74 (fun s => s.RIP = 0x102a74) (andR32Imm8Effect 0x102a74 4 14 0xf) (Reg.operands [.gpr 14] [])) #v[63]
    (.letOp (n := 67) (.out 0x102a78 (leaR64Effect 0x102a78 3 (.sib 15 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15, .gpr 12] []) (.reg (.gpr 3))) #v[15, 61]
    (.letOp (n := 68) (.exec 0x102a78 (fun s => s.RIP = 0x102a78) (leaR64Effect 0x102a78 3 (.sib 15 (some 12) 0 .none)) (Reg.operands [.gpr 15, .gpr 12] [])) #v[15, 61]
    (.letOp (n := 69) (.out 0x102a7c (addR64R64Effect 0x102a7c 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[61, 13]
    (.letOp (n := 70) (.exec 0x102a7c (fun s => s.RIP = 0x102a7c) (addR64R64Effect 0x102a7c 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[61, 13]
    (.letOp (n := 71) (.exec 0x102a7f (StorePre 0x102a7f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102a7f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a7f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 72) (.exec 0x102a84 (StorePre 0x102a84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102a84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a84 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 73) (.exec 0x102a89 (StorePre 0x102a89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102a89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a89 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 74) (.exec 0x102a8e (StorePre 0x102a8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102a8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102a8e 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 75) (.out 0x102a93 (leaR64Effect 0x102a93 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x102a93 (fun s => s.RIP = 0x102a93) (leaR64Effect 0x102a93 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x102a98 (leaR64Effect 0x102a98 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x102a98 (fun s => s.RIP = 0x102a98) (leaR64Effect 0x102a98 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x102a9d (callEffect (fun _ => 0x1084e0) 0x102aa2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 80) (.exec 0x102a9d (PushPre 0x102a9d 5) (callEffect (fun _ => 0x1084e0) 0x102aa2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.const ⟨64, 0x102aa2⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(0, 55), (1, 1), (3, 67), (4, 79), (5, 5), (6, 77), (7, 75), (11, 11), (12, 69), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l102aa2, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l102a59 : List UInt8 :=
  [0x48, 0x89, 0xE8, 0x48, 0xC1, 0xE8, 0x04, 0x49, 0xBC, 0xE0, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x00,
    0x00, 0x49, 0x83, 0xC4, 0x10, 0x49, 0x21, 0xEC, 0x41, 0x89, 0xEE, 0x41, 0x83, 0xE6, 0x0F, 0x4B,
    0x8D, 0x1C, 0x27, 0x4D, 0x01, 0xEC, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x4C, 0x89, 0x7C, 0x24, 0x18,
    0x4C, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8D, 0x7C, 0x24, 0x30, 0x48,
    0x8D, 0x74, 0x24, 0x10, 0xE8, 0x3E, 0x5A, 0x00, 0x00]

theorem code_l102a59 : ∀ x ∈ codeRange 0x102a59 bytes_l102a59, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2a59 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102aa2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102aa2 (movR64R64Effect 0x102aa2 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[3]
    (.letOp (n := 54) (.exec 0x102aa2 (fun s => s.RIP = 0x102aa2) (movR64R64Effect 0x102aa2 15 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x102aa5 (testR64R64Effect 0x102aa5 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 56) (.exec 0x102aa5 (fun s => s.RIP = 0x102aa5) (testR64R64Effect 0x102aa5 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l102abe, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l102aaa, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l102aa2 : List UInt8 :=
  [0x49, 0x89, 0xDF, 0x4D, 0x85, 0xF6, 0x75, 0x14]

theorem code_l102aa2 : ∀ x ∈ codeRange 0x102aa2 bytes_l102aa2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2aa2 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102aaa : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l102b3e, RegMap.args (entryMap (live .l102aaa)) 53⟩)

def bytes_l102aaa : List UInt8 :=
  [0xE9, 0x8F, 0x00, 0x00, 0x00]

theorem code_l102aaa : ∀ x ∈ codeRange 0x102aaa bytes_l102aaa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2aaa 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102aaf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102aaf (movR64R64Effect 0x102aaf 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 13] []) (.reg (.gpr 12))) #v[13]
    (.letOp (n := 54) (.exec 0x102aaf (fun s => s.RIP = 0x102aaf) (movR64R64Effect 0x102aaf 12 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x102ab2 (movR64R64Effect 0x102ab2 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[5]
    (.letOp (n := 56) (.exec 0x102ab2 (fun s => s.RIP = 0x102ab2) (movR64R64Effect 0x102ab2 14 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x102ab5 (testR64R64Effect 0x102ab5 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x102ab5 (fun s => s.RIP = 0x102ab5) (testR64R64Effect 0x102ab5 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l102b3e, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l102abe, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (9, 9), (11, 11), (12, 53), (13, 13), (14, 55), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l102aaf : List UInt8 :=
  [0x4D, 0x89, 0xEC, 0x49, 0x89, 0xEE, 0x4D, 0x85, 0xF6, 0x0F, 0x84, 0x80, 0x00, 0x00, 0x00]

theorem code_l102aaf : ∀ x ∈ codeRange 0x102aaf bytes_l102aaf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2aaf 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102abe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102abe (movR32Imm32Effect 0x102abe 5 0 0x10) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x102abe (fun s => s.RIP = 0x102abe) (movR32Imm32Effect 0x102abe 5 0 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x102ac3 (subR64R64Effect 0x102ac3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x102ac3 (fun s => s.RIP = 0x102ac3) (subR64R64Effect 0x102ac3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x102ac6 (xorR32R32Effect 0x102ac6 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x102ac6 (fun s => s.RIP = 0x102ac6) (xorR32R32Effect 0x102ac6 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x102ac8 (cmpR64Imm8Effect 0x102ac8 14 0x10) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 60) (.exec 0x102ac8 (fun s => s.RIP = 0x102ac8) (cmpR64Imm8Effect 0x102ac8 14 0x10) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x102acc (atFlags (condHolds 2) (cmovR64R64Effect 0x102acc 4 2 0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[57, 55, 59]
    (.letOp (n := 62) (.exec 0x102acc (fun s => s.RIP = 0x102acc) (atFlags (condHolds 2) (cmovR64R64Effect 0x102acc 4 2 0)) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 55, 59]
    (.letOp (n := 63) (.out 0x102ad0 (leaR64Effect 0x102ad0 7 (.sib 4 (some 14) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 14] []) (.reg (.gpr 7))) #v[4, 14]
    (.letOp (n := 64) (.exec 0x102ad0 (fun s => s.RIP = 0x102ad0) (leaR64Effect 0x102ad0 7 (.sib 4 (some 14) 0 .none)) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 65) (.out 0x102ad4 (addR64Imm32Effect 0x102ad4 7 0x88) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x102ad4 (fun s => s.RIP = 0x102ad4) (addR64Imm32Effect 0x102ad4 7 0x88) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x102adb (xorR32R32Effect 0x102adb 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 68) (.exec 0x102adb (fun s => s.RIP = 0x102adb) (xorR32R32Effect 0x102adb 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 69) (.out 0x102add (callEffect (callMemPtr 0x102add (.rip 0xfe745)) (0x102add + BitVec.ofNat 64 (callMemLen (.rip 0xfe745)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x102add (GoesTo (CallMemPre 0x102add (.rip 0xfe745)) (callEffect (callMemPtr 0x102add (.rip 0xfe745)) (0x102add + BitVec.ofNat 64 (callMemLen (.rip 0xfe745)))) 0x103eb0) (callEffect (callMemPtr 0x102add (.rip 0xfe745)) (0x102add + BitVec.ofNat 64 (callMemLen (.rip 0xfe745)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x102ae3⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(0, 55), (2, 61), (3, 3), (4, 69), (5, 5), (6, 67), (7, 65), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l102ae3, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l102abe : List UInt8 :=
  [0xB8, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xF0, 0x31, 0xD2, 0x49, 0x83, 0xFE, 0x10, 0x48, 0x0F,
    0x42, 0xD0, 0x4A, 0x8D, 0x3C, 0x34, 0x48, 0x81, 0xC7, 0x88, 0x00, 0x00, 0x00, 0x31, 0xF6, 0xFF,
    0x15, 0x45, 0xE7, 0x0F, 0x00]

theorem code_l102abe : ∀ x ∈ codeRange 0x102abe bytes_l102abe, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2abe 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102ae3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102ae3 (StorePre 0x102ae3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102ae3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102ae3 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 54) (.out 0x102ae8 (leaR64Effect 0x102ae8 13 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 55) (.exec 0x102ae8 (fun s => s.RIP = 0x102ae8) (leaR64Effect 0x102ae8 13 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x102af0 (leaR64Effect 0x102af0 3 (.rip 0x1409)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 57) (.exec 0x102af0 (fun s => s.RIP = 0x102af0) (leaR64Effect 0x102af0 3 (.rip 0x1409)) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x102af7 (movR64R64Effect 0x102af7 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[54]
    (.letOp (n := 59) (.exec 0x102af7 (fun s => s.RIP = 0x102af7) (movR64R64Effect 0x102af7 7 13) (Reg.operands [.gpr 13] [])) #v[54]
    (.letOp (n := 60) (.out 0x102afa (movR64R64Effect 0x102afa 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 61) (.exec 0x102afa (fun s => s.RIP = 0x102afa) (movR64R64Effect 0x102afa 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 62) (.out 0x102afd (movR64R64Effect 0x102afd 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 63) (.exec 0x102afd (fun s => s.RIP = 0x102afd) (movR64R64Effect 0x102afd 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 64) (.out 0x102b00 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b02) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 56]
    (.letOp (n := 65) (.exec 0x102b00 (GoesTo (CallPre 0x102b00 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b02) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b02) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 56]
    (.letOp (n := 66) (.const ⟨64, 0x102b02⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 62), (3, 56), (4, 64), (5, 5), (6, 60), (7, 58), (9, 9), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l102b02, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l102ae3 : List UInt8 :=
  [0x4C, 0x89, 0x6C, 0x24, 0x50, 0x4C, 0x8D, 0xAC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x1D,
    0x09, 0x14, 0x00, 0x00, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2, 0xFF, 0xD3]

theorem code_l102ae3 : ∀ x ∈ codeRange 0x102ae3 bytes_l102ae3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2ae3 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b02 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102b02 (leaR64Effect 0x102b02 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x102b02 (fun s => s.RIP = 0x102b02) (leaR64Effect 0x102b02 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x102b07 (StorePre 0x102b07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102b07 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b07 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x102b0c (StorePre 0x102b0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102b0c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b0c 13 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 57) (.exec 0x102b11 (StorePre 0x102b11 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102b11 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b11 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 58) (.exec 0x102b16 (StorePre 0x102b16 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102b16 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102b16 (.sib 4 none 0 (.d8 0x28)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102b1f (leaR64Effect 0x102b1f 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x102b1f (fun s => s.RIP = 0x102b1f) (leaR64Effect 0x102b1f 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x102b24 (leaR64Effect 0x102b24 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x102b24 (fun s => s.RIP = 0x102b24) (leaR64Effect 0x102b24 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x102b29 (callEffect (fun _ => 0x1084e0) 0x102b2e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x102b29 (PushPre 0x102b29 5) (callEffect (fun _ => 0x1084e0) 0x102b2e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x102b2e⟩) #v[]
    (.terminate (.call ⟨.l1084e0, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 63), (5, 5), (6, 61), (7, 59), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l102b2e, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l102b02 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4C, 0x89, 0x6C, 0x24, 0x18, 0x4C,
    0x89, 0x6C, 0x24, 0x20, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C,
    0x24, 0x30, 0x48, 0x8D, 0x74, 0x24, 0x10, 0xE8, 0xB2, 0x59, 0x00, 0x00]

theorem code_l102b02 : ∀ x ∈ codeRange 0x102b02 bytes_l102b02, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b02 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b2e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102b2e (movR64R64Effect 0x102b2e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 54) (.exec 0x102b2e (fun s => s.RIP = 0x102b2e) (movR64R64Effect 0x102b2e 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x102b31 (movR64R64Effect 0x102b31 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 56) (.exec 0x102b31 (fun s => s.RIP = 0x102b31) (movR64R64Effect 0x102b31 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x102b34 (movR64M64Effect 0x102b34 13 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x102b34 (LoadPre 0x102b34 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102b34 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b34 13 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x102b39 (movR64R64Effect 0x102b39 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x102b39 (fun s => s.RIP = 0x102b39) (movR64R64Effect 0x102b39 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x102b3c (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b3e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 62) (.exec 0x102b3c (GoesTo (CallPre 0x102b3c 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b3e) 0x103f00) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x102b3e) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 63) (.const ⟨64, 0x102b3e⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(2, 59), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l102b3e, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l102b2e : List UInt8 :=
  [0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xEE, 0x4C, 0x8B, 0x6C, 0x24, 0x50, 0x4C, 0x89, 0xF2, 0xFF, 0xD3]

theorem code_l102b2e : ∀ x ∈ codeRange 0x102b2e bytes_l102b2e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b2e 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b3e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102b3e (movR64M64Effect 0x102b3e 3 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x102b3e (LoadPre 0x102b3e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x102b3e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b3e 3 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102b43 (leaR64Effect 0x102b43 7 (.base 3 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x102b43 (fun s => s.RIP = 0x102b43) (leaR64Effect 0x102b43 7 (.base 3 (.d8 0x1))) (Reg.operands [.gpr 3] [])) #v[53]
    (.letOp (n := 57) (.exec 0x102b47 (StorePre 0x102b47 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102b47 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102b47 5 (.sib 4 none 0 .none)) (Reg.operands [.gpr 5, .gpr 4] [])) #v[5, 4]
    (.letOp (n := 58) (.out 0x102b4b (leaR64Effect 0x102b4b 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x102b4b (fun s => s.RIP = 0x102b4b) (leaR64Effect 0x102b4b 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x102b50 (movR64M64Effect 0x102b50 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x102b50 (LoadPre 0x102b50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102b50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b50 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x102b55 (movR64M64Effect 0x102b55 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x102b55 (LoadPre 0x102b55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x102b55 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b55 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x102b5a (movR64M64Effect 0x102b5a 8 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 65) (.exec 0x102b5a (LoadPre 0x102b5a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x102b5a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102b5a 8 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x102b5f (movR64R64Effect 0x102b5f 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[13]
    (.letOp (n := 67) (.exec 0x102b5f (fun s => s.RIP = 0x102b5f) (movR64R64Effect 0x102b5f 9 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 68) (.out 0x102b62 (callEffect (fun _ => 0x101c20) 0x102b67) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x102b62 (PushPre 0x102b62 5) (callEffect (fun _ => 0x101c20) 0x102b67) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.const ⟨64, 0x102b67⟩) #v[]
    (.terminate (.call ⟨.l101c20, RegMap.args [(1, 62), (2, 58), (3, 53), (4, 68), (5, 5), (6, 60), (7, 55), (8, 64), (9, 66), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ { target := .l102b67, kept := #v[], arity := rfl, guard := some (Fin.last 70) })))))))))))))))))))

def bytes_l102b3e : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x58, 0x48, 0x8D, 0x7B, 0x01, 0x48, 0x89, 0x2C, 0x24, 0x48, 0x8D, 0x54,
    0x24, 0x78, 0x48, 0x8B, 0x74, 0x24, 0x60, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x4C, 0x8B, 0x44, 0x24,
    0x70, 0x4D, 0x89, 0xE9, 0xE8, 0xB9, 0xF0, 0xFF, 0xFF]

theorem code_l102b3e : ∀ x ∈ codeRange 0x102b3e bytes_l102b3e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b3e 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b67 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102b67 (StorePre 0x102b67 3 (fun s => AddrMode.addr (.base 3 .none) s (0x102b67 + BitVec.ofNat 64 3)) 1) (movM8Imm8Effect 0x102b67 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l102b6a, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l102b67 : List UInt8 :=
  [0xC6, 0x03, 0x00]

theorem code_l102b67 : ∀ x ∈ codeRange 0x102b67 bytes_l102b67, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b67 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102b6a (movR64R64Effect 0x102b6a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x102b6a (fun s => s.RIP = 0x102b6a) (movR64R64Effect 0x102b6a 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x102b6d (addR64Imm32Effect 0x102b6d 4 0x98) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x102b6d (fun s => s.RIP = 0x102b6d) (addR64Imm32Effect 0x102b6d 4 0x98) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102b74 (popR64Effect 0x102b74 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x102b74 (popR64Effect 0x102b74 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x102b74 (PopPre 0x102b74) (popR64Effect 0x102b74 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x102b75 (popR64Effect 0x102b75 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x102b75 (popR64Effect 0x102b75 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x102b75 (PopPre 0x102b75) (popR64Effect 0x102b75 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x102b77 (popR64Effect 0x102b77 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x102b77 (popR64Effect 0x102b77 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x102b77 (PopPre 0x102b77) (popR64Effect 0x102b77 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x102b79 (popR64Effect 0x102b79 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x102b79 (popR64Effect 0x102b79 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x102b79 (PopPre 0x102b79) (popR64Effect 0x102b79 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x102b7b (popR64Effect 0x102b7b 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x102b7b (popR64Effect 0x102b7b 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x102b7b (PopPre 0x102b7b) (popR64Effect 0x102b7b 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x102b7d (popR64Effect 0x102b7d 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x102b7d (popR64Effect 0x102b7d 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x102b7d (PopPre 0x102b7d) (popR64Effect 0x102b7d 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x102b7e (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x102b7e (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x102b7e (RetPre 0x102b7e) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l102b6a : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x98, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l102b6a : ∀ x ∈ codeRange 0x102b6a bytes_l102b6a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b6a 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102b80 (subR64Imm8Effect 0x102b80 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x102b80 (fun s => s.RIP = 0x102b80) (subR64Imm8Effect 0x102b80 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102b84 (movR64R64Effect 0x102b84 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x102b84 (fun s => s.RIP = 0x102b84) (movR64R64Effect 0x102b84 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x102b87 (movR64M64Effect 0x102b87 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 58) (.exec 0x102b87 (LoadPre 0x102b87 (fun s => AddrMode.addr (.base 6 .none) s (0x102b87 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102b87 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x102b8a (movR64M64Effect 0x102b8a 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 60) (.exec 0x102b8a (LoadPre 0x102b8a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x102b8a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102b8a 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.exec 0x102b8e (StorePre 0x102b8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102b8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102b8e 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[59, 53]
    (.letOp (n := 62) (.exec 0x102b93 (StorePre 0x102b93 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102b93 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102b93 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 53]
    (.letOp (n := 63) (.exec 0x102b97 (StorePre 0x102b97 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102b97 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102b97 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.exec 0x102ba0 (StorePre 0x102ba0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102ba0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102ba0 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 65) (.exec 0x102ba9 (StorePre 0x102ba9 3 (fun s => AddrMode.addr (.base 7 .none) s (0x102ba9 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x102ba9 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 66) (.exec 0x102bac (StorePre 0x102bac 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x102bac + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102bac 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[59, 7]
    (.letOp (n := 67) (.exec 0x102bb0 (StorePre 0x102bb0 8 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x102bb0 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102bb0 (.base 7 (.d8 0x18)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 68) (.exec 0x102bb8 (StorePre 0x102bb8 8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102bb8 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x102bb8 (.base 7 (.d8 0x10)) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x102bc0 (addR64Imm8Effect 0x102bc0 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 70) (.exec 0x102bc0 (fun s => s.RIP = 0x102bc0) (addR64Imm8Effect 0x102bc0 4 0x28) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 71) (.out 0x102bc4 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[69]
    (.letOp (n := 72) (.out 0x102bc4 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x102bc4 (RetPre 0x102bc4) (retEffect) (Reg.operands [.gpr 4] [])) #v[69]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 57), (2, 59), (3, 3), (4, 72), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74) (some ⟨71, by decide⟩)))))))))))))))))))))))

def bytes_l102b80 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x28, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x0E, 0x48, 0x8B, 0x56, 0x08, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x89, 0x0C, 0x24, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x0F, 0x48, 0x89, 0x57, 0x08,
    0x48, 0xC7, 0x47, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00,
    0x48, 0x83, 0xC4, 0x28, 0xC3]

theorem code_l102b80 : ∀ x ∈ codeRange 0x102b80 bytes_l102b80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2b80 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l102bd0_30 : Block Op Label signature Reg.count 1242 :=
  .letOp (n := 1242) (.out 0x10347e (movR64M64Effect 0x10347e 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 1243) (.exec 0x10347e (LoadPre 0x10347e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10347e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10347e 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1244) (.exec 0x103483 (StorePre 0x103483 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x103483 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103483 0 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1228, 1242]
    (.letOp (n := 1245) (.exec 0x103487 (StorePre 0x103487 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x103487 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103487 13 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 1] [])) #v[1240, 1242]
    (.letOp (n := 1246) (.out 0x10348b (addR64Imm8Effect 0x10348b 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 1247) (.exec 0x10348b (fun s => s.RIP = 0x10348b) (addR64Imm8Effect 0x10348b 4 0x50) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1248) (.out 0x10348f (popR64Effect 0x10348f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[1246]
    (.letOp (n := 1249) (.out 0x10348f (popR64Effect 0x10348f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1246]
    (.letOp (n := 1250) (.exec 0x10348f (PopPre 0x10348f) (popR64Effect 0x10348f 1 3) (Reg.operands [.gpr 4] [])) #v[1246]
    (.letOp (n := 1251) (.out 0x103490 (popR64Effect 0x103490 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[1249]
    (.letOp (n := 1252) (.out 0x103490 (popR64Effect 0x103490 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1249]
    (.letOp (n := 1253) (.exec 0x103490 (PopPre 0x103490) (popR64Effect 0x103490 2 12) (Reg.operands [.gpr 4] [])) #v[1249]
    (.letOp (n := 1254) (.out 0x103492 (popR64Effect 0x103492 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[1252]
    (.letOp (n := 1255) (.out 0x103492 (popR64Effect 0x103492 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1252]
    (.letOp (n := 1256) (.exec 0x103492 (PopPre 0x103492) (popR64Effect 0x103492 2 13) (Reg.operands [.gpr 4] [])) #v[1252]
    (.letOp (n := 1257) (.out 0x103494 (popR64Effect 0x103494 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[1255]
    (.letOp (n := 1258) (.out 0x103494 (popR64Effect 0x103494 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1255]
    (.letOp (n := 1259) (.exec 0x103494 (PopPre 0x103494) (popR64Effect 0x103494 2 14) (Reg.operands [.gpr 4] [])) #v[1255]
    (.letOp (n := 1260) (.out 0x103496 (popR64Effect 0x103496 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[1258]
    (.letOp (n := 1261) (.out 0x103496 (popR64Effect 0x103496 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1258]
    (.letOp (n := 1262) (.exec 0x103496 (PopPre 0x103496) (popR64Effect 0x103496 2 15) (Reg.operands [.gpr 4] [])) #v[1258]
    (.letOp (n := 1263) (.out 0x103498 (popR64Effect 0x103498 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[1261]
    (.letOp (n := 1264) (.out 0x103498 (popR64Effect 0x103498 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1261]
    (.letOp (n := 1265) (.exec 0x103498 (PopPre 0x103498) (popR64Effect 0x103498 1 5) (Reg.operands [.gpr 4] [])) #v[1261]
    (.letOp (n := 1266) (.out 0x103499 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[1264]
    (.letOp (n := 1267) (.out 0x103499 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[1264]
    (.letOp (n := 1268) (.exec 0x103499 (RetPre 0x103499) (retEffect) (Reg.operands [.gpr 4] [])) #v[1264]
    (.terminate (.ret (RegMap.args [(0, 1228), (1, 1242), (2, 1032), (3, 1248), (4, 1267), (5, 1263), (6, 1230), (7, 1220), (8, 1194), (9, 1236), (10, 1210), (11, 1164), (12, 1251), (13, 1254), (14, 1257), (15, 1260), (22, 22), (39, 39), (50, 50), (51, 51)] 1269) (some ⟨1266, by decide⟩)))))))))))))))))))))))))))))

def bytes_l102bd0_30 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x41, 0x18, 0x4C, 0x89, 0x69, 0x10, 0x48, 0x83, 0xC4,
    0x50, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l102bd0_30 : ∀ x ∈ codeRange 0x10347e bytes_l102bd0_30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x347e 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l102bd0_29 : Block Op Label signature Reg.count 1202 :=
  .letOp (n := 1202) (.out 0x10343d (xorR64R64Effect 0x10343d 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[1200, 1156]
    (.letOp (n := 1203) (.exec 0x10343d (fun s => s.RIP = 0x10343d) (xorR64R64Effect 0x10343d 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[1200, 1156]
    (.letOp (n := 1204) (.out 0x103440 (shrR64Effect 0x103440 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1160]
    (.letOp (n := 1205) (.exec 0x103440 (fun s => s.RIP = 0x103440) (shrR64Effect 0x103440 3 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1160]
    (.letOp (n := 1206) (.out 0x103443 (shrR64Effect 0x103443 4 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1156]
    (.letOp (n := 1207) (.exec 0x103443 (fun s => s.RIP = 0x103443) (shrR64Effect 0x103443 4 10 7) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1156]
    (.letOp (n := 1208) (.out 0x103447 (xorR64R64Effect 0x103447 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[1206, 1178]
    (.letOp (n := 1209) (.exec 0x103447 (fun s => s.RIP = 0x103447) (xorR64R64Effect 0x103447 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[1206, 1178]
    (.letOp (n := 1210) (.out 0x10344a (xorR64R64Effect 0x10344a 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[1208, 1204]
    (.letOp (n := 1211) (.exec 0x10344a (fun s => s.RIP = 0x10344a) (xorR64R64Effect 0x10344a 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[1208, 1204]
    (.letOp (n := 1212) (.out 0x10344d (movR64R64Effect 0x10344d 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1194]
    (.letOp (n := 1213) (.exec 0x10344d (fun s => s.RIP = 0x10344d) (movR64R64Effect 0x10344d 1 8) (Reg.operands [.gpr 8] [])) #v[1194]
    (.letOp (n := 1214) (.out 0x103450 (shrR64Effect 0x103450 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1212]
    (.letOp (n := 1215) (.exec 0x103450 (fun s => s.RIP = 0x103450) (shrR64Effect 0x103450 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1212]
    (.letOp (n := 1216) (.out 0x103454 (movR64R64Effect 0x103454 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[1194]
    (.letOp (n := 1217) (.exec 0x103454 (fun s => s.RIP = 0x103454) (movR64R64Effect 0x103454 7 8) (Reg.operands [.gpr 8] [])) #v[1194]
    (.letOp (n := 1218) (.out 0x103457 (shrR64Effect 0x103457 4 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1216]
    (.letOp (n := 1219) (.exec 0x103457 (fun s => s.RIP = 0x103457) (shrR64Effect 0x103457 4 7 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1216]
    (.letOp (n := 1220) (.out 0x10345b (xorR64R64Effect 0x10345b 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[1218, 1214]
    (.letOp (n := 1221) (.exec 0x10345b (fun s => s.RIP = 0x10345b) (xorR64R64Effect 0x10345b 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[1218, 1214]
    (.letOp (n := 1222) (.out 0x10345e (xorR64R64Effect 0x10345e 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1120, 1194]
    (.letOp (n := 1223) (.exec 0x10345e (fun s => s.RIP = 0x10345e) (xorR64R64Effect 0x10345e 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1120, 1194]
    (.letOp (n := 1224) (.out 0x103461 (shrR64Effect 0x103461 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1222]
    (.letOp (n := 1225) (.exec 0x103461 (fun s => s.RIP = 0x103461) (shrR64Effect 0x103461 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1222]
    (.letOp (n := 1226) (.out 0x103464 (xorR64R64Effect 0x103464 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[1224, 1220]
    (.letOp (n := 1227) (.exec 0x103464 (fun s => s.RIP = 0x103464) (xorR64R64Effect 0x103464 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[1224, 1220]
    (.letOp (n := 1228) (.out 0x103467 (xorR64R64Effect 0x103467 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[1226, 1194]
    (.letOp (n := 1229) (.exec 0x103467 (fun s => s.RIP = 0x103467) (xorR64R64Effect 0x103467 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[1226, 1194]
    (.letOp (n := 1230) (.out 0x10346a (shlR64Effect 0x10346a 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1196]
    (.letOp (n := 1231) (.exec 0x10346a (fun s => s.RIP = 0x10346a) (shlR64Effect 0x10346a 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1196]
    (.letOp (n := 1232) (.out 0x10346e (shlR64Effect 0x10346e 4 9 62) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1198]
    (.letOp (n := 1233) (.exec 0x10346e (fun s => s.RIP = 0x10346e) (shlR64Effect 0x10346e 4 9 62) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1198]
    (.letOp (n := 1234) (.out 0x103472 (xorR64R64Effect 0x103472 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[1232, 1230]
    (.letOp (n := 1235) (.exec 0x103472 (fun s => s.RIP = 0x103472) (xorR64R64Effect 0x103472 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[1232, 1230]
    (.letOp (n := 1236) (.out 0x103475 (xorR64R64Effect 0x103475 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[1234, 1210]
    (.letOp (n := 1237) (.exec 0x103475 (fun s => s.RIP = 0x103475) (xorR64R64Effect 0x103475 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[1234, 1210]
    (.letOp (n := 1238) (.out 0x103478 (xorR64R64Effect 0x103478 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[1202, 1164]
    (.letOp (n := 1239) (.exec 0x103478 (fun s => s.RIP = 0x103478) (xorR64R64Effect 0x103478 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[1202, 1164]
    (.letOp (n := 1240) (.out 0x10347b (xorR64R64Effect 0x10347b 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 9] []) (.reg (.gpr 13))) #v[1238, 1236]
    (.letOp (n := 1241) (.exec 0x10347b (fun s => s.RIP = 0x10347b) (xorR64R64Effect 0x10347b 13 9) (Reg.operands [.gpr 13, .gpr 9] [])) #v[1238, 1236]
    (b_l102bd0_30))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_29 : List UInt8 :=
  [0x4D, 0x31, 0xD5, 0x48, 0xD1, 0xE9, 0x49, 0xC1, 0xEA, 0x07, 0x49, 0x31, 0xFA, 0x49, 0x31, 0xCA,
    0x4C, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x02, 0x4C, 0x89, 0xC7, 0x48, 0xC1, 0xEF, 0x07, 0x48, 0x31,
    0xCF, 0x4C, 0x31, 0xC0, 0x48, 0xD1, 0xE8, 0x48, 0x31, 0xF8, 0x4C, 0x31, 0xC0, 0x48, 0xC1, 0xE6,
    0x3F, 0x49, 0xC1, 0xE1, 0x3E, 0x49, 0x31, 0xF1, 0x4D, 0x31, 0xD1, 0x4D, 0x31, 0xDD, 0x4D, 0x31,
    0xCD] ++ bytes_l102bd0_30

theorem code_l102bd0_29 : ∀ x ∈ codeRange 0x10343d bytes_l102bd0_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x343d 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_30

def b_l102bd0_28 : Block Op Label signature Reg.count 1162 :=
  .letOp (n := 1162) (.out 0x1033f8 (xorR64R64Effect 0x1033f8 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[627, 1156]
    (.letOp (n := 1163) (.exec 0x1033f8 (fun s => s.RIP = 0x1033f8) (xorR64R64Effect 0x1033f8 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[627, 1156]
    (.letOp (n := 1164) (.out 0x1033fb (movR64M64Effect 0x1033fb 11 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 1165) (.exec 0x1033fb (LoadPre 0x1033fb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1033fb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033fb 11 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1166) (.out 0x103400 (xorR64R64Effect 0x103400 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[1162, 1164]
    (.letOp (n := 1167) (.exec 0x103400 (fun s => s.RIP = 0x103400) (xorR64R64Effect 0x103400 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[1162, 1164]
    (.letOp (n := 1168) (.out 0x103403 (xorR64R64Effect 0x103403 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[1166, 1158]
    (.letOp (n := 1169) (.exec 0x103403 (fun s => s.RIP = 0x103403) (xorR64R64Effect 0x103403 13 7) (Reg.operands [.gpr 13, .gpr 7] [])) #v[1166, 1158]
    (.letOp (n := 1170) (.out 0x103406 (movR64R64Effect 0x103406 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 10] []) (.reg (.gpr 7))) #v[1156]
    (.letOp (n := 1171) (.exec 0x103406 (fun s => s.RIP = 0x103406) (movR64R64Effect 0x103406 7 10) (Reg.operands [.gpr 10] [])) #v[1156]
    (.letOp (n := 1172) (.out 0x103409 (movR64R64Effect 0x103409 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[1156]
    (.letOp (n := 1173) (.exec 0x103409 (fun s => s.RIP = 0x103409) (movR64R64Effect 0x103409 6 10) (Reg.operands [.gpr 10] [])) #v[1156]
    (.letOp (n := 1174) (.out 0x10340c (shrR64Effect 0x10340c 3 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1172]
    (.letOp (n := 1175) (.exec 0x10340c (fun s => s.RIP = 0x10340c) (shrR64Effect 0x10340c 3 6 1) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1172]
    (.letOp (n := 1176) (.out 0x10340f (shrR64Effect 0x10340f 4 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1170]
    (.letOp (n := 1177) (.exec 0x10340f (fun s => s.RIP = 0x10340f) (shrR64Effect 0x10340f 4 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1170]
    (.letOp (n := 1178) (.out 0x103413 (xorR64R64Effect 0x103413 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[1176, 1174]
    (.letOp (n := 1179) (.exec 0x103413 (fun s => s.RIP = 0x103413) (xorR64R64Effect 0x103413 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[1176, 1174]
    (.letOp (n := 1180) (.out 0x103416 (movR64R64Effect 0x103416 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[1156]
    (.letOp (n := 1181) (.exec 0x103416 (fun s => s.RIP = 0x103416) (movR64R64Effect 0x103416 8 10) (Reg.operands [.gpr 10] [])) #v[1156]
    (.letOp (n := 1182) (.out 0x103419 (movR64M64Effect 0x103419 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 1183) (.exec 0x103419 (LoadPre 0x103419 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x103419 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103419 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1184) (.out 0x10341e (shlR64Effect 0x10341e 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1182]
    (.letOp (n := 1185) (.exec 0x10341e (fun s => s.RIP = 0x10341e) (shlR64Effect 0x10341e 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1182]
    (.letOp (n := 1186) (.out 0x103422 (shlR64Effect 0x103422 4 9 62) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1154]
    (.letOp (n := 1187) (.exec 0x103422 (fun s => s.RIP = 0x103422) (shlR64Effect 0x103422 4 9 62) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1154]
    (.letOp (n := 1188) (.out 0x103426 (xorR64R64Effect 0x103426 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[1186, 1184]
    (.letOp (n := 1189) (.exec 0x103426 (fun s => s.RIP = 0x103426) (xorR64R64Effect 0x103426 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[1186, 1184]
    (.letOp (n := 1190) (.out 0x103429 (shlR64Effect 0x103429 4 8 57) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1180]
    (.letOp (n := 1191) (.exec 0x103429 (fun s => s.RIP = 0x103429) (shlR64Effect 0x103429 4 8 57) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1180]
    (.letOp (n := 1192) (.out 0x10342d (xorR64R64Effect 0x10342d 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[1190, 1188]
    (.letOp (n := 1193) (.exec 0x10342d (fun s => s.RIP = 0x10342d) (xorR64R64Effect 0x10342d 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[1190, 1188]
    (.letOp (n := 1194) (.out 0x103430 (xorR64R64Effect 0x103430 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[1192, 1168]
    (.letOp (n := 1195) (.exec 0x103430 (fun s => s.RIP = 0x103430) (xorR64R64Effect 0x103430 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[1192, 1168]
    (.letOp (n := 1196) (.out 0x103433 (movR64R64Effect 0x103433 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[1168]
    (.letOp (n := 1197) (.exec 0x103433 (fun s => s.RIP = 0x103433) (movR64R64Effect 0x103433 6 13) (Reg.operands [.gpr 13] [])) #v[1168]
    (.letOp (n := 1198) (.out 0x103436 (movR64R64Effect 0x103436 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 13] []) (.reg (.gpr 9))) #v[1168]
    (.letOp (n := 1199) (.exec 0x103436 (fun s => s.RIP = 0x103436) (movR64R64Effect 0x103436 9 13) (Reg.operands [.gpr 13] [])) #v[1168]
    (.letOp (n := 1200) (.out 0x103439 (shlR64Effect 0x103439 4 13 57) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1168]
    (.letOp (n := 1201) (.exec 0x103439 (fun s => s.RIP = 0x103439) (shlR64Effect 0x103439 4 13 57) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1168]
    (b_l102bd0_29))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_28 : List UInt8 :=
  [0x4D, 0x31, 0xD5, 0x4C, 0x8B, 0x5C, 0x24, 0x28, 0x4D, 0x31, 0xDD, 0x49, 0x31, 0xFD, 0x4C, 0x89,
    0xD7, 0x4C, 0x89, 0xD6, 0x48, 0xD1, 0xEE, 0x48, 0xC1, 0xEF, 0x02, 0x48, 0x31, 0xF7, 0x4D, 0x89,
    0xD0, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0xC1, 0xE6, 0x3F, 0x49, 0xC1, 0xE1, 0x3E, 0x49, 0x31,
    0xF1, 0x49, 0xC1, 0xE0, 0x39, 0x4D, 0x31, 0xC8, 0x4D, 0x31, 0xE8, 0x4C, 0x89, 0xEE, 0x4D, 0x89,
    0xE9, 0x49, 0xC1, 0xE5, 0x39] ++ bytes_l102bd0_29

theorem code_l102bd0_28 : ∀ x ∈ codeRange 0x1033f8 bytes_l102bd0_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x33f8 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_29

def b_l102bd0_27 : Block Op Label signature Reg.count 1122 :=
  .letOp (n := 1122) (.out 0x1033b3 (bswapR64Effect 0x1033b3 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[1044]
    (.letOp (n := 1123) (.exec 0x1033b3 (fun s => s.RIP = 0x1033b3) (bswapR64Effect 0x1033b3 3 8) (Reg.operands [.gpr 8] [])) #v[1044]
    (.letOp (n := 1124) (.out 0x1033b6 (movR64R64Effect 0x1033b6 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1122]
    (.letOp (n := 1125) (.exec 0x1033b6 (fun s => s.RIP = 0x1033b6) (movR64R64Effect 0x1033b6 1 8) (Reg.operands [.gpr 8] [])) #v[1122]
    (.letOp (n := 1126) (.out 0x1033b9 (shrR64Effect 0x1033b9 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1124]
    (.letOp (n := 1127) (.exec 0x1033b9 (fun s => s.RIP = 0x1033b9) (shrR64Effect 0x1033b9 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1124]
    (.letOp (n := 1128) (.out 0x1033bd (andR64R64Effect 0x1033bd 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[1126, 1050]
    (.letOp (n := 1129) (.exec 0x1033bd (fun s => s.RIP = 0x1033bd) (andR64R64Effect 0x1033bd 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[1126, 1050]
    (.letOp (n := 1130) (.out 0x1033c0 (andR64R64Effect 0x1033c0 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[1122, 1050]
    (.letOp (n := 1131) (.exec 0x1033c0 (fun s => s.RIP = 0x1033c0) (andR64R64Effect 0x1033c0 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[1122, 1050]
    (.letOp (n := 1132) (.out 0x1033c3 (shlR64Effect 0x1033c3 4 8 4) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1130]
    (.letOp (n := 1133) (.exec 0x1033c3 (fun s => s.RIP = 0x1033c3) (shlR64Effect 0x1033c3 4 8 4) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1130]
    (.letOp (n := 1134) (.out 0x1033c7 (orR64R64Effect 0x1033c7 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1132, 1128]
    (.letOp (n := 1135) (.exec 0x1033c7 (fun s => s.RIP = 0x1033c7) (orR64R64Effect 0x1033c7 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1132, 1128]
    (.letOp (n := 1136) (.out 0x1033ca (movR64R64Effect 0x1033ca 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[1134]
    (.letOp (n := 1137) (.exec 0x1033ca (fun s => s.RIP = 0x1033ca) (movR64R64Effect 0x1033ca 1 8) (Reg.operands [.gpr 8] [])) #v[1134]
    (.letOp (n := 1138) (.out 0x1033cd (andR64R64Effect 0x1033cd 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1136, 1062]
    (.letOp (n := 1139) (.exec 0x1033cd (fun s => s.RIP = 0x1033cd) (andR64R64Effect 0x1033cd 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1136, 1062]
    (.letOp (n := 1140) (.out 0x1033d0 (shrR64Effect 0x1033d0 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1134]
    (.letOp (n := 1141) (.exec 0x1033d0 (fun s => s.RIP = 0x1033d0) (shrR64Effect 0x1033d0 4 8 2) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1134]
    (.letOp (n := 1142) (.out 0x1033d4 (andR64R64Effect 0x1033d4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[1140, 1062]
    (.letOp (n := 1143) (.exec 0x1033d4 (fun s => s.RIP = 0x1033d4) (andR64R64Effect 0x1033d4 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[1140, 1062]
    (.letOp (n := 1144) (.out 0x1033d7 (leaR64Effect 0x1033d7 1 (.sib 8 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8, .gpr 1] []) (.reg (.gpr 1))) #v[1142, 1138]
    (.letOp (n := 1145) (.exec 0x1033d7 (fun s => s.RIP = 0x1033d7) (leaR64Effect 0x1033d7 1 (.sib 8 (some 1) 2 .none)) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1142, 1138]
    (.letOp (n := 1146) (.out 0x1033db (andR64R64Effect 0x1033db 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1114, 1144]
    (.letOp (n := 1147) (.exec 0x1033db (fun s => s.RIP = 0x1033db) (andR64R64Effect 0x1033db 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1114, 1144]
    (.letOp (n := 1148) (.out 0x1033de (shrR64Effect 0x1033de 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1144]
    (.letOp (n := 1149) (.exec 0x1033de (fun s => s.RIP = 0x1033de) (shrR64Effect 0x1033de 3 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1144]
    (.letOp (n := 1150) (.out 0x1033e1 (andR64R64Effect 0x1033e1 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[1148, 1080]
    (.letOp (n := 1151) (.exec 0x1033e1 (fun s => s.RIP = 0x1033e1) (andR64R64Effect 0x1033e1 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[1148, 1080]
    (.letOp (n := 1152) (.out 0x1033e4 (movR64M64Effect 0x1033e4 10 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 1153) (.exec 0x1033e4 (LoadPre 0x1033e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1033e4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033e4 10 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1154) (.out 0x1033e9 (movR64M64Effect 0x1033e9 9 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 1155) (.exec 0x1033e9 (LoadPre 0x1033e9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1033e9 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1033e9 9 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1156) (.out 0x1033ee (orR64R64Effect 0x1033ee 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[1152, 1154]
    (.letOp (n := 1157) (.exec 0x1033ee (fun s => s.RIP = 0x1033ee) (orR64R64Effect 0x1033ee 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[1152, 1154]
    (.letOp (n := 1158) (.out 0x1033f1 (shrR64Effect 0x1033f1 3 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[1084]
    (.letOp (n := 1159) (.exec 0x1033f1 (fun s => s.RIP = 0x1033f1) (shrR64Effect 0x1033f1 3 7 1) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1084]
    (.letOp (n := 1160) (.out 0x1033f4 (leaR64Effect 0x1033f4 1 (.sib 1 (some 6) 1 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1150, 1146]
    (.letOp (n := 1161) (.exec 0x1033f4 (fun s => s.RIP = 0x1033f4) (leaR64Effect 0x1033f4 1 (.sib 1 (some 6) 1 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1150, 1146]
    (b_l102bd0_28))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_27 : List UInt8 :=
  [0x49, 0x0F, 0xC8, 0x4C, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x04, 0x4C, 0x21, 0xD9, 0x4D, 0x21, 0xD8,
    0x49, 0xC1, 0xE0, 0x04, 0x49, 0x09, 0xC8, 0x4C, 0x89, 0xC1, 0x4C, 0x21, 0xD1, 0x49, 0xC1, 0xE8,
    0x02, 0x4D, 0x21, 0xD0, 0x49, 0x8D, 0x0C, 0x88, 0x48, 0x21, 0xCE, 0x48, 0xD1, 0xE9, 0x4C, 0x21,
    0xC9, 0x4C, 0x8B, 0x54, 0x24, 0x30, 0x4C, 0x8B, 0x4C, 0x24, 0x38, 0x4D, 0x09, 0xCA, 0x48, 0xD1,
    0xEF, 0x48, 0x8D, 0x0C, 0x71] ++ bytes_l102bd0_28

theorem code_l102bd0_27 : ∀ x ∈ codeRange 0x1033b3 bytes_l102bd0_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x33b3 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_28

def b_l102bd0_26 : Block Op Label signature Reg.count 1082 :=
  .letOp (n := 1082) (.out 0x103371 (andR64R64Effect 0x103371 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1078, 1080]
    (.letOp (n := 1083) (.exec 0x103371 (fun s => s.RIP = 0x103371) (andR64R64Effect 0x103371 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1078, 1080]
    (.letOp (n := 1084) (.out 0x103374 (leaR64Effect 0x103374 7 (.sib 0 (some 6) 1 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0, .gpr 6] []) (.reg (.gpr 7))) #v[1082, 1076]
    (.letOp (n := 1085) (.exec 0x103374 (fun s => s.RIP = 0x103374) (leaR64Effect 0x103374 7 (.sib 0 (some 6) 1 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1082, 1076]
    (.letOp (n := 1086) (.out 0x103378 (bswapR64Effect 0x103378 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[908]
    (.letOp (n := 1087) (.exec 0x103378 (fun s => s.RIP = 0x103378) (bswapR64Effect 0x103378 3 1) (Reg.operands [.gpr 1] [])) #v[908]
    (.letOp (n := 1088) (.out 0x10337b (movR64R64Effect 0x10337b 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1086]
    (.letOp (n := 1089) (.exec 0x10337b (fun s => s.RIP = 0x10337b) (movR64R64Effect 0x10337b 0 1) (Reg.operands [.gpr 1] [])) #v[1086]
    (.letOp (n := 1090) (.out 0x10337e (shrR64Effect 0x10337e 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1088]
    (.letOp (n := 1091) (.exec 0x10337e (fun s => s.RIP = 0x10337e) (shrR64Effect 0x10337e 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1088]
    (.letOp (n := 1092) (.out 0x103382 (andR64R64Effect 0x103382 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1090, 1050]
    (.letOp (n := 1093) (.exec 0x103382 (fun s => s.RIP = 0x103382) (andR64R64Effect 0x103382 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1090, 1050]
    (.letOp (n := 1094) (.out 0x103385 (andR64R64Effect 0x103385 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[1086, 1050]
    (.letOp (n := 1095) (.exec 0x103385 (fun s => s.RIP = 0x103385) (andR64R64Effect 0x103385 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[1086, 1050]
    (.letOp (n := 1096) (.out 0x103388 (shlR64Effect 0x103388 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1094]
    (.letOp (n := 1097) (.exec 0x103388 (fun s => s.RIP = 0x103388) (shlR64Effect 0x103388 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1094]
    (.letOp (n := 1098) (.out 0x10338c (orR64R64Effect 0x10338c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1096, 1092]
    (.letOp (n := 1099) (.exec 0x10338c (fun s => s.RIP = 0x10338c) (orR64R64Effect 0x10338c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1096, 1092]
    (.letOp (n := 1100) (.out 0x10338f (movR64R64Effect 0x10338f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1098]
    (.letOp (n := 1101) (.exec 0x10338f (fun s => s.RIP = 0x10338f) (movR64R64Effect 0x10338f 0 1) (Reg.operands [.gpr 1] [])) #v[1098]
    (.letOp (n := 1102) (.out 0x103392 (andR64R64Effect 0x103392 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1100, 1062]
    (.letOp (n := 1103) (.exec 0x103392 (fun s => s.RIP = 0x103392) (andR64R64Effect 0x103392 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1100, 1062]
    (.letOp (n := 1104) (.out 0x103395 (shrR64Effect 0x103395 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1098]
    (.letOp (n := 1105) (.exec 0x103395 (fun s => s.RIP = 0x103395) (shrR64Effect 0x103395 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1098]
    (.letOp (n := 1106) (.out 0x103399 (andR64R64Effect 0x103399 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1104, 1062]
    (.letOp (n := 1107) (.exec 0x103399 (fun s => s.RIP = 0x103399) (andR64R64Effect 0x103399 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1104, 1062]
    (.letOp (n := 1108) (.out 0x10339c (leaR64Effect 0x10339c 0 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[1106, 1102]
    (.letOp (n := 1109) (.exec 0x10339c (fun s => s.RIP = 0x10339c) (leaR64Effect 0x10339c 0 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1106, 1102]
    (.letOp (n := 1110) (.out 0x1033a0 (movR64R64Effect 0x1033a0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1108]
    (.letOp (n := 1111) (.exec 0x1033a0 (fun s => s.RIP = 0x1033a0) (movR64R64Effect 0x1033a0 1 0) (Reg.operands [.gpr 0] [])) #v[1108]
    (.letOp (n := 1112) (.out 0x1033a3 (andR64R64Effect 0x1033a3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[1110, 1074]
    (.letOp (n := 1113) (.exec 0x1033a3 (fun s => s.RIP = 0x1033a3) (andR64R64Effect 0x1033a3 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1110, 1074]
    (.letOp (n := 1114) (.out 0x1033a6 (movR64R64Effect 0x1033a6 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[1074]
    (.letOp (n := 1115) (.exec 0x1033a6 (fun s => s.RIP = 0x1033a6) (movR64R64Effect 0x1033a6 6 3) (Reg.operands [.gpr 3] [])) #v[1074]
    (.letOp (n := 1116) (.out 0x1033a9 (shrR64Effect 0x1033a9 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1108]
    (.letOp (n := 1117) (.exec 0x1033a9 (fun s => s.RIP = 0x1033a9) (shrR64Effect 0x1033a9 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1108]
    (.letOp (n := 1118) (.out 0x1033ac (andR64R64Effect 0x1033ac 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1116, 1080]
    (.letOp (n := 1119) (.exec 0x1033ac (fun s => s.RIP = 0x1033ac) (andR64R64Effect 0x1033ac 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1116, 1080]
    (.letOp (n := 1120) (.out 0x1033af (leaR64Effect 0x1033af 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1118, 1112]
    (.letOp (n := 1121) (.exec 0x1033af (fun s => s.RIP = 0x1033af) (leaR64Effect 0x1033af 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1118, 1112]
    (b_l102bd0_27))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_26 : List UInt8 :=
  [0x4C, 0x21, 0xC8, 0x48, 0x8D, 0x3C, 0x70, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xC8, 0x48, 0xC1, 0xE8,
    0x04, 0x4C, 0x21, 0xD8, 0x4C, 0x21, 0xD9, 0x48, 0xC1, 0xE1, 0x04, 0x48, 0x09, 0xC1, 0x48, 0x89,
    0xC8, 0x4C, 0x21, 0xD0, 0x48, 0xC1, 0xE9, 0x02, 0x4C, 0x21, 0xD1, 0x48, 0x8D, 0x04, 0x81, 0x48,
    0x89, 0xC1, 0x48, 0x21, 0xD9, 0x48, 0x89, 0xDE, 0x48, 0xD1, 0xE8, 0x4C, 0x21, 0xC8, 0x48, 0x8D,
    0x04, 0x48] ++ bytes_l102bd0_27

theorem code_l102bd0_26 : ∀ x ∈ codeRange 0x103371 bytes_l102bd0_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3371 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_27

def b_l102bd0_25 : Block Op Label signature Reg.count 1042 :=
  .letOp (n := 1042) (.out 0x103315 (bswapR64Effect 0x103315 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[774]
    (.letOp (n := 1043) (.exec 0x103315 (fun s => s.RIP = 0x103315) (bswapR64Effect 0x103315 3 0) (Reg.operands [.gpr 0] [])) #v[774]
    (.letOp (n := 1044) (.out 0x103318 (xorR64R64Effect 0x103318 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[1040, 1036]
    (.letOp (n := 1045) (.exec 0x103318 (fun s => s.RIP = 0x103318) (xorR64R64Effect 0x103318 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[1040, 1036]
    (.letOp (n := 1046) (.out 0x10331b (movR64R64Effect 0x10331b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1042]
    (.letOp (n := 1047) (.exec 0x10331b (fun s => s.RIP = 0x10331b) (movR64R64Effect 0x10331b 6 0) (Reg.operands [.gpr 0] [])) #v[1042]
    (.letOp (n := 1048) (.out 0x10331e (shrR64Effect 0x10331e 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[1046]
    (.letOp (n := 1049) (.exec 0x10331e (fun s => s.RIP = 0x10331e) (shrR64Effect 0x10331e 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1046]
    (.letOp (n := 1050) (.out 0x103322 (movR64Imm64Effect 0x103322 11 0xf0f0f0f0f0f0f0f) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 1051) (.exec 0x103322 (fun s => s.RIP = 0x103322) (movR64Imm64Effect 0x103322 11 0xf0f0f0f0f0f0f0f) (Reg.operands [] [])) #v[]
    (.letOp (n := 1052) (.out 0x10332c (andR64R64Effect 0x10332c 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[1048, 1050]
    (.letOp (n := 1053) (.exec 0x10332c (fun s => s.RIP = 0x10332c) (andR64R64Effect 0x10332c 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[1048, 1050]
    (.letOp (n := 1054) (.out 0x10332f (andR64R64Effect 0x10332f 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1042, 1050]
    (.letOp (n := 1055) (.exec 0x10332f (fun s => s.RIP = 0x10332f) (andR64R64Effect 0x10332f 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1042, 1050]
    (.letOp (n := 1056) (.out 0x103332 (shlR64Effect 0x103332 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1054]
    (.letOp (n := 1057) (.exec 0x103332 (fun s => s.RIP = 0x103332) (shlR64Effect 0x103332 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1054]
    (.letOp (n := 1058) (.out 0x103336 (orR64R64Effect 0x103336 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1056, 1052]
    (.letOp (n := 1059) (.exec 0x103336 (fun s => s.RIP = 0x103336) (orR64R64Effect 0x103336 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1056, 1052]
    (.letOp (n := 1060) (.out 0x103339 (movR64R64Effect 0x103339 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1058]
    (.letOp (n := 1061) (.exec 0x103339 (fun s => s.RIP = 0x103339) (movR64R64Effect 0x103339 6 0) (Reg.operands [.gpr 0] [])) #v[1058]
    (.letOp (n := 1062) (.out 0x10333c (movR64Imm64Effect 0x10333c 10 0x3333333333333333) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 1063) (.exec 0x10333c (fun s => s.RIP = 0x10333c) (movR64Imm64Effect 0x10333c 10 0x3333333333333333) (Reg.operands [] [])) #v[]
    (.letOp (n := 1064) (.out 0x103346 (andR64R64Effect 0x103346 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[1060, 1062]
    (.letOp (n := 1065) (.exec 0x103346 (fun s => s.RIP = 0x103346) (andR64R64Effect 0x103346 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[1060, 1062]
    (.letOp (n := 1066) (.out 0x103349 (shrR64Effect 0x103349 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1058]
    (.letOp (n := 1067) (.exec 0x103349 (fun s => s.RIP = 0x103349) (shrR64Effect 0x103349 4 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1058]
    (.letOp (n := 1068) (.out 0x10334d (andR64R64Effect 0x10334d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[1066, 1062]
    (.letOp (n := 1069) (.exec 0x10334d (fun s => s.RIP = 0x10334d) (andR64R64Effect 0x10334d 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[1066, 1062]
    (.letOp (n := 1070) (.out 0x103350 (leaR64Effect 0x103350 0 (.sib 0 (some 6) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1068, 1064]
    (.letOp (n := 1071) (.exec 0x103350 (fun s => s.RIP = 0x103350) (leaR64Effect 0x103350 0 (.sib 0 (some 6) 2 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1068, 1064]
    (.letOp (n := 1072) (.out 0x103354 (movR64R64Effect 0x103354 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[1070]
    (.letOp (n := 1073) (.exec 0x103354 (fun s => s.RIP = 0x103354) (movR64R64Effect 0x103354 6 0) (Reg.operands [.gpr 0] [])) #v[1070]
    (.letOp (n := 1074) (.out 0x103357 (movR64Imm64Effect 0x103357 3 0x5555555555555555) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 1075) (.exec 0x103357 (fun s => s.RIP = 0x103357) (movR64Imm64Effect 0x103357 3 0x5555555555555555) (Reg.operands [] [])) #v[]
    (.letOp (n := 1076) (.out 0x103361 (andR64R64Effect 0x103361 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[1072, 1074]
    (.letOp (n := 1077) (.exec 0x103361 (fun s => s.RIP = 0x103361) (andR64R64Effect 0x103361 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[1072, 1074]
    (.letOp (n := 1078) (.out 0x103364 (shrR64Effect 0x103364 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1070]
    (.letOp (n := 1079) (.exec 0x103364 (fun s => s.RIP = 0x103364) (shrR64Effect 0x103364 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1070]
    (.letOp (n := 1080) (.out 0x103367 (movR64Imm64Effect 0x103367 9 0x5555555555555554) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 1081) (.exec 0x103367 (fun s => s.RIP = 0x103367) (movR64Imm64Effect 0x103367 9 0x5555555555555554) (Reg.operands [] [])) #v[]
    (b_l102bd0_26))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_25 : List UInt8 :=
  [0x48, 0x0F, 0xC8, 0x49, 0x31, 0xF8, 0x48, 0x89, 0xC6, 0x48, 0xC1, 0xEE, 0x04, 0x49, 0xBB, 0x0F,
    0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F, 0x4C, 0x21, 0xDE, 0x4C, 0x21, 0xD8, 0x48, 0xC1, 0xE0,
    0x04, 0x48, 0x09, 0xF0, 0x48, 0x89, 0xC6, 0x49, 0xBA, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
    0x33, 0x4C, 0x21, 0xD6, 0x48, 0xC1, 0xE8, 0x02, 0x4C, 0x21, 0xD0, 0x48, 0x8D, 0x04, 0xB0, 0x48,
    0x89, 0xC6, 0x48, 0xBB, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x48, 0x21, 0xDE, 0x48,
    0xD1, 0xE8, 0x49, 0xB9, 0x54, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55] ++ bytes_l102bd0_26

theorem code_l102bd0_25 : ∀ x ∈ codeRange 0x103315 bytes_l102bd0_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3315 92 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_26

def b_l102bd0_24 : Block Op Label signature Reg.count 1002 :=
  .letOp (n := 1002) (.out 0x1032bb (imulR64R64Effect 0x1032bb 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[944, 922]
    (.letOp (n := 1003) (.exec 0x1032bb (fun s => s.RIP = 0x1032bb) (imulR64R64Effect 0x1032bb 4 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[944, 922]
    (.letOp (n := 1004) (.out 0x1032bf (xorR64R64Effect 0x1032bf 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[988, 1002]
    (.letOp (n := 1005) (.exec 0x1032bf (fun s => s.RIP = 0x1032bf) (xorR64R64Effect 0x1032bf 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[988, 1002]
    (.letOp (n := 1006) (.out 0x1032c2 (xorR64R64Effect 0x1032c2 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[1004, 998]
    (.letOp (n := 1007) (.exec 0x1032c2 (fun s => s.RIP = 0x1032c2) (xorR64R64Effect 0x1032c2 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[1004, 998]
    (.letOp (n := 1008) (.out 0x1032c5 (xorR64R64Effect 0x1032c5 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[994, 990]
    (.letOp (n := 1009) (.exec 0x1032c5 (fun s => s.RIP = 0x1032c5) (xorR64R64Effect 0x1032c5 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[994, 990]
    (.letOp (n := 1010) (.out 0x1032c8 (imulR64R64Effect 0x1032c8 4 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[922, 946]
    (.letOp (n := 1011) (.exec 0x1032c8 (fun s => s.RIP = 0x1032c8) (imulR64R64Effect 0x1032c8 4 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[922, 946]
    (.letOp (n := 1012) (.out 0x1032cc (xorR64R64Effect 0x1032cc 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[1010, 1000]
    (.letOp (n := 1013) (.exec 0x1032cc (fun s => s.RIP = 0x1032cc) (xorR64R64Effect 0x1032cc 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[1010, 1000]
    (.letOp (n := 1014) (.out 0x1032cf (xorR64R64Effect 0x1032cf 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[1012, 1008]
    (.letOp (n := 1015) (.exec 0x1032cf (fun s => s.RIP = 0x1032cf) (xorR64R64Effect 0x1032cf 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[1012, 1008]
    (.letOp (n := 1016) (.out 0x1032d2 (movR64Imm64Effect 0x1032d2 2 0x1111111111111111) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1017) (.exec 0x1032d2 (fun s => s.RIP = 0x1032d2) (movR64Imm64Effect 0x1032d2 2 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 1018) (.out 0x1032dc (andR64R64Effect 0x1032dc 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[962, 1016]
    (.letOp (n := 1019) (.exec 0x1032dc (fun s => s.RIP = 0x1032dc) (andR64R64Effect 0x1032dc 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[962, 1016]
    (.letOp (n := 1020) (.out 0x1032df (movR64Imm64Effect 0x1032df 2 0x2222222222222222) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1021) (.exec 0x1032df (fun s => s.RIP = 0x1032df) (movR64Imm64Effect 0x1032df 2 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 1022) (.out 0x1032e9 (andR64R64Effect 0x1032e9 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[984, 1020]
    (.letOp (n := 1023) (.exec 0x1032e9 (fun s => s.RIP = 0x1032e9) (andR64R64Effect 0x1032e9 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[984, 1020]
    (.letOp (n := 1024) (.out 0x1032ec (orR64R64Effect 0x1032ec 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[1022, 1018]
    (.letOp (n := 1025) (.exec 0x1032ec (fun s => s.RIP = 0x1032ec) (orR64R64Effect 0x1032ec 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[1022, 1018]
    (.letOp (n := 1026) (.out 0x1032ef (movR64Imm64Effect 0x1032ef 2 0x4444444444444444) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1027) (.exec 0x1032ef (fun s => s.RIP = 0x1032ef) (movR64Imm64Effect 0x1032ef 2 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 1028) (.out 0x1032f9 (andR64R64Effect 0x1032f9 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[1006, 1026]
    (.letOp (n := 1029) (.exec 0x1032f9 (fun s => s.RIP = 0x1032f9) (andR64R64Effect 0x1032f9 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[1006, 1026]
    (.letOp (n := 1030) (.out 0x1032fc (orR64R64Effect 0x1032fc 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12] []) (.reg (.gpr 14))) #v[1028, 1024]
    (.letOp (n := 1031) (.exec 0x1032fc (fun s => s.RIP = 0x1032fc) (orR64R64Effect 0x1032fc 14 12) (Reg.operands [.gpr 14, .gpr 12] [])) #v[1028, 1024]
    (.letOp (n := 1032) (.out 0x1032ff (movR64Imm64Effect 0x1032ff 2 0x8888888888888888) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 1033) (.exec 0x1032ff (fun s => s.RIP = 0x1032ff) (movR64Imm64Effect 0x1032ff 2 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 1034) (.out 0x103309 (andR64R64Effect 0x103309 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[1014, 1032]
    (.letOp (n := 1035) (.exec 0x103309 (fun s => s.RIP = 0x103309) (andR64R64Effect 0x103309 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[1014, 1032]
    (.letOp (n := 1036) (.out 0x10330c (orR64R64Effect 0x10330c 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[1034, 1030]
    (.letOp (n := 1037) (.exec 0x10330c (fun s => s.RIP = 0x10330c) (orR64R64Effect 0x10330c 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[1034, 1030]
    (.letOp (n := 1038) (.out 0x10330f (movR64R64Effect 0x10330f 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[774]
    (.letOp (n := 1039) (.exec 0x10330f (fun s => s.RIP = 0x10330f) (movR64R64Effect 0x10330f 8 0) (Reg.operands [.gpr 0] [])) #v[774]
    (.letOp (n := 1040) (.out 0x103312 (xorR64R64Effect 0x103312 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1038, 908]
    (.letOp (n := 1041) (.exec 0x103312 (fun s => s.RIP = 0x103312) (xorR64R64Effect 0x103312 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1038, 908]
    (b_l102bd0_25))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_24 : List UInt8 :=
  [0x4C, 0x0F, 0xAF, 0xFF, 0x4D, 0x31, 0xFE, 0x49, 0x31, 0xEE, 0x49, 0x31, 0xF0, 0x48, 0x0F, 0xAF,
    0xFA, 0x4C, 0x31, 0xCF, 0x4C, 0x31, 0xC7, 0x48, 0xBA, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x48, 0x21, 0xD3, 0x48, 0xBA, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x49, 0x21,
    0xD4, 0x49, 0x09, 0xDC, 0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x49, 0x21,
    0xD6, 0x4D, 0x09, 0xE6, 0x48, 0xBA, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x48, 0x21,
    0xD7, 0x4C, 0x09, 0xF7, 0x49, 0x89, 0xC0, 0x49, 0x31, 0xC8] ++ bytes_l102bd0_25

theorem code_l102bd0_24 : ∀ x ∈ codeRange 0x1032bb bytes_l102bd0_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x32bb 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_25

def b_l102bd0_23 : Block Op Label signature Reg.count 962 :=
  .letOp (n := 962) (.out 0x103275 (xorR64R64Effect 0x103275 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[960, 938]
    (.letOp (n := 963) (.exec 0x103275 (fun s => s.RIP = 0x103275) (xorR64R64Effect 0x103275 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[960, 938]
    (.letOp (n := 964) (.out 0x103278 (movR64R64Effect 0x103278 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[914]
    (.letOp (n := 965) (.exec 0x103278 (fun s => s.RIP = 0x103278) (movR64R64Effect 0x103278 14 11) (Reg.operands [.gpr 11] [])) #v[914]
    (.letOp (n := 966) (.out 0x10327b (imulR64R64Effect 0x10327b 4 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[964, 948]
    (.letOp (n := 967) (.exec 0x10327b (fun s => s.RIP = 0x10327b) (imulR64R64Effect 0x10327b 4 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[964, 948]
    (.letOp (n := 968) (.out 0x10327f (movR64R64Effect 0x10327f 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[918]
    (.letOp (n := 969) (.exec 0x10327f (fun s => s.RIP = 0x10327f) (movR64R64Effect 0x10327f 10 5) (Reg.operands [.gpr 5] [])) #v[918]
    (.letOp (n := 970) (.out 0x103282 (imulR64R64Effect 0x103282 4 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[968, 922]
    (.letOp (n := 971) (.exec 0x103282 (fun s => s.RIP = 0x103282) (imulR64R64Effect 0x103282 4 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[968, 922]
    (.letOp (n := 972) (.out 0x103286 (xorR64R64Effect 0x103286 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[970, 966]
    (.letOp (n := 973) (.exec 0x103286 (fun s => s.RIP = 0x103286) (xorR64R64Effect 0x103286 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[970, 966]
    (.letOp (n := 974) (.out 0x103289 (movR64R64Effect 0x103289 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 15] []) (.reg (.gpr 14))) #v[944]
    (.letOp (n := 975) (.exec 0x103289 (fun s => s.RIP = 0x103289) (movR64R64Effect 0x103289 14 15) (Reg.operands [.gpr 15] [])) #v[944]
    (.letOp (n := 976) (.out 0x10328c (imulR64R64Effect 0x10328c 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[974, 928]
    (.letOp (n := 977) (.exec 0x10328c (fun s => s.RIP = 0x10328c) (imulR64R64Effect 0x10328c 4 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[974, 928]
    (.letOp (n := 978) (.out 0x103290 (movR64R64Effect 0x103290 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[946]
    (.letOp (n := 979) (.exec 0x103290 (fun s => s.RIP = 0x103290) (movR64R64Effect 0x103290 12 2) (Reg.operands [.gpr 2] [])) #v[946]
    (.letOp (n := 980) (.out 0x103293 (imulR64R64Effect 0x103293 4 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[978, 950]
    (.letOp (n := 981) (.exec 0x103293 (fun s => s.RIP = 0x103293) (imulR64R64Effect 0x103293 4 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[978, 950]
    (.letOp (n := 982) (.out 0x103297 (xorR64R64Effect 0x103297 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[980, 976]
    (.letOp (n := 983) (.exec 0x103297 (fun s => s.RIP = 0x103297) (xorR64R64Effect 0x103297 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[980, 976]
    (.letOp (n := 984) (.out 0x10329a (xorR64R64Effect 0x10329a 12 10) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 10] []) (.reg (.gpr 12))) #v[982, 972]
    (.letOp (n := 985) (.exec 0x10329a (fun s => s.RIP = 0x10329a) (xorR64R64Effect 0x10329a 12 10) (Reg.operands [.gpr 12, .gpr 10] [])) #v[982, 972]
    (.letOp (n := 986) (.out 0x10329d (movR64R64Effect 0x10329d 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[946]
    (.letOp (n := 987) (.exec 0x10329d (fun s => s.RIP = 0x10329d) (movR64R64Effect 0x10329d 14 2) (Reg.operands [.gpr 2] [])) #v[946]
    (.letOp (n := 988) (.out 0x1032a0 (imulR64R64Effect 0x1032a0 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[986, 928]
    (.letOp (n := 989) (.exec 0x1032a0 (fun s => s.RIP = 0x1032a0) (imulR64R64Effect 0x1032a0 4 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[986, 928]
    (.letOp (n := 990) (.out 0x1032a4 (imulR64R64Effect 0x1032a4 4 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[928, 914]
    (.letOp (n := 991) (.exec 0x1032a4 (fun s => s.RIP = 0x1032a4) (imulR64R64Effect 0x1032a4 4 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[928, 914]
    (.letOp (n := 992) (.out 0x1032a8 (imulR64R64Effect 0x1032a8 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[914, 950]
    (.letOp (n := 993) (.exec 0x1032a8 (fun s => s.RIP = 0x1032a8) (imulR64R64Effect 0x1032a8 4 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[914, 950]
    (.letOp (n := 994) (.out 0x1032ac (imulR64R64Effect 0x1032ac 4 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[950, 918]
    (.letOp (n := 995) (.exec 0x1032ac (fun s => s.RIP = 0x1032ac) (imulR64R64Effect 0x1032ac 4 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[950, 918]
    (.letOp (n := 996) (.out 0x1032b0 (imulR64R64Effect 0x1032b0 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[918, 948]
    (.letOp (n := 997) (.exec 0x1032b0 (fun s => s.RIP = 0x1032b0) (imulR64R64Effect 0x1032b0 4 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[918, 948]
    (.letOp (n := 998) (.out 0x1032b4 (xorR64R64Effect 0x1032b4 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[996, 992]
    (.letOp (n := 999) (.exec 0x1032b4 (fun s => s.RIP = 0x1032b4) (xorR64R64Effect 0x1032b4 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[996, 992]
    (.letOp (n := 1000) (.out 0x1032b7 (imulR64R64Effect 0x1032b7 4 9 15) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15] []) (.reg (.gpr 9))) #v[948, 944]
    (.letOp (n := 1001) (.exec 0x1032b7 (fun s => s.RIP = 0x1032b7) (imulR64R64Effect 0x1032b7 4 9 15) (Reg.operands [.gpr 9, .gpr 15] [])) #v[948, 944]
    (b_l102bd0_24))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_23 : List UInt8 :=
  [0x4C, 0x31, 0xF3, 0x4D, 0x89, 0xDE, 0x4D, 0x0F, 0xAF, 0xF1, 0x49, 0x89, 0xEA, 0x4C, 0x0F, 0xAF,
    0xD7, 0x4D, 0x31, 0xF2, 0x4D, 0x89, 0xFE, 0x4C, 0x0F, 0xAF, 0xF6, 0x49, 0x89, 0xD4, 0x4D, 0x0F,
    0xAF, 0xE0, 0x4D, 0x31, 0xF4, 0x4D, 0x31, 0xD4, 0x49, 0x89, 0xD6, 0x4C, 0x0F, 0xAF, 0xF6, 0x49,
    0x0F, 0xAF, 0xF3, 0x4D, 0x0F, 0xAF, 0xD8, 0x4C, 0x0F, 0xAF, 0xC5, 0x49, 0x0F, 0xAF, 0xE9, 0x4C,
    0x31, 0xDD, 0x4D, 0x0F, 0xAF, 0xCF] ++ bytes_l102bd0_24

theorem code_l102bd0_23 : ∀ x ∈ codeRange 0x103275 bytes_l102bd0_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3275 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_24

def b_l102bd0_22 : Block Op Label signature Reg.count 922 :=
  .letOp (n := 922) (.out 0x10322e (andR64R64Effect 0x10322e 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[920, 888]
    (.letOp (n := 923) (.exec 0x10322e (fun s => s.RIP = 0x10322e) (andR64R64Effect 0x10322e 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[920, 888]
    (.letOp (n := 924) (.out 0x103231 (movR64R64Effect 0x103231 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[633]
    (.letOp (n := 925) (.exec 0x103231 (fun s => s.RIP = 0x103231) (movR64R64Effect 0x103231 9 6) (Reg.operands [.gpr 6] [])) #v[633]
    (.letOp (n := 926) (.out 0x103234 (movR64R64Effect 0x103234 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[633]
    (.letOp (n := 927) (.exec 0x103234 (fun s => s.RIP = 0x103234) (movR64R64Effect 0x103234 8 6) (Reg.operands [.gpr 6] [])) #v[633]
    (.letOp (n := 928) (.out 0x103237 (andR64R64Effect 0x103237 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[633, 904]
    (.letOp (n := 929) (.exec 0x103237 (fun s => s.RIP = 0x103237) (andR64R64Effect 0x103237 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[633, 904]
    (.letOp (n := 930) (.out 0x10323a (movR64R64Effect 0x10323a 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[914]
    (.letOp (n := 931) (.exec 0x10323a (fun s => s.RIP = 0x10323a) (movR64R64Effect 0x10323a 3 11) (Reg.operands [.gpr 11] [])) #v[914]
    (.letOp (n := 932) (.out 0x10323d (imulR64R64Effect 0x10323d 4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[930, 922]
    (.letOp (n := 933) (.exec 0x10323d (fun s => s.RIP = 0x10323d) (imulR64R64Effect 0x10323d 4 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[930, 922]
    (.letOp (n := 934) (.out 0x103241 (movR64R64Effect 0x103241 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[918]
    (.letOp (n := 935) (.exec 0x103241 (fun s => s.RIP = 0x103241) (movR64R64Effect 0x103241 14 5) (Reg.operands [.gpr 5] [])) #v[918]
    (.letOp (n := 936) (.out 0x103244 (imulR64R64Effect 0x103244 4 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[934, 928]
    (.letOp (n := 937) (.exec 0x103244 (fun s => s.RIP = 0x103244) (imulR64R64Effect 0x103244 4 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[934, 928]
    (.letOp (n := 938) (.out 0x103248 (xorR64R64Effect 0x103248 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[936, 932]
    (.letOp (n := 939) (.exec 0x103248 (fun s => s.RIP = 0x103248) (xorR64R64Effect 0x103248 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[936, 932]
    (.letOp (n := 940) (.out 0x10324b (movR64R64Effect 0x10324b 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[910]
    (.letOp (n := 941) (.exec 0x10324b (fun s => s.RIP = 0x10324b) (movR64R64Effect 0x10324b 15 2) (Reg.operands [.gpr 2] [])) #v[910]
    (.letOp (n := 942) (.out 0x10324e (movR64Imm64Effect 0x10324e 3 0x4444444444444444) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 943) (.exec 0x10324e (fun s => s.RIP = 0x10324e) (movR64Imm64Effect 0x10324e 3 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 944) (.out 0x103258 (andR64R64Effect 0x103258 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[940, 942]
    (.letOp (n := 945) (.exec 0x103258 (fun s => s.RIP = 0x103258) (andR64R64Effect 0x103258 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[940, 942]
    (.letOp (n := 946) (.out 0x10325b (andR64R64Effect 0x10325b 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[910, 904]
    (.letOp (n := 947) (.exec 0x10325b (fun s => s.RIP = 0x10325b) (andR64R64Effect 0x10325b 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[910, 904]
    (.letOp (n := 948) (.out 0x10325e (andR64R64Effect 0x10325e 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[924, 892]
    (.letOp (n := 949) (.exec 0x10325e (fun s => s.RIP = 0x10325e) (andR64R64Effect 0x10325e 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[924, 892]
    (.letOp (n := 950) (.out 0x103261 (andR64R64Effect 0x103261 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[926, 942]
    (.letOp (n := 951) (.exec 0x103261 (fun s => s.RIP = 0x103261) (andR64R64Effect 0x103261 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[926, 942]
    (.letOp (n := 952) (.out 0x103264 (movR64R64Effect 0x103264 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[944]
    (.letOp (n := 953) (.exec 0x103264 (fun s => s.RIP = 0x103264) (movR64R64Effect 0x103264 12 15) (Reg.operands [.gpr 15] [])) #v[944]
    (.letOp (n := 954) (.out 0x103267 (imulR64R64Effect 0x103267 4 12 8) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 8] []) (.reg (.gpr 12))) #v[952, 950]
    (.letOp (n := 955) (.exec 0x103267 (fun s => s.RIP = 0x103267) (imulR64R64Effect 0x103267 4 12 8) (Reg.operands [.gpr 12, .gpr 8] [])) #v[952, 950]
    (.letOp (n := 956) (.out 0x10326b (movR64R64Effect 0x10326b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[946]
    (.letOp (n := 957) (.exec 0x10326b (fun s => s.RIP = 0x10326b) (movR64R64Effect 0x10326b 3 2) (Reg.operands [.gpr 2] [])) #v[946]
    (.letOp (n := 958) (.out 0x10326e (imulR64R64Effect 0x10326e 4 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[956, 948]
    (.letOp (n := 959) (.exec 0x10326e (fun s => s.RIP = 0x10326e) (imulR64R64Effect 0x10326e 4 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[956, 948]
    (.letOp (n := 960) (.out 0x103272 (xorR64R64Effect 0x103272 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[958, 954]
    (.letOp (n := 961) (.exec 0x103272 (fun s => s.RIP = 0x103272) (xorR64R64Effect 0x103272 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[958, 954]
    (b_l102bd0_23))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_22 : List UInt8 :=
  [0x4C, 0x21, 0xC7, 0x49, 0x89, 0xF1, 0x49, 0x89, 0xF0, 0x4C, 0x21, 0xD6, 0x4C, 0x89, 0xDB, 0x48,
    0x0F, 0xAF, 0xDF, 0x49, 0x89, 0xEE, 0x4C, 0x0F, 0xAF, 0xF6, 0x49, 0x31, 0xDE, 0x49, 0x89, 0xD7,
    0x48, 0xBB, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x49, 0x21, 0xDF, 0x4C, 0x21, 0xD2,
    0x4D, 0x21, 0xE1, 0x49, 0x21, 0xD8, 0x4D, 0x89, 0xFC, 0x4D, 0x0F, 0xAF, 0xE0, 0x48, 0x89, 0xD3,
    0x49, 0x0F, 0xAF, 0xD9, 0x4C, 0x31, 0xE3] ++ bytes_l102bd0_23

theorem code_l102bd0_22 : ∀ x ∈ codeRange 0x10322e bytes_l102bd0_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x322e 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_23

def b_l102bd0_21 : Block Op Label signature Reg.count 882 :=
  .letOp (n := 882) (.out 0x1031d4 (imulR64R64Effect 0x1031d4 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[792, 818]
    (.letOp (n := 883) (.exec 0x1031d4 (fun s => s.RIP = 0x1031d4) (imulR64R64Effect 0x1031d4 4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[792, 818]
    (.letOp (n := 884) (.out 0x1031d8 (xorR64R64Effect 0x1031d8 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[882, 872]
    (.letOp (n := 885) (.exec 0x1031d8 (fun s => s.RIP = 0x1031d8) (xorR64R64Effect 0x1031d8 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[882, 872]
    (.letOp (n := 886) (.out 0x1031db (xorR64R64Effect 0x1031db 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[884, 880]
    (.letOp (n := 887) (.exec 0x1031db (fun s => s.RIP = 0x1031db) (xorR64R64Effect 0x1031db 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[884, 880]
    (.letOp (n := 888) (.out 0x1031de (movR64Imm64Effect 0x1031de 8 0x1111111111111111) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 889) (.exec 0x1031de (fun s => s.RIP = 0x1031de) (movR64Imm64Effect 0x1031de 8 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 890) (.out 0x1031e8 (andR64R64Effect 0x1031e8 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[834, 888]
    (.letOp (n := 891) (.exec 0x1031e8 (fun s => s.RIP = 0x1031e8) (andR64R64Effect 0x1031e8 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[834, 888]
    (.letOp (n := 892) (.out 0x1031eb (movR64Imm64Effect 0x1031eb 12 0x2222222222222222) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 893) (.exec 0x1031eb (fun s => s.RIP = 0x1031eb) (movR64Imm64Effect 0x1031eb 12 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 894) (.out 0x1031f5 (andR64R64Effect 0x1031f5 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[856, 892]
    (.letOp (n := 895) (.exec 0x1031f5 (fun s => s.RIP = 0x1031f5) (andR64R64Effect 0x1031f5 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[856, 892]
    (.letOp (n := 896) (.out 0x1031f8 (orR64R64Effect 0x1031f8 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[894, 890]
    (.letOp (n := 897) (.exec 0x1031f8 (fun s => s.RIP = 0x1031f8) (orR64R64Effect 0x1031f8 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[894, 890]
    (.letOp (n := 898) (.out 0x1031fb (movR64Imm64Effect 0x1031fb 2 0x4444444444444444) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 899) (.exec 0x1031fb (fun s => s.RIP = 0x1031fb) (movR64Imm64Effect 0x1031fb 2 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 900) (.out 0x103205 (andR64R64Effect 0x103205 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[878, 898]
    (.letOp (n := 901) (.exec 0x103205 (fun s => s.RIP = 0x103205) (andR64R64Effect 0x103205 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[878, 898]
    (.letOp (n := 902) (.out 0x103208 (orR64R64Effect 0x103208 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[900, 896]
    (.letOp (n := 903) (.exec 0x103208 (fun s => s.RIP = 0x103208) (orR64R64Effect 0x103208 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[900, 896]
    (.letOp (n := 904) (.out 0x10320b (movR64Imm64Effect 0x10320b 10 0x8888888888888888) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 905) (.exec 0x10320b (fun s => s.RIP = 0x10320b) (movR64Imm64Effect 0x10320b 10 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 906) (.out 0x103215 (andR64R64Effect 0x103215 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[886, 904]
    (.letOp (n := 907) (.exec 0x103215 (fun s => s.RIP = 0x103215) (andR64R64Effect 0x103215 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[886, 904]
    (.letOp (n := 908) (.out 0x103218 (orR64R64Effect 0x103218 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[906, 902]
    (.letOp (n := 909) (.exec 0x103218 (fun s => s.RIP = 0x103218) (orR64R64Effect 0x103218 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[906, 902]
    (.letOp (n := 910) (.out 0x10321b (movR64M64Effect 0x10321b 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 911) (.exec 0x10321b (LoadPre 0x10321b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10321b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10321b 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 912) (.out 0x10321f (movR64R64Effect 0x10321f 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[910]
    (.letOp (n := 913) (.exec 0x10321f (fun s => s.RIP = 0x10321f) (movR64R64Effect 0x10321f 11 2) (Reg.operands [.gpr 2] [])) #v[910]
    (.letOp (n := 914) (.out 0x103222 (andR64R64Effect 0x103222 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[912, 888]
    (.letOp (n := 915) (.exec 0x103222 (fun s => s.RIP = 0x103222) (andR64R64Effect 0x103222 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[912, 888]
    (.letOp (n := 916) (.out 0x103225 (movR64R64Effect 0x103225 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[910]
    (.letOp (n := 917) (.exec 0x103225 (fun s => s.RIP = 0x103225) (movR64R64Effect 0x103225 5 2) (Reg.operands [.gpr 2] [])) #v[910]
    (.letOp (n := 918) (.out 0x103228 (andR64R64Effect 0x103228 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12] []) (.reg (.gpr 5))) #v[916, 892]
    (.letOp (n := 919) (.exec 0x103228 (fun s => s.RIP = 0x103228) (andR64R64Effect 0x103228 5 12) (Reg.operands [.gpr 5, .gpr 12] [])) #v[916, 892]
    (.letOp (n := 920) (.out 0x10322b (movR64R64Effect 0x10322b 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[633]
    (.letOp (n := 921) (.exec 0x10322b (fun s => s.RIP = 0x10322b) (movR64R64Effect 0x10322b 7 6) (Reg.operands [.gpr 6] [])) #v[633]
    (b_l102bd0_22))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_21 : List UInt8 :=
  [0x48, 0x0F, 0xAF, 0xCA, 0x4C, 0x31, 0xC1, 0x48, 0x31, 0xF9, 0x49, 0xB8, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x4D, 0x21, 0xC3, 0x49, 0xBC, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22,
    0x22, 0x4D, 0x21, 0xE7, 0x4D, 0x09, 0xDF, 0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x49, 0x21, 0xD6, 0x4D, 0x09, 0xFE, 0x49, 0xBA, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
    0x88, 0x4C, 0x21, 0xD1, 0x4C, 0x09, 0xF1, 0x48, 0x8B, 0x14, 0x24, 0x49, 0x89, 0xD3, 0x4D, 0x21,
    0xC3, 0x48, 0x89, 0xD5, 0x4C, 0x21, 0xE5, 0x48, 0x89, 0xF7] ++ bytes_l102bd0_22

theorem code_l102bd0_21 : ∀ x ∈ codeRange 0x1031d4 bytes_l102bd0_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x31d4 90 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_22

def b_l102bd0_20 : Block Op Label signature Reg.count 842 :=
  .letOp (n := 842) (.out 0x10318e (imulR64R64Effect 0x10318e 4 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[840, 792]
    (.letOp (n := 843) (.exec 0x10318e (fun s => s.RIP = 0x10318e) (imulR64R64Effect 0x10318e 4 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[840, 792]
    (.letOp (n := 844) (.out 0x103192 (xorR64R64Effect 0x103192 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 14] []) (.reg (.gpr 12))) #v[842, 838]
    (.letOp (n := 845) (.exec 0x103192 (fun s => s.RIP = 0x103192) (xorR64R64Effect 0x103192 12 14) (Reg.operands [.gpr 12, .gpr 14] [])) #v[842, 838]
    (.letOp (n := 846) (.out 0x103195 (movR64R64Effect 0x103195 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 3] []) (.reg (.gpr 14))) #v[816]
    (.letOp (n := 847) (.exec 0x103195 (fun s => s.RIP = 0x103195) (movR64R64Effect 0x103195 14 3) (Reg.operands [.gpr 3] [])) #v[816]
    (.letOp (n := 848) (.out 0x103198 (imulR64R64Effect 0x103198 4 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[846, 808]
    (.letOp (n := 849) (.exec 0x103198 (fun s => s.RIP = 0x103198) (imulR64R64Effect 0x103198 4 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[846, 808]
    (.letOp (n := 850) (.out 0x10319c (movR64R64Effect 0x10319c 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[818]
    (.letOp (n := 851) (.exec 0x10319c (fun s => s.RIP = 0x10319c) (movR64R64Effect 0x10319c 15 2) (Reg.operands [.gpr 2] [])) #v[818]
    (.letOp (n := 852) (.out 0x10319f (imulR64R64Effect 0x10319f 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[850, 822]
    (.letOp (n := 853) (.exec 0x10319f (fun s => s.RIP = 0x10319f) (imulR64R64Effect 0x10319f 4 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[850, 822]
    (.letOp (n := 854) (.out 0x1031a3 (xorR64R64Effect 0x1031a3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[852, 848]
    (.letOp (n := 855) (.exec 0x1031a3 (fun s => s.RIP = 0x1031a3) (xorR64R64Effect 0x1031a3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[852, 848]
    (.letOp (n := 856) (.out 0x1031a6 (xorR64R64Effect 0x1031a6 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[854, 844]
    (.letOp (n := 857) (.exec 0x1031a6 (fun s => s.RIP = 0x1031a6) (xorR64R64Effect 0x1031a6 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[854, 844]
    (.letOp (n := 858) (.out 0x1031a9 (movR64R64Effect 0x1031a9 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[818]
    (.letOp (n := 859) (.exec 0x1031a9 (fun s => s.RIP = 0x1031a9) (movR64R64Effect 0x1031a9 14 2) (Reg.operands [.gpr 2] [])) #v[818]
    (.letOp (n := 860) (.out 0x1031ac (imulR64R64Effect 0x1031ac 4 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[858, 808]
    (.letOp (n := 861) (.exec 0x1031ac (fun s => s.RIP = 0x1031ac) (imulR64R64Effect 0x1031ac 4 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[858, 808]
    (.letOp (n := 862) (.out 0x1031b0 (imulR64R64Effect 0x1031b0 4 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[808, 778]
    (.letOp (n := 863) (.exec 0x1031b0 (fun s => s.RIP = 0x1031b0) (imulR64R64Effect 0x1031b0 4 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[808, 778]
    (.letOp (n := 864) (.out 0x1031b4 (imulR64R64Effect 0x1031b4 4 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[778, 822]
    (.letOp (n := 865) (.exec 0x1031b4 (fun s => s.RIP = 0x1031b4) (imulR64R64Effect 0x1031b4 4 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[778, 822]
    (.letOp (n := 866) (.out 0x1031b8 (imulR64R64Effect 0x1031b8 4 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[822, 784]
    (.letOp (n := 867) (.exec 0x1031b8 (fun s => s.RIP = 0x1031b8) (imulR64R64Effect 0x1031b8 4 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[822, 784]
    (.letOp (n := 868) (.out 0x1031bc (imulR64R64Effect 0x1031bc 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[784, 820]
    (.letOp (n := 869) (.exec 0x1031bc (fun s => s.RIP = 0x1031bc) (imulR64R64Effect 0x1031bc 4 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[784, 820]
    (.letOp (n := 870) (.out 0x1031c0 (xorR64R64Effect 0x1031c0 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[868, 864]
    (.letOp (n := 871) (.exec 0x1031c0 (fun s => s.RIP = 0x1031c0) (xorR64R64Effect 0x1031c0 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[868, 864]
    (.letOp (n := 872) (.out 0x1031c3 (imulR64R64Effect 0x1031c3 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[820, 816]
    (.letOp (n := 873) (.exec 0x1031c3 (fun s => s.RIP = 0x1031c3) (imulR64R64Effect 0x1031c3 4 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[820, 816]
    (.letOp (n := 874) (.out 0x1031c7 (imulR64R64Effect 0x1031c7 4 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[816, 792]
    (.letOp (n := 875) (.exec 0x1031c7 (fun s => s.RIP = 0x1031c7) (imulR64R64Effect 0x1031c7 4 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[816, 792]
    (.letOp (n := 876) (.out 0x1031cb (xorR64R64Effect 0x1031cb 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[860, 874]
    (.letOp (n := 877) (.exec 0x1031cb (fun s => s.RIP = 0x1031cb) (xorR64R64Effect 0x1031cb 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[860, 874]
    (.letOp (n := 878) (.out 0x1031ce (xorR64R64Effect 0x1031ce 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9] []) (.reg (.gpr 14))) #v[876, 870]
    (.letOp (n := 879) (.exec 0x1031ce (fun s => s.RIP = 0x1031ce) (xorR64R64Effect 0x1031ce 14 9) (Reg.operands [.gpr 14, .gpr 9] [])) #v[876, 870]
    (.letOp (n := 880) (.out 0x1031d1 (xorR64R64Effect 0x1031d1 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[866, 862]
    (.letOp (n := 881) (.exec 0x1031d1 (fun s => s.RIP = 0x1031d1) (xorR64R64Effect 0x1031d1 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[866, 862]
    (b_l102bd0_21))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_20 : List UInt8 :=
  [0x4C, 0x0F, 0xAF, 0xE1, 0x4D, 0x31, 0xF4, 0x49, 0x89, 0xDE, 0x4C, 0x0F, 0xAF, 0xF5, 0x49, 0x89,
    0xD7, 0x4C, 0x0F, 0xAF, 0xFF, 0x4D, 0x31, 0xF7, 0x4D, 0x31, 0xE7, 0x49, 0x89, 0xD6, 0x4C, 0x0F,
    0xAF, 0xF5, 0x49, 0x0F, 0xAF, 0xEA, 0x4C, 0x0F, 0xAF, 0xD7, 0x49, 0x0F, 0xAF, 0xF9, 0x4D, 0x0F,
    0xAF, 0xC8, 0x4D, 0x31, 0xD1, 0x4C, 0x0F, 0xAF, 0xC3, 0x48, 0x0F, 0xAF, 0xD9, 0x49, 0x31, 0xDE,
    0x4D, 0x31, 0xCE, 0x48, 0x31, 0xEF] ++ bytes_l102bd0_21

theorem code_l102bd0_20 : ∀ x ∈ codeRange 0x10318e bytes_l102bd0_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x318e 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_21

def b_l102bd0_19 : Block Op Label signature Reg.count 802 :=
  .letOp (n := 802) (.out 0x103146 (imulR64R64Effect 0x103146 4 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[800, 792]
    (.letOp (n := 803) (.exec 0x103146 (fun s => s.RIP = 0x103146) (imulR64R64Effect 0x103146 4 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[800, 792]
    (.letOp (n := 804) (.out 0x10314a (movR64R64Effect 0x10314a 14 9) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[784]
    (.letOp (n := 805) (.exec 0x10314a (fun s => s.RIP = 0x10314a) (movR64R64Effect 0x10314a 14 9) (Reg.operands [.gpr 9] [])) #v[784]
    (.letOp (n := 806) (.out 0x10314d (imulR64R64Effect 0x10314d 4 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[804, 798]
    (.letOp (n := 807) (.exec 0x10314d (fun s => s.RIP = 0x10314d) (imulR64R64Effect 0x10314d 4 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[804, 798]
    (.letOp (n := 808) (.out 0x103151 (movR64R64Effect 0x103151 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[798]
    (.letOp (n := 809) (.exec 0x103151 (fun s => s.RIP = 0x103151) (movR64R64Effect 0x103151 5 3) (Reg.operands [.gpr 3] [])) #v[798]
    (.letOp (n := 810) (.out 0x103154 (xorR64R64Effect 0x103154 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[806, 802]
    (.letOp (n := 811) (.exec 0x103154 (fun s => s.RIP = 0x103154) (xorR64R64Effect 0x103154 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[806, 802]
    (.letOp (n := 812) (.out 0x103157 (movR64R64Effect 0x103157 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[782]
    (.letOp (n := 813) (.exec 0x103157 (fun s => s.RIP = 0x103157) (movR64R64Effect 0x103157 3 2) (Reg.operands [.gpr 2] [])) #v[782]
    (.letOp (n := 814) (.out 0x10315a (movR64Imm64Effect 0x10315a 11 0x4444444444444444) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 815) (.exec 0x10315a (fun s => s.RIP = 0x10315a) (movR64Imm64Effect 0x10315a 11 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 816) (.out 0x103164 (andR64R64Effect 0x103164 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[812, 814]
    (.letOp (n := 817) (.exec 0x103164 (fun s => s.RIP = 0x103164) (andR64R64Effect 0x103164 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[812, 814]
    (.letOp (n := 818) (.out 0x103167 (andR64R64Effect 0x103167 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[782, 770]
    (.letOp (n := 819) (.exec 0x103167 (fun s => s.RIP = 0x103167) (andR64R64Effect 0x103167 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[782, 770]
    (.letOp (n := 820) (.out 0x10316a (andR64R64Effect 0x10316a 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12] []) (.reg (.gpr 8))) #v[794, 786]
    (.letOp (n := 821) (.exec 0x10316a (fun s => s.RIP = 0x10316a) (andR64R64Effect 0x10316a 8 12) (Reg.operands [.gpr 8, .gpr 12] [])) #v[794, 786]
    (.letOp (n := 822) (.out 0x10316d (andR64R64Effect 0x10316d 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[796, 814]
    (.letOp (n := 823) (.exec 0x10316d (fun s => s.RIP = 0x10316d) (andR64R64Effect 0x10316d 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[796, 814]
    (.letOp (n := 824) (.out 0x103170 (movR64R64Effect 0x103170 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[816]
    (.letOp (n := 825) (.exec 0x103170 (fun s => s.RIP = 0x103170) (movR64R64Effect 0x103170 15 3) (Reg.operands [.gpr 3] [])) #v[816]
    (.letOp (n := 826) (.out 0x103173 (imulR64R64Effect 0x103173 4 15 7) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 7] []) (.reg (.gpr 15))) #v[824, 822]
    (.letOp (n := 827) (.exec 0x103173 (fun s => s.RIP = 0x103173) (imulR64R64Effect 0x103173 4 15 7) (Reg.operands [.gpr 15, .gpr 7] [])) #v[824, 822]
    (.letOp (n := 828) (.out 0x103177 (movR64R64Effect 0x103177 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[818]
    (.letOp (n := 829) (.exec 0x103177 (fun s => s.RIP = 0x103177) (movR64R64Effect 0x103177 11 2) (Reg.operands [.gpr 2] [])) #v[818]
    (.letOp (n := 830) (.out 0x10317a (imulR64R64Effect 0x10317a 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[828, 820]
    (.letOp (n := 831) (.exec 0x10317a (fun s => s.RIP = 0x10317a) (imulR64R64Effect 0x10317a 4 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[828, 820]
    (.letOp (n := 832) (.out 0x10317e (xorR64R64Effect 0x10317e 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[830, 826]
    (.letOp (n := 833) (.exec 0x10317e (fun s => s.RIP = 0x10317e) (xorR64R64Effect 0x10317e 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[830, 826]
    (.letOp (n := 834) (.out 0x103181 (xorR64R64Effect 0x103181 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[832, 810]
    (.letOp (n := 835) (.exec 0x103181 (fun s => s.RIP = 0x103181) (xorR64R64Effect 0x103181 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[832, 810]
    (.letOp (n := 836) (.out 0x103184 (movR64R64Effect 0x103184 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[778]
    (.letOp (n := 837) (.exec 0x103184 (fun s => s.RIP = 0x103184) (movR64R64Effect 0x103184 14 10) (Reg.operands [.gpr 10] [])) #v[778]
    (.letOp (n := 838) (.out 0x103187 (imulR64R64Effect 0x103187 4 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 8] []) (.reg (.gpr 14))) #v[836, 820]
    (.letOp (n := 839) (.exec 0x103187 (fun s => s.RIP = 0x103187) (imulR64R64Effect 0x103187 4 14 8) (Reg.operands [.gpr 14, .gpr 8] [])) #v[836, 820]
    (.letOp (n := 840) (.out 0x10318b (movR64R64Effect 0x10318b 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[784]
    (.letOp (n := 841) (.exec 0x10318b (fun s => s.RIP = 0x10318b) (movR64R64Effect 0x10318b 12 9) (Reg.operands [.gpr 9] [])) #v[784]
    (b_l102bd0_20))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_19 : List UInt8 :=
  [0x4C, 0x0F, 0xAF, 0xD9, 0x4D, 0x89, 0xCE, 0x4C, 0x0F, 0xAF, 0xF3, 0x48, 0x89, 0xDD, 0x4D, 0x31,
    0xDE, 0x48, 0x89, 0xD3, 0x49, 0xBB, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x4C, 0x21,
    0xDB, 0x4C, 0x21, 0xFA, 0x4D, 0x21, 0xE0, 0x4C, 0x21, 0xDF, 0x49, 0x89, 0xDF, 0x4C, 0x0F, 0xAF,
    0xFF, 0x49, 0x89, 0xD3, 0x4D, 0x0F, 0xAF, 0xD8, 0x4D, 0x31, 0xFB, 0x4D, 0x31, 0xF3, 0x4D, 0x89,
    0xD6, 0x4D, 0x0F, 0xAF, 0xF0, 0x4D, 0x89, 0xCC] ++ bytes_l102bd0_20

theorem code_l102bd0_19 : ∀ x ∈ codeRange 0x103146 bytes_l102bd0_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3146 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_20

def b_l102bd0_18 : Block Op Label signature Reg.count 762 :=
  .letOp (n := 762) (.out 0x1030fa (orR64R64Effect 0x1030fa 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[760, 756]
    (.letOp (n := 763) (.exec 0x1030fa (fun s => s.RIP = 0x1030fa) (orR64R64Effect 0x1030fa 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[760, 756]
    (.letOp (n := 764) (.out 0x1030fd (movR64Imm64Effect 0x1030fd 2 0x4444444444444444) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 765) (.exec 0x1030fd (fun s => s.RIP = 0x1030fd) (movR64Imm64Effect 0x1030fd 2 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 766) (.out 0x103107 (andR64R64Effect 0x103107 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[744, 764]
    (.letOp (n := 767) (.exec 0x103107 (fun s => s.RIP = 0x103107) (andR64R64Effect 0x103107 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[744, 764]
    (.letOp (n := 768) (.out 0x10310a (orR64R64Effect 0x10310a 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[766, 762]
    (.letOp (n := 769) (.exec 0x10310a (fun s => s.RIP = 0x10310a) (orR64R64Effect 0x10310a 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[766, 762]
    (.letOp (n := 770) (.out 0x10310d (movR64Imm64Effect 0x10310d 15 0x8888888888888888) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 771) (.exec 0x10310d (fun s => s.RIP = 0x10310d) (movR64Imm64Effect 0x10310d 15 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 772) (.out 0x103117 (andR64R64Effect 0x103117 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[752, 770]
    (.letOp (n := 773) (.exec 0x103117 (fun s => s.RIP = 0x103117) (andR64R64Effect 0x103117 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[752, 770]
    (.letOp (n := 774) (.out 0x10311a (orR64R64Effect 0x10311a 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[772, 768]
    (.letOp (n := 775) (.exec 0x10311a (fun s => s.RIP = 0x10311a) (orR64R64Effect 0x10311a 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[772, 768]
    (.letOp (n := 776) (.out 0x10311d (movR64R64Effect 0x10311d 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[671]
    (.letOp (n := 777) (.exec 0x10311d (fun s => s.RIP = 0x10311d) (movR64R64Effect 0x10311d 10 12) (Reg.operands [.gpr 12] [])) #v[671]
    (.letOp (n := 778) (.out 0x103120 (andR64R64Effect 0x103120 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[776, 754]
    (.letOp (n := 779) (.exec 0x103120 (fun s => s.RIP = 0x103120) (andR64R64Effect 0x103120 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[776, 754]
    (.letOp (n := 780) (.out 0x103123 (movR64R64Effect 0x103123 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[671]
    (.letOp (n := 781) (.exec 0x103123 (fun s => s.RIP = 0x103123) (movR64R64Effect 0x103123 9 12) (Reg.operands [.gpr 12] [])) #v[671]
    (.letOp (n := 782) (.out 0x103126 (movR64R64Effect 0x103126 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[671]
    (.letOp (n := 783) (.exec 0x103126 (fun s => s.RIP = 0x103126) (movR64R64Effect 0x103126 2 12) (Reg.operands [.gpr 12] [])) #v[671]
    (.letOp (n := 784) (.out 0x103129 (andR64R64Effect 0x103129 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[780, 758]
    (.letOp (n := 785) (.exec 0x103129 (fun s => s.RIP = 0x103129) (andR64R64Effect 0x103129 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[780, 758]
    (.letOp (n := 786) (.out 0x10312c (movR64R64Effect 0x10312c 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[758]
    (.letOp (n := 787) (.exec 0x10312c (fun s => s.RIP = 0x10312c) (movR64R64Effect 0x10312c 12 1) (Reg.operands [.gpr 1] [])) #v[758]
    (.letOp (n := 788) (.out 0x10312f (movR64M64Effect 0x10312f 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 789) (.exec 0x10312f (LoadPre 0x10312f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10312f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10312f 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 790) (.out 0x103134 (movR64R64Effect 0x103134 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[788]
    (.letOp (n := 791) (.exec 0x103134 (fun s => s.RIP = 0x103134) (movR64R64Effect 0x103134 1 3) (Reg.operands [.gpr 3] [])) #v[788]
    (.letOp (n := 792) (.out 0x103137 (andR64R64Effect 0x103137 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[790, 754]
    (.letOp (n := 793) (.exec 0x103137 (fun s => s.RIP = 0x103137) (andR64R64Effect 0x103137 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[790, 754]
    (.letOp (n := 794) (.out 0x10313a (movR64R64Effect 0x10313a 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[788]
    (.letOp (n := 795) (.exec 0x10313a (fun s => s.RIP = 0x10313a) (movR64R64Effect 0x10313a 8 3) (Reg.operands [.gpr 3] [])) #v[788]
    (.letOp (n := 796) (.out 0x10313d (movR64R64Effect 0x10313d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[788]
    (.letOp (n := 797) (.exec 0x10313d (fun s => s.RIP = 0x10313d) (movR64R64Effect 0x10313d 7 3) (Reg.operands [.gpr 3] [])) #v[788]
    (.letOp (n := 798) (.out 0x103140 (andR64R64Effect 0x103140 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[788, 770]
    (.letOp (n := 799) (.exec 0x103140 (fun s => s.RIP = 0x103140) (andR64R64Effect 0x103140 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[788, 770]
    (.letOp (n := 800) (.out 0x103143 (movR64R64Effect 0x103143 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[778]
    (.letOp (n := 801) (.exec 0x103143 (fun s => s.RIP = 0x103143) (movR64R64Effect 0x103143 11 10) (Reg.operands [.gpr 10] [])) #v[778]
    (b_l102bd0_19))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_18 : List UInt8 :=
  [0x4C, 0x09, 0xD3, 0x48, 0xBA, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x49, 0x21, 0xD6,
    0x49, 0x09, 0xDE, 0x49, 0xBF, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x4C, 0x21, 0xF8,
    0x4C, 0x09, 0xF0, 0x4D, 0x89, 0xE2, 0x49, 0x21, 0xFA, 0x4D, 0x89, 0xE1, 0x4C, 0x89, 0xE2, 0x49,
    0x21, 0xC9, 0x49, 0x89, 0xCC, 0x48, 0x8B, 0x5C, 0x24, 0x08, 0x48, 0x89, 0xD9, 0x48, 0x21, 0xF9,
    0x49, 0x89, 0xD8, 0x48, 0x89, 0xDF, 0x4C, 0x21, 0xFB, 0x4D, 0x89, 0xD3] ++ bytes_l102bd0_19

theorem code_l102bd0_18 : ∀ x ∈ codeRange 0x1030fa bytes_l102bd0_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x30fa 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_19

def b_l102bd0_17 : Block Op Label signature Reg.count 722 :=
  .letOp (n := 722) (.out 0x1030a8 (xorR64R64Effect 0x1030a8 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[720, 710]
    (.letOp (n := 723) (.exec 0x1030a8 (fun s => s.RIP = 0x1030a8) (xorR64R64Effect 0x1030a8 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[720, 710]
    (.letOp (n := 724) (.out 0x1030ab (movR64R64Effect 0x1030ab 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 5] []) (.reg (.gpr 14))) #v[684]
    (.letOp (n := 725) (.exec 0x1030ab (fun s => s.RIP = 0x1030ab) (movR64R64Effect 0x1030ab 14 5) (Reg.operands [.gpr 5] [])) #v[684]
    (.letOp (n := 726) (.out 0x1030ae (imulR64R64Effect 0x1030ae 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[724, 659]
    (.letOp (n := 727) (.exec 0x1030ae (fun s => s.RIP = 0x1030ae) (imulR64R64Effect 0x1030ae 4 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[724, 659]
    (.letOp (n := 728) (.out 0x1030b2 (imulR64R64Effect 0x1030b2 4 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[659, 641]
    (.letOp (n := 729) (.exec 0x1030b2 (fun s => s.RIP = 0x1030b2) (imulR64R64Effect 0x1030b2 4 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[659, 641]
    (.letOp (n := 730) (.out 0x1030b6 (imulR64R64Effect 0x1030b6 4 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[641, 688]
    (.letOp (n := 731) (.exec 0x1030b6 (fun s => s.RIP = 0x1030b6) (imulR64R64Effect 0x1030b6 4 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[641, 688]
    (.letOp (n := 732) (.out 0x1030ba (imulR64R64Effect 0x1030ba 4 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[688, 647]
    (.letOp (n := 733) (.exec 0x1030ba (fun s => s.RIP = 0x1030ba) (imulR64R64Effect 0x1030ba 4 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[688, 647]
    (.letOp (n := 734) (.out 0x1030be (imulR64R64Effect 0x1030be 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[647, 686]
    (.letOp (n := 735) (.exec 0x1030be (fun s => s.RIP = 0x1030be) (imulR64R64Effect 0x1030be 4 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[647, 686]
    (.letOp (n := 736) (.out 0x1030c2 (xorR64R64Effect 0x1030c2 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[734, 730]
    (.letOp (n := 737) (.exec 0x1030c2 (fun s => s.RIP = 0x1030c2) (xorR64R64Effect 0x1030c2 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[734, 730]
    (.letOp (n := 738) (.out 0x1030c5 (imulR64R64Effect 0x1030c5 4 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[686, 682]
    (.letOp (n := 739) (.exec 0x1030c5 (fun s => s.RIP = 0x1030c5) (imulR64R64Effect 0x1030c5 4 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[686, 682]
    (.letOp (n := 740) (.out 0x1030c9 (imulR64R64Effect 0x1030c9 4 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[682, 653]
    (.letOp (n := 741) (.exec 0x1030c9 (fun s => s.RIP = 0x1030c9) (imulR64R64Effect 0x1030c9 4 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[682, 653]
    (.letOp (n := 742) (.out 0x1030cd (xorR64R64Effect 0x1030cd 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[726, 740]
    (.letOp (n := 743) (.exec 0x1030cd (fun s => s.RIP = 0x1030cd) (xorR64R64Effect 0x1030cd 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[726, 740]
    (.letOp (n := 744) (.out 0x1030d0 (xorR64R64Effect 0x1030d0 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[742, 736]
    (.letOp (n := 745) (.exec 0x1030d0 (fun s => s.RIP = 0x1030d0) (xorR64R64Effect 0x1030d0 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[742, 736]
    (.letOp (n := 746) (.out 0x1030d3 (xorR64R64Effect 0x1030d3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[732, 728]
    (.letOp (n := 747) (.exec 0x1030d3 (fun s => s.RIP = 0x1030d3) (xorR64R64Effect 0x1030d3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[732, 728]
    (.letOp (n := 748) (.out 0x1030d6 (imulR64R64Effect 0x1030d6 4 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[653, 684]
    (.letOp (n := 749) (.exec 0x1030d6 (fun s => s.RIP = 0x1030d6) (imulR64R64Effect 0x1030d6 4 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[653, 684]
    (.letOp (n := 750) (.out 0x1030da (xorR64R64Effect 0x1030da 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[748, 738]
    (.letOp (n := 751) (.exec 0x1030da (fun s => s.RIP = 0x1030da) (xorR64R64Effect 0x1030da 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[748, 738]
    (.letOp (n := 752) (.out 0x1030dd (xorR64R64Effect 0x1030dd 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[750, 746]
    (.letOp (n := 753) (.exec 0x1030dd (fun s => s.RIP = 0x1030dd) (xorR64R64Effect 0x1030dd 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[750, 746]
    (.letOp (n := 754) (.out 0x1030e0 (movR64Imm64Effect 0x1030e0 7 0x1111111111111111) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 755) (.exec 0x1030e0 (fun s => s.RIP = 0x1030e0) (movR64Imm64Effect 0x1030e0 7 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 756) (.out 0x1030ea (andR64R64Effect 0x1030ea 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[700, 754]
    (.letOp (n := 757) (.exec 0x1030ea (fun s => s.RIP = 0x1030ea) (andR64R64Effect 0x1030ea 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[700, 754]
    (.letOp (n := 758) (.out 0x1030ed (movR64Imm64Effect 0x1030ed 1 0x2222222222222222) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 759) (.exec 0x1030ed (fun s => s.RIP = 0x1030ed) (movR64Imm64Effect 0x1030ed 1 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 760) (.out 0x1030f7 (andR64R64Effect 0x1030f7 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[722, 758]
    (.letOp (n := 761) (.exec 0x1030f7 (fun s => s.RIP = 0x1030f7) (andR64R64Effect 0x1030f7 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[722, 758]
    (b_l102bd0_18))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_17 : List UInt8 :=
  [0x4C, 0x31, 0xF3, 0x49, 0x89, 0xEE, 0x4C, 0x0F, 0xAF, 0xF2, 0x49, 0x0F, 0xAF, 0xD1, 0x4C, 0x0F,
    0xAF, 0xC9, 0x48, 0x0F, 0xAF, 0xCF, 0x49, 0x0F, 0xAF, 0xF8, 0x4C, 0x31, 0xCF, 0x4D, 0x0F, 0xAF,
    0xC3, 0x4C, 0x0F, 0xAF, 0xD8, 0x4D, 0x31, 0xDE, 0x49, 0x31, 0xFE, 0x48, 0x31, 0xD1, 0x48, 0x0F,
    0xAF, 0xC5, 0x4C, 0x31, 0xC0, 0x48, 0x31, 0xC8, 0x48, 0xBF, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11,
    0x11, 0x11, 0x49, 0x21, 0xFA, 0x48, 0xB9, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x48,
    0x21, 0xCB] ++ bytes_l102bd0_18

theorem code_l102bd0_17 : ∀ x ∈ codeRange 0x1030a8 bytes_l102bd0_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x30a8 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_18

def b_l102bd0_16 : Block Op Label signature Reg.count 682 :=
  .letOp (n := 682) (.out 0x103066 (andR64R64Effect 0x103066 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[678, 680]
    (.letOp (n := 683) (.exec 0x103066 (fun s => s.RIP = 0x103066) (andR64R64Effect 0x103066 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[678, 680]
    (.letOp (n := 684) (.out 0x103069 (andR64R64Effect 0x103069 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[645, 623]
    (.letOp (n := 685) (.exec 0x103069 (fun s => s.RIP = 0x103069) (andR64R64Effect 0x103069 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[645, 623]
    (.letOp (n := 686) (.out 0x10306c (andR64R64Effect 0x10306c 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[655, 649]
    (.letOp (n := 687) (.exec 0x10306c (fun s => s.RIP = 0x10306c) (andR64R64Effect 0x10306c 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[655, 649]
    (.letOp (n := 688) (.out 0x10306f (andR64R64Effect 0x10306f 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[657, 680]
    (.letOp (n := 689) (.exec 0x10306f (fun s => s.RIP = 0x10306f) (andR64R64Effect 0x10306f 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[657, 680]
    (.letOp (n := 690) (.out 0x103072 (movR64R64Effect 0x103072 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[682]
    (.letOp (n := 691) (.exec 0x103072 (fun s => s.RIP = 0x103072) (movR64R64Effect 0x103072 14 11) (Reg.operands [.gpr 11] [])) #v[682]
    (.letOp (n := 692) (.out 0x103075 (imulR64R64Effect 0x103075 4 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[690, 688]
    (.letOp (n := 693) (.exec 0x103075 (fun s => s.RIP = 0x103075) (imulR64R64Effect 0x103075 4 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[690, 688]
    (.letOp (n := 694) (.out 0x103079 (movR64R64Effect 0x103079 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 5] []) (.reg (.gpr 10))) #v[684]
    (.letOp (n := 695) (.exec 0x103079 (fun s => s.RIP = 0x103079) (movR64R64Effect 0x103079 10 5) (Reg.operands [.gpr 5] [])) #v[684]
    (.letOp (n := 696) (.out 0x10307c (imulR64R64Effect 0x10307c 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[694, 686]
    (.letOp (n := 697) (.exec 0x10307c (fun s => s.RIP = 0x10307c) (imulR64R64Effect 0x10307c 4 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[694, 686]
    (.letOp (n := 698) (.out 0x103080 (xorR64R64Effect 0x103080 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[696, 692]
    (.letOp (n := 699) (.exec 0x103080 (fun s => s.RIP = 0x103080) (xorR64R64Effect 0x103080 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[696, 692]
    (.letOp (n := 700) (.out 0x103083 (xorR64R64Effect 0x103083 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[698, 669]
    (.letOp (n := 701) (.exec 0x103083 (fun s => s.RIP = 0x103083) (xorR64R64Effect 0x103083 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[698, 669]
    (.letOp (n := 702) (.out 0x103086 (movR64R64Effect 0x103086 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[641]
    (.letOp (n := 703) (.exec 0x103086 (fun s => s.RIP = 0x103086) (movR64R64Effect 0x103086 3 9) (Reg.operands [.gpr 9] [])) #v[641]
    (.letOp (n := 704) (.out 0x103089 (imulR64R64Effect 0x103089 4 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[702, 686]
    (.letOp (n := 705) (.exec 0x103089 (fun s => s.RIP = 0x103089) (imulR64R64Effect 0x103089 4 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[702, 686]
    (.letOp (n := 706) (.out 0x10308d (movR64R64Effect 0x10308d 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[647]
    (.letOp (n := 707) (.exec 0x10308d (fun s => s.RIP = 0x10308d) (movR64R64Effect 0x10308d 14 7) (Reg.operands [.gpr 7] [])) #v[647]
    (.letOp (n := 708) (.out 0x103090 (imulR64R64Effect 0x103090 4 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[706, 653]
    (.letOp (n := 709) (.exec 0x103090 (fun s => s.RIP = 0x103090) (imulR64R64Effect 0x103090 4 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[706, 653]
    (.letOp (n := 710) (.out 0x103094 (xorR64R64Effect 0x103094 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[708, 704]
    (.letOp (n := 711) (.exec 0x103094 (fun s => s.RIP = 0x103094) (xorR64R64Effect 0x103094 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[708, 704]
    (.letOp (n := 712) (.out 0x103097 (movR64R64Effect 0x103097 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 11] []) (.reg (.gpr 15))) #v[682]
    (.letOp (n := 713) (.exec 0x103097 (fun s => s.RIP = 0x103097) (movR64R64Effect 0x103097 15 11) (Reg.operands [.gpr 11] [])) #v[682]
    (.letOp (n := 714) (.out 0x10309a (imulR64R64Effect 0x10309a 4 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[712, 659]
    (.letOp (n := 715) (.exec 0x10309a (fun s => s.RIP = 0x10309a) (imulR64R64Effect 0x10309a 4 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[712, 659]
    (.letOp (n := 716) (.out 0x10309e (movR64R64Effect 0x10309e 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 5] []) (.reg (.gpr 3))) #v[684]
    (.letOp (n := 717) (.exec 0x10309e (fun s => s.RIP = 0x10309e) (movR64R64Effect 0x10309e 3 5) (Reg.operands [.gpr 5] [])) #v[684]
    (.letOp (n := 718) (.out 0x1030a1 (imulR64R64Effect 0x1030a1 4 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[716, 688]
    (.letOp (n := 719) (.exec 0x1030a1 (fun s => s.RIP = 0x1030a1) (imulR64R64Effect 0x1030a1 4 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[716, 688]
    (.letOp (n := 720) (.out 0x1030a5 (xorR64R64Effect 0x1030a5 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[718, 714]
    (.letOp (n := 721) (.exec 0x1030a5 (fun s => s.RIP = 0x1030a5) (xorR64R64Effect 0x1030a5 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[718, 714]
    (b_l102bd0_17))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_16 : List UInt8 :=
  [0x4D, 0x21, 0xD3, 0x4C, 0x21, 0xF5, 0x4D, 0x21, 0xF8, 0x4C, 0x21, 0xD1, 0x4D, 0x89, 0xDE, 0x4C,
    0x0F, 0xAF, 0xF1, 0x49, 0x89, 0xEA, 0x4D, 0x0F, 0xAF, 0xD0, 0x4D, 0x31, 0xF2, 0x49, 0x31, 0xDA,
    0x4C, 0x89, 0xCB, 0x49, 0x0F, 0xAF, 0xD8, 0x49, 0x89, 0xFE, 0x4C, 0x0F, 0xAF, 0xF0, 0x49, 0x31,
    0xDE, 0x4D, 0x89, 0xDF, 0x4C, 0x0F, 0xAF, 0xFA, 0x48, 0x89, 0xEB, 0x48, 0x0F, 0xAF, 0xD9, 0x4C,
    0x31, 0xFB] ++ bytes_l102bd0_17

theorem code_l102bd0_16 : ∀ x ∈ codeRange 0x103066 bytes_l102bd0_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3066 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_17

def b_l102bd0_15 : Block Op Label signature Reg.count 643 :=
  .letOp (n := 643) (.out 0x10301e (movR64R64Effect 0x10301e 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[635]
    (.letOp (n := 644) (.exec 0x10301e (fun s => s.RIP = 0x10301e) (movR64R64Effect 0x10301e 7 0) (Reg.operands [.gpr 0] [])) #v[635]
    (.letOp (n := 645) (.out 0x103021 (movR64R64Effect 0x103021 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[635]
    (.letOp (n := 646) (.exec 0x103021 (fun s => s.RIP = 0x103021) (movR64R64Effect 0x103021 5 0) (Reg.operands [.gpr 0] [])) #v[635]
    (.letOp (n := 647) (.out 0x103024 (andR64R64Effect 0x103024 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[643, 611]
    (.letOp (n := 648) (.exec 0x103024 (fun s => s.RIP = 0x103024) (andR64R64Effect 0x103024 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[643, 611]
    (.letOp (n := 649) (.out 0x103027 (movR64R64Effect 0x103027 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[611]
    (.letOp (n := 650) (.exec 0x103027 (fun s => s.RIP = 0x103027) (movR64R64Effect 0x103027 15 8) (Reg.operands [.gpr 8] [])) #v[611]
    (.letOp (n := 651) (.out 0x10302a (movR64R64Effect 0x10302a 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[631]
    (.letOp (n := 652) (.exec 0x10302a (fun s => s.RIP = 0x10302a) (movR64R64Effect 0x10302a 0 2) (Reg.operands [.gpr 2] [])) #v[631]
    (.letOp (n := 653) (.out 0x10302d (andR64R64Effect 0x10302d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[651, 639]
    (.letOp (n := 654) (.exec 0x10302d (fun s => s.RIP = 0x10302d) (andR64R64Effect 0x10302d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[651, 639]
    (.letOp (n := 655) (.out 0x103030 (movR64R64Effect 0x103030 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[631]
    (.letOp (n := 656) (.exec 0x103030 (fun s => s.RIP = 0x103030) (movR64R64Effect 0x103030 8 2) (Reg.operands [.gpr 2] [])) #v[631]
    (.letOp (n := 657) (.out 0x103033 (movR64R64Effect 0x103033 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[631]
    (.letOp (n := 658) (.exec 0x103033 (fun s => s.RIP = 0x103033) (movR64R64Effect 0x103033 1 2) (Reg.operands [.gpr 2] [])) #v[631]
    (.letOp (n := 659) (.out 0x103036 (andR64R64Effect 0x103036 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[631, 623]
    (.letOp (n := 660) (.exec 0x103036 (fun s => s.RIP = 0x103036) (andR64R64Effect 0x103036 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[631, 623]
    (.letOp (n := 661) (.out 0x103039 (movR64R64Effect 0x103039 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[641]
    (.letOp (n := 662) (.exec 0x103039 (fun s => s.RIP = 0x103039) (movR64R64Effect 0x103039 10 9) (Reg.operands [.gpr 9] [])) #v[641]
    (.letOp (n := 663) (.out 0x10303c (imulR64R64Effect 0x10303c 4 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[661, 653]
    (.letOp (n := 664) (.exec 0x10303c (fun s => s.RIP = 0x10303c) (imulR64R64Effect 0x10303c 4 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[661, 653]
    (.letOp (n := 665) (.out 0x103040 (movR64R64Effect 0x103040 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[647]
    (.letOp (n := 666) (.exec 0x103040 (fun s => s.RIP = 0x103040) (movR64R64Effect 0x103040 3 7) (Reg.operands [.gpr 7] [])) #v[647]
    (.letOp (n := 667) (.out 0x103043 (imulR64R64Effect 0x103043 4 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[665, 659]
    (.letOp (n := 668) (.exec 0x103043 (fun s => s.RIP = 0x103043) (imulR64R64Effect 0x103043 4 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[665, 659]
    (.letOp (n := 669) (.out 0x103047 (xorR64R64Effect 0x103047 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[667, 663]
    (.letOp (n := 670) (.exec 0x103047 (fun s => s.RIP = 0x103047) (xorR64R64Effect 0x103047 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[667, 663]
    (.letOp (n := 671) (.out 0x10304a (movR64M64Effect 0x10304a 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 672) (.exec 0x10304a (LoadPre 0x10304a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10304a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10304a 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 673) (.out 0x10304f (movR64R64Effect 0x10304f 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[671]
    (.letOp (n := 674) (.exec 0x10304f (fun s => s.RIP = 0x10304f) (movR64R64Effect 0x10304f 10 12) (Reg.operands [.gpr 12] [])) #v[671]
    (.letOp (n := 675) (.out 0x103052 (xorR64R64Effect 0x103052 10 5) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5] []) (.reg (.gpr 10))) #v[673, 645]
    (.letOp (n := 676) (.exec 0x103052 (fun s => s.RIP = 0x103052) (xorR64R64Effect 0x103052 10 5) (Reg.operands [.gpr 10, .gpr 5] [])) #v[673, 645]
    (.letOp (n := 677) (.exec 0x103055 (StorePre 0x103055 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103055 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103055 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[675, 65]
    (.letOp (n := 678) (.out 0x103059 (movR64R64Effect 0x103059 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 5] []) (.reg (.gpr 11))) #v[645]
    (.letOp (n := 679) (.exec 0x103059 (fun s => s.RIP = 0x103059) (movR64R64Effect 0x103059 11 5) (Reg.operands [.gpr 5] [])) #v[645]
    (.letOp (n := 680) (.out 0x10305c (movR64Imm64Effect 0x10305c 10 0x4444444444444444) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 681) (.exec 0x10305c (fun s => s.RIP = 0x10305c) (movR64Imm64Effect 0x10305c 10 0x4444444444444444) (Reg.operands [] [])) #v[]
    (b_l102bd0_16)))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_15 : List UInt8 :=
  [0x48, 0x89, 0xC7, 0x48, 0x89, 0xC5, 0x4C, 0x21, 0xC7, 0x4D, 0x89, 0xC7, 0x48, 0x89, 0xD0, 0x48,
    0x21, 0xC8, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xD1, 0x4C, 0x21, 0xF2, 0x4D, 0x89, 0xCA, 0x4C, 0x0F,
    0xAF, 0xD0, 0x48, 0x89, 0xFB, 0x48, 0x0F, 0xAF, 0xDA, 0x4C, 0x31, 0xD3, 0x4C, 0x8B, 0x64, 0x24,
    0x18, 0x4D, 0x89, 0xE2, 0x49, 0x31, 0xEA, 0x4C, 0x89, 0x14, 0x24, 0x49, 0x89, 0xEB, 0x49, 0xBA,
    0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44] ++ bytes_l102bd0_16

theorem code_l102bd0_15 : ∀ x ∈ codeRange 0x10301e bytes_l102bd0_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x301e 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_16

def b_l102bd0_14 : Block Op Label signature Reg.count 603 :=
  .letOp (n := 603) (.out 0x102fce (imulR64R64Effect 0x102fce 4 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[515, 539]
    (.letOp (n := 604) (.exec 0x102fce (fun s => s.RIP = 0x102fce) (imulR64R64Effect 0x102fce 4 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[515, 539]
    (.letOp (n := 605) (.out 0x102fd2 (xorR64R64Effect 0x102fd2 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[603, 593]
    (.letOp (n := 606) (.exec 0x102fd2 (fun s => s.RIP = 0x102fd2) (xorR64R64Effect 0x102fd2 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[603, 593]
    (.letOp (n := 607) (.out 0x102fd5 (xorR64R64Effect 0x102fd5 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[605, 601]
    (.letOp (n := 608) (.exec 0x102fd5 (fun s => s.RIP = 0x102fd5) (xorR64R64Effect 0x102fd5 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[605, 601]
    (.letOp (n := 609) (.out 0x102fd8 (andR64R64Effect 0x102fd8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[555, 517]
    (.letOp (n := 610) (.exec 0x102fd8 (fun s => s.RIP = 0x102fd8) (andR64R64Effect 0x102fd8 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[555, 517]
    (.letOp (n := 611) (.out 0x102fdb (movR64R64Effect 0x102fdb 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[488]
    (.letOp (n := 612) (.exec 0x102fdb (fun s => s.RIP = 0x102fdb) (movR64R64Effect 0x102fdb 8 2) (Reg.operands [.gpr 2] [])) #v[488]
    (.letOp (n := 613) (.out 0x102fde (andR64R64Effect 0x102fde 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[577, 488]
    (.letOp (n := 614) (.exec 0x102fde (fun s => s.RIP = 0x102fde) (andR64R64Effect 0x102fde 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[577, 488]
    (.letOp (n := 615) (.out 0x102fe1 (orR64R64Effect 0x102fe1 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[613, 609]
    (.letOp (n := 616) (.exec 0x102fe1 (fun s => s.RIP = 0x102fe1) (orR64R64Effect 0x102fe1 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[613, 609]
    (.letOp (n := 617) (.out 0x102fe4 (movR64Imm64Effect 0x102fe4 0 0x4444444444444444) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 618) (.exec 0x102fe4 (fun s => s.RIP = 0x102fe4) (movR64Imm64Effect 0x102fe4 0 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 619) (.out 0x102fee (andR64R64Effect 0x102fee 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[599, 617]
    (.letOp (n := 620) (.exec 0x102fee (fun s => s.RIP = 0x102fee) (andR64R64Effect 0x102fee 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[599, 617]
    (.letOp (n := 621) (.out 0x102ff1 (orR64R64Effect 0x102ff1 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[619, 615]
    (.letOp (n := 622) (.exec 0x102ff1 (fun s => s.RIP = 0x102ff1) (orR64R64Effect 0x102ff1 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[619, 615]
    (.letOp (n := 623) (.out 0x102ff4 (movR64Imm64Effect 0x102ff4 14 0x8888888888888888) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 624) (.exec 0x102ff4 (fun s => s.RIP = 0x102ff4) (movR64Imm64Effect 0x102ff4 14 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 625) (.out 0x102ffe (andR64R64Effect 0x102ffe 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[607, 623]
    (.letOp (n := 626) (.exec 0x102ffe (fun s => s.RIP = 0x102ffe) (andR64R64Effect 0x102ffe 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[607, 623]
    (.letOp (n := 627) (.out 0x103001 (orR64R64Effect 0x103001 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[625, 621]
    (.letOp (n := 628) (.exec 0x103001 (fun s => s.RIP = 0x103001) (orR64R64Effect 0x103001 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[625, 621]
    (.letOp (n := 629) (.out 0x103004 (movR64M64Effect 0x103004 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 630) (.exec 0x103004 (LoadPre 0x103004 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x103004 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103004 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 631) (.out 0x103009 (movR64M64Effect 0x103009 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 632) (.exec 0x103009 (LoadPre 0x103009 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x103009 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103009 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 633) (.out 0x10300d (xorR64R64Effect 0x10300d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[629, 631]
    (.letOp (n := 634) (.exec 0x10300d (fun s => s.RIP = 0x10300d) (xorR64R64Effect 0x10300d 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[629, 631]
    (.letOp (n := 635) (.out 0x103010 (movR64M64Effect 0x103010 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 636) (.exec 0x103010 (LoadPre 0x103010 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x103010 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103010 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 637) (.out 0x103015 (movR64R64Effect 0x103015 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[635]
    (.letOp (n := 638) (.exec 0x103015 (fun s => s.RIP = 0x103015) (movR64R64Effect 0x103015 9 0) (Reg.operands [.gpr 0] [])) #v[635]
    (.letOp (n := 639) (.out 0x103018 (movR64R64Effect 0x103018 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[517]
    (.letOp (n := 640) (.exec 0x103018 (fun s => s.RIP = 0x103018) (movR64R64Effect 0x103018 1 5) (Reg.operands [.gpr 5] [])) #v[517]
    (.letOp (n := 641) (.out 0x10301b (andR64R64Effect 0x10301b 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[637, 517]
    (.letOp (n := 642) (.exec 0x10301b (fun s => s.RIP = 0x10301b) (andR64R64Effect 0x10301b 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[637, 517]
    (b_l102bd0_15))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_14 : List UInt8 :=
  [0x4D, 0x0F, 0xAF, 0xEC, 0x4D, 0x31, 0xC5, 0x49, 0x31, 0xC5, 0x48, 0x21, 0xEF, 0x49, 0x89, 0xD0,
    0x49, 0x21, 0xD3, 0x49, 0x09, 0xFB, 0x48, 0xB8, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
    0x48, 0x21, 0xC3, 0x4C, 0x09, 0xDB, 0x49, 0xBE, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88,
    0x4D, 0x21, 0xF5, 0x49, 0x09, 0xDD, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x14, 0x24, 0x48,
    0x31, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x49, 0x89, 0xC1, 0x48, 0x89, 0xE9, 0x49, 0x21, 0xE9] ++ bytes_l102bd0_15

theorem code_l102bd0_14 : ∀ x ∈ codeRange 0x102fce bytes_l102bd0_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2fce 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_15

def b_l102bd0_13 : Block Op Label signature Reg.count 563 :=
  .letOp (n := 563) (.out 0x102f88 (imulR64R64Effect 0x102f88 4 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[561, 515]
    (.letOp (n := 564) (.exec 0x102f88 (fun s => s.RIP = 0x102f88) (imulR64R64Effect 0x102f88 4 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[561, 515]
    (.letOp (n := 565) (.out 0x102f8c (xorR64R64Effect 0x102f8c 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[563, 559]
    (.letOp (n := 566) (.exec 0x102f8c (fun s => s.RIP = 0x102f8c) (xorR64R64Effect 0x102f8c 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[563, 559]
    (.letOp (n := 567) (.out 0x102f8f (movR64R64Effect 0x102f8f 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[537]
    (.letOp (n := 568) (.exec 0x102f8f (fun s => s.RIP = 0x102f8f) (movR64R64Effect 0x102f8f 14 10) (Reg.operands [.gpr 10] [])) #v[537]
    (.letOp (n := 569) (.out 0x102f92 (imulR64R64Effect 0x102f92 4 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[567, 523]
    (.letOp (n := 570) (.exec 0x102f92 (fun s => s.RIP = 0x102f92) (imulR64R64Effect 0x102f92 4 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[567, 523]
    (.letOp (n := 571) (.out 0x102f96 (movR64R64Effect 0x102f96 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[539]
    (.letOp (n := 572) (.exec 0x102f96 (fun s => s.RIP = 0x102f96) (movR64R64Effect 0x102f96 11 12) (Reg.operands [.gpr 12] [])) #v[539]
    (.letOp (n := 573) (.out 0x102f99 (imulR64R64Effect 0x102f99 4 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[571, 543]
    (.letOp (n := 574) (.exec 0x102f99 (fun s => s.RIP = 0x102f99) (imulR64R64Effect 0x102f99 4 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[571, 543]
    (.letOp (n := 575) (.out 0x102f9d (xorR64R64Effect 0x102f9d 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[573, 569]
    (.letOp (n := 576) (.exec 0x102f9d (fun s => s.RIP = 0x102f9d) (xorR64R64Effect 0x102f9d 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[573, 569]
    (.letOp (n := 577) (.out 0x102fa0 (xorR64R64Effect 0x102fa0 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[575, 565]
    (.letOp (n := 578) (.exec 0x102fa0 (fun s => s.RIP = 0x102fa0) (xorR64R64Effect 0x102fa0 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[575, 565]
    (.letOp (n := 579) (.out 0x102fa3 (movR64R64Effect 0x102fa3 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[539]
    (.letOp (n := 580) (.exec 0x102fa3 (fun s => s.RIP = 0x102fa3) (movR64R64Effect 0x102fa3 3 12) (Reg.operands [.gpr 12] [])) #v[539]
    (.letOp (n := 581) (.out 0x102fa6 (imulR64R64Effect 0x102fa6 4 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[579, 523]
    (.letOp (n := 582) (.exec 0x102fa6 (fun s => s.RIP = 0x102fa6) (imulR64R64Effect 0x102fa6 4 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[579, 523]
    (.letOp (n := 583) (.out 0x102faa (imulR64R64Effect 0x102faa 4 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[523, 507]
    (.letOp (n := 584) (.exec 0x102faa (fun s => s.RIP = 0x102faa) (imulR64R64Effect 0x102faa 4 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[523, 507]
    (.letOp (n := 585) (.out 0x102fae (imulR64R64Effect 0x102fae 4 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[507, 543]
    (.letOp (n := 586) (.exec 0x102fae (fun s => s.RIP = 0x102fae) (imulR64R64Effect 0x102fae 4 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[507, 543]
    (.letOp (n := 587) (.out 0x102fb2 (imulR64R64Effect 0x102fb2 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[543, 511]
    (.letOp (n := 588) (.exec 0x102fb2 (fun s => s.RIP = 0x102fb2) (imulR64R64Effect 0x102fb2 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[543, 511]
    (.letOp (n := 589) (.out 0x102fb6 (imulR64R64Effect 0x102fb6 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[511, 541]
    (.letOp (n := 590) (.exec 0x102fb6 (fun s => s.RIP = 0x102fb6) (imulR64R64Effect 0x102fb6 4 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[511, 541]
    (.letOp (n := 591) (.out 0x102fba (xorR64R64Effect 0x102fba 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[589, 585]
    (.letOp (n := 592) (.exec 0x102fba (fun s => s.RIP = 0x102fba) (xorR64R64Effect 0x102fba 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[589, 585]
    (.letOp (n := 593) (.out 0x102fbd (imulR64R64Effect 0x102fbd 4 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[541, 537]
    (.letOp (n := 594) (.exec 0x102fbd (fun s => s.RIP = 0x102fbd) (imulR64R64Effect 0x102fbd 4 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[541, 537]
    (.letOp (n := 595) (.out 0x102fc1 (imulR64R64Effect 0x102fc1 4 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[537, 515]
    (.letOp (n := 596) (.exec 0x102fc1 (fun s => s.RIP = 0x102fc1) (imulR64R64Effect 0x102fc1 4 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[537, 515]
    (.letOp (n := 597) (.out 0x102fc5 (xorR64R64Effect 0x102fc5 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[581, 595]
    (.letOp (n := 598) (.exec 0x102fc5 (fun s => s.RIP = 0x102fc5) (xorR64R64Effect 0x102fc5 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[581, 595]
    (.letOp (n := 599) (.out 0x102fc8 (xorR64R64Effect 0x102fc8 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[597, 591]
    (.letOp (n := 600) (.exec 0x102fc8 (fun s => s.RIP = 0x102fc8) (xorR64R64Effect 0x102fc8 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[597, 591]
    (.letOp (n := 601) (.out 0x102fcb (xorR64R64Effect 0x102fcb 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[587, 583]
    (.letOp (n := 602) (.exec 0x102fcb (fun s => s.RIP = 0x102fcb) (xorR64R64Effect 0x102fcb 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[587, 583]
    (b_l102bd0_14))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_13 : List UInt8 :=
  [0x49, 0x0F, 0xAF, 0xDD, 0x4C, 0x31, 0xDB, 0x4D, 0x89, 0xD6, 0x4D, 0x0F, 0xAF, 0xF7, 0x4D, 0x89,
    0xE3, 0x4C, 0x0F, 0xAF, 0xD8, 0x4D, 0x31, 0xF3, 0x49, 0x31, 0xDB, 0x4C, 0x89, 0xE3, 0x49, 0x0F,
    0xAF, 0xDF, 0x4D, 0x0F, 0xAF, 0xF9, 0x4C, 0x0F, 0xAF, 0xC8, 0x48, 0x0F, 0xAF, 0xC1, 0x49, 0x0F,
    0xAF, 0xC8, 0x4C, 0x31, 0xC9, 0x4D, 0x0F, 0xAF, 0xC2, 0x4D, 0x0F, 0xAF, 0xD5, 0x4C, 0x31, 0xD3,
    0x48, 0x31, 0xCB, 0x4C, 0x31, 0xF8] ++ bytes_l102bd0_14

theorem code_l102bd0_13 : ∀ x ∈ codeRange 0x102f88 bytes_l102bd0_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2f88 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_14

def b_l102bd0_12 : Block Op Label signature Reg.count 523 :=
  .letOp (n := 523) (.out 0x102f47 (andR64R64Effect 0x102f47 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[275, 371]
    (.letOp (n := 524) (.exec 0x102f47 (fun s => s.RIP = 0x102f47) (andR64R64Effect 0x102f47 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[275, 371]
    (.letOp (n := 525) (.out 0x102f4a (movR64R64Effect 0x102f4a 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 9] []) (.reg (.gpr 7))) #v[507]
    (.letOp (n := 526) (.exec 0x102f4a (fun s => s.RIP = 0x102f4a) (movR64R64Effect 0x102f4a 7 9) (Reg.operands [.gpr 9] [])) #v[507]
    (.letOp (n := 527) (.out 0x102f4d (imulR64R64Effect 0x102f4d 4 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[525, 515]
    (.letOp (n := 528) (.exec 0x102f4d (fun s => s.RIP = 0x102f4d) (imulR64R64Effect 0x102f4d 4 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[525, 515]
    (.letOp (n := 529) (.out 0x102f51 (movR64R64Effect 0x102f51 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[511]
    (.letOp (n := 530) (.exec 0x102f51 (fun s => s.RIP = 0x102f51) (movR64R64Effect 0x102f51 11 1) (Reg.operands [.gpr 1] [])) #v[511]
    (.letOp (n := 531) (.out 0x102f54 (imulR64R64Effect 0x102f54 4 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[529, 523]
    (.letOp (n := 532) (.exec 0x102f54 (fun s => s.RIP = 0x102f54) (imulR64R64Effect 0x102f54 4 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[529, 523]
    (.letOp (n := 533) (.out 0x102f58 (xorR64R64Effect 0x102f58 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[531, 527]
    (.letOp (n := 534) (.exec 0x102f58 (fun s => s.RIP = 0x102f58) (xorR64R64Effect 0x102f58 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[531, 527]
    (.letOp (n := 535) (.out 0x102f5b (movR64R64Effect 0x102f5b 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 12] []) (.reg (.gpr 10))) #v[503]
    (.letOp (n := 536) (.exec 0x102f5b (fun s => s.RIP = 0x102f5b) (movR64R64Effect 0x102f5b 10 12) (Reg.operands [.gpr 12] [])) #v[503]
    (.letOp (n := 537) (.out 0x102f5e (andR64R64Effect 0x102f5e 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[535, 367]
    (.letOp (n := 538) (.exec 0x102f5e (fun s => s.RIP = 0x102f5e) (andR64R64Effect 0x102f5e 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[535, 367]
    (.letOp (n := 539) (.out 0x102f61 (andR64R64Effect 0x102f61 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[503, 371]
    (.letOp (n := 540) (.exec 0x102f61 (fun s => s.RIP = 0x102f61) (andR64R64Effect 0x102f61 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[503, 371]
    (.letOp (n := 541) (.out 0x102f64 (andR64R64Effect 0x102f64 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[519, 488]
    (.letOp (n := 542) (.exec 0x102f64 (fun s => s.RIP = 0x102f64) (andR64R64Effect 0x102f64 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[519, 488]
    (.letOp (n := 543) (.out 0x102f67 (andR64R64Effect 0x102f67 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[521, 367]
    (.letOp (n := 544) (.exec 0x102f67 (fun s => s.RIP = 0x102f67) (andR64R64Effect 0x102f67 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[521, 367]
    (.letOp (n := 545) (.out 0x102f6a (movR64R64Effect 0x102f6a 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 10] []) (.reg (.gpr 3))) #v[537]
    (.letOp (n := 546) (.exec 0x102f6a (fun s => s.RIP = 0x102f6a) (movR64R64Effect 0x102f6a 3 10) (Reg.operands [.gpr 10] [])) #v[537]
    (.letOp (n := 547) (.out 0x102f6d (imulR64R64Effect 0x102f6d 4 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[545, 543]
    (.letOp (n := 548) (.exec 0x102f6d (fun s => s.RIP = 0x102f6d) (imulR64R64Effect 0x102f6d 4 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[545, 543]
    (.letOp (n := 549) (.out 0x102f71 (movR64R64Effect 0x102f71 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[539]
    (.letOp (n := 550) (.exec 0x102f71 (fun s => s.RIP = 0x102f71) (movR64R64Effect 0x102f71 7 12) (Reg.operands [.gpr 12] [])) #v[539]
    (.letOp (n := 551) (.out 0x102f74 (imulR64R64Effect 0x102f74 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[549, 541]
    (.letOp (n := 552) (.exec 0x102f74 (fun s => s.RIP = 0x102f74) (imulR64R64Effect 0x102f74 4 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[549, 541]
    (.letOp (n := 553) (.out 0x102f78 (xorR64R64Effect 0x102f78 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3] []) (.reg (.gpr 7))) #v[551, 547]
    (.letOp (n := 554) (.exec 0x102f78 (fun s => s.RIP = 0x102f78) (xorR64R64Effect 0x102f78 7 3) (Reg.operands [.gpr 7, .gpr 3] [])) #v[551, 547]
    (.letOp (n := 555) (.out 0x102f7b (xorR64R64Effect 0x102f7b 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[553, 533]
    (.letOp (n := 556) (.exec 0x102f7b (fun s => s.RIP = 0x102f7b) (xorR64R64Effect 0x102f7b 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[553, 533]
    (.letOp (n := 557) (.out 0x102f7e (movR64R64Effect 0x102f7e 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[507]
    (.letOp (n := 558) (.exec 0x102f7e (fun s => s.RIP = 0x102f7e) (movR64R64Effect 0x102f7e 11 9) (Reg.operands [.gpr 9] [])) #v[507]
    (.letOp (n := 559) (.out 0x102f81 (imulR64R64Effect 0x102f81 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[557, 541]
    (.letOp (n := 560) (.exec 0x102f81 (fun s => s.RIP = 0x102f81) (imulR64R64Effect 0x102f81 4 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[557, 541]
    (.letOp (n := 561) (.out 0x102f85 (movR64R64Effect 0x102f85 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[511]
    (.letOp (n := 562) (.exec 0x102f85 (fun s => s.RIP = 0x102f85) (movR64R64Effect 0x102f85 3 1) (Reg.operands [.gpr 1] [])) #v[511]
    (b_l102bd0_13))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_12 : List UInt8 :=
  [0x49, 0x21, 0xDF, 0x4C, 0x89, 0xCF, 0x49, 0x0F, 0xAF, 0xFD, 0x49, 0x89, 0xCB, 0x4D, 0x0F, 0xAF,
    0xDF, 0x49, 0x31, 0xFB, 0x4D, 0x89, 0xE2, 0x4D, 0x21, 0xF2, 0x49, 0x21, 0xDC, 0x49, 0x21, 0xD0,
    0x4C, 0x21, 0xF0, 0x4C, 0x89, 0xD3, 0x48, 0x0F, 0xAF, 0xD8, 0x4C, 0x89, 0xE7, 0x49, 0x0F, 0xAF,
    0xF8, 0x48, 0x31, 0xDF, 0x4C, 0x31, 0xDF, 0x4D, 0x89, 0xCB, 0x4D, 0x0F, 0xAF, 0xD8, 0x48, 0x89,
    0xCB] ++ bytes_l102bd0_13

theorem code_l102bd0_12 : ∀ x ∈ codeRange 0x102f47 bytes_l102bd0_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2f47 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_13

def b_l102bd0_11 : Block Op Label signature Reg.count 484 :=
  .letOp (n := 484) (.out 0x102ef9 (movR64Imm64Effect 0x102ef9 0 0x1111111111111111) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 485) (.exec 0x102ef9 (fun s => s.RIP = 0x102ef9) (movR64Imm64Effect 0x102ef9 0 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 486) (.out 0x102f03 (andR64R64Effect 0x102f03 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[430, 484]
    (.letOp (n := 487) (.exec 0x102f03 (fun s => s.RIP = 0x102f03) (andR64R64Effect 0x102f03 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[430, 484]
    (.letOp (n := 488) (.out 0x102f06 (movR64Imm64Effect 0x102f06 2 0x2222222222222222) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 489) (.exec 0x102f06 (fun s => s.RIP = 0x102f06) (movR64Imm64Effect 0x102f06 2 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 490) (.out 0x102f10 (andR64R64Effect 0x102f10 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[452, 488]
    (.letOp (n := 491) (.exec 0x102f10 (fun s => s.RIP = 0x102f10) (andR64R64Effect 0x102f10 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[452, 488]
    (.letOp (n := 492) (.out 0x102f13 (orR64R64Effect 0x102f13 11 7) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 7] []) (.reg (.gpr 11))) #v[490, 486]
    (.letOp (n := 493) (.exec 0x102f13 (fun s => s.RIP = 0x102f13) (orR64R64Effect 0x102f13 11 7) (Reg.operands [.gpr 11, .gpr 7] [])) #v[490, 486]
    (.letOp (n := 494) (.out 0x102f16 (andR64R64Effect 0x102f16 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[474, 367]
    (.letOp (n := 495) (.exec 0x102f16 (fun s => s.RIP = 0x102f16) (andR64R64Effect 0x102f16 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[474, 367]
    (.letOp (n := 496) (.out 0x102f19 (orR64R64Effect 0x102f19 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[494, 492]
    (.letOp (n := 497) (.exec 0x102f19 (fun s => s.RIP = 0x102f19) (orR64R64Effect 0x102f19 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[494, 492]
    (.letOp (n := 498) (.out 0x102f1c (andR64R64Effect 0x102f1c 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[482, 371]
    (.letOp (n := 499) (.exec 0x102f1c (fun s => s.RIP = 0x102f1c) (andR64R64Effect 0x102f1c 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[482, 371]
    (.letOp (n := 500) (.out 0x102f1f (orR64R64Effect 0x102f1f 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[498, 496]
    (.letOp (n := 501) (.exec 0x102f1f (fun s => s.RIP = 0x102f1f) (orR64R64Effect 0x102f1f 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[498, 496]
    (.letOp (n := 502) (.exec 0x102f22 (StorePre 0x102f22 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102f22 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102f22 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[500, 65]
    (.letOp (n := 503) (.out 0x102f27 (movR64M64Effect 0x102f27 12 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 504) (.exec 0x102f27 (LoadPre 0x102f27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102f27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102f27 12 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 505) (.out 0x102f2c (movR64R64Effect 0x102f2c 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[503]
    (.letOp (n := 506) (.exec 0x102f2c (fun s => s.RIP = 0x102f2c) (movR64R64Effect 0x102f2c 9 12) (Reg.operands [.gpr 12] [])) #v[503]
    (.letOp (n := 507) (.out 0x102f2f (andR64R64Effect 0x102f2f 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[505, 484]
    (.letOp (n := 508) (.exec 0x102f2f (fun s => s.RIP = 0x102f2f) (andR64R64Effect 0x102f2f 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[505, 484]
    (.letOp (n := 509) (.out 0x102f32 (movR64R64Effect 0x102f32 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[503]
    (.letOp (n := 510) (.exec 0x102f32 (fun s => s.RIP = 0x102f32) (movR64R64Effect 0x102f32 1 12) (Reg.operands [.gpr 12] [])) #v[503]
    (.letOp (n := 511) (.out 0x102f35 (andR64R64Effect 0x102f35 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[509, 488]
    (.letOp (n := 512) (.exec 0x102f35 (fun s => s.RIP = 0x102f35) (andR64R64Effect 0x102f35 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[509, 488]
    (.letOp (n := 513) (.out 0x102f38 (movR64R64Effect 0x102f38 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[275]
    (.letOp (n := 514) (.exec 0x102f38 (fun s => s.RIP = 0x102f38) (movR64R64Effect 0x102f38 13 15) (Reg.operands [.gpr 15] [])) #v[275]
    (.letOp (n := 515) (.out 0x102f3b (andR64R64Effect 0x102f3b 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[513, 484]
    (.letOp (n := 516) (.exec 0x102f3b (fun s => s.RIP = 0x102f3b) (andR64R64Effect 0x102f3b 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[513, 484]
    (.letOp (n := 517) (.out 0x102f3e (movR64R64Effect 0x102f3e 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[484]
    (.letOp (n := 518) (.exec 0x102f3e (fun s => s.RIP = 0x102f3e) (movR64R64Effect 0x102f3e 5 0) (Reg.operands [.gpr 0] [])) #v[484]
    (.letOp (n := 519) (.out 0x102f41 (movR64R64Effect 0x102f41 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[275]
    (.letOp (n := 520) (.exec 0x102f41 (fun s => s.RIP = 0x102f41) (movR64R64Effect 0x102f41 8 15) (Reg.operands [.gpr 15] [])) #v[275]
    (.letOp (n := 521) (.out 0x102f44 (movR64R64Effect 0x102f44 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[275]
    (.letOp (n := 522) (.exec 0x102f44 (fun s => s.RIP = 0x102f44) (movR64R64Effect 0x102f44 0 15) (Reg.operands [.gpr 15] [])) #v[275]
    (b_l102bd0_12)))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_11 : List UInt8 :=
  [0x48, 0xB8, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x48, 0x21, 0xC7, 0x48, 0xBA, 0x22,
    0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x49, 0x21, 0xD3, 0x49, 0x09, 0xFB, 0x4C, 0x21, 0xF5,
    0x4C, 0x09, 0xDD, 0x48, 0x21, 0xDE, 0x48, 0x09, 0xEE, 0x48, 0x89, 0x74, 0x24, 0x28, 0x4C, 0x8B,
    0x64, 0x24, 0x10, 0x4D, 0x89, 0xE1, 0x49, 0x21, 0xC1, 0x4C, 0x89, 0xE1, 0x48, 0x21, 0xD1, 0x4D,
    0x89, 0xFD, 0x49, 0x21, 0xC5, 0x48, 0x89, 0xC5, 0x4D, 0x89, 0xF8, 0x4C, 0x89, 0xF8] ++ bytes_l102bd0_12

theorem code_l102bd0_11 : ∀ x ∈ codeRange 0x102ef9 bytes_l102bd0_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2ef9 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_12

def b_l102bd0_10 : Block Op Label signature Reg.count 444 :=
  .letOp (n := 444) (.out 0x102eb3 (imulR64R64Effect 0x102eb3 4 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[442, 398]
    (.letOp (n := 445) (.exec 0x102eb3 (fun s => s.RIP = 0x102eb3) (imulR64R64Effect 0x102eb3 4 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[442, 398]
    (.letOp (n := 446) (.out 0x102eb7 (movR64R64Effect 0x102eb7 11 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 12] []) (.reg (.gpr 11))) #v[414]
    (.letOp (n := 447) (.exec 0x102eb7 (fun s => s.RIP = 0x102eb7) (movR64R64Effect 0x102eb7 11 12) (Reg.operands [.gpr 12] [])) #v[414]
    (.letOp (n := 448) (.out 0x102eba (imulR64R64Effect 0x102eba 4 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[446, 418]
    (.letOp (n := 449) (.exec 0x102eba (fun s => s.RIP = 0x102eba) (imulR64R64Effect 0x102eba 4 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[446, 418]
    (.letOp (n := 450) (.out 0x102ebe (xorR64R64Effect 0x102ebe 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[448, 444]
    (.letOp (n := 451) (.exec 0x102ebe (fun s => s.RIP = 0x102ebe) (xorR64R64Effect 0x102ebe 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[448, 444]
    (.letOp (n := 452) (.out 0x102ec1 (xorR64R64Effect 0x102ec1 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[450, 440]
    (.letOp (n := 453) (.exec 0x102ec1 (fun s => s.RIP = 0x102ec1) (xorR64R64Effect 0x102ec1 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[450, 440]
    (.letOp (n := 454) (.out 0x102ec4 (movR64R64Effect 0x102ec4 5 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 12] []) (.reg (.gpr 5))) #v[414]
    (.letOp (n := 455) (.exec 0x102ec4 (fun s => s.RIP = 0x102ec4) (movR64R64Effect 0x102ec4 5 12) (Reg.operands [.gpr 12] [])) #v[414]
    (.letOp (n := 456) (.out 0x102ec7 (imulR64R64Effect 0x102ec7 4 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[454, 398]
    (.letOp (n := 457) (.exec 0x102ec7 (fun s => s.RIP = 0x102ec7) (imulR64R64Effect 0x102ec7 4 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[454, 398]
    (.letOp (n := 458) (.out 0x102ecb (imulR64R64Effect 0x102ecb 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[398, 382]
    (.letOp (n := 459) (.exec 0x102ecb (fun s => s.RIP = 0x102ecb) (imulR64R64Effect 0x102ecb 4 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[398, 382]
    (.letOp (n := 460) (.out 0x102ecf (imulR64R64Effect 0x102ecf 4 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[382, 418]
    (.letOp (n := 461) (.exec 0x102ecf (fun s => s.RIP = 0x102ecf) (imulR64R64Effect 0x102ecf 4 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[382, 418]
    (.letOp (n := 462) (.out 0x102ed3 (imulR64R64Effect 0x102ed3 4 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[418, 386]
    (.letOp (n := 463) (.exec 0x102ed3 (fun s => s.RIP = 0x102ed3) (imulR64R64Effect 0x102ed3 4 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[418, 386]
    (.letOp (n := 464) (.out 0x102ed7 (imulR64R64Effect 0x102ed7 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[386, 416]
    (.letOp (n := 465) (.exec 0x102ed7 (fun s => s.RIP = 0x102ed7) (imulR64R64Effect 0x102ed7 4 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[386, 416]
    (.letOp (n := 466) (.out 0x102edb (xorR64R64Effect 0x102edb 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[464, 460]
    (.letOp (n := 467) (.exec 0x102edb (fun s => s.RIP = 0x102edb) (xorR64R64Effect 0x102edb 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[464, 460]
    (.letOp (n := 468) (.out 0x102ede (imulR64R64Effect 0x102ede 4 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[416, 412]
    (.letOp (n := 469) (.exec 0x102ede (fun s => s.RIP = 0x102ede) (imulR64R64Effect 0x102ede 4 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[416, 412]
    (.letOp (n := 470) (.out 0x102ee2 (imulR64R64Effect 0x102ee2 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[412, 392]
    (.letOp (n := 471) (.exec 0x102ee2 (fun s => s.RIP = 0x102ee2) (imulR64R64Effect 0x102ee2 4 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[412, 392]
    (.letOp (n := 472) (.out 0x102ee6 (xorR64R64Effect 0x102ee6 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[456, 470]
    (.letOp (n := 473) (.exec 0x102ee6 (fun s => s.RIP = 0x102ee6) (xorR64R64Effect 0x102ee6 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[456, 470]
    (.letOp (n := 474) (.out 0x102ee9 (xorR64R64Effect 0x102ee9 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[472, 466]
    (.letOp (n := 475) (.exec 0x102ee9 (fun s => s.RIP = 0x102ee9) (xorR64R64Effect 0x102ee9 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[472, 466]
    (.letOp (n := 476) (.out 0x102eec (xorR64R64Effect 0x102eec 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[462, 458]
    (.letOp (n := 477) (.exec 0x102eec (fun s => s.RIP = 0x102eec) (xorR64R64Effect 0x102eec 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[462, 458]
    (.letOp (n := 478) (.out 0x102eef (imulR64R64Effect 0x102eef 4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[392, 414]
    (.letOp (n := 479) (.exec 0x102eef (fun s => s.RIP = 0x102eef) (imulR64R64Effect 0x102eef 4 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[392, 414]
    (.letOp (n := 480) (.out 0x102ef3 (xorR64R64Effect 0x102ef3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[478, 468]
    (.letOp (n := 481) (.exec 0x102ef3 (fun s => s.RIP = 0x102ef3) (xorR64R64Effect 0x102ef3 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[478, 468]
    (.letOp (n := 482) (.out 0x102ef6 (xorR64R64Effect 0x102ef6 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[480, 476]
    (.letOp (n := 483) (.exec 0x102ef6 (fun s => s.RIP = 0x102ef6) (xorR64R64Effect 0x102ef6 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[480, 476]
    (b_l102bd0_11))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_10 : List UInt8 :=
  [0x4D, 0x0F, 0xAF, 0xD5, 0x4D, 0x89, 0xE3, 0x4C, 0x0F, 0xAF, 0xD8, 0x4D, 0x31, 0xD3, 0x49, 0x31,
    0xEB, 0x4C, 0x89, 0xE5, 0x49, 0x0F, 0xAF, 0xED, 0x4C, 0x0F, 0xAF, 0xEA, 0x48, 0x0F, 0xAF, 0xD0,
    0x48, 0x0F, 0xAF, 0xC1, 0x49, 0x0F, 0xAF, 0xC8, 0x48, 0x31, 0xD1, 0x4D, 0x0F, 0xAF, 0xC1, 0x4C,
    0x0F, 0xAF, 0xCE, 0x4C, 0x31, 0xCD, 0x48, 0x31, 0xCD, 0x4C, 0x31, 0xE8, 0x49, 0x0F, 0xAF, 0xF4,
    0x4C, 0x31, 0xC6, 0x48, 0x31, 0xC6] ++ bytes_l102bd0_11

theorem code_l102bd0_10 : ∀ x ∈ codeRange 0x102eb3 bytes_l102bd0_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2eb3 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_11

def b_l102bd0_9 : Block Op Label signature Reg.count 404 :=
  .letOp (n := 404) (.out 0x102e72 (movR64R64Effect 0x102e72 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[386]
    (.letOp (n := 405) (.exec 0x102e72 (fun s => s.RIP = 0x102e72) (movR64R64Effect 0x102e72 10 1) (Reg.operands [.gpr 1] [])) #v[386]
    (.letOp (n := 406) (.out 0x102e75 (imulR64R64Effect 0x102e75 4 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 13] []) (.reg (.gpr 10))) #v[404, 398]
    (.letOp (n := 407) (.exec 0x102e75 (fun s => s.RIP = 0x102e75) (imulR64R64Effect 0x102e75 4 10 13) (Reg.operands [.gpr 10, .gpr 13] [])) #v[404, 398]
    (.letOp (n := 408) (.out 0x102e79 (xorR64R64Effect 0x102e79 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[406, 402]
    (.letOp (n := 409) (.exec 0x102e79 (fun s => s.RIP = 0x102e79) (xorR64R64Effect 0x102e79 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[406, 402]
    (.letOp (n := 410) (.out 0x102e7c (movR64R64Effect 0x102e7c 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 12] []) (.reg (.gpr 9))) #v[158]
    (.letOp (n := 411) (.exec 0x102e7c (fun s => s.RIP = 0x102e7c) (movR64R64Effect 0x102e7c 9 12) (Reg.operands [.gpr 12] [])) #v[158]
    (.letOp (n := 412) (.out 0x102e7f (andR64R64Effect 0x102e7f 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[410, 367]
    (.letOp (n := 413) (.exec 0x102e7f (fun s => s.RIP = 0x102e7f) (andR64R64Effect 0x102e7f 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[410, 367]
    (.letOp (n := 414) (.out 0x102e82 (andR64R64Effect 0x102e82 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3] []) (.reg (.gpr 12))) #v[158, 371]
    (.letOp (n := 415) (.exec 0x102e82 (fun s => s.RIP = 0x102e82) (andR64R64Effect 0x102e82 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[158, 371]
    (.letOp (n := 416) (.out 0x102e85 (andR64R64Effect 0x102e85 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[394, 388]
    (.letOp (n := 417) (.exec 0x102e85 (fun s => s.RIP = 0x102e85) (andR64R64Effect 0x102e85 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[394, 388]
    (.letOp (n := 418) (.out 0x102e88 (andR64R64Effect 0x102e88 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[396, 367]
    (.letOp (n := 419) (.exec 0x102e88 (fun s => s.RIP = 0x102e88) (andR64R64Effect 0x102e88 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[396, 367]
    (.letOp (n := 420) (.out 0x102e8b (movR64R64Effect 0x102e8b 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[412]
    (.letOp (n := 421) (.exec 0x102e8b (fun s => s.RIP = 0x102e8b) (movR64R64Effect 0x102e8b 11 9) (Reg.operands [.gpr 9] [])) #v[412]
    (.letOp (n := 422) (.out 0x102e8e (imulR64R64Effect 0x102e8e 4 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[420, 418]
    (.letOp (n := 423) (.exec 0x102e8e (fun s => s.RIP = 0x102e8e) (imulR64R64Effect 0x102e8e 4 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[420, 418]
    (.letOp (n := 424) (.out 0x102e92 (movR64R64Effect 0x102e92 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[414]
    (.letOp (n := 425) (.exec 0x102e92 (fun s => s.RIP = 0x102e92) (movR64R64Effect 0x102e92 7 12) (Reg.operands [.gpr 12] [])) #v[414]
    (.letOp (n := 426) (.out 0x102e95 (imulR64R64Effect 0x102e95 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[424, 416]
    (.letOp (n := 427) (.exec 0x102e95 (fun s => s.RIP = 0x102e95) (imulR64R64Effect 0x102e95 4 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[424, 416]
    (.letOp (n := 428) (.out 0x102e99 (xorR64R64Effect 0x102e99 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[426, 422]
    (.letOp (n := 429) (.exec 0x102e99 (fun s => s.RIP = 0x102e99) (xorR64R64Effect 0x102e99 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[426, 422]
    (.letOp (n := 430) (.out 0x102e9c (xorR64R64Effect 0x102e9c 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[428, 408]
    (.letOp (n := 431) (.exec 0x102e9c (fun s => s.RIP = 0x102e9c) (xorR64R64Effect 0x102e9c 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[428, 408]
    (.letOp (n := 432) (.out 0x102e9f (movR64R64Effect 0x102e9f 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[382]
    (.letOp (n := 433) (.exec 0x102e9f (fun s => s.RIP = 0x102e9f) (movR64R64Effect 0x102e9f 10 2) (Reg.operands [.gpr 2] [])) #v[382]
    (.letOp (n := 434) (.out 0x102ea2 (imulR64R64Effect 0x102ea2 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[432, 416]
    (.letOp (n := 435) (.exec 0x102ea2 (fun s => s.RIP = 0x102ea2) (imulR64R64Effect 0x102ea2 4 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[432, 416]
    (.letOp (n := 436) (.out 0x102ea6 (movR64R64Effect 0x102ea6 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[386]
    (.letOp (n := 437) (.exec 0x102ea6 (fun s => s.RIP = 0x102ea6) (movR64R64Effect 0x102ea6 5 1) (Reg.operands [.gpr 1] [])) #v[386]
    (.letOp (n := 438) (.out 0x102ea9 (imulR64R64Effect 0x102ea9 4 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[436, 392]
    (.letOp (n := 439) (.exec 0x102ea9 (fun s => s.RIP = 0x102ea9) (imulR64R64Effect 0x102ea9 4 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[436, 392]
    (.letOp (n := 440) (.out 0x102ead (xorR64R64Effect 0x102ead 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[438, 434]
    (.letOp (n := 441) (.exec 0x102ead (fun s => s.RIP = 0x102ead) (xorR64R64Effect 0x102ead 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[438, 434]
    (.letOp (n := 442) (.out 0x102eb0 (movR64R64Effect 0x102eb0 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[412]
    (.letOp (n := 443) (.exec 0x102eb0 (fun s => s.RIP = 0x102eb0) (movR64R64Effect 0x102eb0 10 9) (Reg.operands [.gpr 9] [])) #v[412]
    (b_l102bd0_10))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_9 : List UInt8 :=
  [0x49, 0x89, 0xCA, 0x4D, 0x0F, 0xAF, 0xD5, 0x49, 0x31, 0xFA, 0x4D, 0x89, 0xE1, 0x4D, 0x21, 0xF1,
    0x49, 0x21, 0xDC, 0x4D, 0x21, 0xD8, 0x4C, 0x21, 0xF0, 0x4D, 0x89, 0xCB, 0x4C, 0x0F, 0xAF, 0xD8,
    0x4C, 0x89, 0xE7, 0x49, 0x0F, 0xAF, 0xF8, 0x4C, 0x31, 0xDF, 0x4C, 0x31, 0xD7, 0x49, 0x89, 0xD2,
    0x4D, 0x0F, 0xAF, 0xD0, 0x48, 0x89, 0xCD, 0x48, 0x0F, 0xAF, 0xEE, 0x4C, 0x31, 0xD5, 0x4D, 0x89,
    0xCA] ++ bytes_l102bd0_10

theorem code_l102bd0_9 : ∀ x ∈ codeRange 0x102e72 bytes_l102bd0_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2e72 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_10

def b_l102bd0_8 : Block Op Label signature Reg.count 366 :=
  .letOp (n := 366) (.exec 0x102e23 (StorePre 0x102e23 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102e23 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102e23 7 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[364, 65]
    (.letOp (n := 367) (.out 0x102e28 (movR64Imm64Effect 0x102e28 14 0x4444444444444444) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 368) (.exec 0x102e28 (fun s => s.RIP = 0x102e28) (movR64Imm64Effect 0x102e28 14 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 369) (.out 0x102e32 (andR64R64Effect 0x102e32 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[346, 367]
    (.letOp (n := 370) (.exec 0x102e32 (fun s => s.RIP = 0x102e32) (andR64R64Effect 0x102e32 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[346, 367]
    (.letOp (n := 371) (.out 0x102e35 (movR64Imm64Effect 0x102e35 3 0x8888888888888888) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 372) (.exec 0x102e35 (fun s => s.RIP = 0x102e35) (movR64Imm64Effect 0x102e35 3 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 373) (.out 0x102e3f (andR64R64Effect 0x102e3f 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[354, 371]
    (.letOp (n := 374) (.exec 0x102e3f (fun s => s.RIP = 0x102e3f) (andR64R64Effect 0x102e3f 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[354, 371]
    (.letOp (n := 375) (.out 0x102e42 (orR64R64Effect 0x102e42 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 5] []) (.reg (.gpr 8))) #v[373, 369]
    (.letOp (n := 376) (.exec 0x102e42 (fun s => s.RIP = 0x102e42) (orR64R64Effect 0x102e42 8 5) (Reg.operands [.gpr 8, .gpr 5] [])) #v[373, 369]
    (.letOp (n := 377) (.exec 0x102e45 (StorePre 0x102e45 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102e45 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102e45 8 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[375, 65]
    (.letOp (n := 378) (.out 0x102e4a (movR64R64Effect 0x102e4a 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[158]
    (.letOp (n := 379) (.exec 0x102e4a (fun s => s.RIP = 0x102e4a) (movR64R64Effect 0x102e4a 2 12) (Reg.operands [.gpr 12] [])) #v[158]
    (.letOp (n := 380) (.out 0x102e4d (movR64R64Effect 0x102e4d 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[356]
    (.letOp (n := 381) (.exec 0x102e4d (fun s => s.RIP = 0x102e4d) (movR64R64Effect 0x102e4d 7 1) (Reg.operands [.gpr 1] [])) #v[356]
    (.letOp (n := 382) (.out 0x102e50 (andR64R64Effect 0x102e50 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[378, 356]
    (.letOp (n := 383) (.exec 0x102e50 (fun s => s.RIP = 0x102e50) (andR64R64Effect 0x102e50 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[378, 356]
    (.letOp (n := 384) (.out 0x102e53 (movR64R64Effect 0x102e53 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[158]
    (.letOp (n := 385) (.exec 0x102e53 (fun s => s.RIP = 0x102e53) (movR64R64Effect 0x102e53 1 12) (Reg.operands [.gpr 12] [])) #v[158]
    (.letOp (n := 386) (.out 0x102e56 (andR64R64Effect 0x102e56 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[384, 360]
    (.letOp (n := 387) (.exec 0x102e56 (fun s => s.RIP = 0x102e56) (andR64R64Effect 0x102e56 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[384, 360]
    (.letOp (n := 388) (.out 0x102e59 (movR64R64Effect 0x102e59 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[360]
    (.letOp (n := 389) (.exec 0x102e59 (fun s => s.RIP = 0x102e59) (movR64R64Effect 0x102e59 11 0) (Reg.operands [.gpr 0] [])) #v[360]
    (.letOp (n := 390) (.out 0x102e5c (movR64R64Effect 0x102e5c 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 391) (.exec 0x102e5c (fun s => s.RIP = 0x102e5c) (movR64R64Effect 0x102e5c 6 13) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 392) (.out 0x102e5f (andR64R64Effect 0x102e5f 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[390, 380]
    (.letOp (n := 393) (.exec 0x102e5f (fun s => s.RIP = 0x102e5f) (andR64R64Effect 0x102e5f 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[390, 380]
    (.letOp (n := 394) (.out 0x102e62 (movR64R64Effect 0x102e62 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[71]
    (.letOp (n := 395) (.exec 0x102e62 (fun s => s.RIP = 0x102e62) (movR64R64Effect 0x102e62 8 13) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 396) (.out 0x102e65 (movR64R64Effect 0x102e65 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 397) (.exec 0x102e65 (fun s => s.RIP = 0x102e65) (movR64R64Effect 0x102e65 0 13) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 398) (.out 0x102e68 (andR64R64Effect 0x102e68 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[71, 371]
    (.letOp (n := 399) (.exec 0x102e68 (fun s => s.RIP = 0x102e68) (andR64R64Effect 0x102e68 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[71, 371]
    (.letOp (n := 400) (.out 0x102e6b (movR64R64Effect 0x102e6b 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[382]
    (.letOp (n := 401) (.exec 0x102e6b (fun s => s.RIP = 0x102e6b) (movR64R64Effect 0x102e6b 7 2) (Reg.operands [.gpr 2] [])) #v[382]
    (.letOp (n := 402) (.out 0x102e6e (imulR64R64Effect 0x102e6e 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[400, 392]
    (.letOp (n := 403) (.exec 0x102e6e (fun s => s.RIP = 0x102e6e) (imulR64R64Effect 0x102e6e 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[400, 392]
    (b_l102bd0_9))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_8 : List UInt8 :=
  [0x48, 0x89, 0x7C, 0x24, 0x38, 0x49, 0xBE, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44, 0x4C,
    0x21, 0xF5, 0x48, 0xBB, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x49, 0x21, 0xD8, 0x49,
    0x09, 0xE8, 0x4C, 0x89, 0x44, 0x24, 0x30, 0x4C, 0x89, 0xE2, 0x48, 0x89, 0xCF, 0x48, 0x21, 0xCA,
    0x4C, 0x89, 0xE1, 0x48, 0x21, 0xC1, 0x49, 0x89, 0xC3, 0x4C, 0x89, 0xEE, 0x48, 0x21, 0xFE, 0x4D,
    0x89, 0xE8, 0x4C, 0x89, 0xE8, 0x49, 0x21, 0xDD, 0x48, 0x89, 0xD7, 0x48, 0x0F, 0xAF, 0xFE] ++ bytes_l102bd0_9

theorem code_l102bd0_8 : ∀ x ∈ codeRange 0x102e23 bytes_l102bd0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2e23 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_9

def b_l102bd0_7 : Block Op Label signature Reg.count 326 :=
  .letOp (n := 326) (.out 0x102dd1 (movR64R64Effect 0x102dd1 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[251]
    (.letOp (n := 327) (.exec 0x102dd1 (fun s => s.RIP = 0x102dd1) (movR64R64Effect 0x102dd1 5 3) (Reg.operands [.gpr 3] [])) #v[251]
    (.letOp (n := 328) (.out 0x102dd4 (imulR64R64Effect 0x102dd4 4 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[326, 289]
    (.letOp (n := 329) (.exec 0x102dd4 (fun s => s.RIP = 0x102dd4) (imulR64R64Effect 0x102dd4 4 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[326, 289]
    (.letOp (n := 330) (.out 0x102dd8 (imulR64R64Effect 0x102dd8 4 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[289, 279]
    (.letOp (n := 331) (.exec 0x102dd8 (fun s => s.RIP = 0x102dd8) (imulR64R64Effect 0x102dd8 4 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[289, 279]
    (.letOp (n := 332) (.out 0x102ddc (imulR64R64Effect 0x102ddc 4 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[279, 261]
    (.letOp (n := 333) (.exec 0x102ddc (fun s => s.RIP = 0x102ddc) (imulR64R64Effect 0x102ddc 4 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[279, 261]
    (.letOp (n := 334) (.out 0x102de0 (imulR64R64Effect 0x102de0 4 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[261, 281]
    (.letOp (n := 335) (.exec 0x102de0 (fun s => s.RIP = 0x102de0) (imulR64R64Effect 0x102de0 4 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[261, 281]
    (.letOp (n := 336) (.out 0x102de4 (imulR64R64Effect 0x102de4 4 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[281, 257]
    (.letOp (n := 337) (.exec 0x102de4 (fun s => s.RIP = 0x102de4) (imulR64R64Effect 0x102de4 4 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[281, 257]
    (.letOp (n := 338) (.out 0x102de8 (xorR64R64Effect 0x102de8 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[336, 332]
    (.letOp (n := 339) (.exec 0x102de8 (fun s => s.RIP = 0x102de8) (xorR64R64Effect 0x102de8 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[336, 332]
    (.letOp (n := 340) (.out 0x102deb (imulR64R64Effect 0x102deb 4 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[257, 243]
    (.letOp (n := 341) (.exec 0x102deb (fun s => s.RIP = 0x102deb) (imulR64R64Effect 0x102deb 4 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[257, 243]
    (.letOp (n := 342) (.out 0x102def (imulR64R64Effect 0x102def 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[243, 285]
    (.letOp (n := 343) (.exec 0x102def (fun s => s.RIP = 0x102def) (imulR64R64Effect 0x102def 4 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[243, 285]
    (.letOp (n := 344) (.out 0x102df3 (xorR64R64Effect 0x102df3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[328, 342]
    (.letOp (n := 345) (.exec 0x102df3 (fun s => s.RIP = 0x102df3) (xorR64R64Effect 0x102df3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[328, 342]
    (.letOp (n := 346) (.out 0x102df6 (xorR64R64Effect 0x102df6 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[344, 338]
    (.letOp (n := 347) (.exec 0x102df6 (fun s => s.RIP = 0x102df6) (xorR64R64Effect 0x102df6 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[344, 338]
    (.letOp (n := 348) (.out 0x102df9 (xorR64R64Effect 0x102df9 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[334, 330]
    (.letOp (n := 349) (.exec 0x102df9 (fun s => s.RIP = 0x102df9) (xorR64R64Effect 0x102df9 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[334, 330]
    (.letOp (n := 350) (.out 0x102dfc (imulR64R64Effect 0x102dfc 4 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[285, 251]
    (.letOp (n := 351) (.exec 0x102dfc (fun s => s.RIP = 0x102dfc) (imulR64R64Effect 0x102dfc 4 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[285, 251]
    (.letOp (n := 352) (.out 0x102e00 (xorR64R64Effect 0x102e00 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[350, 340]
    (.letOp (n := 353) (.exec 0x102e00 (fun s => s.RIP = 0x102e00) (xorR64R64Effect 0x102e00 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[350, 340]
    (.letOp (n := 354) (.out 0x102e03 (xorR64R64Effect 0x102e03 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[352, 348]
    (.letOp (n := 355) (.exec 0x102e03 (fun s => s.RIP = 0x102e03) (xorR64R64Effect 0x102e03 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[352, 348]
    (.letOp (n := 356) (.out 0x102e06 (movR64Imm64Effect 0x102e06 1 0x1111111111111111) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 357) (.exec 0x102e06 (fun s => s.RIP = 0x102e06) (movR64Imm64Effect 0x102e06 1 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 358) (.out 0x102e10 (andR64R64Effect 0x102e10 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[302, 356]
    (.letOp (n := 359) (.exec 0x102e10 (fun s => s.RIP = 0x102e10) (andR64R64Effect 0x102e10 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[302, 356]
    (.letOp (n := 360) (.out 0x102e13 (movR64Imm64Effect 0x102e13 0 0x2222222222222222) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 361) (.exec 0x102e13 (fun s => s.RIP = 0x102e13) (movR64Imm64Effect 0x102e13 0 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 362) (.out 0x102e1d (andR64R64Effect 0x102e1d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[324, 360]
    (.letOp (n := 363) (.exec 0x102e1d (fun s => s.RIP = 0x102e1d) (andR64R64Effect 0x102e1d 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[324, 360]
    (.letOp (n := 364) (.out 0x102e20 (orR64R64Effect 0x102e20 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[362, 358]
    (.letOp (n := 365) (.exec 0x102e20 (fun s => s.RIP = 0x102e20) (orR64R64Effect 0x102e20 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[362, 358]
    (b_l102bd0_8))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_7 : List UInt8 :=
  [0x48, 0x89, 0xDD, 0x49, 0x0F, 0xAF, 0xEE, 0x4C, 0x0F, 0xAF, 0xF0, 0x48, 0x0F, 0xAF, 0xC6, 0x48,
    0x0F, 0xAF, 0xF2, 0x49, 0x0F, 0xAF, 0xD1, 0x48, 0x31, 0xC2, 0x4D, 0x0F, 0xAF, 0xCA, 0x4D, 0x0F,
    0xAF, 0xD0, 0x4C, 0x31, 0xD5, 0x48, 0x31, 0xD5, 0x4C, 0x31, 0xF6, 0x4C, 0x0F, 0xAF, 0xC3, 0x4D,
    0x31, 0xC8, 0x49, 0x31, 0xF0, 0x48, 0xB9, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x49,
    0x21, 0xCB, 0x48, 0xB8, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x48, 0x21, 0xC7, 0x4C,
    0x09, 0xDF] ++ bytes_l102bd0_8

theorem code_l102bd0_7 : ∀ x ∈ codeRange 0x102dd1 bytes_l102bd0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2dd1 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_8

def b_l102bd0_6 : Block Op Label signature Reg.count 287 :=
  .letOp (n := 287) (.out 0x102d86 (movR64Imm64Effect 0x102d86 1 0x8888888888888888) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 288) (.exec 0x102d86 (fun s => s.RIP = 0x102d86) (movR64Imm64Effect 0x102d86 1 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 289) (.out 0x102d90 (andR64R64Effect 0x102d90 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[73, 287]
    (.letOp (n := 290) (.exec 0x102d90 (fun s => s.RIP = 0x102d90) (andR64R64Effect 0x102d90 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[73, 287]
    (.letOp (n := 291) (.out 0x102d93 (movR64R64Effect 0x102d93 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[279]
    (.letOp (n := 292) (.exec 0x102d93 (fun s => s.RIP = 0x102d93) (movR64R64Effect 0x102d93 1 0) (Reg.operands [.gpr 0] [])) #v[279]
    (.letOp (n := 293) (.out 0x102d96 (imulR64R64Effect 0x102d96 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[291, 285]
    (.letOp (n := 294) (.exec 0x102d96 (fun s => s.RIP = 0x102d96) (imulR64R64Effect 0x102d96 4 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[291, 285]
    (.letOp (n := 295) (.exec 0x102d9a (StorePre 0x102d9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x102d9a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d9a 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[293, 65]
    (.letOp (n := 296) (.out 0x102d9f (movR64R64Effect 0x102d9f 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[281]
    (.letOp (n := 297) (.exec 0x102d9f (fun s => s.RIP = 0x102d9f) (movR64R64Effect 0x102d9f 11 2) (Reg.operands [.gpr 2] [])) #v[281]
    (.letOp (n := 298) (.out 0x102da2 (imulR64R64Effect 0x102da2 4 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[296, 289]
    (.letOp (n := 299) (.exec 0x102da2 (fun s => s.RIP = 0x102da2) (imulR64R64Effect 0x102da2 4 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[296, 289]
    (.letOp (n := 300) (.out 0x102da6 (xorR64R64Effect 0x102da6 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[298, 293]
    (.letOp (n := 301) (.exec 0x102da6 (fun s => s.RIP = 0x102da6) (xorR64R64Effect 0x102da6 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[298, 293]
    (.letOp (n := 302) (.out 0x102da9 (xorR64R64Effect 0x102da9 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[300, 271]
    (.letOp (n := 303) (.exec 0x102da9 (fun s => s.RIP = 0x102da9) (xorR64R64Effect 0x102da9 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[300, 271]
    (.letOp (n := 304) (.out 0x102dac (movR64R64Effect 0x102dac 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[279]
    (.letOp (n := 305) (.exec 0x102dac (fun s => s.RIP = 0x102dac) (movR64R64Effect 0x102dac 5 0) (Reg.operands [.gpr 0] [])) #v[279]
    (.letOp (n := 306) (.out 0x102daf (imulR64R64Effect 0x102daf 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[304, 257]
    (.letOp (n := 307) (.exec 0x102daf (fun s => s.RIP = 0x102daf) (imulR64R64Effect 0x102daf 4 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[304, 257]
    (.letOp (n := 308) (.out 0x102db3 (movR64R64Effect 0x102db3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[281]
    (.letOp (n := 309) (.exec 0x102db3 (fun s => s.RIP = 0x102db3) (movR64R64Effect 0x102db3 1 2) (Reg.operands [.gpr 2] [])) #v[281]
    (.letOp (n := 310) (.out 0x102db6 (imulR64R64Effect 0x102db6 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[308, 285]
    (.letOp (n := 311) (.exec 0x102db6 (fun s => s.RIP = 0x102db6) (imulR64R64Effect 0x102db6 4 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[308, 285]
    (.letOp (n := 312) (.out 0x102dba (xorR64R64Effect 0x102dba 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[310, 306]
    (.letOp (n := 313) (.exec 0x102dba (fun s => s.RIP = 0x102dba) (xorR64R64Effect 0x102dba 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[310, 306]
    (.letOp (n := 314) (.out 0x102dbd (movR64R64Effect 0x102dbd 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 10] []) (.reg (.gpr 5))) #v[243]
    (.letOp (n := 315) (.exec 0x102dbd (fun s => s.RIP = 0x102dbd) (movR64R64Effect 0x102dbd 5 10) (Reg.operands [.gpr 10] [])) #v[243]
    (.letOp (n := 316) (.out 0x102dc0 (imulR64R64Effect 0x102dc0 4 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[314, 289]
    (.letOp (n := 317) (.exec 0x102dc0 (fun s => s.RIP = 0x102dc0) (imulR64R64Effect 0x102dc0 4 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[314, 289]
    (.letOp (n := 318) (.out 0x102dc4 (movR64R64Effect 0x102dc4 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[251]
    (.letOp (n := 319) (.exec 0x102dc4 (fun s => s.RIP = 0x102dc4) (movR64R64Effect 0x102dc4 7 3) (Reg.operands [.gpr 3] [])) #v[251]
    (.letOp (n := 320) (.out 0x102dc7 (imulR64R64Effect 0x102dc7 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[318, 261]
    (.letOp (n := 321) (.exec 0x102dc7 (fun s => s.RIP = 0x102dc7) (imulR64R64Effect 0x102dc7 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[318, 261]
    (.letOp (n := 322) (.out 0x102dcb (xorR64R64Effect 0x102dcb 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 5] []) (.reg (.gpr 7))) #v[320, 316]
    (.letOp (n := 323) (.exec 0x102dcb (fun s => s.RIP = 0x102dcb) (xorR64R64Effect 0x102dcb 7 5) (Reg.operands [.gpr 7, .gpr 5] [])) #v[320, 316]
    (.letOp (n := 324) (.out 0x102dce (xorR64R64Effect 0x102dce 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[322, 312]
    (.letOp (n := 325) (.exec 0x102dce (fun s => s.RIP = 0x102dce) (xorR64R64Effect 0x102dce 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[322, 312]
    (b_l102bd0_7)))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_6 : List UInt8 :=
  [0x48, 0xB9, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x49, 0x21, 0xCE, 0x48, 0x89, 0xC1,
    0x49, 0x0F, 0xAF, 0xC8, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x49, 0x89, 0xD3, 0x4D, 0x0F, 0xAF, 0xDE,
    0x49, 0x31, 0xCB, 0x49, 0x31, 0xEB, 0x48, 0x89, 0xC5, 0x49, 0x0F, 0xAF, 0xE9, 0x48, 0x89, 0xD1,
    0x49, 0x0F, 0xAF, 0xC8, 0x48, 0x31, 0xE9, 0x4C, 0x89, 0xD5, 0x49, 0x0F, 0xAF, 0xEE, 0x48, 0x89,
    0xDF, 0x48, 0x0F, 0xAF, 0xFE, 0x48, 0x31, 0xEF, 0x48, 0x31, 0xCF] ++ bytes_l102bd0_7

theorem code_l102bd0_6 : ∀ x ∈ codeRange 0x102d86 bytes_l102bd0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2d86 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_7

def b_l102bd0_5 : Block Op Label signature Reg.count 247 :=
  .letOp (n := 247) (.out 0x102d33 (movR64R64Effect 0x102d33 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[156]
    (.letOp (n := 248) (.exec 0x102d33 (fun s => s.RIP = 0x102d33) (movR64R64Effect 0x102d33 2 3) (Reg.operands [.gpr 3] [])) #v[156]
    (.letOp (n := 249) (.out 0x102d36 (movR64Imm64Effect 0x102d36 1 0x8888888888888888) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 250) (.exec 0x102d36 (fun s => s.RIP = 0x102d36) (movR64Imm64Effect 0x102d36 1 0x8888888888888888) (Reg.operands [] [])) #v[]
    (.letOp (n := 251) (.out 0x102d40 (andR64R64Effect 0x102d40 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[156, 249]
    (.letOp (n := 252) (.exec 0x102d40 (fun s => s.RIP = 0x102d40) (andR64R64Effect 0x102d40 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[156, 249]
    (.letOp (n := 253) (.out 0x102d43 (movR64Imm64Effect 0x102d43 8 0x2222222222222222) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 254) (.exec 0x102d43 (fun s => s.RIP = 0x102d43) (movR64Imm64Effect 0x102d43 8 0x2222222222222222) (Reg.operands [] [])) #v[]
    (.letOp (n := 255) (.out 0x102d4d (movR64R64Effect 0x102d4d 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 14] []) (.reg (.gpr 9))) #v[73]
    (.letOp (n := 256) (.exec 0x102d4d (fun s => s.RIP = 0x102d4d) (movR64R64Effect 0x102d4d 9 14) (Reg.operands [.gpr 14] [])) #v[73]
    (.letOp (n := 257) (.out 0x102d50 (andR64R64Effect 0x102d50 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[255, 253]
    (.letOp (n := 258) (.exec 0x102d50 (fun s => s.RIP = 0x102d50) (andR64R64Effect 0x102d50 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[255, 253]
    (.letOp (n := 259) (.out 0x102d53 (movR64R64Effect 0x102d53 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 260) (.exec 0x102d53 (fun s => s.RIP = 0x102d53) (movR64R64Effect 0x102d53 6 14) (Reg.operands [.gpr 14] [])) #v[73]
    (.letOp (n := 261) (.out 0x102d56 (andR64R64Effect 0x102d56 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[259, 239]
    (.letOp (n := 262) (.exec 0x102d56 (fun s => s.RIP = 0x102d56) (andR64R64Effect 0x102d56 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[259, 239]
    (.letOp (n := 263) (.out 0x102d59 (movR64R64Effect 0x102d59 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[243]
    (.letOp (n := 264) (.exec 0x102d59 (fun s => s.RIP = 0x102d59) (movR64R64Effect 0x102d59 11 10) (Reg.operands [.gpr 10] [])) #v[243]
    (.letOp (n := 265) (.out 0x102d5c (imulR64R64Effect 0x102d5c 4 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[263, 261]
    (.letOp (n := 266) (.exec 0x102d5c (fun s => s.RIP = 0x102d5c) (imulR64R64Effect 0x102d5c 4 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[263, 261]
    (.letOp (n := 267) (.out 0x102d60 (movR64R64Effect 0x102d60 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[251]
    (.letOp (n := 268) (.exec 0x102d60 (fun s => s.RIP = 0x102d60) (movR64R64Effect 0x102d60 5 3) (Reg.operands [.gpr 3] [])) #v[251]
    (.letOp (n := 269) (.out 0x102d63 (imulR64R64Effect 0x102d63 4 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 9] []) (.reg (.gpr 5))) #v[267, 257]
    (.letOp (n := 270) (.exec 0x102d63 (fun s => s.RIP = 0x102d63) (imulR64R64Effect 0x102d63 4 5 9) (Reg.operands [.gpr 5, .gpr 9] [])) #v[267, 257]
    (.letOp (n := 271) (.out 0x102d67 (xorR64R64Effect 0x102d67 5 11) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 11] []) (.reg (.gpr 5))) #v[269, 265]
    (.letOp (n := 272) (.exec 0x102d67 (fun s => s.RIP = 0x102d67) (xorR64R64Effect 0x102d67 5 11) (Reg.operands [.gpr 5, .gpr 11] [])) #v[269, 265]
    (.letOp (n := 273) (.out 0x102d6a (movR64R64Effect 0x102d6a 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 13] []) (.reg (.gpr 15))) #v[71]
    (.letOp (n := 274) (.exec 0x102d6a (fun s => s.RIP = 0x102d6a) (movR64R64Effect 0x102d6a 15 13) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 275) (.out 0x102d6d (xorR64R64Effect 0x102d6d 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[273, 73]
    (.letOp (n := 276) (.exec 0x102d6d (fun s => s.RIP = 0x102d6d) (xorR64R64Effect 0x102d6d 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[273, 73]
    (.letOp (n := 277) (.out 0x102d70 (movR64Imm64Effect 0x102d70 1 0x1111111111111111) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 278) (.exec 0x102d70 (fun s => s.RIP = 0x102d70) (movR64Imm64Effect 0x102d70 1 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 279) (.out 0x102d7a (andR64R64Effect 0x102d7a 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[245, 277]
    (.letOp (n := 280) (.exec 0x102d7a (fun s => s.RIP = 0x102d7a) (andR64R64Effect 0x102d7a 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[245, 277]
    (.letOp (n := 281) (.out 0x102d7d (andR64R64Effect 0x102d7d 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[247, 253]
    (.letOp (n := 282) (.exec 0x102d7d (fun s => s.RIP = 0x102d7d) (andR64R64Effect 0x102d7d 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[247, 253]
    (.letOp (n := 283) (.out 0x102d80 (movR64R64Effect 0x102d80 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 14] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 284) (.exec 0x102d80 (fun s => s.RIP = 0x102d80) (movR64R64Effect 0x102d80 8 14) (Reg.operands [.gpr 14] [])) #v[73]
    (.letOp (n := 285) (.out 0x102d83 (andR64R64Effect 0x102d83 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[283, 277]
    (.letOp (n := 286) (.exec 0x102d83 (fun s => s.RIP = 0x102d83) (andR64R64Effect 0x102d83 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[283, 277]
    (b_l102bd0_6))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_5 : List UInt8 :=
  [0x48, 0x89, 0xDA, 0x48, 0xB9, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x88, 0x48, 0x21, 0xCB,
    0x49, 0xB8, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x22, 0x4D, 0x89, 0xF1, 0x4D, 0x21, 0xC1,
    0x4C, 0x89, 0xF6, 0x48, 0x21, 0xFE, 0x4D, 0x89, 0xD3, 0x4C, 0x0F, 0xAF, 0xDE, 0x48, 0x89, 0xDD,
    0x49, 0x0F, 0xAF, 0xE9, 0x4C, 0x31, 0xDD, 0x4D, 0x89, 0xEF, 0x4D, 0x31, 0xF7, 0x48, 0xB9, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x48, 0x21, 0xC8, 0x4C, 0x21, 0xC2, 0x4D, 0x89, 0xF0,
    0x49, 0x21, 0xC8] ++ bytes_l102bd0_6

theorem code_l102bd0_5 : ∀ x ∈ codeRange 0x102d33 bytes_l102bd0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2d33 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_6

def b_l102bd0_4 : Block Op Label signature Reg.count 209 :=
  .letOp (n := 209) (.out 0x102ce8 (shlR64Effect 0x102ce8 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[207]
    (.letOp (n := 210) (.exec 0x102ce8 (fun s => s.RIP = 0x102ce8) (shlR64Effect 0x102ce8 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[207]
    (.letOp (n := 211) (.out 0x102cec (orR64R64Effect 0x102cec 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[209, 205]
    (.letOp (n := 212) (.exec 0x102cec (fun s => s.RIP = 0x102cec) (orR64R64Effect 0x102cec 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[209, 205]
    (.letOp (n := 213) (.out 0x102cef (movR64R64Effect 0x102cef 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[211]
    (.letOp (n := 214) (.exec 0x102cef (fun s => s.RIP = 0x102cef) (movR64R64Effect 0x102cef 1 0) (Reg.operands [.gpr 0] [])) #v[211]
    (.letOp (n := 215) (.out 0x102cf2 (andR64R64Effect 0x102cf2 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[213, 93]
    (.letOp (n := 216) (.exec 0x102cf2 (fun s => s.RIP = 0x102cf2) (andR64R64Effect 0x102cf2 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[213, 93]
    (.letOp (n := 217) (.out 0x102cf5 (shrR64Effect 0x102cf5 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[211]
    (.letOp (n := 218) (.exec 0x102cf5 (fun s => s.RIP = 0x102cf5) (shrR64Effect 0x102cf5 4 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[211]
    (.letOp (n := 219) (.out 0x102cf9 (andR64R64Effect 0x102cf9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[217, 93]
    (.letOp (n := 220) (.exec 0x102cf9 (fun s => s.RIP = 0x102cf9) (andR64R64Effect 0x102cf9 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[217, 93]
    (.letOp (n := 221) (.out 0x102cfc (leaR64Effect 0x102cfc 0 (.sib 0 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[219, 215]
    (.letOp (n := 222) (.exec 0x102cfc (fun s => s.RIP = 0x102cfc) (leaR64Effect 0x102cfc 0 (.sib 0 (some 1) 2 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[219, 215]
    (.letOp (n := 223) (.out 0x102d00 (movR64R64Effect 0x102d00 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[221]
    (.letOp (n := 224) (.exec 0x102d00 (fun s => s.RIP = 0x102d00) (movR64R64Effect 0x102d00 1 0) (Reg.operands [.gpr 0] [])) #v[221]
    (.letOp (n := 225) (.out 0x102d03 (andR64R64Effect 0x102d03 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[223, 105]
    (.letOp (n := 226) (.exec 0x102d03 (fun s => s.RIP = 0x102d03) (andR64R64Effect 0x102d03 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[223, 105]
    (.letOp (n := 227) (.out 0x102d06 (shrR64Effect 0x102d06 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[221]
    (.letOp (n := 228) (.exec 0x102d06 (fun s => s.RIP = 0x102d06) (shrR64Effect 0x102d06 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[221]
    (.letOp (n := 229) (.out 0x102d09 (andR64R64Effect 0x102d09 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[227, 105]
    (.letOp (n := 230) (.exec 0x102d09 (fun s => s.RIP = 0x102d09) (andR64R64Effect 0x102d09 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[227, 105]
    (.letOp (n := 231) (.out 0x102d0c (leaR64Effect 0x102d0c 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[229, 225]
    (.letOp (n := 232) (.exec 0x102d0c (fun s => s.RIP = 0x102d0c) (leaR64Effect 0x102d0c 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[229, 225]
    (.letOp (n := 233) (.exec 0x102d10 (StorePre 0x102d10 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102d10 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d10 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[231, 65]
    (.letOp (n := 234) (.out 0x102d15 (movR64R64Effect 0x102d15 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[158]
    (.letOp (n := 235) (.exec 0x102d15 (fun s => s.RIP = 0x102d15) (movR64R64Effect 0x102d15 0 12) (Reg.operands [.gpr 12] [])) #v[158]
    (.letOp (n := 236) (.out 0x102d18 (xorR64R64Effect 0x102d18 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[234, 156]
    (.letOp (n := 237) (.exec 0x102d18 (fun s => s.RIP = 0x102d18) (xorR64R64Effect 0x102d18 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[234, 156]
    (.letOp (n := 238) (.exec 0x102d1b (StorePre 0x102d1b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x102d1b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102d1b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[236, 65]
    (.letOp (n := 239) (.out 0x102d20 (movR64Imm64Effect 0x102d20 7 0x4444444444444444) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 240) (.exec 0x102d20 (fun s => s.RIP = 0x102d20) (movR64Imm64Effect 0x102d20 7 0x4444444444444444) (Reg.operands [] [])) #v[]
    (.letOp (n := 241) (.out 0x102d2a (movR64R64Effect 0x102d2a 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[156]
    (.letOp (n := 242) (.exec 0x102d2a (fun s => s.RIP = 0x102d2a) (movR64R64Effect 0x102d2a 10 3) (Reg.operands [.gpr 3] [])) #v[156]
    (.letOp (n := 243) (.out 0x102d2d (andR64R64Effect 0x102d2d 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 7] []) (.reg (.gpr 10))) #v[241, 239]
    (.letOp (n := 244) (.exec 0x102d2d (fun s => s.RIP = 0x102d2d) (andR64R64Effect 0x102d2d 10 7) (Reg.operands [.gpr 10, .gpr 7] [])) #v[241, 239]
    (.letOp (n := 245) (.out 0x102d30 (movR64R64Effect 0x102d30 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[156]
    (.letOp (n := 246) (.exec 0x102d30 (fun s => s.RIP = 0x102d30) (movR64R64Effect 0x102d30 0 3) (Reg.operands [.gpr 3] [])) #v[156]
    (b_l102bd0_5))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_4 : List UInt8 :=
  [0x48, 0xC1, 0xE0, 0x04, 0x48, 0x09, 0xC8, 0x48, 0x89, 0xC1, 0x4C, 0x21, 0xC9, 0x48, 0xC1, 0xE8,
    0x02, 0x4C, 0x21, 0xC8, 0x48, 0x8D, 0x04, 0x88, 0x48, 0x89, 0xC1, 0x48, 0x21, 0xD1, 0x48, 0xD1,
    0xE8, 0x48, 0x21, 0xD0, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xE0,
    0x48, 0x31, 0xD8, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0xBF, 0x44, 0x44, 0x44, 0x44, 0x44, 0x44,
    0x44, 0x44, 0x49, 0x89, 0xDA, 0x49, 0x21, 0xFA, 0x48, 0x89, 0xD8] ++ bytes_l102bd0_5

theorem code_l102bd0_4 : ∀ x ∈ codeRange 0x102ce8 bytes_l102bd0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2ce8 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_5

def b_l102bd0_3 : Block Op Label signature Reg.count 170 :=
  .letOp (n := 170) (.out 0x102ca5 (andR64R64Effect 0x102ca5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[162, 83]
    (.letOp (n := 171) (.exec 0x102ca5 (fun s => s.RIP = 0x102ca5) (andR64R64Effect 0x102ca5 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[162, 83]
    (.letOp (n := 172) (.out 0x102ca8 (shlR64Effect 0x102ca8 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[170]
    (.letOp (n := 173) (.exec 0x102ca8 (fun s => s.RIP = 0x102ca8) (shlR64Effect 0x102ca8 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x102cac (orR64R64Effect 0x102cac 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[172, 168]
    (.letOp (n := 175) (.exec 0x102cac (fun s => s.RIP = 0x102cac) (orR64R64Effect 0x102cac 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[172, 168]
    (.letOp (n := 176) (.out 0x102caf (movR64R64Effect 0x102caf 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[174]
    (.letOp (n := 177) (.exec 0x102caf (fun s => s.RIP = 0x102caf) (movR64R64Effect 0x102caf 1 0) (Reg.operands [.gpr 0] [])) #v[174]
    (.letOp (n := 178) (.out 0x102cb2 (andR64R64Effect 0x102cb2 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[176, 93]
    (.letOp (n := 179) (.exec 0x102cb2 (fun s => s.RIP = 0x102cb2) (andR64R64Effect 0x102cb2 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[176, 93]
    (.letOp (n := 180) (.out 0x102cb5 (shrR64Effect 0x102cb5 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[174]
    (.letOp (n := 181) (.exec 0x102cb5 (fun s => s.RIP = 0x102cb5) (shrR64Effect 0x102cb5 4 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[174]
    (.letOp (n := 182) (.out 0x102cb9 (andR64R64Effect 0x102cb9 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[180, 93]
    (.letOp (n := 183) (.exec 0x102cb9 (fun s => s.RIP = 0x102cb9) (andR64R64Effect 0x102cb9 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[180, 93]
    (.letOp (n := 184) (.out 0x102cbc (leaR64Effect 0x102cbc 0 (.sib 0 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[182, 178]
    (.letOp (n := 185) (.exec 0x102cbc (fun s => s.RIP = 0x102cbc) (leaR64Effect 0x102cbc 0 (.sib 0 (some 1) 2 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[182, 178]
    (.letOp (n := 186) (.out 0x102cc0 (movR64R64Effect 0x102cc0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[184]
    (.letOp (n := 187) (.exec 0x102cc0 (fun s => s.RIP = 0x102cc0) (movR64R64Effect 0x102cc0 1 0) (Reg.operands [.gpr 0] [])) #v[184]
    (.letOp (n := 188) (.out 0x102cc3 (andR64R64Effect 0x102cc3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[186, 105]
    (.letOp (n := 189) (.exec 0x102cc3 (fun s => s.RIP = 0x102cc3) (andR64R64Effect 0x102cc3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[186, 105]
    (.letOp (n := 190) (.out 0x102cc6 (shrR64Effect 0x102cc6 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[184]
    (.letOp (n := 191) (.exec 0x102cc6 (fun s => s.RIP = 0x102cc6) (shrR64Effect 0x102cc6 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[184]
    (.letOp (n := 192) (.out 0x102cc9 (andR64R64Effect 0x102cc9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[190, 105]
    (.letOp (n := 193) (.exec 0x102cc9 (fun s => s.RIP = 0x102cc9) (andR64R64Effect 0x102cc9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[190, 105]
    (.letOp (n := 194) (.out 0x102ccc (leaR64Effect 0x102ccc 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[192, 188]
    (.letOp (n := 195) (.exec 0x102ccc (fun s => s.RIP = 0x102ccc) (leaR64Effect 0x102ccc 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[192, 188]
    (.letOp (n := 196) (.exec 0x102cd0 (StorePre 0x102cd0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102cd0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102cd0 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[194, 65]
    (.letOp (n := 197) (.out 0x102cd5 (movR64R64Effect 0x102cd5 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[158]
    (.letOp (n := 198) (.exec 0x102cd5 (fun s => s.RIP = 0x102cd5) (movR64R64Effect 0x102cd5 0 12) (Reg.operands [.gpr 12] [])) #v[158]
    (.letOp (n := 199) (.out 0x102cd8 (bswapR64Effect 0x102cd8 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[197]
    (.letOp (n := 200) (.exec 0x102cd8 (fun s => s.RIP = 0x102cd8) (bswapR64Effect 0x102cd8 3 0) (Reg.operands [.gpr 0] [])) #v[197]
    (.letOp (n := 201) (.out 0x102cdb (movR64R64Effect 0x102cdb 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[199]
    (.letOp (n := 202) (.exec 0x102cdb (fun s => s.RIP = 0x102cdb) (movR64R64Effect 0x102cdb 1 0) (Reg.operands [.gpr 0] [])) #v[199]
    (.letOp (n := 203) (.out 0x102cde (shrR64Effect 0x102cde 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[201]
    (.letOp (n := 204) (.exec 0x102cde (fun s => s.RIP = 0x102cde) (shrR64Effect 0x102cde 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (.letOp (n := 205) (.out 0x102ce2 (andR64R64Effect 0x102ce2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[203, 83]
    (.letOp (n := 206) (.exec 0x102ce2 (fun s => s.RIP = 0x102ce2) (andR64R64Effect 0x102ce2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[203, 83]
    (.letOp (n := 207) (.out 0x102ce5 (andR64R64Effect 0x102ce5 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[199, 83]
    (.letOp (n := 208) (.exec 0x102ce5 (fun s => s.RIP = 0x102ce5) (andR64R64Effect 0x102ce5 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[199, 83]
    (b_l102bd0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_3 : List UInt8 :=
  [0x48, 0x21, 0xF0, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0x09, 0xC8, 0x48, 0x89, 0xC1, 0x4C, 0x21, 0xC9,
    0x48, 0xC1, 0xE8, 0x02, 0x4C, 0x21, 0xC8, 0x48, 0x8D, 0x04, 0x88, 0x48, 0x89, 0xC1, 0x48, 0x21,
    0xD1, 0x48, 0xD1, 0xE8, 0x48, 0x21, 0xD0, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x44, 0x24, 0x20,
    0x4C, 0x89, 0xE0, 0x48, 0x0F, 0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x21, 0xF1,
    0x48, 0x21, 0xF0] ++ bytes_l102bd0_4

theorem code_l102bd0_3 : ∀ x ∈ codeRange 0x102ca5 bytes_l102bd0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2ca5 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_4

def b_l102bd0_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x102c60 (orR64R64Effect 0x102c60 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[130, 126]
    (.letOp (n := 133) (.exec 0x102c60 (fun s => s.RIP = 0x102c60) (orR64R64Effect 0x102c60 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[130, 126]
    (.letOp (n := 134) (.out 0x102c63 (movR64R64Effect 0x102c63 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[132]
    (.letOp (n := 135) (.exec 0x102c63 (fun s => s.RIP = 0x102c63) (movR64R64Effect 0x102c63 1 0) (Reg.operands [.gpr 0] [])) #v[132]
    (.letOp (n := 136) (.out 0x102c66 (andR64R64Effect 0x102c66 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[134, 93]
    (.letOp (n := 137) (.exec 0x102c66 (fun s => s.RIP = 0x102c66) (andR64R64Effect 0x102c66 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[134, 93]
    (.letOp (n := 138) (.out 0x102c69 (shrR64Effect 0x102c69 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 139) (.exec 0x102c69 (fun s => s.RIP = 0x102c69) (shrR64Effect 0x102c69 4 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 140) (.out 0x102c6d (andR64R64Effect 0x102c6d 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[138, 93]
    (.letOp (n := 141) (.exec 0x102c6d (fun s => s.RIP = 0x102c6d) (andR64R64Effect 0x102c6d 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[138, 93]
    (.letOp (n := 142) (.out 0x102c70 (leaR64Effect 0x102c70 0 (.sib 0 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[140, 136]
    (.letOp (n := 143) (.exec 0x102c70 (fun s => s.RIP = 0x102c70) (leaR64Effect 0x102c70 0 (.sib 0 (some 1) 2 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[140, 136]
    (.letOp (n := 144) (.out 0x102c74 (movR64R64Effect 0x102c74 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[142]
    (.letOp (n := 145) (.exec 0x102c74 (fun s => s.RIP = 0x102c74) (movR64R64Effect 0x102c74 1 0) (Reg.operands [.gpr 0] [])) #v[142]
    (.letOp (n := 146) (.out 0x102c77 (andR64R64Effect 0x102c77 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[144, 105]
    (.letOp (n := 147) (.exec 0x102c77 (fun s => s.RIP = 0x102c77) (andR64R64Effect 0x102c77 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[144, 105]
    (.letOp (n := 148) (.out 0x102c7a (shrR64Effect 0x102c7a 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[142]
    (.letOp (n := 149) (.exec 0x102c7a (fun s => s.RIP = 0x102c7a) (shrR64Effect 0x102c7a 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[142]
    (.letOp (n := 150) (.out 0x102c7d (andR64R64Effect 0x102c7d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[148, 105]
    (.letOp (n := 151) (.exec 0x102c7d (fun s => s.RIP = 0x102c7d) (andR64R64Effect 0x102c7d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[148, 105]
    (.letOp (n := 152) (.out 0x102c80 (leaR64Effect 0x102c80 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[150, 146]
    (.letOp (n := 153) (.exec 0x102c80 (fun s => s.RIP = 0x102c80) (leaR64Effect 0x102c80 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[150, 146]
    (.letOp (n := 154) (.exec 0x102c84 (StorePre 0x102c84 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x102c84 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102c84 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[152, 65]
    (.letOp (n := 155) (.exec 0x102c89 (StorePre 0x102c89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102c89 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102c89 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 156) (.out 0x102c8e (movR64M64Effect 0x102c8e 3 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 157) (.exec 0x102c8e (LoadPre 0x102c8e (fun s => AddrMode.addr (.base 7 .none) s (0x102c8e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x102c8e 3 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 158) (.out 0x102c91 (movR64M64Effect 0x102c91 12 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 159) (.exec 0x102c91 (LoadPre 0x102c91 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x102c91 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x102c91 12 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 160) (.out 0x102c95 (movR64R64Effect 0x102c95 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[156]
    (.letOp (n := 161) (.exec 0x102c95 (fun s => s.RIP = 0x102c95) (movR64R64Effect 0x102c95 0 3) (Reg.operands [.gpr 3] [])) #v[156]
    (.letOp (n := 162) (.out 0x102c98 (bswapR64Effect 0x102c98 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[160]
    (.letOp (n := 163) (.exec 0x102c98 (fun s => s.RIP = 0x102c98) (bswapR64Effect 0x102c98 3 0) (Reg.operands [.gpr 0] [])) #v[160]
    (.letOp (n := 164) (.out 0x102c9b (movR64R64Effect 0x102c9b 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x102c9b (fun s => s.RIP = 0x102c9b) (movR64R64Effect 0x102c9b 1 0) (Reg.operands [.gpr 0] [])) #v[162]
    (.letOp (n := 166) (.out 0x102c9e (shrR64Effect 0x102c9e 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[164]
    (.letOp (n := 167) (.exec 0x102c9e (fun s => s.RIP = 0x102c9e) (shrR64Effect 0x102c9e 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 168) (.out 0x102ca2 (andR64R64Effect 0x102ca2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[166, 83]
    (.letOp (n := 169) (.exec 0x102ca2 (fun s => s.RIP = 0x102ca2) (andR64R64Effect 0x102ca2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[166, 83]
    (b_l102bd0_3))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_2 : List UInt8 :=
  [0x48, 0x09, 0xC8, 0x48, 0x89, 0xC1, 0x4C, 0x21, 0xC9, 0x48, 0xC1, 0xE8, 0x02, 0x4C, 0x21, 0xC8,
    0x48, 0x8D, 0x04, 0x88, 0x48, 0x89, 0xC1, 0x48, 0x21, 0xD1, 0x48, 0xD1, 0xE8, 0x48, 0x21, 0xD0,
    0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0x7C, 0x24, 0x48, 0x48, 0x8B,
    0x1F, 0x4C, 0x8B, 0x67, 0x08, 0x48, 0x89, 0xD8, 0x48, 0x0F, 0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1,
    0xE9, 0x04, 0x48, 0x21, 0xF1] ++ bytes_l102bd0_3

theorem code_l102bd0_2 : ∀ x ∈ codeRange 0x102c60 bytes_l102bd0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2c60 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_3

def b_l102bd0_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x102c10 (movR64Imm64Effect 0x102c10 9 0x3333333333333333) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 94) (.exec 0x102c10 (fun s => s.RIP = 0x102c10) (movR64Imm64Effect 0x102c10 9 0x3333333333333333) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.out 0x102c1a (movR64R64Effect 0x102c1a 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 96) (.exec 0x102c1a (fun s => s.RIP = 0x102c1a) (movR64R64Effect 0x102c1a 1 0) (Reg.operands [.gpr 0] [])) #v[91]
    (.letOp (n := 97) (.out 0x102c1d (andR64R64Effect 0x102c1d 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[95, 93]
    (.letOp (n := 98) (.exec 0x102c1d (fun s => s.RIP = 0x102c1d) (andR64R64Effect 0x102c1d 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[95, 93]
    (.letOp (n := 99) (.out 0x102c20 (shrR64Effect 0x102c20 4 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[91]
    (.letOp (n := 100) (.exec 0x102c20 (fun s => s.RIP = 0x102c20) (shrR64Effect 0x102c20 4 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 101) (.out 0x102c24 (andR64R64Effect 0x102c24 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[99, 93]
    (.letOp (n := 102) (.exec 0x102c24 (fun s => s.RIP = 0x102c24) (andR64R64Effect 0x102c24 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[99, 93]
    (.letOp (n := 103) (.out 0x102c27 (leaR64Effect 0x102c27 0 (.sib 0 (some 1) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[101, 97]
    (.letOp (n := 104) (.exec 0x102c27 (fun s => s.RIP = 0x102c27) (leaR64Effect 0x102c27 0 (.sib 0 (some 1) 2 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[101, 97]
    (.letOp (n := 105) (.out 0x102c2b (movR64Imm64Effect 0x102c2b 2 0x5555555555555555) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 106) (.exec 0x102c2b (fun s => s.RIP = 0x102c2b) (movR64Imm64Effect 0x102c2b 2 0x5555555555555555) (Reg.operands [] [])) #v[]
    (.letOp (n := 107) (.out 0x102c35 (movR64R64Effect 0x102c35 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 108) (.exec 0x102c35 (fun s => s.RIP = 0x102c35) (movR64R64Effect 0x102c35 1 0) (Reg.operands [.gpr 0] [])) #v[103]
    (.letOp (n := 109) (.out 0x102c38 (andR64R64Effect 0x102c38 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[107, 105]
    (.letOp (n := 110) (.exec 0x102c38 (fun s => s.RIP = 0x102c38) (andR64R64Effect 0x102c38 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[107, 105]
    (.letOp (n := 111) (.out 0x102c3b (shrR64Effect 0x102c3b 3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[103]
    (.letOp (n := 112) (.exec 0x102c3b (fun s => s.RIP = 0x102c3b) (shrR64Effect 0x102c3b 3 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 113) (.out 0x102c3e (andR64R64Effect 0x102c3e 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[111, 105]
    (.letOp (n := 114) (.exec 0x102c3e (fun s => s.RIP = 0x102c3e) (andR64R64Effect 0x102c3e 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[111, 105]
    (.letOp (n := 115) (.out 0x102c41 (leaR64Effect 0x102c41 0 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[113, 109]
    (.letOp (n := 116) (.exec 0x102c41 (fun s => s.RIP = 0x102c41) (leaR64Effect 0x102c41 0 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[113, 109]
    (.letOp (n := 117) (.exec 0x102c45 (StorePre 0x102c45 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102c45 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102c45 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[115, 65]
    (.letOp (n := 118) (.out 0x102c49 (movR64R64Effect 0x102c49 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 119) (.exec 0x102c49 (fun s => s.RIP = 0x102c49) (movR64R64Effect 0x102c49 0 13) (Reg.operands [.gpr 13] [])) #v[71]
    (.letOp (n := 120) (.out 0x102c4c (bswapR64Effect 0x102c4c 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[118]
    (.letOp (n := 121) (.exec 0x102c4c (fun s => s.RIP = 0x102c4c) (bswapR64Effect 0x102c4c 3 0) (Reg.operands [.gpr 0] [])) #v[118]
    (.letOp (n := 122) (.out 0x102c4f (movR64R64Effect 0x102c4f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[120]
    (.letOp (n := 123) (.exec 0x102c4f (fun s => s.RIP = 0x102c4f) (movR64R64Effect 0x102c4f 1 0) (Reg.operands [.gpr 0] [])) #v[120]
    (.letOp (n := 124) (.out 0x102c52 (shrR64Effect 0x102c52 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[122]
    (.letOp (n := 125) (.exec 0x102c52 (fun s => s.RIP = 0x102c52) (shrR64Effect 0x102c52 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 126) (.out 0x102c56 (andR64R64Effect 0x102c56 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[124, 83]
    (.letOp (n := 127) (.exec 0x102c56 (fun s => s.RIP = 0x102c56) (andR64R64Effect 0x102c56 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[124, 83]
    (.letOp (n := 128) (.out 0x102c59 (andR64R64Effect 0x102c59 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[120, 83]
    (.letOp (n := 129) (.exec 0x102c59 (fun s => s.RIP = 0x102c59) (andR64R64Effect 0x102c59 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[120, 83]
    (.letOp (n := 130) (.out 0x102c5c (shlR64Effect 0x102c5c 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[128]
    (.letOp (n := 131) (.exec 0x102c5c (fun s => s.RIP = 0x102c5c) (shlR64Effect 0x102c5c 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (b_l102bd0_2)))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0_1 : List UInt8 :=
  [0x49, 0xB9, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x48, 0x89, 0xC1, 0x4C, 0x21, 0xC9,
    0x48, 0xC1, 0xE8, 0x02, 0x4C, 0x21, 0xC8, 0x48, 0x8D, 0x04, 0x88, 0x48, 0xBA, 0x55, 0x55, 0x55,
    0x55, 0x55, 0x55, 0x55, 0x55, 0x48, 0x89, 0xC1, 0x48, 0x21, 0xD1, 0x48, 0xD1, 0xE8, 0x48, 0x21,
    0xD0, 0x48, 0x8D, 0x04, 0x48, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x89, 0xE8, 0x48, 0x0F, 0xC8, 0x48,
    0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0x21, 0xF1, 0x48, 0x21, 0xF0, 0x48, 0xC1, 0xE0, 0x04] ++ bytes_l102bd0_2

theorem code_l102bd0_1 : ∀ x ∈ codeRange 0x102c10 bytes_l102bd0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2c10 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_2

def b_l102bd0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102bd0 (pushR64Effect 0x102bd0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x102bd0 (PushPre 0x102bd0 1) (pushR64Effect 0x102bd0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x102bd1 (pushR64Effect 0x102bd1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x102bd1 (PushPre 0x102bd1 2) (pushR64Effect 0x102bd1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x102bd3 (pushR64Effect 0x102bd3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x102bd3 (PushPre 0x102bd3 2) (pushR64Effect 0x102bd3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x102bd5 (pushR64Effect 0x102bd5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x102bd5 (PushPre 0x102bd5 2) (pushR64Effect 0x102bd5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x102bd7 (pushR64Effect 0x102bd7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x102bd7 (PushPre 0x102bd7 2) (pushR64Effect 0x102bd7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x102bd9 (pushR64Effect 0x102bd9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x102bd9 (PushPre 0x102bd9 1) (pushR64Effect 0x102bd9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x102bda (subR64Imm8Effect 0x102bda 4 0x50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x102bda (fun s => s.RIP = 0x102bda) (subR64Imm8Effect 0x102bda 4 0x50) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x102bde (movR64R64Effect 0x102bde 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 68) (.exec 0x102bde (fun s => s.RIP = 0x102bde) (movR64R64Effect 0x102bde 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x102be1 (movR64R64Effect 0x102be1 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 70) (.exec 0x102be1 (fun s => s.RIP = 0x102be1) (movR64R64Effect 0x102be1 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x102be4 (xorR64M64Effect 0x102be4 13 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 7] []) (.reg (.gpr 13))) #v[67, 7]
    (.letOp (n := 72) (.exec 0x102be4 (LoadPre 0x102be4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x102be4 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x102be4 13 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 13, .gpr 7] [])) #v[67, 7]
    (.letOp (n := 73) (.out 0x102be8 (xorR64M64Effect 0x102be8 14 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[69, 7]
    (.letOp (n := 74) (.exec 0x102be8 (LoadPre 0x102be8 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x102be8 + BitVec.ofNat 64 4)) 8) (xorR64M64Effect 0x102be8 14 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[69, 7]
    (.letOp (n := 75) (.out 0x102bec (movR64R64Effect 0x102bec 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x102bec (fun s => s.RIP = 0x102bec) (movR64R64Effect 0x102bec 0 14) (Reg.operands [.gpr 14] [])) #v[73]
    (.letOp (n := 77) (.out 0x102bef (bswapR64Effect 0x102bef 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 78) (.exec 0x102bef (fun s => s.RIP = 0x102bef) (bswapR64Effect 0x102bef 3 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 79) (.out 0x102bf2 (movR64R64Effect 0x102bf2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 80) (.exec 0x102bf2 (fun s => s.RIP = 0x102bf2) (movR64R64Effect 0x102bf2 1 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 81) (.out 0x102bf5 (shrR64Effect 0x102bf5 4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x102bf5 (fun s => s.RIP = 0x102bf5) (shrR64Effect 0x102bf5 4 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x102bf9 (movR64Imm64Effect 0x102bf9 6 0xf0f0f0f0f0f0f0f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 84) (.exec 0x102bf9 (fun s => s.RIP = 0x102bf9) (movR64Imm64Effect 0x102bf9 6 0xf0f0f0f0f0f0f0f) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x102c03 (andR64R64Effect 0x102c03 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[81, 83]
    (.letOp (n := 86) (.exec 0x102c03 (fun s => s.RIP = 0x102c03) (andR64R64Effect 0x102c03 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[81, 83]
    (.letOp (n := 87) (.out 0x102c06 (andR64R64Effect 0x102c06 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[77, 83]
    (.letOp (n := 88) (.exec 0x102c06 (fun s => s.RIP = 0x102c06) (andR64R64Effect 0x102c06 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[77, 83]
    (.letOp (n := 89) (.out 0x102c09 (shlR64Effect 0x102c09 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[87]
    (.letOp (n := 90) (.exec 0x102c09 (fun s => s.RIP = 0x102c09) (shlR64Effect 0x102c09 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x102c0d (orR64R64Effect 0x102c0d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x102c0d (fun s => s.RIP = 0x102c0d) (orR64R64Effect 0x102c0d 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[89, 85]
    (b_l102bd0_1))))))))))))))))))))))))))))))))))))))))

def bytes_l102bd0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x50, 0x49, 0x89,
    0xD5, 0x49, 0x89, 0xF6, 0x4C, 0x33, 0x6F, 0x18, 0x4C, 0x33, 0x77, 0x10, 0x4C, 0x89, 0xF0, 0x48,
    0x0F, 0xC8, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x04, 0x48, 0xBE, 0x0F, 0x0F, 0x0F, 0x0F, 0x0F,
    0x0F, 0x0F, 0x0F, 0x48, 0x21, 0xF1, 0x48, 0x21, 0xF0, 0x48, 0xC1, 0xE0, 0x04, 0x48, 0x09, 0xC8] ++ bytes_l102bd0_1

theorem code_l102bd0 : ∀ x ∈ codeRange 0x102bd0 bytes_l102bd0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x2bd0 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l102bd0_1

@[cfg_block] def b_l1034a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034a0 (movR64R64Effect 0x1034a0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1034a0 (fun s => s.RIP = 0x1034a0) (movR64R64Effect 0x1034a0 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1034a3 (movR64M64Effect 0x1034a3 1 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x1034a3 (LoadPre 0x1034a3 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1034a3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034a3 1 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1034a7 (movR64M64Effect 0x1034a7 2 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 58) (.exec 0x1034a7 (LoadPre 0x1034a7 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1034a7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034a7 2 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.exec 0x1034ab (StorePre 0x1034ab 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1034ab + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1034ab 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 60) (.exec 0x1034af (StorePre 0x1034af 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1034af + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1034af 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[55, 7]
    (.letOp (n := 61) (.out 0x1034b2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 62) (.out 0x1034b2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 63) (.exec 0x1034b2 (RetPre 0x1034b2) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 55), (2, 57), (3, 3), (4, 62), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64) (some ⟨61, by decide⟩)))))))))))))

def bytes_l1034a0 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x4E, 0x10, 0x48, 0x8B, 0x56, 0x18, 0x48, 0x89, 0x57, 0x08, 0x48,
    0x89, 0x0F, 0xC3]

theorem code_l1034a0 : ∀ x ∈ codeRange 0x1034a0 bytes_l1034a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34a0 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1034c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034c0 (movR64M64Effect 0x1034c0 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1034c0 (LoadPre 0x1034c0 (fun s => AddrMode.addr (.base 6 .none) s (0x1034c0 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034c0 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1034c3 (movR64M64Effect 0x1034c3 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 56) (.exec 0x1034c3 (LoadPre 0x1034c3 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1034c3 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034c3 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1034c7 (movR64R64Effect 0x1034c7 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 58) (.exec 0x1034c7 (fun s => s.RIP = 0x1034c7) (movR64R64Effect 0x1034c7 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.terminate (.br ⟨.l102bd0, RegMap.args [(0, 53), (2, 55), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1034c0 : List UInt8 :=
  [0x48, 0x8B, 0x06, 0x48, 0x8B, 0x56, 0x08, 0x48, 0x89, 0xC6, 0xE9, 0x01, 0xF7, 0xFF, 0xFF]

theorem code_l1034c0 : ∀ x ∈ codeRange 0x1034c0 bytes_l1034c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34c0 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1034d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034d0 (pushR64Effect 0x1034d0 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[4, 14]
    (.letOp (n := 54) (.exec 0x1034d0 (PushPre 0x1034d0 2) (pushR64Effect 0x1034d0 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[4, 14]
    (.letOp (n := 55) (.out 0x1034d2 (pushR64Effect 0x1034d2 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[53, 3]
    (.letOp (n := 56) (.exec 0x1034d2 (PushPre 0x1034d2 1) (pushR64Effect 0x1034d2 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 57) (.out 0x1034d3 (pushR64Effect 0x1034d3 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[55, 0]
    (.letOp (n := 58) (.exec 0x1034d3 (PushPre 0x1034d3 1) (pushR64Effect 0x1034d3 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.out 0x1034d4 (movR64R64Effect 0x1034d4 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 60) (.exec 0x1034d4 (fun s => s.RIP = 0x1034d4) (movR64R64Effect 0x1034d4 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1034d7 (movR64R64Effect 0x1034d7 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[7]
    (.letOp (n := 62) (.exec 0x1034d7 (fun s => s.RIP = 0x1034d7) (movR64R64Effect 0x1034d7 14 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x1034da (movR64M64Effect 0x1034da 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 64) (.exec 0x1034da (LoadPre 0x1034da (fun s => AddrMode.addr (.base 6 .none) s (0x1034da + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1034da 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x1034dd (movR64M64Effect 0x1034dd 2 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 66) (.exec 0x1034dd (LoadPre 0x1034dd (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1034dd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034dd 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[59]
    (.letOp (n := 67) (.out 0x1034e1 (callEffect (fun _ => 0x102bd0) 0x1034e6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 68) (.exec 0x1034e1 (PushPre 0x1034e1 5) (callEffect (fun _ => 0x102bd0) 0x1034e6) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 69) (.const ⟨64, 0x1034e6⟩) #v[]
    (.terminate (.call ⟨.l102bd0, RegMap.args [(0, 0), (2, 65), (3, 59), (4, 67), (5, 5), (6, 63), (7, 7), (12, 12), (13, 13), (14, 61), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1034e6, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l1034d0 : List UInt8 :=
  [0x41, 0x56, 0x53, 0x50, 0x48, 0x89, 0xF3, 0x49, 0x89, 0xFE, 0x48, 0x8B, 0x36, 0x48, 0x8B, 0x53,
    0x08, 0xE8, 0xEA, 0xF6, 0xFF, 0xFF]

theorem code_l1034d0 : ∀ x ∈ codeRange 0x1034d0 bytes_l1034d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34d0 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1034e6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034e6 (movR64M64Effect 0x1034e6 6 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x1034e6 (LoadPre 0x1034e6 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1034e6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034e6 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1034ea (movR64M64Effect 0x1034ea 2 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 56) (.exec 0x1034ea (LoadPre 0x1034ea (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1034ea + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034ea 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x1034ee (movR64R64Effect 0x1034ee 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 58) (.exec 0x1034ee (fun s => s.RIP = 0x1034ee) (movR64R64Effect 0x1034ee 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1034f1 (callEffect (fun _ => 0x102bd0) 0x1034f6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1034f1 (PushPre 0x1034f1 5) (callEffect (fun _ => 0x102bd0) 0x1034f6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1034f6⟩) #v[]
    (.terminate (.call ⟨.l102bd0, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1034f6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1034e6 : List UInt8 :=
  [0x48, 0x8B, 0x73, 0x10, 0x48, 0x8B, 0x53, 0x18, 0x4C, 0x89, 0xF7, 0xE8, 0xDA, 0xF6, 0xFF, 0xFF]

theorem code_l1034e6 : ∀ x ∈ codeRange 0x1034e6 bytes_l1034e6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34e6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1034f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1034f6 (movR64M64Effect 0x1034f6 6 (.base 3 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x1034f6 (LoadPre 0x1034f6 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1034f6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034f6 6 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1034fa (movR64M64Effect 0x1034fa 2 (.base 3 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 56) (.exec 0x1034fa (LoadPre 0x1034fa (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1034fa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1034fa 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x1034fe (movR64R64Effect 0x1034fe 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 58) (.exec 0x1034fe (fun s => s.RIP = 0x1034fe) (movR64R64Effect 0x1034fe 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x103501 (callEffect (fun _ => 0x102bd0) 0x103506) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x103501 (PushPre 0x103501 5) (callEffect (fun _ => 0x102bd0) 0x103506) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x103506⟩) #v[]
    (.terminate (.call ⟨.l102bd0, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l103506, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1034f6 : List UInt8 :=
  [0x48, 0x8B, 0x73, 0x20, 0x48, 0x8B, 0x53, 0x28, 0x4C, 0x89, 0xF7, 0xE8, 0xCA, 0xF6, 0xFF, 0xFF]

theorem code_l1034f6 : ∀ x ∈ codeRange 0x1034f6 bytes_l1034f6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x34f6 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103506 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103506 (movR64M64Effect 0x103506 6 (.base 3 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 54) (.exec 0x103506 (LoadPre 0x103506 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x103506 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103506 6 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10350a (movR64M64Effect 0x10350a 2 (.base 3 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 56) (.exec 0x10350a (LoadPre 0x10350a (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x10350a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10350a 2 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x10350e (movR64R64Effect 0x10350e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 58) (.exec 0x10350e (fun s => s.RIP = 0x10350e) (movR64R64Effect 0x10350e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x103511 (addR64Imm8Effect 0x103511 4 0x8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x103511 (fun s => s.RIP = 0x103511) (addR64Imm8Effect 0x103511 4 0x8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x103515 (popR64Effect 0x103515 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[59]
    (.letOp (n := 62) (.out 0x103515 (popR64Effect 0x103515 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x103515 (PopPre 0x103515) (popR64Effect 0x103515 1 3) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x103516 (popR64Effect 0x103516 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x103516 (popR64Effect 0x103516 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x103516 (PopPre 0x103516) (popR64Effect 0x103516 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.terminate (.br ⟨.l102bd0, RegMap.args [(2, 55), (3, 61), (4, 65), (5, 5), (6, 53), (7, 57), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l103506 : List UInt8 :=
  [0x48, 0x8B, 0x73, 0x30, 0x48, 0x8B, 0x53, 0x38, 0x4C, 0x89, 0xF7, 0x48, 0x83, 0xC4, 0x08, 0x5B,
    0x41, 0x5E, 0xE9, 0xB3, 0xF6, 0xFF, 0xFF]

theorem code_l103506 : ∀ x ∈ codeRange 0x103506 bytes_l103506, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3506 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103520_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x10355a (testR32R32Effect 0x10355a 2 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 93) (.exec 0x10355a (fun s => s.RIP = 0x10355a) (testR32R32Effect 0x10355a 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 94) (.out 0x10355c (movR32Imm32Effect 0x10355c 5 6 0x2d) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 95) (.exec 0x10355c (fun s => s.RIP = 0x10355c) (movR32Imm32Effect 0x10355c 5 6 0x2d) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.out 0x103561 (atFlags (condHolds 5) (cmovR32R32Effect 0x103561 3 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[94, 88, 92]
    (.letOp (n := 97) (.exec 0x103561 (fun s => s.RIP = 0x103561) (atFlags (condHolds 5) (cmovR32R32Effect 0x103561 3 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[94, 88, 92]
    (.letOp (n := 98) (.exec 0x103564 (StorePre 0x103564 3 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x103564 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x103564 6 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[96, 55]
    (.letOp (n := 99) (.out 0x103567 (movR32Imm32Effect 0x103567 6 9 0x1) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 100) (.exec 0x103567 (fun s => s.RIP = 0x103567) (movR32Imm32Effect 0x103567 6 9 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x10356d (atFlags (condHolds 5) (cmovR64R64Effect 0x10356d 4 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[99, 90, 92]
    (.letOp (n := 102) (.exec 0x10356d (fun s => s.RIP = 0x10356d) (atFlags (condHolds 5) (cmovR64R64Effect 0x10356d 4 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[99, 90, 92]
    (.letOp (n := 103) (.out 0x103571 (addR64R64Effect 0x103571 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[101, 69]
    (.letOp (n := 104) (.exec 0x103571 (fun s => s.RIP = 0x103571) (addR64R64Effect 0x103571 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[101, 69]
    (.letOp (n := 105) (.out 0x103574 (testR32Imm32Effect 0x103574 7 15 0x800000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[76]
    (.letOp (n := 106) (.exec 0x103574 (fun s => s.RIP = 0x103574) (testR32Imm32Effect 0x103574 7 15 0x800000) (Reg.operands [.gpr 15] [])) #v[76]
    (.letOp (n := 107) (.exec 0x10357b (StorePre 0x10357b 4 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x10357b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10357b 1 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 1, .gpr 5] [])) #v[1, 55]
    (.letOp (n := 108) (.pure (condOp 5)) #v[105]
    (.terminate (.condBr (Fin.last 108) ⟨.l1035dc, RegMap.args [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)] 109⟩ ⟨.l103581, RegMap.args [(0, 90), (1, 1), (2, 88), (3, 3), (4, 67), (5, 55), (6, 96), (7, 7), (8, 8), (9, 103), (11, 11), (12, 74), (13, 69), (14, 72), (15, 76), (19, 105), (22, 22), (39, 39), (50, 50), (51, 51)] 109⟩))))))))))))))))))

def bytes_l103520_1 : List UInt8 :=
  [0x85, 0xF6, 0xBE, 0x2D, 0x00, 0x00, 0x00, 0x0F, 0x45, 0xF2, 0x89, 0x75, 0xD4, 0x41, 0xB9, 0x01,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0x45, 0xC8, 0x4D, 0x01, 0xE9, 0x41, 0xF7, 0xC7, 0x00, 0x00, 0x80,
    0x00, 0x48, 0x89, 0x4D, 0xB8, 0x75, 0x5B]

theorem code_l103520_1 : ∀ x ∈ codeRange 0x10355a bytes_l103520_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x355a 39 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103520 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103520 (pushR64Effect 0x103520 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103520 (PushPre 0x103520 1) (pushR64Effect 0x103520 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103521 (movR64R64Effect 0x103521 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x103521 (fun s => s.RIP = 0x103521) (movR64R64Effect 0x103521 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x103524 (pushR64Effect 0x103524 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 58) (.exec 0x103524 (PushPre 0x103524 2) (pushR64Effect 0x103524 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 59) (.out 0x103526 (pushR64Effect 0x103526 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x103526 (PushPre 0x103526 2) (pushR64Effect 0x103526 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x103528 (pushR64Effect 0x103528 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[59, 13]
    (.letOp (n := 62) (.exec 0x103528 (PushPre 0x103528 2) (pushR64Effect 0x103528 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[59, 13]
    (.letOp (n := 63) (.out 0x10352a (pushR64Effect 0x10352a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[61, 12]
    (.letOp (n := 64) (.exec 0x10352a (PushPre 0x10352a 2) (pushR64Effect 0x10352a 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[61, 12]
    (.letOp (n := 65) (.out 0x10352c (pushR64Effect 0x10352c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[63, 3]
    (.letOp (n := 66) (.exec 0x10352c (PushPre 0x10352c 1) (pushR64Effect 0x10352c 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 67) (.out 0x10352d (subR64Imm8Effect 0x10352d 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x10352d (fun s => s.RIP = 0x10352d) (subR64Imm8Effect 0x10352d 4 0x48) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.out 0x103531 (movR64R64Effect 0x103531 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[9]
    (.letOp (n := 70) (.exec 0x103531 (fun s => s.RIP = 0x103531) (movR64R64Effect 0x103531 13 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 71) (.exec 0x103534 (StorePre 0x103534 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x103534 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103534 8 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 8, .gpr 5] [])) #v[8, 55]
    (.letOp (n := 72) (.out 0x103538 (movR64R64Effect 0x103538 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 73) (.exec 0x103538 (fun s => s.RIP = 0x103538) (movR64R64Effect 0x103538 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 74) (.out 0x10353b (movR64R64Effect 0x10353b 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 7] []) (.reg (.gpr 12))) #v[7]
    (.letOp (n := 75) (.exec 0x10353b (fun s => s.RIP = 0x10353b) (movR64R64Effect 0x10353b 12 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 76) (.out 0x10353e (movR32M32Effect 0x10353e 15 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[7]
    (.letOp (n := 77) (.exec 0x10353e (LoadPre 0x10353e (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10353e + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x10353e 15 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 78) (.out 0x103542 (movR32R32Effect 0x103542 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[76]
    (.letOp (n := 79) (.exec 0x103542 (fun s => s.RIP = 0x103542) (movR32R32Effect 0x103542 3 0 15) (Reg.operands [.gpr 15] [])) #v[76]
    (.letOp (n := 80) (.out 0x103545 (andEaxImm32Effect 0x103545 0x200000) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[78]
    (.letOp (n := 81) (.exec 0x103545 (fun s => s.RIP = 0x103545) (andEaxImm32Effect 0x103545 0x200000) (Reg.operands [.gpr 0] [])) #v[78]
    (.letOp (n := 82) (.out 0x10354a (cmpR32Imm8Effect 0x10354a 3 0 0x1) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[80]
    (.letOp (n := 83) (.exec 0x10354a (fun s => s.RIP = 0x10354a) (cmpR32Imm8Effect 0x10354a 3 0 0x1) (Reg.operands [.gpr 0] [])) #v[80]
    (.letOp (n := 84) (.out 0x10354d (movR32Imm32Effect 0x10354d 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 85) (.exec 0x10354d (fun s => s.RIP = 0x10354d) (movR32Imm32Effect 0x10354d 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 86) (.out 0x103552 (atFlags StatusFlags.CF (sbbR32R32Effect 0x103552 2 2 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[84, 84, 82]
    (.letOp (n := 87) (.exec 0x103552 (fun s => s.RIP = 0x103552) (atFlags StatusFlags.CF (sbbR32R32Effect 0x103552 2 2 2)) (Reg.operands [.gpr 2, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 84, 82]
    (.letOp (n := 88) (.out 0x103554 (orR32Imm8Effect 0x103554 3 2 0x2b) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[86]
    (.letOp (n := 89) (.exec 0x103554 (fun s => s.RIP = 0x103554) (orR32Imm8Effect 0x103554 3 2 0x2b) (Reg.operands [.gpr 2] [])) #v[86]
    (.letOp (n := 90) (.out 0x103557 (shrR32Effect 0x103557 3 0 21) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[80]
    (.letOp (n := 91) (.exec 0x103557 (fun s => s.RIP = 0x103557) (shrR32Effect 0x103557 3 0 21) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (b_l103520_1)))))))))))))))))))))))))))))))))))))))

def bytes_l103520 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC,
    0x48, 0x4D, 0x89, 0xCD, 0x4C, 0x89, 0x45, 0xC0, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xFC, 0x44, 0x8B,
    0x7F, 0x10, 0x44, 0x89, 0xF8, 0x25, 0x00, 0x00, 0x20, 0x00, 0x83, 0xF8, 0x01, 0xBA, 0x00, 0x00,
    0x00, 0x00, 0x19, 0xD2, 0x83, 0xCA, 0x2B, 0xC1, 0xE8, 0x15] ++ bytes_l103520_1

theorem code_l103520 : ∀ x ∈ codeRange 0x103520 bytes_l103520, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x3520 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l103520_1

@[cfg_block] def b_l103581 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103581 (xorR32R32Effect 0x103581 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[14, 14]
    (.letOp (n := 54) (.exec 0x103581 (fun s => s.RIP = 0x103581) (xorR32R32Effect 0x103581 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 55) (.out 0x103584 (movzxR32M16Effect 0x103584 6 3 (.sib 12 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 56) (.exec 0x103584 (LoadPre 0x103584 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x103584 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x103584 6 3 (.sib 12 none 0 (.d8 0x14))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10358a (cmpR64R64Effect 0x10358a 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[9, 55]
    (.letOp (n := 58) (.exec 0x10358a (fun s => s.RIP = 0x10358a) (cmpR64R64Effect 0x10358a 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[9, 55]
    (.letOp (n := 59) (.pure (condOp 2)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103697, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l103593, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 53), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103581 : List UInt8 :=
  [0x45, 0x31, 0xF6, 0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14, 0x49, 0x39, 0xD9, 0x0F, 0x82, 0x04, 0x01,
    0x00, 0x00]

theorem code_l103581 : ∀ x ∈ codeRange 0x103581 bytes_l103581, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3581 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103593 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103593 (movR64M64Effect 0x103593 15 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 54) (.exec 0x103593 (LoadPre 0x103593 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x103593 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103593 15 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x103597 (movR64M64Effect 0x103597 12 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 56) (.exec 0x103597 (LoadPre 0x103597 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x103597 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x103597 12 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10359c (movR64R64Effect 0x10359c 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10359c (fun s => s.RIP = 0x10359c) (movR64R64Effect 0x10359c 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x10359f (movR64R64Effect 0x10359f 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 60) (.exec 0x10359f (fun s => s.RIP = 0x10359f) (movR64R64Effect 0x10359f 6 12) (Reg.operands [.gpr 12] [])) #v[55]
    (.letOp (n := 61) (.out 0x1035a2 (movR32M32LowEffect 0x1035a2 2 (.base 5 (.d8 0xd4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 62) (.exec 0x1035a2 (LoadPre 0x1035a2 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x1035a2 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1035a2 2 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x1035a5 (movR64R64Effect 0x1035a5 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 64) (.exec 0x1035a5 (fun s => s.RIP = 0x1035a5) (movR64R64Effect 0x1035a5 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x1035a8 (movR64M64Effect 0x1035a8 8 (.base 5 (.d8 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 66) (.exec 0x1035a8 (LoadPre 0x1035a8 (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1035a8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1035a8 8 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 67) (.out 0x1035ac (callEffect (fun _ => 0x103d40) 0x1035b1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x1035ac (PushPre 0x1035ac 5) (callEffect (fun _ => 0x103d40) 0x1035b1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x1035b1⟩) #v[]
    (.terminate (.call ⟨.l103d40, RegMap.args [(0, 0), (1, 63), (2, 61), (3, 3), (4, 67), (5, 5), (6, 59), (7, 57), (8, 65), (9, 9), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l1035b1, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l103593 : List UInt8 :=
  [0x4D, 0x8B, 0x3C, 0x24, 0x4D, 0x8B, 0x64, 0x24, 0x08, 0x4C, 0x89, 0xFF, 0x4C, 0x89, 0xE6, 0x8B,
    0x55, 0xD4, 0x4C, 0x89, 0xF1, 0x4C, 0x8B, 0x45, 0xB8, 0xE8, 0x8F, 0x07, 0x00, 0x00]

theorem code_l103593 : ∀ x ∈ codeRange 0x103593 bytes_l103593, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3593 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035b1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035b1 (movR32R32Effect 0x1035b1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x1035b1 (fun s => s.RIP = 0x1035b1) (movR32R32Effect 0x1035b1 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1035b3 (movR8Imm8Effect 0x1035b3 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x1035b3 (fun s => s.RIP = 0x1035b3) (movR8Imm8Effect 0x1035b3 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x1035b5 (testR8R8Effect 0x1035b5 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x1035b5 (fun s => s.RIP = 0x1035b5) (testR8R8Effect 0x1035b5 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103828, RegMap.args [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1035bd, RegMap.args [(0, 55), (1, 53), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1035b1 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x0F, 0x85, 0x6B, 0x02, 0x00, 0x00]

theorem code_l1035b1 : ∀ x ∈ codeRange 0x1035b1 bytes_l1035b1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35b1 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035bd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1035bd (LoadPre 0x1035bd (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x1035bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1035bd 0 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 54) (.exec 0x1035c2 (fun s => s.RIP = 0x1035c2) (movR64R64Effect 0x1035c2 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x1035c5 (LoadPre 0x1035c5 (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x1035c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1035c5 6 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 56) (.exec 0x1035c9 (fun s => s.RIP = 0x1035c9) (movR64R64Effect 0x1035c9 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x1035cc (addR64Imm8Effect 0x1035cc 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1035cc (fun s => s.RIP = 0x1035cc) (addR64Imm8Effect 0x1035cc 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1035d0 (popR64Effect 0x1035d0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 60) (.exec 0x1035d0 (PopPre 0x1035d0) (popR64Effect 0x1035d0 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 61) (.out 0x1035d1 (popR64Effect 0x1035d1 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x1035d1 (PopPre 0x1035d1) (popR64Effect 0x1035d1 2 12) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x1035d3 (popR64Effect 0x1035d3 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x1035d3 (PopPre 0x1035d3) (popR64Effect 0x1035d3 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x1035d5 (popR64Effect 0x1035d5 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1035d5 (PopPre 0x1035d5) (popR64Effect 0x1035d5 2 14) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1035d7 (popR64Effect 0x1035d7 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 68) (.exec 0x1035d7 (PopPre 0x1035d7) (popR64Effect 0x1035d7 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 69) (.exec 0x1035d9 (PopPre 0x1035d9) (popR64Effect 0x1035d9 1 5) (Reg.operands [.gpr 4] [])) #v[67]
    (cutBlock 0x1035da)))))))))))))))))

def bytes_l1035bd : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x18, 0x4C, 0x89, 0xFF, 0x48, 0x8B, 0x75, 0xC0, 0x4C, 0x89, 0xEA, 0x48,
    0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xFF, 0xE0]

theorem code_l1035bd : ∀ x ∈ codeRange 0x1035bd bytes_l1035bd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35bd 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035dc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035dc (cmpR64Imm8Effect 0x1035dc 1 0x20) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 54) (.exec 0x1035dc (fun s => s.RIP = 0x1035dc) (cmpR64Imm8Effect 0x1035dc 1 0x20) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.pure (condOp 3)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1035fa, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1035e2, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1035dc : List UInt8 :=
  [0x48, 0x83, 0xF9, 0x20, 0x73, 0x18]

theorem code_l1035dc : ∀ x ∈ codeRange 0x1035dc bytes_l1035dc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35dc 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035e2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035e2 (testR64R64Effect 0x1035e2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[1, 1]
    (.letOp (n := 54) (.exec 0x1035e2 (fun s => s.RIP = 0x1035e2) (testR64R64Effect 0x1035e2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10360e, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1035e7, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1035e2 : List UInt8 :=
  [0x48, 0x85, 0xC9, 0x74, 0x27]

theorem code_l1035e2 : ∀ x ∈ codeRange 0x1035e2 bytes_l1035e2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35e2 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035e7 (movR32R32Effect 0x1035e7 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[1]
    (.letOp (n := 54) (.exec 0x1035e7 (fun s => s.RIP = 0x1035e7) (movR32R32Effect 0x1035e7 3 10 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1035ea (andR32Imm8Effect 0x1035ea 4 10 0x3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 56) (.exec 0x1035ea (fun s => s.RIP = 0x1035ea) (andR32Imm8Effect 0x1035ea 4 10 0x3) (Reg.operands [.gpr 10] [])) #v[53]
    (.letOp (n := 57) (.out 0x1035ee (cmpR64Imm8Effect 0x1035ee 1 0x4) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[1]
    (.letOp (n := 58) (.exec 0x1035ee (fun s => s.RIP = 0x1035ee) (cmpR64Imm8Effect 0x1035ee 1 0x4) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103612, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1035f4, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 55), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1035e7 : List UInt8 :=
  [0x41, 0x89, 0xCA, 0x41, 0x83, 0xE2, 0x03, 0x48, 0x83, 0xF9, 0x04, 0x73, 0x1E]

theorem code_l1035e7 : ∀ x ∈ codeRange 0x1035e7 bytes_l1035e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35e7 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035f4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035f4 (xorR32R32Effect 0x1035f4 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1035f4 (fun s => s.RIP = 0x1035f4) (xorR32R32Effect 0x1035f4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x1035f6 (xorR32R32Effect 0x1035f6 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x1035f6 (fun s => s.RIP = 0x1035f6) (xorR32R32Effect 0x1035f6 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103668, RegMap.args [(0, 55), (2, 53), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1035f4 : List UInt8 :=
  [0x31, 0xD2, 0x31, 0xC0, 0xEB, 0x6E]

theorem code_l1035f4 : ∀ x ∈ codeRange 0x1035f4 bytes_l1035f4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35f4 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1035fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1035fa (movR64R64Effect 0x1035fa 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x1035fa (fun s => s.RIP = 0x1035fa) (movR64R64Effect 0x1035fa 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x1035fd (movR64R64Effect 0x1035fd 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 56) (.exec 0x1035fd (fun s => s.RIP = 0x1035fd) (movR64R64Effect 0x1035fd 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x103600 (movR64R64Effect 0x103600 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[9]
    (.letOp (n := 58) (.exec 0x103600 (fun s => s.RIP = 0x103600) (movR64R64Effect 0x103600 3 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 59) (.out 0x103603 (callEffect (callMemPtr 0x103603 (.rip 0xfdc17)) (0x103603 + BitVec.ofNat 64 (callMemLen (.rip 0xfdc17)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x103603 (GoesTo (CallMemPre 0x103603 (.rip 0xfdc17)) (callEffect (callMemPtr 0x103603 (.rip 0xfdc17)) (0x103603 + BitVec.ofNat 64 (callMemLen (.rip 0xfdc17)))) 0x1038b0) (callEffect (callMemPtr 0x103603 (.rip 0xfdc17)) (0x103603 + BitVec.ofNat 64 (callMemLen (.rip 0xfdc17)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x103609⟩) #v[]
    (.terminate (.call ⟨.l1038b0, RegMap.args [(1, 1), (3, 57), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l103609, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1035fa : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x48, 0x89, 0xCE, 0x4C, 0x89, 0xCB, 0xFF, 0x15, 0x17, 0xDC, 0x0F, 0x00]

theorem code_l1035fa : ∀ x ∈ codeRange 0x1035fa bytes_l1035fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x35fa 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103609 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103609 (movR64R64Effect 0x103609 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3]
    (.letOp (n := 54) (.exec 0x103609 (fun s => s.RIP = 0x103609) (movR64R64Effect 0x103609 9 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l103685, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l103609 : List UInt8 :=
  [0x49, 0x89, 0xD9, 0xEB, 0x77]

theorem code_l103609 : ∀ x ∈ codeRange 0x103609 bytes_l103609, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3609 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10360e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10360e (xorR32R32Effect 0x10360e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10360e (fun s => s.RIP = 0x10360e) (xorR32R32Effect 0x10360e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103685, RegMap.args [(0, 53), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10360e : List UInt8 :=
  [0x31, 0xC0, 0xEB, 0x73]

theorem code_l10360e : ∀ x ∈ codeRange 0x10360e bytes_l10360e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x360e 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103612 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103612 (movR32R32Effect 0x103612 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 54) (.exec 0x103612 (fun s => s.RIP = 0x103612) (movR32R32Effect 0x103612 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x103614 (andR32Imm8Effect 0x103614 3 6 0x1c) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x103614 (fun s => s.RIP = 0x103614) (andR32Imm8Effect 0x103614 3 6 0x1c) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x103617 (xorR32R32Effect 0x103617 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x103617 (fun s => s.RIP = 0x103617) (xorR32R32Effect 0x103617 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x103619 (xorR32R32Effect 0x103619 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 60) (.exec 0x103619 (fun s => s.RIP = 0x103619) (xorR32R32Effect 0x103619 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 61) (.exec 0x10361b (fun s => s.RIP = 0x10361b) (fun _ => nopEffect 0x10361b 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103620, RegMap.args [(0, 59), (1, 1), (2, 57), (4, 4), (5, 5), (6, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l103612 : List UInt8 :=
  [0x89, 0xCE, 0x83, 0xE6, 0x1C, 0x31, 0xD2, 0x31, 0xC0, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l103612 : ∀ x ∈ codeRange 0x103612 bytes_l103612, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3612 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103620 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103620 (xorR32R32Effect 0x103620 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x103620 (fun s => s.RIP = 0x103620) (xorR32R32Effect 0x103620 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x103622 (cmpM8Imm8Effect 0x103622 5 (.sib 14 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 56) (.out 0x103622 (cmpM8Imm8Effect 0x103622 5 (.sib 14 (some 2) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 57) (.exec 0x103622 (LoadPre 0x103622 (fun s => AddrMode.addr (.sib 14 (some 2) 0 .none) s (0x103622 + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x103622 5 (.sib 14 (some 2) 0 .none) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 58) (.out 0x103627 (atFlags (condHolds 13) (setccR8Effect 0x103627 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 7))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103627 (fun s => s.RIP = 0x103627) (atFlags (condHolds 13) (setccR8Effect 0x103627 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x10362b (addR64R64Effect 0x10362b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[58, 0]
    (.letOp (n := 61) (.exec 0x10362b (fun s => s.RIP = 0x10362b) (addR64R64Effect 0x10362b 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[58, 0]
    (.letOp (n := 62) (.out 0x10362e (xorR32R32Effect 0x10362e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 63) (.exec 0x10362e (fun s => s.RIP = 0x10362e) (xorR32R32Effect 0x10362e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 64) (.out 0x103630 (cmpM8Imm8Effect 0x103630 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 65) (.out 0x103630 (cmpM8Imm8Effect 0x103630 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 66) (.exec 0x103630 (LoadPre 0x103630 (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x1)) s (0x103630 + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x103630 6 (.sib 14 (some 2) 0 (.d8 0x1)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 67) (.out 0x103636 (atFlags (condHolds 13) (setccR8Effect 0x103636 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[62, 64, 65]
    (.letOp (n := 68) (.exec 0x103636 (fun s => s.RIP = 0x103636) (atFlags (condHolds 13) (setccR8Effect 0x103636 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[62, 64, 65]
    (.letOp (n := 69) (.out 0x103639 (xorR32R32Effect 0x103639 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 70) (.exec 0x103639 (fun s => s.RIP = 0x103639) (xorR32R32Effect 0x103639 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 71) (.out 0x10363c (cmpM8Imm8Effect 0x10363c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 72) (.out 0x10363c (cmpM8Imm8Effect 0x10363c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 73) (.exec 0x10363c (LoadPre 0x10363c (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x2)) s (0x10363c + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x10363c 6 (.sib 14 (some 2) 0 (.d8 0x2)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 74) (.out 0x103642 (atFlags (condHolds 13) (setccR8Effect 0x103642 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 8))) #v[69, 71, 72]
    (.letOp (n := 75) (.exec 0x103642 (fun s => s.RIP = 0x103642) (atFlags (condHolds 13) (setccR8Effect 0x103642 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[69, 71, 72]
    (.letOp (n := 76) (.out 0x103646 (addR64R64Effect 0x103646 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[74, 67]
    (.letOp (n := 77) (.exec 0x103646 (fun s => s.RIP = 0x103646) (addR64R64Effect 0x103646 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[74, 67]
    (.letOp (n := 78) (.out 0x103649 (addR64R64Effect 0x103649 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[76, 60]
    (.letOp (n := 79) (.exec 0x103649 (fun s => s.RIP = 0x103649) (addR64R64Effect 0x103649 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[76, 60]
    (.letOp (n := 80) (.out 0x10364c (xorR32R32Effect 0x10364c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[67, 67]
    (.letOp (n := 81) (.exec 0x10364c (fun s => s.RIP = 0x10364c) (xorR32R32Effect 0x10364c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[67, 67]
    (.letOp (n := 82) (.out 0x10364e (cmpM8Imm8Effect 0x10364e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 14, .gpr 2] []) (.flag .SF)) #v[14, 2]
    (.letOp (n := 83) (.out 0x10364e (cmpM8Imm8Effect 0x10364e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 14, .gpr 2] []) (.flag .OF)) #v[14, 2]
    (.letOp (n := 84) (.exec 0x10364e (LoadPre 0x10364e (fun s => AddrMode.addr (.sib 14 (some 2) 0 (.d8 0x3)) s (0x10364e + BitVec.ofNat 64 6)) 1) (cmpM8Imm8Effect 0x10364e 6 (.sib 14 (some 2) 0 (.d8 0x3)) 0xc0) (Reg.operands [.gpr 14, .gpr 2] [])) #v[14, 2]
    (.letOp (n := 85) (.out 0x103654 (atFlags (condHolds 13) (setccR8Effect 0x103654 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 0))) #v[80, 82, 83]
    (.letOp (n := 86) (.exec 0x103654 (fun s => s.RIP = 0x103654) (atFlags (condHolds 13) (setccR8Effect 0x103654 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[80, 82, 83]
    (.letOp (n := 87) (.out 0x103657 (addR64R64Effect 0x103657 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[85, 78]
    (.letOp (n := 88) (.exec 0x103657 (fun s => s.RIP = 0x103657) (addR64R64Effect 0x103657 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[85, 78]
    (.letOp (n := 89) (.out 0x10365a (addR64Imm8Effect 0x10365a 2 0x4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 90) (.exec 0x10365a (fun s => s.RIP = 0x10365a) (addR64Imm8Effect 0x10365a 2 0x4) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 91) (.out 0x10365e (cmpR64R64Effect 0x10365e 6 2) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 2] []) (.flag .ZF)) #v[6, 89]
    (.letOp (n := 92) (.exec 0x10365e (fun s => s.RIP = 0x10365e) (cmpR64R64Effect 0x10365e 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[6, 89]
    (.letOp (n := 93) (.pure (condOp 5)) #v[91]
    (.terminate (.condBr (Fin.last 93) ⟨.l103620, RegMap.args [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩ ⟨.l103663, RegMap.args [(0, 87), (2, 89), (4, 4), (5, 5), (6, 6), (7, 60), (8, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 91), (22, 22), (39, 39), (50, 50), (51, 51)] 94⟩))))))))))))))))))))))))))))))))))))))))))

def bytes_l103620 : List UInt8 :=
  [0x31, 0xFF, 0x41, 0x80, 0x3C, 0x16, 0xC0, 0x40, 0x0F, 0x9D, 0xC7, 0x48, 0x01, 0xC7, 0x31, 0xC0,
    0x41, 0x80, 0x7C, 0x16, 0x01, 0xC0, 0x0F, 0x9D, 0xC0, 0x45, 0x31, 0xC0, 0x41, 0x80, 0x7C, 0x16,
    0x02, 0xC0, 0x41, 0x0F, 0x9D, 0xC0, 0x49, 0x01, 0xC0, 0x49, 0x01, 0xF8, 0x31, 0xC0, 0x41, 0x80,
    0x7C, 0x16, 0x03, 0xC0, 0x0F, 0x9D, 0xC0, 0x4C, 0x01, 0xC0, 0x48, 0x83, 0xC2, 0x04, 0x48, 0x39,
    0xD6, 0x75, 0xBD]

theorem code_l103620 : ∀ x ∈ codeRange 0x103620 bytes_l103620, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3620 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103663 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103663 (testR64R64Effect 0x103663 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[10, 10]
    (.letOp (n := 54) (.exec 0x103663 (fun s => s.RIP = 0x103663) (testR64R64Effect 0x103663 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103685, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103668, RegMap.args [(0, 0), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103663 : List UInt8 :=
  [0x4D, 0x85, 0xD2, 0x74, 0x1D]

theorem code_l103663 : ∀ x ∈ codeRange 0x103663 bytes_l103663, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3663 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103668 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103668 (addR64R64Effect 0x103668 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[2, 14]
    (.letOp (n := 54) (.exec 0x103668 (fun s => s.RIP = 0x103668) (addR64R64Effect 0x103668 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[2, 14]
    (.letOp (n := 55) (.out 0x10366b (xorR32R32Effect 0x10366b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 56) (.exec 0x10366b (fun s => s.RIP = 0x10366b) (xorR32R32Effect 0x10366b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 57) (.exec 0x10366d (fun s => s.RIP = 0x10366d) (fun _ => nopEffect 0x10366d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103670, RegMap.args [(0, 0), (2, 53), (4, 4), (5, 5), (6, 55), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103668 : List UInt8 :=
  [0x4C, 0x01, 0xF2, 0x31, 0xF6, 0x0F, 0x1F, 0x00]

theorem code_l103668 : ∀ x ∈ codeRange 0x103668 bytes_l103668, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3668 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103670 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103670 (xorR32R32Effect 0x103670 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x103670 (fun s => s.RIP = 0x103670) (xorR32R32Effect 0x103670 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x103672 (cmpM8Imm8Effect 0x103672 4 (.sib 2 (some 6) 0 .none) 0xc0) (EffectPart.reads (.flag .SF) [.gpr 2, .gpr 6] []) (.flag .SF)) #v[2, 6]
    (.letOp (n := 56) (.out 0x103672 (cmpM8Imm8Effect 0x103672 4 (.sib 2 (some 6) 0 .none) 0xc0) (EffectPart.reads (.flag .OF) [.gpr 2, .gpr 6] []) (.flag .OF)) #v[2, 6]
    (.letOp (n := 57) (.exec 0x103672 (LoadPre 0x103672 (fun s => AddrMode.addr (.sib 2 (some 6) 0 .none) s (0x103672 + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x103672 4 (.sib 2 (some 6) 0 .none) 0xc0) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 58) (.out 0x103676 (atFlags (condHolds 13) (setccR8Effect 0x103676 4 7)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF]) (.reg (.gpr 7))) #v[53, 55, 56]
    (.letOp (n := 59) (.exec 0x103676 (fun s => s.RIP = 0x103676) (atFlags (condHolds 13) (setccR8Effect 0x103676 4 7)) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.SF, .OF])) #v[53, 55, 56]
    (.letOp (n := 60) (.out 0x10367a (addR64R64Effect 0x10367a 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[0, 58]
    (.letOp (n := 61) (.exec 0x10367a (fun s => s.RIP = 0x10367a) (addR64R64Effect 0x10367a 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[0, 58]
    (.letOp (n := 62) (.out 0x10367d (incR64Effect 0x10367d 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 63) (.exec 0x10367d (fun s => s.RIP = 0x10367d) (incR64Effect 0x10367d 6) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[6]
    (.letOp (n := 64) (.out 0x103680 (cmpR64R64Effect 0x103680 10 6) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 6] []) (.flag .ZF)) #v[10, 62]
    (.letOp (n := 65) (.exec 0x103680 (fun s => s.RIP = 0x103680) (cmpR64R64Effect 0x103680 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[10, 62]
    (.letOp (n := 66) (.pure (condOp 5)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l103670, RegMap.args [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l103685, RegMap.args [(0, 60), (2, 2), (4, 4), (5, 5), (6, 62), (7, 58), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l103670 : List UInt8 :=
  [0x31, 0xFF, 0x80, 0x3C, 0x32, 0xC0, 0x40, 0x0F, 0x9D, 0xC7, 0x48, 0x01, 0xF8, 0x48, 0xFF, 0xC6,
    0x49, 0x39, 0xF2, 0x75, 0xEB]

theorem code_l103670 : ∀ x ∈ codeRange 0x103670 bytes_l103670, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3670 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103685 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103685 (addR64R64Effect 0x103685 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[9, 0]
    (.letOp (n := 54) (.exec 0x103685 (fun s => s.RIP = 0x103685) (addR64R64Effect 0x103685 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 0]
    (.letOp (n := 55) (.out 0x103688 (movzxR32M16Effect 0x103688 6 3 (.sib 12 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 12] []) (.reg (.gpr 3))) #v[12]
    (.letOp (n := 56) (.exec 0x103688 (LoadPre 0x103688 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x14)) s (0x103688 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x103688 6 3 (.sib 12 none 0 (.d8 0x14))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10368e (cmpR64R64Effect 0x10368e 9 3) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 3] []) (.flag .CF)) #v[53, 55]
    (.letOp (n := 58) (.exec 0x10368e (fun s => s.RIP = 0x10368e) (cmpR64R64Effect 0x10368e 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[53, 55]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103593, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l103697, RegMap.args [(0, 0), (3, 55), (4, 4), (5, 5), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103685 : List UInt8 :=
  [0x49, 0x01, 0xC1, 0x41, 0x0F, 0xB7, 0x5C, 0x24, 0x14, 0x49, 0x39, 0xD9, 0x0F, 0x83, 0xFC, 0xFE,
    0xFF, 0xFF]

theorem code_l103685 : ∀ x ∈ codeRange 0x103685 bytes_l103685, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3685 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103697 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103697 (testR32Imm32Effect 0x103697 7 15 0x1000000) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 54) (.exec 0x103697 (fun s => s.RIP = 0x103697) (testR32Imm32Effect 0x103697 7 15 0x1000000) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.exec 0x10369e (StorePre 0x10369e 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x10369e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10369e 13 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 56) (.exec 0x1036a2 (StorePre 0x1036a2 4 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x1036a2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036a2 9 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 9, .gpr 5] [])) #v[9, 5]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l1036d0, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1036a8, RegMap.args [(3, 3), (4, 4), (5, 5), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103697 : List UInt8 :=
  [0x41, 0xF7, 0xC7, 0x00, 0x00, 0x00, 0x01, 0x4C, 0x89, 0x6D, 0xA8, 0x4C, 0x89, 0x4D, 0xA0, 0x75,
    0x28]

theorem code_l103697 : ∀ x ∈ codeRange 0x103697 bytes_l103697, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3697 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036a8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036a8 (movR32R32Effect 0x1036a8 2 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 54) (.exec 0x1036a8 (fun s => s.RIP = 0x1036a8) (movR32R32Effect 0x1036a8 2 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1036aa (subR32R32Effect 0x1036aa 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[53, 9]
    (.letOp (n := 56) (.exec 0x1036aa (fun s => s.RIP = 0x1036aa) (subR32R32Effect 0x1036aa 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[53, 9]
    (.letOp (n := 57) (.out 0x1036ad (movR32R32Effect 0x1036ad 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 58) (.exec 0x1036ad (fun s => s.RIP = 0x1036ad) (movR32R32Effect 0x1036ad 3 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1036b0 (shrR32Effect 0x1036b0 3 0 29) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 60) (.exec 0x1036b0 (fun s => s.RIP = 0x1036b0) (shrR32Effect 0x1036b0 3 0 29) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x1036b3 (andR32Imm8Effect 0x1036b3 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 62) (.exec 0x1036b3 (fun s => s.RIP = 0x1036b3) (andR32Imm8Effect 0x1036b3 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 63) (.out 0x1036b6 (leaR64Effect 0x1036b6 1 (.rip 0xfd863)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 64) (.exec 0x1036b6 (fun s => s.RIP = 0x1036b6) (leaR64Effect 0x1036b6 1 (.rip 0xfd863)) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x1036bd (movsxdR64M32Effect 0x1036bd 4 0 (.sib 1 (some 0) 2 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x1036bd (LoadPre 0x1036bd (fun s => AddrMode.addr (.sib 1 (some 0) 2 .none) s (0x1036bd + BitVec.ofNat 64 4)) 4) (movsxdR64M32Effect 0x1036bd 4 0 (.sib 1 (some 0) 2 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[63, 61]
    (.letOp (n := 67) (.exec 0x1036c1 (fun s => s.RIP = 0x1036c1) (addR64R64Effect 0x1036c1 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[65, 63]
    (.letOp (n := 68) (.exec 0x1036c4 (StorePre 0x1036c4 3 (fun s => AddrMode.addr (.base 5 (.d8 0xb4)) s (0x1036c4 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1036c4 2 (.base 5 (.d8 0xb4))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[55, 5]
    (cutBlock 0x1036c7))))))))))))))))

def bytes_l1036a8 : List UInt8 :=
  [0x89, 0xDA, 0x44, 0x29, 0xCA, 0x44, 0x89, 0xF8, 0xC1, 0xE8, 0x1D, 0x83, 0xE0, 0x03, 0x48, 0x8D,
    0x0D, 0x63, 0xD8, 0x0F, 0x00, 0x48, 0x63, 0x04, 0x81, 0x48, 0x01, 0xC8, 0x89, 0x55, 0xB4, 0xFF,
    0xE0]

theorem code_l1036a8 : ∀ x ∈ codeRange 0x1036a8 bytes_l1036a8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36a8 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1036d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1036d0 (movR64M64Effect 0x1036d0 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x1036d0 (LoadPre 0x1036d0 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1036d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036d0 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.exec 0x1036d5 (StorePre 0x1036d5 4 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x1036d5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1036d5 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[53, 5]
    (.letOp (n := 56) (.out 0x1036d9 (andEaxImm32Effect 0x1036d9 0x9fe00000) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 57) (.exec 0x1036d9 (fun s => s.RIP = 0x1036d9) (andEaxImm32Effect 0x1036d9 0x9fe00000) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 58) (.out 0x1036de (orEaxImm32Effect 0x1036de 0x20000030) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 59) (.exec 0x1036de (fun s => s.RIP = 0x1036de) (orEaxImm32Effect 0x1036de 0x20000030) (Reg.operands [.gpr 0] [])) #v[56]
    (.letOp (n := 60) (.exec 0x1036e3 (StorePre 0x1036e3 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x1036e3 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x1036e3 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 12] [])) #v[58, 12]
    (.letOp (n := 61) (.out 0x1036e8 (movR64M64Effect 0x1036e8 13 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 12] []) (.reg (.gpr 13))) #v[12]
    (.letOp (n := 62) (.exec 0x1036e8 (LoadPre 0x1036e8 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1036e8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036e8 13 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 63) (.out 0x1036ec (movR64M64Effect 0x1036ec 15 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[12]
    (.letOp (n := 64) (.exec 0x1036ec (LoadPre 0x1036ec (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1036ec + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1036ec 15 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 65) (.out 0x1036f1 (movR64R64Effect 0x1036f1 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 66) (.exec 0x1036f1 (fun s => s.RIP = 0x1036f1) (movR64R64Effect 0x1036f1 7 13) (Reg.operands [.gpr 13] [])) #v[61]
    (.letOp (n := 67) (.out 0x1036f4 (movR64R64Effect 0x1036f4 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 68) (.exec 0x1036f4 (fun s => s.RIP = 0x1036f4) (movR64R64Effect 0x1036f4 6 15) (Reg.operands [.gpr 15] [])) #v[63]
    (.letOp (n := 69) (.out 0x1036f7 (movR32M32LowEffect 0x1036f7 2 (.base 5 (.d8 0xd4))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 70) (.exec 0x1036f7 (LoadPre 0x1036f7 (fun s => AddrMode.addr (.base 5 (.d8 0xd4)) s (0x1036f7 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x1036f7 2 (.base 5 (.d8 0xd4))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x1036fa (movR64R64Effect 0x1036fa 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 72) (.exec 0x1036fa (fun s => s.RIP = 0x1036fa) (movR64R64Effect 0x1036fa 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x1036fd (movR64M64Effect 0x1036fd 8 (.base 5 (.d8 0xb8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 74) (.exec 0x1036fd (LoadPre 0x1036fd (fun s => AddrMode.addr (.base 5 (.d8 0xb8)) s (0x1036fd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1036fd 8 (.base 5 (.d8 0xb8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 75) (.out 0x103701 (callEffect (fun _ => 0x103d40) 0x103706) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x103701 (PushPre 0x103701 5) (callEffect (fun _ => 0x103d40) 0x103706) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x103706⟩) #v[]
    (.terminate (.call ⟨.l103d40, RegMap.args [(0, 58), (1, 71), (2, 69), (3, 3), (4, 75), (5, 5), (6, 67), (7, 65), (8, 73), (9, 9), (11, 11), (12, 12), (13, 61), (14, 14), (15, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l103706, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l1036d0 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x45, 0xC8, 0x25, 0x00, 0x00, 0xE0, 0x9F, 0x0D, 0x30,
    0x00, 0x00, 0x20, 0x41, 0x89, 0x44, 0x24, 0x10, 0x4D, 0x8B, 0x2C, 0x24, 0x4D, 0x8B, 0x7C, 0x24,
    0x08, 0x4C, 0x89, 0xEF, 0x4C, 0x89, 0xFE, 0x8B, 0x55, 0xD4, 0x4C, 0x89, 0xF1, 0x4C, 0x8B, 0x45,
    0xB8, 0xE8, 0x3A, 0x06, 0x00, 0x00]

theorem code_l1036d0 : ∀ x ∈ codeRange 0x1036d0 bytes_l1036d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36d0 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103706 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103706 (movR32R32Effect 0x103706 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x103706 (fun s => s.RIP = 0x103706) (movR32R32Effect 0x103706 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103708 (movR8Imm8Effect 0x103708 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x103708 (fun s => s.RIP = 0x103708) (movR8Imm8Effect 0x103708 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.out 0x10370a (testR8R8Effect 0x10370a 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 58) (.exec 0x10370a (fun s => s.RIP = 0x10370a) (testR8R8Effect 0x10370a 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[53, 53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103828, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l103712, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l103706 : List UInt8 :=
  [0x89, 0xC1, 0xB0, 0x01, 0x84, 0xC9, 0x0F, 0x85, 0x16, 0x01, 0x00, 0x00]

theorem code_l103706 : ∀ x ∈ codeRange 0x103706 bytes_l103706, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3706 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103712 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103712 (subR32M32Effect 0x103712 3 3 (.base 5 (.d8 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[3, 5]
    (.letOp (n := 54) (.exec 0x103712 (LoadPre 0x103712 (fun s => AddrMode.addr (.base 5 (.d8 0xa0)) s (0x103712 + BitVec.ofNat 64 3)) 4) (subR32M32Effect 0x103712 3 3 (.base 5 (.d8 0xa0))) (Reg.operands [.gpr 3, .gpr 5] [])) #v[3, 5]
    (.letOp (n := 55) (.out 0x103715 (incR32Effect 0x103715 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.exec 0x103715 (fun s => s.RIP = 0x103715) (incR32Effect 0x103715 2 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.exec 0x103717 (fun s => s.RIP = 0x103717) (fun _ => nopEffect 0x103717 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103720, RegMap.args [(3, 55), (5, 5), (13, 13)] 58⟩))))))

def bytes_l103712 : List UInt8 :=
  [0x2B, 0x5D, 0xA0, 0xFF, 0xC3, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l103712 : ∀ x ∈ codeRange 0x103712 bytes_l103712, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3712 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103720 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103720 (decR16Effect 0x103720 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[3]
    (.letOp (n := 54) (.exec 0x103720 (fun s => s.RIP = 0x103720) (decR16Effect 0x103720 3 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[3]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103737, RegMap.args [(5, 5), (13, 13), (19, 53)] 56⟩ ⟨.l103725, RegMap.args [(5, 5), (13, 13), (19, 53)] 56⟩))))

def bytes_l103720 : List UInt8 :=
  [0x66, 0xFF, 0xCB, 0x74, 0x12]

theorem code_l103720 : ∀ x ∈ codeRange 0x103720 bytes_l103720, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3720 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103725 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103725 (fun s => s.RIP = 0x103725) (movR64R64Effect 0x103725 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 54) (.exec 0x103728 (fun s => s.RIP = 0x103728) (movR32Imm32Effect 0x103728 5 6 0x30) (Reg.operands [] [])) #v[]
    (cutBlock 0x10372d))

def bytes_l103725 : List UInt8 :=
  [0x4C, 0x89, 0xEF, 0xBE, 0x30, 0x00, 0x00, 0x00, 0x41, 0xFF, 0x57, 0x20]

theorem code_l103725 : ∀ x ∈ codeRange 0x103725 bytes_l103725, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3725 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103731 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103731 (testR8R8Effect 0x103731 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103731 (fun s => s.RIP = 0x103731) (testR8R8Effect 0x103731 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103720, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l103735, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l103731 : List UInt8 :=
  [0x84, 0xC0, 0x74, 0xEB]

theorem code_l103731 : ∀ x ∈ codeRange 0x103731 bytes_l103731, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3731 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103735 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1037a6, RegMap.args (entryMap (live .l103735)) 53⟩)

def bytes_l103735 : List UInt8 :=
  [0xEB, 0x6F]

theorem code_l103735 : ∀ x ∈ codeRange 0x103735 bytes_l103735, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3735 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103737 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103737 (fun s => s.RIP = 0x103737) (movR64R64Effect 0x103737 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 54) (.exec 0x10373a (LoadPre 0x10373a (fun s => AddrMode.addr (.base 5 (.d8 0xc0)) s (0x10373a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10373a 6 (.base 5 (.d8 0xc0))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x10373e (LoadPre 0x10373e (fun s => AddrMode.addr (.base 5 (.d8 0xa8)) s (0x10373e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10373e 2 (.base 5 (.d8 0xa8))) (Reg.operands [.gpr 5] [])) #v[5]
    (cutBlock 0x103742)))

def bytes_l103737 : List UInt8 :=
  [0x4C, 0x89, 0xEF, 0x48, 0x8B, 0x75, 0xC0, 0x48, 0x8B, 0x55, 0xA8, 0x41, 0xFF, 0x57, 0x18]

theorem code_l103737 : ∀ x ∈ codeRange 0x103737 bytes_l103737, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3737 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103746 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103746 (testR8R8Effect 0x103746 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103746 (fun s => s.RIP = 0x103746) (testR8R8Effect 0x103746 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x103748 (movR8Imm8Effect 0x103748 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 56) (.exec 0x103748 (fun s => s.RIP = 0x103748) (movR8Imm8Effect 0x103748 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 57) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l103828, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l103750, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103746 : List UInt8 :=
  [0x84, 0xC0, 0xB0, 0x01, 0x0F, 0x85, 0xD8, 0x00, 0x00, 0x00]

theorem code_l103746 : ∀ x ∈ codeRange 0x103746 bytes_l103746, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3746 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103750 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103750 (movR64M64Effect 0x103750 0 (.base 5 (.d8 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[5]
    (.letOp (n := 54) (.exec 0x103750 (LoadPre 0x103750 (fun s => AddrMode.addr (.base 5 (.d8 0xc8)) s (0x103750 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x103750 0 (.base 5 (.d8 0xc8))) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.exec 0x103754 (StorePre 0x103754 5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x103754 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x103754 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 12] [])) #v[53, 12]
    (.letOp (n := 56) (.out 0x103759 (xorR32R32Effect 0x103759 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[53, 53]
    (.letOp (n := 57) (.exec 0x103759 (fun s => s.RIP = 0x103759) (xorR32R32Effect 0x103759 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[53, 53]
    (.terminate (.br ⟨.l103828, RegMap.args [(0, 56), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l103750 : List UInt8 :=
  [0x48, 0x8B, 0x45, 0xC8, 0x49, 0x89, 0x44, 0x24, 0x10, 0x31, 0xC0, 0xE9, 0xC8, 0x00, 0x00, 0x00]

theorem code_l103750 : ∀ x ∈ codeRange 0x103750 bytes_l103750, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3750 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1037a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1037a6 (movR8Imm8Effect 0x1037a6 2 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1037a6 (fun s => s.RIP = 0x1037a6) (movR8Imm8Effect 0x1037a6 2 0 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l103828, RegMap.args [(0, 53), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1037a6 : List UInt8 :=
  [0xB0, 0x01, 0xEB, 0x7E]

theorem code_l1037a6 : ∀ x ∈ codeRange 0x1037a6 bytes_l1037a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x37a6 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103828 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103828 (addR64Imm8Effect 0x103828 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x103828 (fun s => s.RIP = 0x103828) (addR64Imm8Effect 0x103828 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10382c (popR64Effect 0x10382c 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x10382c (popR64Effect 0x10382c 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x10382c (PopPre 0x10382c) (popR64Effect 0x10382c 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x10382d (popR64Effect 0x10382d 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x10382d (popR64Effect 0x10382d 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x10382d (PopPre 0x10382d) (popR64Effect 0x10382d 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10382f (popR64Effect 0x10382f 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10382f (popR64Effect 0x10382f 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10382f (PopPre 0x10382f) (popR64Effect 0x10382f 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x103831 (popR64Effect 0x103831 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x103831 (popR64Effect 0x103831 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x103831 (PopPre 0x103831) (popR64Effect 0x103831 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x103833 (popR64Effect 0x103833 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x103833 (popR64Effect 0x103833 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x103833 (PopPre 0x103833) (popR64Effect 0x103833 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x103835 (popR64Effect 0x103835 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x103835 (popR64Effect 0x103835 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x103835 (PopPre 0x103835) (popR64Effect 0x103835 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x103836 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x103836 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x103836 (RetPre 0x103836) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l103828 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l103828 : ∀ x ∈ codeRange 0x103828 bytes_l103828, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3828 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103837 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103837 (pushR64Effect 0x103837 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103837 (PushPre 0x103837 1) (pushR64Effect 0x103837 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103838 (movR64R64Effect 0x103838 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x103838 (fun s => s.RIP = 0x103838) (movR64R64Effect 0x103838 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x10383b (subR64Imm8Effect 0x10383b 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x10383b (fun s => s.RIP = 0x10383b) (subR64Imm8Effect 0x10383b 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x10383f (leaR64Effect 0x10383f 0 (.base 5 (.d8 0xf8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 60) (.exec 0x10383f (fun s => s.RIP = 0x10383f) (leaR64Effect 0x10383f 0 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 61) (.exec 0x103843 (StorePre 0x103843 3 (fun s => AddrMode.addr (.base 0 .none) s (0x103843 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103843 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[7, 59]
    (.letOp (n := 62) (.out 0x103846 (leaR64Effect 0x103846 1 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 63) (.exec 0x103846 (fun s => s.RIP = 0x103846) (leaR64Effect 0x103846 1 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 64) (.exec 0x10384a (StorePre 0x10384a 3 (fun s => AddrMode.addr (.base 1 .none) s (0x10384a + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10384a 6 (.base 1 .none)) (Reg.operands [.gpr 6, .gpr 1] [])) #v[6, 62]
    (.letOp (n := 65) (.out 0x10384d (leaR64Effect 0x10384d 6 (.base 5 (.d8 0xd0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 5] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 66) (.exec 0x10384d (fun s => s.RIP = 0x10384d) (leaR64Effect 0x10384d 6 (.base 5 (.d8 0xd0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 67) (.exec 0x103851 (StorePre 0x103851 3 (fun s => AddrMode.addr (.base 6 .none) s (0x103851 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x103851 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[62, 65]
    (.letOp (n := 68) (.out 0x103854 (leaR64Effect 0x103854 1 (.rip 0x545)) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 69) (.exec 0x103854 (fun s => s.RIP = 0x103854) (leaR64Effect 0x103854 1 (.rip 0x545)) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.exec 0x10385b (StorePre 0x10385b 4 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10385b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10385b 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[68, 65]
    (.letOp (n := 71) (.exec 0x10385f (StorePre 0x10385f 4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10385f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10385f 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 6] [])) #v[59, 65]
    (.letOp (n := 72) (.exec 0x103863 (StorePre 0x103863 4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x103863 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103863 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[68, 65]
    (.letOp (n := 73) (.out 0x103867 (leaR64Effect 0x103867 7 (.rip 0xfcf30)) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 74) (.exec 0x103867 (fun s => s.RIP = 0x103867) (leaR64Effect 0x103867 7 (.rip 0xfcf30)) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10386e (callEffect (callMemPtr 0x10386e (.rip 0xfd99c)) (0x10386e + BitVec.ofNat 64 (callMemLen (.rip 0xfd99c)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 76) (.exec 0x10386e (GoesTo (CallMemPre 0x10386e (.rip 0xfd99c)) (callEffect (callMemPtr 0x10386e (.rip 0xfd99c)) (0x10386e + BitVec.ofNat 64 (callMemLen (.rip 0xfd99c)))) 0x103880) (callEffect (callMemPtr 0x10386e (.rip 0xfd99c)) (0x10386e + BitVec.ofNat 64 (callMemLen (.rip 0xfd99c)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 77) (.const ⟨64, 0x103874⟩) #v[]
    (.terminate (.call ⟨.l103880, RegMap.args [(0, 59), (1, 68), (2, 2), (4, 75), (5, 55), (6, 65), (7, 73)] 78⟩ { target := .l103874, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l103837 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x8D, 0x45, 0xF8, 0x48, 0x89, 0x38, 0x48,
    0x8D, 0x4D, 0xF0, 0x48, 0x89, 0x31, 0x48, 0x8D, 0x75, 0xD0, 0x48, 0x89, 0x0E, 0x48, 0x8D, 0x0D,
    0x45, 0x05, 0x00, 0x00, 0x48, 0x89, 0x4E, 0x08, 0x48, 0x89, 0x46, 0x10, 0x48, 0x89, 0x4E, 0x18,
    0x48, 0x8D, 0x3D, 0x30, 0xCF, 0x0F, 0x00, 0xFF, 0x15, 0x9C, 0xD9, 0x0F, 0x00]

theorem code_l103837 : ∀ x ∈ codeRange 0x103837 bytes_l103837, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3837 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103874 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x103874 (fun s => s.RIP = 0x103874) (fun _ => nopEffect 0x103874 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x10387e (fun s => s.RIP = 0x10387e) (fun _ => nopEffect 0x10387e 2) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l103880, RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 55⟩)))

def bytes_l103874 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90]

theorem code_l103874 : ∀ x ∈ codeRange 0x103874 bytes_l103874, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3874 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103880 (pushR64Effect 0x103880 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x103880 (PushPre 0x103880 1) (pushR64Effect 0x103880 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x103881 (movR64R64Effect 0x103881 5 4) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 56) (.exec 0x103881 (fun s => s.RIP = 0x103881) (movR64R64Effect 0x103881 5 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.out 0x103884 (subR64Imm8Effect 0x103884 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 58) (.exec 0x103884 (fun s => s.RIP = 0x103884) (subR64Imm8Effect 0x103884 4 0x30) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.exec 0x103888 (StorePre 0x103888 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf0)) s (0x103888 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103888 7 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 7, .gpr 5] [])) #v[7, 55]
    (.letOp (n := 60) (.exec 0x10388c (StorePre 0x10388c 4 (fun s => AddrMode.addr (.base 5 (.d8 0xf8)) s (0x10388c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10388c 6 (.base 5 (.d8 0xf8))) (Reg.operands [.gpr 6, .gpr 5] [])) #v[6, 55]
    (.letOp (n := 61) (.out 0x103890 (leaR64Effect 0x103890 0 (.base 5 (.d8 0xf0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 62) (.exec 0x103890 (fun s => s.RIP = 0x103890) (leaR64Effect 0x103890 0 (.base 5 (.d8 0xf0))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 63) (.exec 0x103894 (StorePre 0x103894 4 (fun s => AddrMode.addr (.base 5 (.d8 0xd8)) s (0x103894 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103894 0 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 0, .gpr 5] [])) #v[61, 55]
    (.letOp (n := 64) (.exec 0x103898 (StorePre 0x103898 4 (fun s => AddrMode.addr (.base 5 (.d8 0xe0)) s (0x103898 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x103898 2 (.base 5 (.d8 0xe0))) (Reg.operands [.gpr 2, .gpr 5] [])) #v[2, 55]
    (.letOp (n := 65) (.exec 0x10389c (StorePre 0x10389c 6 (fun s => AddrMode.addr (.base 5 (.d8 0xe8)) s (0x10389c + BitVec.ofNat 64 6)) 2) (movM16Imm16Effect 0x10389c (.base 5 (.d8 0xe8)) 0x1) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 66) (.exec 0x1038a2 (fun s => s.RIP = 0x1038a2) (leaR64Effect 0x1038a2 7 (.base 5 (.d8 0xd8))) (Reg.operands [.gpr 5] [])) #v[55]
    (.letOp (n := 67) (.exec 0x1038a6 (GoesTo (CallMemPre 0x1038a6 (.rip 0xfd984)) (callEffect (callMemPtr 0x1038a6 (.rip 0xfd984)) (0x1038a6 + BitVec.ofNat 64 (callMemLen (.rip 0xfd984)))) 0x101230) (callEffect (callMemPtr 0x1038a6 (.rip 0xfd984)) (0x1038a6 + BitVec.ofNat 64 (callMemLen (.rip 0xfd984)))) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 68) (.const ⟨64, 0x1038ac⟩) #v[]
    (.terminate (.call ⟨.l101230, RegMap.args [(0, 61), (2, 2), (5, 55), (6, 6)] 69⟩ { target := .l1038ac, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l103880 : List UInt8 :=
  [0x55, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0x7D, 0xF0, 0x48, 0x89, 0x75, 0xF8,
    0x48, 0x8D, 0x45, 0xF0, 0x48, 0x89, 0x45, 0xD8, 0x48, 0x89, 0x55, 0xE0, 0x66, 0xC7, 0x45, 0xE8,
    0x01, 0x00, 0x48, 0x8D, 0x7D, 0xD8, 0xFF, 0x15, 0x84, 0xD9, 0x0F, 0x00]

theorem code_l103880 : ∀ x ∈ codeRange 0x103880 bytes_l103880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3880 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1038ac (fun s => s.RIP = 0x1038ac) (fun _ => nopEffect 0x1038ac 4) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1038b0, RegMap.args [(1, 1), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l1038ac : List UInt8 :=
  [0x0F, 0x1F, 0x40, 0x00]

theorem code_l1038ac : ∀ x ∈ codeRange 0x1038ac bytes_l1038ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38ac 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038b0 (leaR64Effect 0x1038b0 8 (.base 7 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 54) (.exec 0x1038b0 (fun s => s.RIP = 0x1038b0) (leaR64Effect 0x1038b0 8 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1038b4 (andR64Imm8Effect 0x1038b4 8 0xf8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[53]
    (.letOp (n := 56) (.exec 0x1038b4 (fun s => s.RIP = 0x1038b4) (andR64Imm8Effect 0x1038b4 8 0xf8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 57) (.out 0x1038b8 (movR64R64Effect 0x1038b8 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x1038b8 (fun s => s.RIP = 0x1038b8) (movR64R64Effect 0x1038b8 0 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x1038bb (subR64R64Effect 0x1038bb 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[57, 7]
    (.letOp (n := 60) (.exec 0x1038bb (fun s => s.RIP = 0x1038bb) (subR64R64Effect 0x1038bb 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 61) (.out 0x1038be (movR64R64Effect 0x1038be 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 62) (.exec 0x1038be (fun s => s.RIP = 0x1038be) (movR64R64Effect 0x1038be 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x1038c1 (subR64R64Effect 0x1038c1 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[61, 59]
    (.letOp (n := 64) (.out 0x1038c1 (subR64R64Effect 0x1038c1 2 0) (EffectPart.reads (.flag .CF) [.gpr 2, .gpr 0] []) (.flag .CF)) #v[61, 59]
    (.letOp (n := 65) (.exec 0x1038c1 (fun s => s.RIP = 0x1038c1) (subR64R64Effect 0x1038c1 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[61, 59]
    (.letOp (n := 66) (.pure (condOp 3)) #v[64]
    (.terminate (.condBr (Fin.last 66) ⟨.l1038df, RegMap.args [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ ⟨.l1038c6, RegMap.args [(0, 59), (1, 1), (2, 63), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩)))))))))))))))

def bytes_l1038b0 : List UInt8 :=
  [0x4C, 0x8D, 0x47, 0x07, 0x49, 0x83, 0xE0, 0xF8, 0x4C, 0x89, 0xC0, 0x48, 0x29, 0xF8, 0x48, 0x89,
    0xF2, 0x48, 0x29, 0xC2, 0x73, 0x19]

theorem code_l1038b0 : ∀ x ∈ codeRange 0x1038b0 bytes_l1038b0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38b0 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038c6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038c6 (testR64R64Effect 0x1038c6 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[6, 6]
    (.letOp (n := 54) (.exec 0x1038c6 (fun s => s.RIP = 0x1038c6) (testR64R64Effect 0x1038c6 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l103925, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1038cb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1038c6 : List UInt8 :=
  [0x48, 0x85, 0xF6, 0x74, 0x5A]

theorem code_l1038c6 : ∀ x ∈ codeRange 0x1038c6 bytes_l1038c6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38c6 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038cb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038cb (movR32R32Effect 0x1038cb 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x1038cb (fun s => s.RIP = 0x1038cb) (movR32R32Effect 0x1038cb 2 1 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1038cd (andR32Imm8Effect 0x1038cd 3 1 0x3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x1038cd (fun s => s.RIP = 0x1038cd) (andR32Imm8Effect 0x1038cd 3 1 0x3) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x1038d0 (cmpR64Imm8Effect 0x1038d0 6 0x4) (EffectPart.reads (.flag .CF) [.gpr 6] []) (.flag .CF)) #v[6]
    (.letOp (n := 58) (.exec 0x1038d0 (fun s => s.RIP = 0x1038d0) (cmpR64Imm8Effect 0x1038d0 6 0x4) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.pure (condOp 3)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l103928, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1038d6, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1038cb : List UInt8 :=
  [0x89, 0xF1, 0x83, 0xE1, 0x03, 0x48, 0x83, 0xFE, 0x04, 0x73, 0x52]

theorem code_l1038cb : ∀ x ∈ codeRange 0x1038cb bytes_l1038cb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38cb 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038d6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038d6 (xorR32R32Effect 0x1038d6 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1038d6 (fun s => s.RIP = 0x1038d6) (xorR32R32Effect 0x1038d6 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.out 0x1038d8 (xorR32R32Effect 0x1038d8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 56) (.exec 0x1038d8 (fun s => s.RIP = 0x1038d8) (xorR32R32Effect 0x1038d8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103975, RegMap.args [(0, 55), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l1038d6 : List UInt8 :=
  [0x31, 0xD2, 0x31, 0xC0, 0xE9, 0x96, 0x00, 0x00, 0x00]

theorem code_l1038d6 : ∀ x ∈ codeRange 0x1038d6 bytes_l1038d6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38d6 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038df (movR64R64Effect 0x1038df 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 54) (.exec 0x1038df (fun s => s.RIP = 0x1038df) (movR64R64Effect 0x1038df 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x1038e2 (shrR64Effect 0x1038e2 4 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.out 0x1038e2 (shrR64Effect 0x1038e2 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x1038e2 (fun s => s.RIP = 0x1038e2) (shrR64Effect 0x1038e2 4 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l1038c6, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l1038e8, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l1038df : List UInt8 :=
  [0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x03, 0x74, 0xDE]

theorem code_l1038df : ∀ x ∈ codeRange 0x1038df bytes_l1038df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38df 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038e8 (pushR64Effect 0x1038e8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x1038e8 (PushPre 0x1038e8 2) (pushR64Effect 0x1038e8 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x1038ea (pushR64Effect 0x1038ea 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x1038ea (PushPre 0x1038ea 2) (pushR64Effect 0x1038ea 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x1038ec (pushR64Effect 0x1038ec 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x1038ec (PushPre 0x1038ec 2) (pushR64Effect 0x1038ec 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x1038ee (pushR64Effect 0x1038ee 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1038ee (PushPre 0x1038ee 2) (pushR64Effect 0x1038ee 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1038f0 (pushR64Effect 0x1038f0 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x1038f0 (PushPre 0x1038f0 1) (pushR64Effect 0x1038f0 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x1038f1 (movR32R32Effect 0x1038f1 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 64) (.exec 0x1038f1 (fun s => s.RIP = 0x1038f1) (movR32R32Effect 0x1038f1 2 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 65) (.out 0x1038f3 (andR32Imm8Effect 0x1038f3 3 6 0x7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 66) (.exec 0x1038f3 (fun s => s.RIP = 0x1038f3) (andR32Imm8Effect 0x1038f3 3 6 0x7) (Reg.operands [.gpr 6] [])) #v[63]
    (.letOp (n := 67) (.out 0x1038f6 (cmpR64R64Effect 0x1038f6 8 7) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 7] []) (.flag .ZF)) #v[8, 7]
    (.letOp (n := 68) (.exec 0x1038f6 (fun s => s.RIP = 0x1038f6) (cmpR64R64Effect 0x1038f6 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 7]
    (.letOp (n := 69) (.pure (condOp 5)) #v[67]
    (.terminate (.condBr (Fin.last 69) ⟨.l103903, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ ⟨.l1038fb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 61), (5, 5), (6, 65), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩))))))))))))))))))

def bytes_l1038e8 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x89, 0xD6, 0x83, 0xE6, 0x07, 0x49, 0x39,
    0xF8, 0x75, 0x08]

theorem code_l1038e8 : ∀ x ∈ codeRange 0x1038e8 bytes_l1038e8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38e8 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1038fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1038fb (xorR32R32Effect 0x1038fb 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 54) (.exec 0x1038fb (fun s => s.RIP = 0x1038fb) (xorR32R32Effect 0x1038fb 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l103a25, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1038fb : List UInt8 :=
  [0x45, 0x31, 0xC0, 0xE9, 0x22, 0x01, 0x00, 0x00]

theorem code_l1038fb : ∀ x ∈ codeRange 0x1038fb bytes_l1038fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x38fb 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103903 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103903 (movR32R32Effect 0x103903 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[0]
    (.letOp (n := 54) (.exec 0x103903 (fun s => s.RIP = 0x103903) (movR32R32Effect 0x103903 3 9 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x103906 (andR32Imm8Effect 0x103906 4 9 0x3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x103906 (fun s => s.RIP = 0x103906) (andR32Imm8Effect 0x103906 4 9 0x3) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 57) (.out 0x10390a (movR64R64Effect 0x10390a 10 7) (EffectPart.reads (.reg (.gpr 10)) [.gpr 7] []) (.reg (.gpr 10))) #v[7]
    (.letOp (n := 58) (.exec 0x10390a (fun s => s.RIP = 0x10390a) (movR64R64Effect 0x10390a 10 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.out 0x10390d (subR64R64Effect 0x10390d 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[57, 8]
    (.letOp (n := 60) (.exec 0x10390d (fun s => s.RIP = 0x10390d) (subR64R64Effect 0x10390d 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[57, 8]
    (.letOp (n := 61) (.out 0x103910 (cmpR64Imm8Effect 0x103910 10 0xfc) (EffectPart.reads (.flag .CF) [.gpr 10] []) (.flag .CF)) #v[59]
    (.letOp (n := 62) (.out 0x103910 (cmpR64Imm8Effect 0x103910 10 0xfc) (EffectPart.reads (.flag .ZF) [.gpr 10] []) (.flag .ZF)) #v[59]
    (.letOp (n := 63) (.exec 0x103910 (fun s => s.RIP = 0x103910) (cmpR64Imm8Effect 0x103910 10 0xfc) (Reg.operands [.gpr 10] [])) #v[59]
    (.letOp (n := 64) (.pure (condOp 6)) #v[61, 62]
    (.terminate (.condBr (Fin.last 64) ⟨.l103996, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩ ⟨.l10391a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 55), (10, 59), (11, 11), (14, 14), (16, 61), (19, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 65⟩)))))))))))))

def bytes_l103903 : List UInt8 :=
  [0x41, 0x89, 0xC1, 0x41, 0x83, 0xE1, 0x03, 0x49, 0x89, 0xFA, 0x4D, 0x29, 0xC2, 0x49, 0x83, 0xFA,
    0xFC, 0x0F, 0x86, 0x7C, 0x00, 0x00, 0x00]

theorem code_l103903 : ∀ x ∈ codeRange 0x103903 bytes_l103903, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3903 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10391a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10391a (xorR32R32Effect 0x10391a 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 54) (.exec 0x10391a (fun s => s.RIP = 0x10391a) (xorR32R32Effect 0x10391a 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 55) (.out 0x10391d (xorR32R32Effect 0x10391d 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 56) (.exec 0x10391d (fun s => s.RIP = 0x10391d) (xorR32R32Effect 0x10391d 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.terminate (.br ⟨.l1039fb, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 55), (9, 9), (10, 53), (11, 11), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10391a : List UInt8 :=
  [0x45, 0x31, 0xD2, 0x45, 0x31, 0xC0, 0xE9, 0xD6, 0x00, 0x00, 0x00]

theorem code_l10391a : ∀ x ∈ codeRange 0x10391a bytes_l10391a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x391a 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103925 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103925 (xorR32R32Effect 0x103925 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x103925 (fun s => s.RIP = 0x103925) (xorR32R32Effect 0x103925 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x103927 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 56) (.out 0x103927 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 57) (.exec 0x103927 (RetPre 0x103927) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 56), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58) (some ⟨55, by decide⟩)))))))

def bytes_l103925 : List UInt8 :=
  [0x31, 0xC0, 0xC3]

theorem code_l103925 : ∀ x ∈ codeRange 0x103925 bytes_l103925, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3925 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l103928 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x103928 (andR64Imm8Effect 0x103928 6 0xfc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 54) (.exec 0x103928 (fun s => s.RIP = 0x103928) (andR64Imm8Effect 0x103928 6 0xfc) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x10392c (xorR32R32Effect 0x10392c 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x10392c (fun s => s.RIP = 0x10392c) (xorR32R32Effect 0x10392c 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x10392e (xorR32R32Effect 0x10392e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 58) (.exec 0x10392e (fun s => s.RIP = 0x10392e) (xorR32R32Effect 0x10392e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.terminate (.br ⟨.l103930, RegMap.args [(0, 57), (1, 1), (2, 55), (3, 3), (4, 4), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l103928 : List UInt8 :=
  [0x48, 0x83, 0xE6, 0xFC, 0x31, 0xD2, 0x31, 0xC0]

theorem code_l103928 : ∀ x ∈ codeRange 0x103928 bytes_l103928, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3928 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end AesGcm.Proofs.Machine.LIR
