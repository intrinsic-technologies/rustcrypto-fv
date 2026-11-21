import K256.Proofs.Verify.LIR.HighByteStore
import K256.Proofs.Verify.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Verify.LIR.Generated.Footprints

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

@[cfg_block] def b_l109d80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109d80 (pushR64Effect 0x109d80 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109d80 (PushPre 0x109d80 2) (pushR64Effect 0x109d80 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109d82 (pushR64Effect 0x109d82 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109d82 (PushPre 0x109d82 2) (pushR64Effect 0x109d82 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109d84 (pushR64Effect 0x109d84 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109d84 (PushPre 0x109d84 2) (pushR64Effect 0x109d84 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109d86 (pushR64Effect 0x109d86 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109d86 (PushPre 0x109d86 2) (pushR64Effect 0x109d86 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109d88 (pushR64Effect 0x109d88 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109d88 (PushPre 0x109d88 1) (pushR64Effect 0x109d88 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109d89 (subR64Imm8Effect 0x109d89 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109d89 (fun s => s.RIP = 0x109d89) (subR64Imm8Effect 0x109d89 4 0x30) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109d8d (movR64R64Effect 0x109d8d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x109d8d (fun s => s.RIP = 0x109d8d) (movR64R64Effect 0x109d8d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x109d90 (leaR64Effect 0x109d90 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 68) (.exec 0x109d90 (fun s => s.RIP = 0x109d90) (leaR64Effect 0x109d90 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 69) (.out 0x109d95 (movR64Imm64Effect 0x109d95 1 0xb4f20099aa774ec1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x109d95 (fun s => s.RIP = 0x109d95) (movR64Imm64Effect 0x109d95 1 0xb4f20099aa774ec1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x109d9f (movR64Imm32Effect 0x109d9f 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x109d9f (fun s => s.RIP = 0x109d9f) (movR64Imm32Effect 0x109d9f 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x109da6 (movR64Imm32Effect 0x109da6 8 0x202180) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 74) (.exec 0x109da6 (fun s => s.RIP = 0x109da6) (movR64Imm32Effect 0x109da6 8 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x109dad (callEffect (fun _ => 0x108e30) 0x109db2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 76) (.exec 0x109dad (PushPre 0x109dad 5) (callEffect (fun _ => 0x108e30) 0x109db2) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 77) (.const ⟨64, 0x109db2⟩) #v[]
    (.terminate (.call ⟨.l108e30, RegMap.args [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l109db2, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l109d80 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0xFB,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4, 0x48,
    0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00, 0xE8, 0x7E, 0xF0,
    0xFF, 0xFF]

theorem code_l109d80 : ∀ x ∈ codeRange 0x109d80 bytes_l109d80, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d80 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109db2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109db2 (movR64M64Effect 0x109db2 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x109db2 (LoadPre 0x109db2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109db2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109db7 (movR64M64Effect 0x109db7 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x109db7 (LoadPre 0x109db7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x109db7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109db7 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109dbc (movR64M64Effect 0x109dbc 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x109dbc (LoadPre 0x109dbc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109dbc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dbc 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x109dc1 (movR64M64Effect 0x109dc1 13 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x109dc1 (LoadPre 0x109dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109dc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109dc1 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x109dc6 (movR32M32LowEffect 0x109dc6 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x109dc6 (LoadPre 0x109dc6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x109dc6 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x109dc6 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x109dca (callEffect (fun _ => 0x127d50) 0x109dcf) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x109dca (PushPre 0x109dca 5) (callEffect (fun _ => 0x127d50) 0x109dcf) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x109dcf⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l109dcf, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l109db2 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x64, 0x24, 0x18, 0x4C,
    0x8B, 0x6C, 0x24, 0x20, 0x8B, 0x7C, 0x24, 0x28, 0xE8, 0x81, 0xDF, 0x01, 0x00]

theorem code_l109db2 : ∀ x ∈ codeRange 0x109db2 bytes_l109db2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9db2 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dcf_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x109e10 (movR64R64Effect 0x109e10 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 87) (.exec 0x109e10 (fun s => s.RIP = 0x109e10) (movR64R64Effect 0x109e10 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 88) (.out 0x109e13 (addR64Imm8Effect 0x109e13 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x109e13 (fun s => s.RIP = 0x109e13) (addR64Imm8Effect 0x109e13 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x109e17 (popR64Effect 0x109e17 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[88]
    (.letOp (n := 91) (.out 0x109e17 (popR64Effect 0x109e17 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x109e17 (PopPre 0x109e17) (popR64Effect 0x109e17 1 3) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x109e18 (popR64Effect 0x109e18 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 94) (.out 0x109e18 (popR64Effect 0x109e18 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x109e18 (PopPre 0x109e18) (popR64Effect 0x109e18 2 12) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x109e1a (popR64Effect 0x109e1a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.out 0x109e1a (popR64Effect 0x109e1a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x109e1a (PopPre 0x109e1a) (popR64Effect 0x109e1a 2 13) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x109e1c (popR64Effect 0x109e1c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x109e1c (popR64Effect 0x109e1c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x109e1c (PopPre 0x109e1c) (popR64Effect 0x109e1c 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x109e1e (popR64Effect 0x109e1e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x109e1e (popR64Effect 0x109e1e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x109e1e (PopPre 0x109e1e) (popR64Effect 0x109e1e 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x109e20 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[103]
    (.letOp (n := 106) (.out 0x109e20 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x109e20 (RetPre 0x109e20) (retEffect) (Reg.operands [.gpr 4] [])) #v[103]
    (.terminate (.ret (RegMap.args [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 108) (some ⟨105, by decide⟩))))))))))))))))))))))))

def bytes_l109dcf_1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x30, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0xC3]

theorem code_l109dcf_1 : ∀ x ∈ codeRange 0x109e10 bytes_l109dcf_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9e10 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109dcf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109dcf (StorePre 0x109dcf 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dcf + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109dcf 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x109dd3 (fun s => s.RIP = 0x109dd3) (leaR64Effect 0x109dd3 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x109dd8 (movzxR32M8Effect 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x109dd8 (LoadPre 0x109dd8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109dd8 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109dd8 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x109ddd (xorR32R32Effect 0x109ddd 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x109ddd (fun s => s.RIP = 0x109ddd) (xorR32R32Effect 0x109ddd 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x109ddf (xorR32R32Effect 0x109ddf 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x109ddf (fun s => s.RIP = 0x109ddf) (xorR32R32Effect 0x109ddf 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x109de1 (testR8R8Effect 0x109de1 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x109de1 (fun s => s.RIP = 0x109de1) (testR8R8Effect 0x109de1 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x109de3 (atFlags (condHolds 5) (cmovR64R64Effect 0x109de3 4 6 14)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[59, 14, 61]
    (.letOp (n := 64) (.exec 0x109de3 (fun s => s.RIP = 0x109de3) (atFlags (condHolds 5) (cmovR64R64Effect 0x109de3 4 6 14)) (Reg.operands [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 14, 61]
    (.letOp (n := 65) (.out 0x109de7 (xorR32R32Effect 0x109de7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 66) (.exec 0x109de7 (fun s => s.RIP = 0x109de7) (xorR32R32Effect 0x109de7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 67) (.out 0x109de9 (testR8R8Effect 0x109de9 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 68) (.exec 0x109de9 (fun s => s.RIP = 0x109de9) (testR8R8Effect 0x109de9 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 69) (.out 0x109deb (atFlags (condHolds 5) (cmovR64R64Effect 0x109deb 4 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[65, 15, 67]
    (.letOp (n := 70) (.exec 0x109deb (fun s => s.RIP = 0x109deb) (atFlags (condHolds 5) (cmovR64R64Effect 0x109deb 4 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 15, 67]
    (.letOp (n := 71) (.out 0x109def (xorR32R32Effect 0x109def 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 72) (.exec 0x109def (fun s => s.RIP = 0x109def) (xorR32R32Effect 0x109def 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 73) (.out 0x109df2 (testR8R8Effect 0x109df2 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x109df2 (fun s => s.RIP = 0x109df2) (testR8R8Effect 0x109df2 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x109df4 (atFlags (condHolds 5) (cmovR64R64Effect 0x109df4 4 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[71, 12, 73]
    (.letOp (n := 76) (.exec 0x109df4 (fun s => s.RIP = 0x109df4) (atFlags (condHolds 5) (cmovR64R64Effect 0x109df4 4 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 12, 73]
    (.letOp (n := 77) (.out 0x109df8 (testR8R8Effect 0x109df8 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 78) (.exec 0x109df8 (fun s => s.RIP = 0x109df8) (testR8R8Effect 0x109df8 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 79) (.out 0x109dfa (atFlags (condHolds 5) (cmovR64R64Effect 0x109dfa 4 2 13)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[57, 13, 77]
    (.letOp (n := 80) (.exec 0x109dfa (fun s => s.RIP = 0x109dfa) (atFlags (condHolds 5) (cmovR64R64Effect 0x109dfa 4 2 13)) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 13, 77]
    (.letOp (n := 81) (.exec 0x109dfe (StorePre 0x109dfe 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109dfe + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109dfe 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 82) (.exec 0x109e01 (StorePre 0x109e01 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109e01 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e01 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 83) (.exec 0x109e05 (StorePre 0x109e05 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109e05 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e05 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 84) (.exec 0x109e09 (StorePre 0x109e09 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109e09 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e09 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 85) (.exec 0x109e0d (StorePre 0x109e0d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109e0d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109e0d 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (b_l109dcf_1)))))))))))))))))))))))))))))))))

def bytes_l109dcf : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07, 0x31, 0xD2,
    0x31, 0xF6, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xF6, 0x31, 0xFF, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFF,
    0x45, 0x31, 0xC0, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xC4, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xD5, 0x48,
    0x89, 0x33, 0x48, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x43, 0x10, 0x48, 0x89, 0x53, 0x18, 0x88, 0x43,
    0x20] ++ bytes_l109dcf_1

theorem code_l109dcf : ∀ x ∈ codeRange 0x109dcf bytes_l109dcf, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9dcf 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109dcf_1

@[cfg_block] def b_l109e30 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109e30 (movR64M64Effect 0x109e30 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 54) (.exec 0x109e30 (LoadPre 0x109e30 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e30 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e30 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x109e34 (bswapR64Effect 0x109e34 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x109e34 (fun s => s.RIP = 0x109e34) (bswapR64Effect 0x109e34 3 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.out 0x109e37 (movR64M64Effect 0x109e37 2 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 58) (.exec 0x109e37 (LoadPre 0x109e37 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e37 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e37 2 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x109e3b (bswapR64Effect 0x109e3b 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x109e3b (fun s => s.RIP = 0x109e3b) (bswapR64Effect 0x109e3b 3 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 61) (.out 0x109e3e (movR64R64Effect 0x109e3e 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 62) (.exec 0x109e3e (fun s => s.RIP = 0x109e3e) (movR64R64Effect 0x109e3e 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 63) (.out 0x109e41 (movR64M64Effect 0x109e41 7 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 64) (.exec 0x109e41 (LoadPre 0x109e41 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e41 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e41 7 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x109e45 (bswapR64Effect 0x109e45 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x109e45 (fun s => s.RIP = 0x109e45) (bswapR64Effect 0x109e45 3 7) (Reg.operands [.gpr 7] [])) #v[63]
    (.letOp (n := 67) (.out 0x109e48 (movR64M64Effect 0x109e48 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 68) (.exec 0x109e48 (LoadPre 0x109e48 (fun s => AddrMode.addr (.base 6 .none) s (0x109e48 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e48 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109e4b (bswapR64Effect 0x109e4b 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 70) (.exec 0x109e4b (fun s => s.RIP = 0x109e4b) (bswapR64Effect 0x109e4b 3 6) (Reg.operands [.gpr 6] [])) #v[67]
    (.letOp (n := 71) (.exec 0x109e4e (StorePre 0x109e4e 3 (fun s => AddrMode.addr (.base 0 .none) s (0x109e4e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109e4e 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[55, 61]
    (.letOp (n := 72) (.exec 0x109e51 (StorePre 0x109e51 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x109e51 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e51 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[59, 61]
    (.letOp (n := 73) (.exec 0x109e55 (StorePre 0x109e55 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x109e55 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e55 7 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[65, 61]
    (.letOp (n := 74) (.exec 0x109e59 (StorePre 0x109e59 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x109e59 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109e59 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[69, 61]
    (.letOp (n := 75) (.out 0x109e5d (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 76) (.out 0x109e5d (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 77) (.exec 0x109e5d (RetPre 0x109e5d) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 61), (1, 55), (2, 59), (3, 3), (4, 76), (5, 5), (6, 69), (7, 65), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l109e30 : List UInt8 :=
  [0x48, 0x8B, 0x4E, 0x18, 0x48, 0x0F, 0xC9, 0x48, 0x8B, 0x56, 0x10, 0x48, 0x0F, 0xCA, 0x48, 0x89,
    0xF8, 0x48, 0x8B, 0x7E, 0x08, 0x48, 0x0F, 0xCF, 0x48, 0x8B, 0x36, 0x48, 0x0F, 0xCE, 0x48, 0x89,
    0x08, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x78, 0x10, 0x48, 0x89, 0x70, 0x18, 0xC3]

theorem code_l109e30 : ∀ x ∈ codeRange 0x109e30 bytes_l109e30, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9e30 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109e60_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x109eef (addR64R64Effect 0x109eef 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[124, 73]
    (.letOp (n := 131) (.exec 0x109eef (fun s => s.RIP = 0x109eef) (addR64R64Effect 0x109eef 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[124, 73]
    (.letOp (n := 132) (.out 0x109ef2 (addR64Imm8Effect 0x109ef2 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[130]
    (.letOp (n := 133) (.exec 0x109ef2 (fun s => s.RIP = 0x109ef2) (addR64Imm8Effect 0x109ef2 2 0x2) (Reg.operands [.gpr 2] [])) #v[130]
    (.letOp (n := 134) (.out 0x109ef6 (orR64R64Effect 0x109ef6 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[132, 128]
    (.letOp (n := 135) (.exec 0x109ef6 (fun s => s.RIP = 0x109ef6) (orR64R64Effect 0x109ef6 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[132, 128]
    (.letOp (n := 136) (.out 0x109ef9 (shrR64Effect 0x109ef9 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[134]
    (.letOp (n := 137) (.exec 0x109ef9 (fun s => s.RIP = 0x109ef9) (shrR64Effect 0x109ef9 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 138) (.exec 0x109efd (StorePre 0x109efd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109efd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109efd 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[136, 63]
    (.letOp (n := 139) (.out 0x109f02 (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[97, 63]
    (.letOp (n := 140) (.exec 0x109f02 (LoadPre 0x109f02 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f02 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109f02 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[97, 63]
    (.letOp (n := 141) (.out 0x109f07 (sarR64Effect 0x109f07 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[139]
    (.letOp (n := 142) (.exec 0x109f07 (fun s => s.RIP = 0x109f07) (sarR64Effect 0x109f07 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 143) (.out 0x109f0b (addR64R64Effect 0x109f0b 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[141, 71]
    (.letOp (n := 144) (.exec 0x109f0b (fun s => s.RIP = 0x109f0b) (addR64R64Effect 0x109f0b 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[141, 71]
    (.letOp (n := 145) (.out 0x109f0e (incR64Effect 0x109f0e 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[143]
    (.letOp (n := 146) (.exec 0x109f0e (fun s => s.RIP = 0x109f0e) (incR64Effect 0x109f0e 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x109f11 (movR64R64Effect 0x109f11 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 148) (.exec 0x109f11 (fun s => s.RIP = 0x109f11) (movR64R64Effect 0x109f11 2 14) (Reg.operands [.gpr 14] [])) #v[71]
    (.letOp (n := 149) (.out 0x109f14 (notR64Effect 0x109f14 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 150) (.exec 0x109f14 (fun s => s.RIP = 0x109f14) (notR64Effect 0x109f14 2) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x109f17 (orR64R64Effect 0x109f17 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[149, 145]
    (.letOp (n := 152) (.exec 0x109f17 (fun s => s.RIP = 0x109f17) (orR64R64Effect 0x109f17 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[149, 145]
    (.letOp (n := 153) (.out 0x109f1a (shrR64Effect 0x109f1a 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[151]
    (.letOp (n := 154) (.exec 0x109f1a (fun s => s.RIP = 0x109f1a) (shrR64Effect 0x109f1a 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.exec 0x109f1e (StorePre 0x109f1e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f1e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f1e 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[153, 63]
    (.letOp (n := 156) (.out 0x109f23 (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 157) (.exec 0x109f23 (LoadPre 0x109f23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109f23 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109f23 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 158) (.out 0x109f28 (andAlImm8Effect 0x109f28 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[156]
    (.letOp (n := 159) (.exec 0x109f28 (fun s => s.RIP = 0x109f28) (andAlImm8Effect 0x109f28 0x1) (Reg.operands [.gpr 0] [])) #v[156]
    (.letOp (n := 160) (.out 0x109f2a (movzxR32R8Effect 0x109f2a 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[158]
    (.letOp (n := 161) (.exec 0x109f2a (fun s => s.RIP = 0x109f2a) (movzxR32R8Effect 0x109f2a 3 7 0) (Reg.operands [.gpr 0] [])) #v[158]
    (.letOp (n := 162) (.out 0x109f2d (callEffect (fun _ => 0x127d50) 0x109f32) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 163) (.exec 0x109f2d (PushPre 0x109f2d 5) (callEffect (fun _ => 0x127d50) 0x109f32) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 164) (.const ⟨64, 0x109f32⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 158), (1, 145), (2, 153), (3, 65), (4, 162), (5, 5), (6, 128), (7, 160), (8, 8), (9, 9), (10, 10), (11, 11), (12, 77), (13, 81), (14, 71), (15, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 165⟩ { target := .l109f32, kept := #v[], arity := rfl, guard := some (Fin.last 164) }))))))))))))))))))))))))))))))))))))

def bytes_l109e60_2 : List UInt8 :=
  [0x4C, 0x01, 0xFA, 0x48, 0x83, 0xC2, 0x02, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89,
    0x54, 0x24, 0x08, 0x48, 0x2B, 0x4C, 0x24, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xF1, 0x48,
    0xFF, 0xC1, 0x4C, 0x89, 0xF2, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xCA, 0x48, 0xC1, 0xEA, 0x3F, 0x48,
    0x89, 0x54, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x1E,
    0xDE, 0x01, 0x00]

theorem code_l109e60_2 : ∀ x ∈ codeRange 0x109eef bytes_l109e60_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9eef 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109e60_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x109ea1 (shrR64Effect 0x109ea1 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 94) (.exec 0x109ea1 (fun s => s.RIP = 0x109ea1) (shrR64Effect 0x109ea1 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.exec 0x109ea5 (StorePre 0x109ea5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ea5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ea5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 63]
    (.letOp (n := 96) (.exec 0x109eaa (fun s => s.RIP = 0x109eaa) (leaR64Effect 0x109eaa 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 97) (.out 0x109eaf (xorR32R32Effect 0x109eaf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[93, 93]
    (.letOp (n := 98) (.exec 0x109eaf (fun s => s.RIP = 0x109eaf) (xorR32R32Effect 0x109eaf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[93, 93]
    (.letOp (n := 99) (.out 0x109eb1 (xorR32R32Effect 0x109eb1 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 100) (.exec 0x109eb1 (fun s => s.RIP = 0x109eb1) (xorR32R32Effect 0x109eb1 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 101) (.out 0x109eb3 (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[99, 63]
    (.letOp (n := 102) (.exec 0x109eb3 (LoadPre 0x109eb3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109eb3 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109eb3 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[99, 63]
    (.letOp (n := 103) (.out 0x109eb8 (sarR64Effect 0x109eb8 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[101]
    (.letOp (n := 104) (.exec 0x109eb8 (fun s => s.RIP = 0x109eb8) (sarR64Effect 0x109eb8 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.out 0x109ebc (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 106) (.exec 0x109ebc (fun s => s.RIP = 0x109ebc) (movR64Imm64Effect 0x109ebc 6 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 107) (.out 0x109ec6 (addR64R64Effect 0x109ec6 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[105, 77]
    (.letOp (n := 108) (.exec 0x109ec6 (fun s => s.RIP = 0x109ec6) (addR64R64Effect 0x109ec6 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[105, 77]
    (.letOp (n := 109) (.out 0x109ec9 (addR64R64Effect 0x109ec9 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[107, 103]
    (.letOp (n := 110) (.exec 0x109ec9 (fun s => s.RIP = 0x109ec9) (addR64R64Effect 0x109ec9 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[107, 103]
    (.letOp (n := 111) (.out 0x109ecc (movR64R64Effect 0x109ecc 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[77]
    (.letOp (n := 112) (.exec 0x109ecc (fun s => s.RIP = 0x109ecc) (movR64R64Effect 0x109ecc 2 12) (Reg.operands [.gpr 12] [])) #v[77]
    (.letOp (n := 113) (.out 0x109ecf (notR64Effect 0x109ecf 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[111]
    (.letOp (n := 114) (.exec 0x109ecf (fun s => s.RIP = 0x109ecf) (notR64Effect 0x109ecf 2) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 115) (.out 0x109ed2 (orR64R64Effect 0x109ed2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[113, 109]
    (.letOp (n := 116) (.exec 0x109ed2 (fun s => s.RIP = 0x109ed2) (orR64R64Effect 0x109ed2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[113, 109]
    (.letOp (n := 117) (.out 0x109ed5 (shrR64Effect 0x109ed5 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[115]
    (.letOp (n := 118) (.exec 0x109ed5 (fun s => s.RIP = 0x109ed5) (shrR64Effect 0x109ed5 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.exec 0x109ed9 (StorePre 0x109ed9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ed9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ed9 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[117, 63]
    (.letOp (n := 120) (.out 0x109ede (xorR32R32Effect 0x109ede 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[117, 117]
    (.letOp (n := 121) (.exec 0x109ede (fun s => s.RIP = 0x109ede) (xorR32R32Effect 0x109ede 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[117, 117]
    (.letOp (n := 122) (.out 0x109ee0 (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[120, 63]
    (.letOp (n := 123) (.exec 0x109ee0 (LoadPre 0x109ee0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ee0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ee0 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[120, 63]
    (.letOp (n := 124) (.out 0x109ee5 (sarR64Effect 0x109ee5 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[122]
    (.letOp (n := 125) (.exec 0x109ee5 (fun s => s.RIP = 0x109ee5) (sarR64Effect 0x109ee5 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 126) (.out 0x109ee9 (movR64R64Effect 0x109ee9 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 127) (.exec 0x109ee9 (fun s => s.RIP = 0x109ee9) (movR64R64Effect 0x109ee9 6 15) (Reg.operands [.gpr 15] [])) #v[73]
    (.letOp (n := 128) (.out 0x109eec (notR64Effect 0x109eec 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[126]
    (.letOp (n := 129) (.exec 0x109eec (fun s => s.RIP = 0x109eec) (notR64Effect 0x109eec 6) (Reg.operands [.gpr 6] [])) #v[126]
    (b_l109e60_2)))))))))))))))))))))))))))))))))))))

def bytes_l109e60_1 : List UInt8 :=
  [0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31, 0xC9,
    0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24, 0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0xBE, 0xC5, 0x5F, 0xB7,
    0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x01, 0xE6, 0x48, 0x01, 0xD6, 0x4C, 0x89, 0xE2, 0x48, 0xF7,
    0xD2, 0x48, 0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x31, 0xD2, 0x48,
    0x2B, 0x54, 0x24, 0x08, 0x48, 0xC1, 0xFA, 0x3F, 0x4C, 0x89, 0xFE, 0x48, 0xF7, 0xD6] ++ bytes_l109e60_2

theorem code_l109e60_1 : ∀ x ∈ codeRange 0x109ea1 bytes_l109e60_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9ea1 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109e60_2

@[cfg_block] def b_l109e60 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109e60 (pushR64Effect 0x109e60 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109e60 (PushPre 0x109e60 2) (pushR64Effect 0x109e60 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109e62 (pushR64Effect 0x109e62 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109e62 (PushPre 0x109e62 2) (pushR64Effect 0x109e62 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109e64 (pushR64Effect 0x109e64 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109e64 (PushPre 0x109e64 2) (pushR64Effect 0x109e64 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109e66 (pushR64Effect 0x109e66 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109e66 (PushPre 0x109e66 2) (pushR64Effect 0x109e66 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109e68 (pushR64Effect 0x109e68 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109e68 (PushPre 0x109e68 1) (pushR64Effect 0x109e68 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109e69 (subR64Imm8Effect 0x109e69 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109e69 (fun s => s.RIP = 0x109e69) (subR64Imm8Effect 0x109e69 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109e6d (movR64R64Effect 0x109e6d 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x109e6d (fun s => s.RIP = 0x109e6d) (movR64R64Effect 0x109e6d 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x109e70 (movR64M64Effect 0x109e70 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x109e70 (LoadPre 0x109e70 (fun s => AddrMode.addr (.base 6 .none) s (0x109e70 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109e70 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109e73 (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 70) (.exec 0x109e73 (LoadPre 0x109e73 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109e73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e73 15 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x109e77 (bswapR64Effect 0x109e77 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 72) (.exec 0x109e77 (fun s => s.RIP = 0x109e77) (bswapR64Effect 0x109e77 3 14) (Reg.operands [.gpr 14] [])) #v[67]
    (.letOp (n := 73) (.out 0x109e7a (bswapR64Effect 0x109e7a 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 74) (.exec 0x109e7a (fun s => s.RIP = 0x109e7a) (bswapR64Effect 0x109e7a 3 15) (Reg.operands [.gpr 15] [])) #v[69]
    (.letOp (n := 75) (.out 0x109e7d (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 76) (.exec 0x109e7d (LoadPre 0x109e7d (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109e7d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e7d 12 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x109e81 (bswapR64Effect 0x109e81 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[75]
    (.letOp (n := 78) (.exec 0x109e81 (fun s => s.RIP = 0x109e81) (bswapR64Effect 0x109e81 3 12) (Reg.operands [.gpr 12] [])) #v[75]
    (.letOp (n := 79) (.out 0x109e84 (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 6] []) (.reg (.gpr 13))) #v[6]
    (.letOp (n := 80) (.exec 0x109e84 (LoadPre 0x109e84 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109e84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109e84 13 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 81) (.out 0x109e88 (bswapR64Effect 0x109e88 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[79]
    (.letOp (n := 82) (.exec 0x109e88 (fun s => s.RIP = 0x109e88) (bswapR64Effect 0x109e88 3 13) (Reg.operands [.gpr 13] [])) #v[79]
    (.letOp (n := 83) (.out 0x109e8b (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 84) (.exec 0x109e8b (fun s => s.RIP = 0x109e8b) (movR64Imm64Effect 0x109e8b 0 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 85) (.out 0x109e95 (addR64R64Effect 0x109e95 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[83, 81]
    (.letOp (n := 86) (.exec 0x109e95 (fun s => s.RIP = 0x109e95) (addR64R64Effect 0x109e95 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[83, 81]
    (.letOp (n := 87) (.out 0x109e98 (movR64R64Effect 0x109e98 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[81]
    (.letOp (n := 88) (.exec 0x109e98 (fun s => s.RIP = 0x109e98) (movR64R64Effect 0x109e98 1 13) (Reg.operands [.gpr 13] [])) #v[81]
    (.letOp (n := 89) (.out 0x109e9b (notR64Effect 0x109e9b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x109e9b (fun s => s.RIP = 0x109e9b) (notR64Effect 0x109e9b 1) (Reg.operands [.gpr 1] [])) #v[87]
    (.letOp (n := 91) (.out 0x109e9e (orR64R64Effect 0x109e9e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x109e9e (fun s => s.RIP = 0x109e9e) (orR64R64Effect 0x109e9e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[89, 85]
    (b_l109e60_1))))))))))))))))))))))))))))))))))))))))

def bytes_l109e60 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x48, 0x89, 0xFB,
    0x4C, 0x8B, 0x36, 0x4C, 0x8B, 0x7E, 0x08, 0x49, 0x0F, 0xCE, 0x49, 0x0F, 0xCF, 0x4C, 0x8B, 0x66,
    0x10, 0x49, 0x0F, 0xCC, 0x4C, 0x8B, 0x6E, 0x18, 0x49, 0x0F, 0xCD, 0x48, 0xB8, 0xBF, 0xBE, 0xC9,
    0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x4C, 0x01, 0xE8, 0x4C, 0x89, 0xE9, 0x48, 0xF7, 0xD1, 0x48, 0x09,
    0xC1] ++ bytes_l109e60_1

theorem code_l109e60 : ∀ x ∈ codeRange 0x109e60 bytes_l109e60, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9e60 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109e60_1

@[cfg_block] def b_l109f32 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x109f32 (StorePre 0x109f32 3 (fun s => AddrMode.addr (.base 3 .none) s (0x109f32 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109f32 13 (.base 3 .none)) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 54) (.exec 0x109f35 (StorePre 0x109f35 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x109f35 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f35 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 55) (.exec 0x109f39 (StorePre 0x109f39 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x109f39 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f39 15 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 56) (.exec 0x109f3d (StorePre 0x109f3d 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x109f3d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109f3d 14 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 57) (.exec 0x109f41 (StorePre 0x109f41 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x109f41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x109f41 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 58) (.out 0x109f44 (movR64R64Effect 0x109f44 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 59) (.exec 0x109f44 (fun s => s.RIP = 0x109f44) (movR64R64Effect 0x109f44 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x109f47 (addR64Imm8Effect 0x109f47 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x109f47 (fun s => s.RIP = 0x109f47) (addR64Imm8Effect 0x109f47 4 0x10) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x109f4b (popR64Effect 0x109f4b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.out 0x109f4b (popR64Effect 0x109f4b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x109f4b (PopPre 0x109f4b) (popR64Effect 0x109f4b 1 3) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x109f4c (popR64Effect 0x109f4c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[63]
    (.letOp (n := 66) (.out 0x109f4c (popR64Effect 0x109f4c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x109f4c (PopPre 0x109f4c) (popR64Effect 0x109f4c 2 12) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x109f4e (popR64Effect 0x109f4e 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[66]
    (.letOp (n := 69) (.out 0x109f4e (popR64Effect 0x109f4e 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x109f4e (PopPre 0x109f4e) (popR64Effect 0x109f4e 2 13) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x109f50 (popR64Effect 0x109f50 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[69]
    (.letOp (n := 72) (.out 0x109f50 (popR64Effect 0x109f50 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x109f50 (PopPre 0x109f50) (popR64Effect 0x109f50 2 14) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x109f52 (popR64Effect 0x109f52 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 75) (.out 0x109f52 (popR64Effect 0x109f52 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x109f52 (PopPre 0x109f52) (popR64Effect 0x109f52 2 15) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x109f54 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[75]
    (.letOp (n := 78) (.out 0x109f54 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x109f54 (RetPre 0x109f54) (retEffect) (Reg.operands [.gpr 4] [])) #v[75]
    (.terminate (.ret (RegMap.args [(0, 58), (1, 1), (2, 2), (3, 62), (4, 78), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 65), (13, 68), (14, 71), (15, 74), (22, 22), (39, 39), (50, 50), (51, 51)] 80) (some ⟨77, by decide⟩)))))))))))))))))))))))))))))

def bytes_l109f32 : List UInt8 :=
  [0x4C, 0x89, 0x2B, 0x4C, 0x89, 0x63, 0x08, 0x4C, 0x89, 0x7B, 0x10, 0x4C, 0x89, 0x73, 0x18, 0x88,
    0x43, 0x20, 0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E,
    0x41, 0x5F, 0xC3]

theorem code_l109f32 : ∀ x ∈ codeRange 0x109f32 bytes_l109f32, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f32 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f60 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1099c0, RegMap.args (entryMap (live .l109f60)) 53⟩)

def bytes_l109f60 : List UInt8 :=
  [0xE9, 0x5B, 0xFA, 0xFF, 0xFF]

theorem code_l109f60 : ∀ x ∈ codeRange 0x109f60 bytes_l109f60, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f60 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f70 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l1099c0, RegMap.args (entryMap (live .l109f70)) 53⟩)

def bytes_l109f70 : List UInt8 :=
  [0xE9, 0x4B, 0xFA, 0xFF, 0xFF]

theorem code_l109f70 : ∀ x ∈ codeRange 0x109f70 bytes_l109f70, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9f70 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f80_2 : Block Op Label signature Reg.count 127 :=
  .letOp (n := 127) (.out 0x10a014 (orR64R64Effect 0x10a014 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[125, 120]
    (.letOp (n := 128) (.exec 0x10a014 (fun s => s.RIP = 0x10a014) (orR64R64Effect 0x10a014 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[125, 120]
    (.letOp (n := 129) (.out 0x10a017 (shrR64Effect 0x10a017 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[127]
    (.letOp (n := 130) (.exec 0x10a017 (fun s => s.RIP = 0x10a017) (shrR64Effect 0x10a017 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127]
    (.letOp (n := 131) (.exec 0x10a01b (StorePre 0x10a01b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a01b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a01b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[129, 65]
    (.letOp (n := 132) (.out 0x10a020 (movR64M64Effect 0x10a020 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 133) (.exec 0x10a020 (LoadPre 0x10a020 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a020 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a020 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 134) (.out 0x10a025 (movR64M64Effect 0x10a025 15 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 135) (.exec 0x10a025 (LoadPre 0x10a025 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a025 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a025 15 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 136) (.out 0x10a029 (decR64Effect 0x10a029 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[132]
    (.letOp (n := 137) (.exec 0x10a029 (fun s => s.RIP = 0x10a029) (decR64Effect 0x10a029 3) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 138) (.out 0x10a02c (shrR64Effect 0x10a02c 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[136]
    (.letOp (n := 139) (.exec 0x10a02c (fun s => s.RIP = 0x10a02c) (shrR64Effect 0x10a02c 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.out 0x10a030 (addR64R64Effect 0x10a030 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[138, 134]
    (.letOp (n := 141) (.exec 0x10a030 (fun s => s.RIP = 0x10a030) (addR64R64Effect 0x10a030 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[138, 134]
    (.letOp (n := 142) (.out 0x10a033 (movR64R64Effect 0x10a033 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[134]
    (.letOp (n := 143) (.exec 0x10a033 (fun s => s.RIP = 0x10a033) (movR64R64Effect 0x10a033 1 15) (Reg.operands [.gpr 15] [])) #v[134]
    (.letOp (n := 144) (.out 0x10a036 (notR64Effect 0x10a036 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[142]
    (.letOp (n := 145) (.exec 0x10a036 (fun s => s.RIP = 0x10a036) (notR64Effect 0x10a036 1) (Reg.operands [.gpr 1] [])) #v[142]
    (.letOp (n := 146) (.out 0x10a039 (orR64R64Effect 0x10a039 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3] []) (.reg (.gpr 1))) #v[144, 140]
    (.letOp (n := 147) (.exec 0x10a039 (fun s => s.RIP = 0x10a039) (orR64R64Effect 0x10a039 1 3) (Reg.operands [.gpr 1, .gpr 3] [])) #v[144, 140]
    (.letOp (n := 148) (.out 0x10a03c (shrR64Effect 0x10a03c 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[146]
    (.letOp (n := 149) (.exec 0x10a03c (fun s => s.RIP = 0x10a03c) (shrR64Effect 0x10a03c 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[146]
    (.letOp (n := 150) (.exec 0x10a040 (StorePre 0x10a040 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a040 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a040 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[148, 65]
    (.letOp (n := 151) (.out 0x10a045 (subR64M64Effect 0x10a045 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[112, 65]
    (.letOp (n := 152) (.exec 0x10a045 (LoadPre 0x10a045 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a045 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10a045 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 153) (.out 0x10a04a (shrR64Effect 0x10a04a 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x10a04a (fun s => s.RIP = 0x10a04a) (shrR64Effect 0x10a04a 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.out 0x10a04e (callEffect (fun _ => 0x127d50) 0x10a053) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 156) (.exec 0x10a04e (PushPre 0x10a04e 5) (callEffect (fun _ => 0x127d50) 0x10a053) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 157) (.const ⟨64, 0x10a053⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 148), (2, 120), (3, 140), (4, 155), (5, 114), (6, 6), (7, 153), (8, 8), (9, 9), (10, 10), (11, 11), (12, 89), (13, 97), (14, 68), (15, 134), (22, 22), (39, 39), (50, 50), (51, 51)] 158⟩ { target := .l10a053, kept := #v[], arity := rfl, guard := some (Fin.last 157) }))))))))))))))))))))))))))))))))

def bytes_l109f80_2 : List UInt8 :=
  [0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8B, 0x5C, 0x24,
    0x08, 0x4C, 0x8B, 0x7E, 0x18, 0x48, 0xFF, 0xCB, 0x48, 0xC1, 0xEB, 0x3F, 0x4C, 0x01, 0xFB, 0x4C,
    0x89, 0xF9, 0x48, 0xF7, 0xD1, 0x48, 0x09, 0xD9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24,
    0x08, 0x48, 0x2B, 0x7C, 0x24, 0x08, 0x48, 0xC1, 0xEF, 0x3F, 0xE8, 0xFD, 0xDC, 0x01, 0x00]

theorem code_l109f80_2 : ∀ x ∈ codeRange 0x10a014 bytes_l109f80_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa014 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109f80_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x109fc6 (movR64M64Effect 0x109fc6 12 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 90) (.exec 0x109fc6 (LoadPre 0x109fc6 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109fc6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109fc6 12 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 91) (.out 0x109fca (sarR64Effect 0x109fca 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 92) (.exec 0x109fca (fun s => s.RIP = 0x109fca) (sarR64Effect 0x109fca 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 93) (.out 0x109fce (movR64Imm64Effect 0x109fce 13 0x4551231950b75fc5) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 94) (.exec 0x109fce (fun s => s.RIP = 0x109fce) (movR64Imm64Effect 0x109fce 13 0x4551231950b75fc5) (Reg.operands [] [])) #v[]
    (.letOp (n := 95) (.out 0x109fd8 (addR64R64Effect 0x109fd8 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[93, 89]
    (.letOp (n := 96) (.exec 0x109fd8 (fun s => s.RIP = 0x109fd8) (addR64R64Effect 0x109fd8 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[93, 89]
    (.letOp (n := 97) (.out 0x109fdb (addR64R64Effect 0x109fdb 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[95, 91]
    (.letOp (n := 98) (.exec 0x109fdb (fun s => s.RIP = 0x109fdb) (addR64R64Effect 0x109fdb 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[95, 91]
    (.letOp (n := 99) (.out 0x109fde (movR64R64Effect 0x109fde 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[89]
    (.letOp (n := 100) (.exec 0x109fde (fun s => s.RIP = 0x109fde) (movR64R64Effect 0x109fde 1 12) (Reg.operands [.gpr 12] [])) #v[89]
    (.letOp (n := 101) (.out 0x109fe1 (notR64Effect 0x109fe1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[99]
    (.letOp (n := 102) (.exec 0x109fe1 (fun s => s.RIP = 0x109fe1) (notR64Effect 0x109fe1 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 103) (.out 0x109fe4 (orR64R64Effect 0x109fe4 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[101, 97]
    (.letOp (n := 104) (.exec 0x109fe4 (fun s => s.RIP = 0x109fe4) (orR64R64Effect 0x109fe4 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[101, 97]
    (.letOp (n := 105) (.out 0x109fe7 (shrR64Effect 0x109fe7 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[103]
    (.letOp (n := 106) (.exec 0x109fe7 (fun s => s.RIP = 0x109fe7) (shrR64Effect 0x109fe7 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[103]
    (.letOp (n := 107) (.exec 0x109feb (StorePre 0x109feb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109feb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109feb 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[105, 65]
    (.letOp (n := 108) (.out 0x109ff0 (xorR32R32Effect 0x109ff0 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[105, 105]
    (.letOp (n := 109) (.exec 0x109ff0 (fun s => s.RIP = 0x109ff0) (xorR32R32Effect 0x109ff0 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[105, 105]
    (.letOp (n := 110) (.out 0x109ff2 (subR64M64Effect 0x109ff2 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[108, 65]
    (.letOp (n := 111) (.exec 0x109ff2 (LoadPre 0x109ff2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ff2 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109ff2 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[108, 65]
    (.letOp (n := 112) (.out 0x109ff7 (xorR32R32Effect 0x109ff7 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 113) (.exec 0x109ff7 (fun s => s.RIP = 0x109ff7) (xorR32R32Effect 0x109ff7 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 114) (.out 0x109ff9 (movR64M64Effect 0x109ff9 5 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 115) (.exec 0x109ff9 (LoadPre 0x109ff9 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109ff9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109ff9 5 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 116) (.out 0x109ffd (sarR64Effect 0x109ffd 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 117) (.exec 0x109ffd (fun s => s.RIP = 0x109ffd) (sarR64Effect 0x109ffd 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 118) (.out 0x10a001 (leaR64Effect 0x10a001 2 (.sib 1 (some 5) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 5] []) (.reg (.gpr 2))) #v[116, 114]
    (.letOp (n := 119) (.exec 0x10a001 (fun s => s.RIP = 0x10a001) (leaR64Effect 0x10a001 2 (.sib 1 (some 5) 0 .none)) (Reg.operands [.gpr 1, .gpr 5] [])) #v[116, 114]
    (.letOp (n := 120) (.out 0x10a005 (addR64Imm8Effect 0x10a005 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[118]
    (.letOp (n := 121) (.exec 0x10a005 (fun s => s.RIP = 0x10a005) (addR64Imm8Effect 0x10a005 2 0x2) (Reg.operands [.gpr 2] [])) #v[118]
    (.letOp (n := 122) (.exec 0x10a009 (StorePre 0x10a009 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a009 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10a009 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[120, 65]
    (.letOp (n := 123) (.out 0x10a00e (movR64R64Effect 0x10a00e 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[114]
    (.letOp (n := 124) (.exec 0x10a00e (fun s => s.RIP = 0x10a00e) (movR64R64Effect 0x10a00e 1 5) (Reg.operands [.gpr 5] [])) #v[114]
    (.letOp (n := 125) (.out 0x10a011 (notR64Effect 0x10a011 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[123]
    (.letOp (n := 126) (.exec 0x10a011 (fun s => s.RIP = 0x10a011) (notR64Effect 0x10a011 1) (Reg.operands [.gpr 1] [])) #v[123]
    (b_l109f80_2))))))))))))))))))))))))))))))))))))))

def bytes_l109f80_1 : List UInt8 :=
  [0x4C, 0x8B, 0x66, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x49, 0xBD, 0xC5, 0x5F, 0xB7, 0x50, 0x19, 0x23,
    0x51, 0x45, 0x4D, 0x01, 0xE5, 0x49, 0x01, 0xCD, 0x4C, 0x89, 0xE1, 0x48, 0xF7, 0xD1, 0x4C, 0x09,
    0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24,
    0x08, 0x31, 0xFF, 0x48, 0x8B, 0x6E, 0x10, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x8D, 0x14, 0x29, 0x48,
    0x83, 0xC2, 0x02, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0xE9, 0x48, 0xF7, 0xD1] ++ bytes_l109f80_2

theorem code_l109f80_1 : ∀ x ∈ codeRange 0x109fc6 bytes_l109f80_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9fc6 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109f80_2

@[cfg_block] def b_l109f80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109f80 (pushR64Effect 0x109f80 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x109f80 (PushPre 0x109f80 1) (pushR64Effect 0x109f80 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x109f81 (pushR64Effect 0x109f81 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x109f81 (PushPre 0x109f81 2) (pushR64Effect 0x109f81 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x109f83 (pushR64Effect 0x109f83 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x109f83 (PushPre 0x109f83 2) (pushR64Effect 0x109f83 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x109f85 (pushR64Effect 0x109f85 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x109f85 (PushPre 0x109f85 2) (pushR64Effect 0x109f85 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x109f87 (pushR64Effect 0x109f87 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x109f87 (PushPre 0x109f87 2) (pushR64Effect 0x109f87 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x109f89 (pushR64Effect 0x109f89 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x109f89 (PushPre 0x109f89 1) (pushR64Effect 0x109f89 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x109f8a (subR64Imm8Effect 0x109f8a 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x109f8a (fun s => s.RIP = 0x109f8a) (subR64Imm8Effect 0x109f8a 4 0x28) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x109f8e (StorePre 0x109f8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x109f8e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109f8e 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 68) (.out 0x109f93 (movR64M64Effect 0x109f93 14 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 69) (.exec 0x109f93 (LoadPre 0x109f93 (fun s => AddrMode.addr (.base 6 .none) s (0x109f93 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109f93 14 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x109f96 (movR64Imm64Effect 0x109f96 1 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 71) (.exec 0x109f96 (fun s => s.RIP = 0x109f96) (movR64Imm64Effect 0x109f96 1 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x109fa0 (addR64R64Effect 0x109fa0 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x109fa0 (fun s => s.RIP = 0x109fa0) (addR64R64Effect 0x109fa0 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[70, 68]
    (.letOp (n := 74) (.exec 0x109fa3 (StorePre 0x109fa3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x109fa3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fa3 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 75) (.out 0x109fa8 (movR64R64Effect 0x109fa8 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 76) (.exec 0x109fa8 (fun s => s.RIP = 0x109fa8) (movR64R64Effect 0x109fa8 0 14) (Reg.operands [.gpr 14] [])) #v[68]
    (.letOp (n := 77) (.out 0x109fab (notR64Effect 0x109fab 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[75]
    (.letOp (n := 78) (.exec 0x109fab (fun s => s.RIP = 0x109fab) (notR64Effect 0x109fab 0) (Reg.operands [.gpr 0] [])) #v[75]
    (.letOp (n := 79) (.out 0x109fae (orR64R64Effect 0x109fae 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[77, 72]
    (.letOp (n := 80) (.exec 0x109fae (fun s => s.RIP = 0x109fae) (orR64R64Effect 0x109fae 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[77, 72]
    (.letOp (n := 81) (.out 0x109fb1 (shrR64Effect 0x109fb1 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 82) (.exec 0x109fb1 (fun s => s.RIP = 0x109fb1) (shrR64Effect 0x109fb1 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x109fb5 (StorePre 0x109fb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fb5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109fb5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 65]
    (.letOp (n := 84) (.exec 0x109fba (fun s => s.RIP = 0x109fba) (leaR64Effect 0x109fba 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 85) (.out 0x109fbf (xorR32R32Effect 0x109fbf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[72, 72]
    (.letOp (n := 86) (.exec 0x109fbf (fun s => s.RIP = 0x109fbf) (xorR32R32Effect 0x109fbf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[72, 72]
    (.letOp (n := 87) (.out 0x109fc1 (subR64M64Effect 0x109fc1 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[85, 65]
    (.letOp (n := 88) (.exec 0x109fc1 (LoadPre 0x109fc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109fc1 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109fc1 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 65]
    (b_l109f80_1))))))))))))))))))))))))))))))))))))

def bytes_l109f80 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x28, 0x48, 0x89,
    0x7C, 0x24, 0x20, 0x4C, 0x8B, 0x36, 0x48, 0xB9, 0xBF, 0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40,
    0x4C, 0x01, 0xF1, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xD0, 0x48, 0x09,
    0xC8, 0x48, 0xC1, 0xE8, 0x3F, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31,
    0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x08] ++ bytes_l109f80_1

theorem code_l109f80 : ∀ x ∈ codeRange 0x109f80 bytes_l109f80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9f80 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109f80_1

@[cfg_block] def b_l10a053 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a053 (notR8Effect 0x10a053 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a053 (fun s => s.RIP = 0x10a053) (notR8Effect 0x10a053 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a055 (andAlImm8Effect 0x10a055 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10a055 (fun s => s.RIP = 0x10a055) (andAlImm8Effect 0x10a055 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a057 (movzxR32R8Effect 0x10a057 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x10a057 (fun s => s.RIP = 0x10a057) (movzxR32R8Effect 0x10a057 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x10a05a (callEffect (fun _ => 0x127d50) 0x10a05f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10a05a (PushPre 0x10a05a 5) (callEffect (fun _ => 0x127d50) 0x10a05f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x10a05f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10a05f, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10a053 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xF1, 0xDC, 0x01, 0x00]

theorem code_l10a053 : ∀ x ∈ codeRange 0x10a053 bytes_l10a053, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa053 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a05f_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.out 0x10a0a8 (popR64Effect 0x10a0a8 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[86]
    (.letOp (n := 89) (.out 0x10a0a8 (popR64Effect 0x10a0a8 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x10a0a8 (PopPre 0x10a0a8) (popR64Effect 0x10a0a8 2 12) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x10a0aa (popR64Effect 0x10a0aa 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[89]
    (.letOp (n := 92) (.out 0x10a0aa (popR64Effect 0x10a0aa 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x10a0aa (PopPre 0x10a0aa) (popR64Effect 0x10a0aa 2 13) (Reg.operands [.gpr 4] [])) #v[89]
    (.letOp (n := 94) (.out 0x10a0ac (popR64Effect 0x10a0ac 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[92]
    (.letOp (n := 95) (.out 0x10a0ac (popR64Effect 0x10a0ac 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[92]
    (.letOp (n := 96) (.exec 0x10a0ac (PopPre 0x10a0ac) (popR64Effect 0x10a0ac 2 14) (Reg.operands [.gpr 4] [])) #v[92]
    (.letOp (n := 97) (.out 0x10a0ae (popR64Effect 0x10a0ae 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[95]
    (.letOp (n := 98) (.out 0x10a0ae (popR64Effect 0x10a0ae 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[95]
    (.letOp (n := 99) (.exec 0x10a0ae (PopPre 0x10a0ae) (popR64Effect 0x10a0ae 2 15) (Reg.operands [.gpr 4] [])) #v[95]
    (.letOp (n := 100) (.out 0x10a0b0 (popR64Effect 0x10a0b0 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[98]
    (.letOp (n := 101) (.out 0x10a0b0 (popR64Effect 0x10a0b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[98]
    (.letOp (n := 102) (.exec 0x10a0b0 (PopPre 0x10a0b0) (popR64Effect 0x10a0b0 1 5) (Reg.operands [.gpr 4] [])) #v[98]
    (.letOp (n := 103) (.out 0x10a0b1 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[101]
    (.letOp (n := 104) (.out 0x10a0b1 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[101]
    (.letOp (n := 105) (.exec 0x10a0b1 (RetPre 0x10a0b1) (retEffect) (Reg.operands [.gpr 4] [])) #v[101]
    (.terminate (.ret (RegMap.args [(0, 77), (1, 67), (2, 2), (3, 85), (4, 104), (5, 100), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 88), (13, 91), (14, 94), (15, 97), (22, 22), (39, 39), (50, 50), (51, 51)] 106) (some ⟨103, by decide⟩))))))))))))))))))))

def bytes_l10a05f_1 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10a05f_1 : ∀ x ∈ codeRange 0x10a0a8 bytes_l10a05f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0a8 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a05f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a05f (StorePre 0x10a05f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a05f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a05f 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x10a063 (fun s => s.RIP = 0x10a063) (leaR64Effect 0x10a063 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a068 (movzxR32M8Effect 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x10a068 (LoadPre 0x10a068 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a068 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a068 5 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a06d (movR64M64Effect 0x10a06d 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x10a06d (LoadPre 0x10a06d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a06d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a06d 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10a072 (testR8R8Effect 0x10a072 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 60) (.exec 0x10a072 (fun s => s.RIP = 0x10a072) (testR8R8Effect 0x10a072 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 61) (.out 0x10a074 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a074 4 14 1)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 14))) #v[14, 57, 59]
    (.letOp (n := 62) (.exec 0x10a074 (fun s => s.RIP = 0x10a074) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a074 4 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[14, 57, 59]
    (.letOp (n := 63) (.out 0x10a078 (testR8R8Effect 0x10a078 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 64) (.exec 0x10a078 (fun s => s.RIP = 0x10a078) (testR8R8Effect 0x10a078 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 65) (.out 0x10a07a (atFlags (condHolds 5) (cmovR64R64Effect 0x10a07a 4 12 13)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 12))) #v[12, 13, 63]
    (.letOp (n := 66) (.exec 0x10a07a (fun s => s.RIP = 0x10a07a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a07a 4 12 13)) (Reg.operands [.gpr 12, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[12, 13, 63]
    (.letOp (n := 67) (.out 0x10a07e (movR64M64Effect 0x10a07e 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 68) (.exec 0x10a07e (LoadPre 0x10a07e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a07e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a07e 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10a083 (testR8R8Effect 0x10a083 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 70) (.exec 0x10a083 (fun s => s.RIP = 0x10a083) (testR8R8Effect 0x10a083 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 71) (.out 0x10a085 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a085 4 5 1)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[5, 67, 69]
    (.letOp (n := 72) (.exec 0x10a085 (fun s => s.RIP = 0x10a085) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a085 4 5 1)) (Reg.operands [.gpr 5, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[5, 67, 69]
    (.letOp (n := 73) (.out 0x10a089 (testR8R8Effect 0x10a089 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x10a089 (fun s => s.RIP = 0x10a089) (testR8R8Effect 0x10a089 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x10a08b (atFlags (condHolds 5) (cmovR64R64Effect 0x10a08b 4 15 3)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 15))) #v[15, 3, 73]
    (.letOp (n := 76) (.exec 0x10a08b (fun s => s.RIP = 0x10a08b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a08b 4 15 3)) (Reg.operands [.gpr 15, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[15, 3, 73]
    (.letOp (n := 77) (.out 0x10a08f (movR64M64Effect 0x10a08f 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x10a08f (LoadPre 0x10a08f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a08f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a08f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10a094 (StorePre 0x10a094 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a094 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a094 14 (.base 0 .none)) (Reg.operands [.gpr 14, .gpr 0] [])) #v[61, 77]
    (.letOp (n := 80) (.exec 0x10a097 (StorePre 0x10a097 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a097 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a097 12 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 0] [])) #v[65, 77]
    (.letOp (n := 81) (.exec 0x10a09b (StorePre 0x10a09b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a09b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09b 5 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 5, .gpr 0] [])) #v[71, 77]
    (.letOp (n := 82) (.exec 0x10a09f (StorePre 0x10a09f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a09f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a09f 15 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[75, 77]
    (.letOp (n := 83) (.out 0x10a0a3 (addR64Imm8Effect 0x10a0a3 4 0x28) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x10a0a3 (fun s => s.RIP = 0x10a0a3) (addR64Imm8Effect 0x10a0a3 4 0x28) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10a0a7 (popR64Effect 0x10a0a7 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[83]
    (.letOp (n := 86) (.out 0x10a0a7 (popR64Effect 0x10a0a7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x10a0a7 (PopPre 0x10a0a7) (popR64Effect 0x10a0a7 1 3) (Reg.operands [.gpr 4] [])) #v[83]
    (b_l10a05f_1)))))))))))))))))))))))))))))))))))

def bytes_l10a05f : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x44, 0x24, 0x07, 0x0F, 0xB6, 0x44, 0x24, 0x07, 0x48, 0x8B,
    0x4C, 0x24, 0x18, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xF1, 0x84, 0xC0, 0x4D, 0x0F, 0x45, 0xE5, 0x48,
    0x8B, 0x4C, 0x24, 0x10, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xE9, 0x84, 0xC0, 0x4C, 0x0F, 0x45, 0xFB,
    0x48, 0x8B, 0x44, 0x24, 0x20, 0x4C, 0x89, 0x30, 0x4C, 0x89, 0x60, 0x08, 0x48, 0x89, 0x68, 0x10,
    0x4C, 0x89, 0x78, 0x18, 0x48, 0x83, 0xC4, 0x28, 0x5B] ++ bytes_l10a05f_1

theorem code_l10a05f : ∀ x ∈ codeRange 0x10a05f bytes_l10a05f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa05f 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a05f_1

@[cfg_block] def b_l10a0c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a0c0 (pushR64Effect 0x10a0c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x10a0c0 (PushPre 0x10a0c0 2) (pushR64Effect 0x10a0c0 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x10a0c2 (pushR64Effect 0x10a0c2 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x10a0c2 (PushPre 0x10a0c2 2) (pushR64Effect 0x10a0c2 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x10a0c4 (pushR64Effect 0x10a0c4 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x10a0c4 (PushPre 0x10a0c4 2) (pushR64Effect 0x10a0c4 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x10a0c6 (pushR64Effect 0x10a0c6 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x10a0c6 (PushPre 0x10a0c6 2) (pushR64Effect 0x10a0c6 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x10a0c8 (pushR64Effect 0x10a0c8 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x10a0c8 (PushPre 0x10a0c8 1) (pushR64Effect 0x10a0c8 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x10a0c9 (subR64Imm8Effect 0x10a0c9 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x10a0c9 (fun s => s.RIP = 0x10a0c9) (subR64Imm8Effect 0x10a0c9 4 0x30) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x10a0cd (movR64R64Effect 0x10a0cd 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 66) (.exec 0x10a0cd (fun s => s.RIP = 0x10a0cd) (movR64R64Effect 0x10a0cd 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 67) (.out 0x10a0d0 (leaR64Effect 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 68) (.exec 0x10a0d0 (fun s => s.RIP = 0x10a0d0) (leaR64Effect 0x10a0d0 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 69) (.out 0x10a0d5 (movR64Imm64Effect 0x10a0d5 1 0xb4f20099aa774ec1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 70) (.exec 0x10a0d5 (fun s => s.RIP = 0x10a0d5) (movR64Imm64Effect 0x10a0d5 1 0xb4f20099aa774ec1) (Reg.operands [] [])) #v[]
    (.letOp (n := 71) (.out 0x10a0df (movR64Imm32Effect 0x10a0df 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 72) (.exec 0x10a0df (fun s => s.RIP = 0x10a0df) (movR64Imm32Effect 0x10a0df 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10a0e6 (movR64Imm32Effect 0x10a0e6 8 0x202180) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 74) (.exec 0x10a0e6 (fun s => s.RIP = 0x10a0e6) (movR64Imm32Effect 0x10a0e6 8 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x10a0ed (callEffect (fun _ => 0x109490) 0x10a0f2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 76) (.exec 0x10a0ed (PushPre 0x10a0ed 5) (callEffect (fun _ => 0x109490) 0x10a0f2) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 77) (.const ⟨64, 0x10a0f2⟩) #v[]
    (.terminate (.call ⟨.l109490, RegMap.args [(1, 69), (2, 71), (3, 65), (4, 75), (5, 5), (6, 6), (7, 67), (8, 73), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l10a0f2, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10a0c0 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x30, 0x48, 0x89, 0xFB,
    0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0xB9, 0xC1, 0x4E, 0x77, 0xAA, 0x99, 0x00, 0xF2, 0xB4, 0x48,
    0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00, 0xE8, 0x9E, 0xF3,
    0xFF, 0xFF]

theorem code_l10a0c0 : ∀ x ∈ codeRange 0x10a0c0 bytes_l10a0c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0c0 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a0f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a0f2 (movR64M64Effect 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x10a0f2 (LoadPre 0x10a0f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10a0f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f2 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a0f7 (movR64M64Effect 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x10a0f7 (LoadPre 0x10a0f7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10a0f7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0f7 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a0fc (movR64M64Effect 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x10a0fc (LoadPre 0x10a0fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10a0fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a0fc 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10a101 (movR64M64Effect 0x10a101 13 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 60) (.exec 0x10a101 (LoadPre 0x10a101 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10a101 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10a101 13 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10a106 (movR32M32LowEffect 0x10a106 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x10a106 (LoadPre 0x10a106 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10a106 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10a106 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10a10a (callEffect (fun _ => 0x127d50) 0x10a10f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10a10a (PushPre 0x10a10a 5) (callEffect (fun _ => 0x127d50) 0x10a10f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10a10f⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 5), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 59), (14, 53), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10a10f, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10a0f2 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x08, 0x4C, 0x8B, 0x7C, 0x24, 0x10, 0x4C, 0x8B, 0x64, 0x24, 0x18, 0x4C,
    0x8B, 0x6C, 0x24, 0x20, 0x8B, 0x7C, 0x24, 0x28, 0xE8, 0x41, 0xDC, 0x01, 0x00]

theorem code_l10a0f2 : ∀ x ∈ codeRange 0x10a0f2 bytes_l10a0f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa0f2 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a10f_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.out 0x10a150 (movR64R64Effect 0x10a150 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 87) (.exec 0x10a150 (fun s => s.RIP = 0x10a150) (movR64R64Effect 0x10a150 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 88) (.out 0x10a153 (addR64Imm8Effect 0x10a153 4 0x30) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 89) (.exec 0x10a153 (fun s => s.RIP = 0x10a153) (addR64Imm8Effect 0x10a153 4 0x30) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x10a157 (popR64Effect 0x10a157 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[88]
    (.letOp (n := 91) (.out 0x10a157 (popR64Effect 0x10a157 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x10a157 (PopPre 0x10a157) (popR64Effect 0x10a157 1 3) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x10a158 (popR64Effect 0x10a158 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[91]
    (.letOp (n := 94) (.out 0x10a158 (popR64Effect 0x10a158 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x10a158 (PopPre 0x10a158) (popR64Effect 0x10a158 2 12) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x10a15a (popR64Effect 0x10a15a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[94]
    (.letOp (n := 97) (.out 0x10a15a (popR64Effect 0x10a15a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x10a15a (PopPre 0x10a15a) (popR64Effect 0x10a15a 2 13) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x10a15c (popR64Effect 0x10a15c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 100) (.out 0x10a15c (popR64Effect 0x10a15c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x10a15c (PopPre 0x10a15c) (popR64Effect 0x10a15c 2 14) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x10a15e (popR64Effect 0x10a15e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[100]
    (.letOp (n := 103) (.out 0x10a15e (popR64Effect 0x10a15e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x10a15e (PopPre 0x10a15e) (popR64Effect 0x10a15e 2 15) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x10a160 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[103]
    (.letOp (n := 106) (.out 0x10a160 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x10a160 (RetPre 0x10a160) (retEffect) (Reg.operands [.gpr 4] [])) #v[103]
    (.terminate (.ret (RegMap.args [(0, 86), (1, 55), (2, 79), (3, 90), (4, 106), (5, 5), (6, 63), (7, 69), (8, 75), (9, 9), (10, 10), (11, 11), (12, 93), (13, 96), (14, 99), (15, 102), (22, 22), (39, 39), (50, 50), (51, 51)] 108) (some ⟨105, by decide⟩))))))))))))))))))))))))

def bytes_l10a10f_1 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x30, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0xC3]

theorem code_l10a10f_1 : ∀ x ∈ codeRange 0x10a150 bytes_l10a10f_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa150 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a10f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10a10f (StorePre 0x10a10f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a10f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10a10f 4 0 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x10a113 (fun s => s.RIP = 0x10a113) (leaR64Effect 0x10a113 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a118 (movzxR32M8Effect 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10a118 (LoadPre 0x10a118 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x10a118 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10a118 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10a11d (xorR32R32Effect 0x10a11d 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x10a11d (fun s => s.RIP = 0x10a11d) (xorR32R32Effect 0x10a11d 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x10a11f (xorR32R32Effect 0x10a11f 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 60) (.exec 0x10a11f (fun s => s.RIP = 0x10a11f) (xorR32R32Effect 0x10a11f 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 61) (.out 0x10a121 (testR8R8Effect 0x10a121 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x10a121 (fun s => s.RIP = 0x10a121) (testR8R8Effect 0x10a121 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x10a123 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a123 4 6 14)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[59, 14, 61]
    (.letOp (n := 64) (.exec 0x10a123 (fun s => s.RIP = 0x10a123) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a123 4 6 14)) (Reg.operands [.gpr 6, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 14, 61]
    (.letOp (n := 65) (.out 0x10a127 (xorR32R32Effect 0x10a127 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 66) (.exec 0x10a127 (fun s => s.RIP = 0x10a127) (xorR32R32Effect 0x10a127 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 67) (.out 0x10a129 (testR8R8Effect 0x10a129 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 68) (.exec 0x10a129 (fun s => s.RIP = 0x10a129) (testR8R8Effect 0x10a129 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 69) (.out 0x10a12b (atFlags (condHolds 5) (cmovR64R64Effect 0x10a12b 4 7 15)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[65, 15, 67]
    (.letOp (n := 70) (.exec 0x10a12b (fun s => s.RIP = 0x10a12b) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a12b 4 7 15)) (Reg.operands [.gpr 7, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 15, 67]
    (.letOp (n := 71) (.out 0x10a12f (xorR32R32Effect 0x10a12f 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 72) (.exec 0x10a12f (fun s => s.RIP = 0x10a12f) (xorR32R32Effect 0x10a12f 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 73) (.out 0x10a132 (testR8R8Effect 0x10a132 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 74) (.exec 0x10a132 (fun s => s.RIP = 0x10a132) (testR8R8Effect 0x10a132 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 75) (.out 0x10a134 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a134 4 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[71, 12, 73]
    (.letOp (n := 76) (.exec 0x10a134 (fun s => s.RIP = 0x10a134) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a134 4 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[71, 12, 73]
    (.letOp (n := 77) (.out 0x10a138 (testR8R8Effect 0x10a138 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 78) (.exec 0x10a138 (fun s => s.RIP = 0x10a138) (testR8R8Effect 0x10a138 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[55, 55]
    (.letOp (n := 79) (.out 0x10a13a (atFlags (condHolds 5) (cmovR64R64Effect 0x10a13a 4 2 13)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[57, 13, 77]
    (.letOp (n := 80) (.exec 0x10a13a (fun s => s.RIP = 0x10a13a) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a13a 4 2 13)) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 13, 77]
    (.letOp (n := 81) (.exec 0x10a13e (StorePre 0x10a13e 3 (fun s => AddrMode.addr (.base 3 .none) s (0x10a13e + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a13e 6 (.base 3 .none)) (Reg.operands [.gpr 6, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 82) (.exec 0x10a141 (StorePre 0x10a141 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10a141 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a141 7 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[69, 3]
    (.letOp (n := 83) (.exec 0x10a145 (StorePre 0x10a145 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10a145 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a145 8 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 84) (.exec 0x10a149 (StorePre 0x10a149 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10a149 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a149 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 85) (.exec 0x10a14d (StorePre 0x10a14d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10a14d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a14d 3 0 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (b_l10a10f_1)))))))))))))))))))))))))))))))))

def bytes_l10a10f : List UInt8 :=
  [0x88, 0x44, 0x24, 0x07, 0x48, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07, 0x31, 0xD2,
    0x31, 0xF6, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xF6, 0x31, 0xFF, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFF,
    0x45, 0x31, 0xC0, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xC4, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xD5, 0x48,
    0x89, 0x33, 0x48, 0x89, 0x7B, 0x08, 0x4C, 0x89, 0x43, 0x10, 0x48, 0x89, 0x53, 0x18, 0x88, 0x43,
    0x20] ++ bytes_l10a10f_1

theorem code_l10a10f : ∀ x ∈ codeRange 0x10a10f bytes_l10a10f, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa10f 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a10f_1

@[cfg_block] def b_l10a170_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x10a209 (movzxR32R8Effect 0x10a209 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[126]
    (.letOp (n := 129) (.exec 0x10a209 (fun s => s.RIP = 0x10a209) (movzxR32R8Effect 0x10a209 3 7 0) (Reg.operands [.gpr 0] [])) #v[126]
    (.letOp (n := 130) (.out 0x10a20c (callEffect (fun _ => 0x127d50) 0x10a211) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 131) (.exec 0x10a20c (PushPre 0x10a20c 5) (callEffect (fun _ => 0x127d50) 0x10a211) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 132) (.const ⟨64, 0x10a211⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 126), (1, 109), (2, 113), (3, 3), (4, 130), (5, 5), (6, 121), (7, 128), (8, 104), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 133⟩ { target := .l10a211, kept := #v[], arity := rfl, guard := some (Fin.last 132) }))))))

def bytes_l10a170_2 : List UInt8 :=
  [0x0F, 0xB6, 0xF8, 0xE8, 0x3F, 0xDB, 0x01, 0x00]

theorem code_l10a170_2 : ∀ x ∈ codeRange 0x10a209 bytes_l10a170_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa209 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a170_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.out 0x10a1be (xorR32R32Effect 0x10a1be 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[71, 71]
    (.letOp (n := 91) (.exec 0x10a1be (fun s => s.RIP = 0x10a1be) (xorR32R32Effect 0x10a1be 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[71, 71]
    (.letOp (n := 92) (.out 0x10a1c0 (movR64M64Effect 0x10a1c0 6 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[7]
    (.letOp (n := 93) (.exec 0x10a1c0 (LoadPre 0x10a1c0 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a1c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1c0 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 94) (.out 0x10a1c4 (sarR64Effect 0x10a1c4 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[88]
    (.letOp (n := 95) (.exec 0x10a1c4 (fun s => s.RIP = 0x10a1c4) (sarR64Effect 0x10a1c4 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[88]
    (.letOp (n := 96) (.out 0x10a1c8 (movR64R64Effect 0x10a1c8 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[92]
    (.letOp (n := 97) (.exec 0x10a1c8 (fun s => s.RIP = 0x10a1c8) (movR64R64Effect 0x10a1c8 8 6) (Reg.operands [.gpr 6] [])) #v[92]
    (.letOp (n := 98) (.out 0x10a1cb (notR64Effect 0x10a1cb 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[96]
    (.letOp (n := 99) (.exec 0x10a1cb (fun s => s.RIP = 0x10a1cb) (notR64Effect 0x10a1cb 8) (Reg.operands [.gpr 8] [])) #v[96]
    (.letOp (n := 100) (.out 0x10a1ce (addR64R64Effect 0x10a1ce 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[98, 94]
    (.letOp (n := 101) (.exec 0x10a1ce (fun s => s.RIP = 0x10a1ce) (addR64R64Effect 0x10a1ce 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[98, 94]
    (.letOp (n := 102) (.out 0x10a1d1 (andR64R64Effect 0x10a1d1 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[100, 92]
    (.letOp (n := 103) (.exec 0x10a1d1 (fun s => s.RIP = 0x10a1d1) (andR64R64Effect 0x10a1d1 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[100, 92]
    (.letOp (n := 104) (.out 0x10a1d4 (shrR64Effect 0x10a1d4 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[102]
    (.letOp (n := 105) (.exec 0x10a1d4 (fun s => s.RIP = 0x10a1d4) (shrR64Effect 0x10a1d4 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.exec 0x10a1d8 (StorePre 0x10a1d8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1d8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1d8 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[104, 53]
    (.letOp (n := 107) (.out 0x10a1dc (subR64M64Effect 0x10a1dc 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[90, 53]
    (.letOp (n := 108) (.exec 0x10a1dc (LoadPre 0x10a1dc (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1dc + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1dc 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[90, 53]
    (.letOp (n := 109) (.out 0x10a1e0 (movR64M64Effect 0x10a1e0 1 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 110) (.exec 0x10a1e0 (LoadPre 0x10a1e0 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a1e0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a1e0 1 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 111) (.out 0x10a1e4 (sarR64Effect 0x10a1e4 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[107]
    (.letOp (n := 112) (.exec 0x10a1e4 (fun s => s.RIP = 0x10a1e4) (sarR64Effect 0x10a1e4 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[107]
    (.letOp (n := 113) (.out 0x10a1e8 (subR64R64Effect 0x10a1e8 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x10a1e8 (fun s => s.RIP = 0x10a1e8) (subR64R64Effect 0x10a1e8 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[111, 109]
    (.letOp (n := 115) (.out 0x10a1eb (movR64Imm64Effect 0x10a1eb 6 0x7fffffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 116) (.exec 0x10a1eb (fun s => s.RIP = 0x10a1eb) (movR64Imm64Effect 0x10a1eb 6 0x7fffffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 117) (.out 0x10a1f5 (addR64R64Effect 0x10a1f5 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x10a1f5 (fun s => s.RIP = 0x10a1f5) (addR64R64Effect 0x10a1f5 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x10a1f8 (orR64R64Effect 0x10a1f8 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[117, 109]
    (.letOp (n := 120) (.exec 0x10a1f8 (fun s => s.RIP = 0x10a1f8) (orR64R64Effect 0x10a1f8 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[117, 109]
    (.letOp (n := 121) (.out 0x10a1fb (shrR64Effect 0x10a1fb 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[119]
    (.letOp (n := 122) (.exec 0x10a1fb (fun s => s.RIP = 0x10a1fb) (shrR64Effect 0x10a1fb 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.exec 0x10a1ff (StorePre 0x10a1ff 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ff + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1ff 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[121, 53]
    (.letOp (n := 124) (.out 0x10a203 (movzxR32M8Effect 0x10a203 4 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 125) (.exec 0x10a203 (LoadPre 0x10a203 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a203 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a203 4 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 126) (.out 0x10a207 (andAlImm8Effect 0x10a207 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[124]
    (.letOp (n := 127) (.exec 0x10a207 (fun s => s.RIP = 0x10a207) (andAlImm8Effect 0x10a207 0x1) (Reg.operands [.gpr 0] [])) #v[124]
    (b_l10a170_2))))))))))))))))))))))))))))))))))))))

def bytes_l10a170_1 : List UInt8 :=
  [0x31, 0xD2, 0x48, 0x8B, 0x77, 0x10, 0x48, 0xC1, 0xF9, 0x3F, 0x49, 0x89, 0xF0, 0x49, 0xF7, 0xD0,
    0x49, 0x01, 0xC8, 0x49, 0x21, 0xF0, 0x49, 0xC1, 0xE8, 0x3F, 0x4C, 0x89, 0x04, 0x24, 0x48, 0x2B,
    0x14, 0x24, 0x48, 0x8B, 0x4F, 0x18, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0x29, 0xCA, 0x48, 0xBE, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x7F, 0x48, 0x01, 0xD6, 0x48, 0x09, 0xCE, 0x48, 0xC1, 0xEE,
    0x3F, 0x48, 0x89, 0x34, 0x24, 0x0F, 0xB6, 0x04, 0x24, 0x24, 0x01] ++ bytes_l10a170_2

theorem code_l10a170_1 : ∀ x ∈ codeRange 0x10a1be bytes_l10a170_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa1be 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a170_2

@[cfg_block] def b_l10a170 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a170 (pushR64Effect 0x10a170 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a170 (PushPre 0x10a170 1) (pushR64Effect 0x10a170 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a171 (movR64M64Effect 0x10a171 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x10a171 (LoadPre 0x10a171 (fun s => AddrMode.addr (.base 7 .none) s (0x10a171 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a171 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10a174 (movR64Imm64Effect 0x10a174 1 0xdfe92f46681b20a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x10a174 (fun s => s.RIP = 0x10a174) (movR64Imm64Effect 0x10a174 1 0xdfe92f46681b20a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a17e (subR64R64Effect 0x10a17e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10a17e (fun s => s.RIP = 0x10a17e) (subR64R64Effect 0x10a17e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x10a181 (andR64R64Effect 0x10a181 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[59, 55]
    (.letOp (n := 62) (.exec 0x10a181 (fun s => s.RIP = 0x10a181) (andR64R64Effect 0x10a181 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[59, 55]
    (.letOp (n := 63) (.out 0x10a184 (shrR64Effect 0x10a184 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x10a184 (fun s => s.RIP = 0x10a184) (shrR64Effect 0x10a184 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.exec 0x10a188 (StorePre 0x10a188 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a188 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a188 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 53]
    (.letOp (n := 66) (.exec 0x10a18c (fun s => s.RIP = 0x10a18c) (movR64R64Effect 0x10a18c 0 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 67) (.out 0x10a18f (xorR32R32Effect 0x10a18f 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[63, 63]
    (.letOp (n := 68) (.exec 0x10a18f (fun s => s.RIP = 0x10a18f) (xorR32R32Effect 0x10a18f 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[63, 63]
    (.letOp (n := 69) (.out 0x10a191 (subR64M64Effect 0x10a191 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[67, 53]
    (.letOp (n := 70) (.exec 0x10a191 (LoadPre 0x10a191 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a191 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a191 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[67, 53]
    (.letOp (n := 71) (.out 0x10a195 (movR64M64Effect 0x10a195 2 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 7] []) (.reg (.gpr 2))) #v[7]
    (.letOp (n := 72) (.exec 0x10a195 (LoadPre 0x10a195 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a195 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a195 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 73) (.out 0x10a199 (sarR64Effect 0x10a199 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[69]
    (.letOp (n := 74) (.exec 0x10a199 (fun s => s.RIP = 0x10a199) (sarR64Effect 0x10a199 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 75) (.out 0x10a19d (subR64R64Effect 0x10a19d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[73, 71]
    (.letOp (n := 76) (.exec 0x10a19d (fun s => s.RIP = 0x10a19d) (subR64R64Effect 0x10a19d 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[73, 71]
    (.letOp (n := 77) (.out 0x10a1a0 (movR64Imm64Effect 0x10a1a0 6 0x5d576e7357a4501d) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x10a1a0 (fun s => s.RIP = 0x10a1a0) (movR64Imm64Effect 0x10a1a0 6 0x5d576e7357a4501d) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x10a1aa (addR64R64Effect 0x10a1aa 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[77, 75]
    (.letOp (n := 80) (.exec 0x10a1aa (fun s => s.RIP = 0x10a1aa) (addR64R64Effect 0x10a1aa 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[77, 75]
    (.letOp (n := 81) (.out 0x10a1ad (orR64R64Effect 0x10a1ad 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[79, 71]
    (.letOp (n := 82) (.exec 0x10a1ad (fun s => s.RIP = 0x10a1ad) (orR64R64Effect 0x10a1ad 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[79, 71]
    (.letOp (n := 83) (.out 0x10a1b0 (shrR64Effect 0x10a1b0 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 84) (.exec 0x10a1b0 (fun s => s.RIP = 0x10a1b0) (shrR64Effect 0x10a1b0 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.exec 0x10a1b4 (StorePre 0x10a1b4 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1b4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a1b4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[83, 53]
    (.letOp (n := 86) (.out 0x10a1b8 (xorR32R32Effect 0x10a1b8 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[75, 75]
    (.letOp (n := 87) (.exec 0x10a1b8 (fun s => s.RIP = 0x10a1b8) (xorR32R32Effect 0x10a1b8 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[75, 75]
    (.letOp (n := 88) (.out 0x10a1ba (subR64M64Effect 0x10a1ba 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[86, 53]
    (.letOp (n := 89) (.exec 0x10a1ba (LoadPre 0x10a1ba (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a1ba + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x10a1ba 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[86, 53]
    (b_l10a170_1)))))))))))))))))))))))))))))))))))))

def bytes_l10a170 : List UInt8 :=
  [0x50, 0x48, 0x8B, 0x07, 0x48, 0xB9, 0xA0, 0x20, 0x1B, 0x68, 0x46, 0x2F, 0xE9, 0xDF, 0x48, 0x29,
    0xC1, 0x48, 0x21, 0xC1, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x0C, 0x24, 0x48, 0x89, 0xE0, 0x31,
    0xC9, 0x48, 0x2B, 0x0C, 0x24, 0x48, 0x8B, 0x57, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x29, 0xD1,
    0x48, 0xBE, 0x1D, 0x50, 0xA4, 0x57, 0x73, 0x6E, 0x57, 0x5D, 0x48, 0x01, 0xCE, 0x48, 0x09, 0xD6,
    0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x34, 0x24, 0x31, 0xC9, 0x48, 0x2B, 0x0C, 0x24] ++ bytes_l10a170_1

theorem code_l10a170 : ∀ x ∈ codeRange 0x10a170 bytes_l10a170, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa170 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a170_1

@[cfg_block] def b_l10a211 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a211 (popR64Effect 0x10a211 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.out 0x10a211 (popR64Effect 0x10a211 1 1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10a211 (PopPre 0x10a211) (popR64Effect 0x10a211 1 1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10a212 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[54]
    (.letOp (n := 57) (.out 0x10a212 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x10a212 (RetPre 0x10a212) (retEffect) (Reg.operands [.gpr 4] [])) #v[54]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59) (some ⟨56, by decide⟩))))))))

def bytes_l10a211 : List UInt8 :=
  [0x59, 0xC3]

theorem code_l10a211 : ∀ x ∈ codeRange 0x10a211 bytes_l10a211, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa211 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a220_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10a263 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[63, 87, 89]
    (.letOp (n := 92) (.exec 0x10a263 (fun s => s.RIP = 0x10a263) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a263 4 6 2)) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[63, 87, 89]
    (.letOp (n := 93) (.exec 0x10a267 (StorePre 0x10a267 3 (fun s => AddrMode.addr (.base 0 .none) s (0x10a267 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10a267 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[75, 55]
    (.letOp (n := 94) (.exec 0x10a26a (StorePre 0x10a26a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10a26a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26a 8 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 0] [])) #v[79, 55]
    (.letOp (n := 95) (.exec 0x10a26e (StorePre 0x10a26e 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10a26e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a26e 9 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 0] [])) #v[85, 55]
    (.letOp (n := 96) (.exec 0x10a272 (StorePre 0x10a272 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10a272 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10a272 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[91, 55]
    (.letOp (n := 97) (.out 0x10a276 (addR64Imm8Effect 0x10a276 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 98) (.exec 0x10a276 (fun s => s.RIP = 0x10a276) (addR64Imm8Effect 0x10a276 4 0x1) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 99) (.out 0x10a27a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[97]
    (.letOp (n := 100) (.out 0x10a27a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x10a27a (RetPre 0x10a27a) (retEffect) (Reg.operands [.gpr 4] [])) #v[97]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 67), (2, 87), (3, 3), (4, 100), (5, 5), (6, 91), (7, 75), (8, 79), (9, 85), (10, 81), (11, 71), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 102) (some ⟨99, by decide⟩)))))))))))))

def bytes_l10a220_1 : List UInt8 :=
  [0x48, 0x0F, 0x45, 0xF2, 0x48, 0x89, 0x38, 0x4C, 0x89, 0x40, 0x08, 0x4C, 0x89, 0x48, 0x10, 0x48,
    0x89, 0x70, 0x18, 0x48, 0x83, 0xC4, 0x01, 0xC3]

theorem code_l10a220_1 : ∀ x ∈ codeRange 0x10a263 bytes_l10a220_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa263 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a220 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a220 (subR64Imm8Effect 0x10a220 4 0x1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x10a220 (fun s => s.RIP = 0x10a220) (subR64Imm8Effect 0x10a220 4 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10a224 (movR64R64Effect 0x10a224 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x10a224 (fun s => s.RIP = 0x10a224) (movR64R64Effect 0x10a224 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10a227 (movR64M64Effect 0x10a227 7 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 58) (.exec 0x10a227 (LoadPre 0x10a227 (fun s => AddrMode.addr (.base 6 .none) s (0x10a227 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a227 7 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x10a22a (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 60) (.exec 0x10a22a (LoadPre 0x10a22a (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a22a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22a 8 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x10a22e (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 62) (.exec 0x10a22e (LoadPre 0x10a22e (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a22e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a22e 9 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 63) (.out 0x10a232 (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 64) (.exec 0x10a232 (LoadPre 0x10a232 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a232 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a232 6 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.exec 0x10a236 (StorePre 0x10a236 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a236 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a236 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 53]
    (.letOp (n := 66) (.exec 0x10a239 (fun s => s.RIP = 0x10a239) (movR64R64Effect 0x10a239 1 4) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 67) (.out 0x10a23c (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 68) (.exec 0x10a23c (LoadPre 0x10a23c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10a23c + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x10a23c 4 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 69) (.out 0x10a240 (movR64M64Effect 0x10a240 10 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2]
    (.letOp (n := 70) (.exec 0x10a240 (LoadPre 0x10a240 (fun s => AddrMode.addr (.base 2 .none) s (0x10a240 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a240 10 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x10a243 (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 72) (.exec 0x10a243 (LoadPre 0x10a243 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x10a243 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a243 11 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x10a247 (testR8R8Effect 0x10a247 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 74) (.exec 0x10a247 (fun s => s.RIP = 0x10a247) (testR8R8Effect 0x10a247 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 75) (.out 0x10a249 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[57, 69, 73]
    (.letOp (n := 76) (.exec 0x10a249 (fun s => s.RIP = 0x10a249) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a249 4 7 10)) (Reg.operands [.gpr 7, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 69, 73]
    (.letOp (n := 77) (.out 0x10a24d (testR8R8Effect 0x10a24d 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 78) (.exec 0x10a24d (fun s => s.RIP = 0x10a24d) (testR8R8Effect 0x10a24d 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 79) (.out 0x10a24f (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 8))) #v[59, 71, 77]
    (.letOp (n := 80) (.exec 0x10a24f (fun s => s.RIP = 0x10a24f) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a24f 4 8 11)) (Reg.operands [.gpr 8, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[59, 71, 77]
    (.letOp (n := 81) (.out 0x10a253 (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[2]
    (.letOp (n := 82) (.exec 0x10a253 (LoadPre 0x10a253 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x10a253 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a253 10 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 83) (.out 0x10a257 (testR8R8Effect 0x10a257 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 84) (.exec 0x10a257 (fun s => s.RIP = 0x10a257) (testR8R8Effect 0x10a257 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (.letOp (n := 85) (.out 0x10a259 (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[61, 81, 83]
    (.letOp (n := 86) (.exec 0x10a259 (fun s => s.RIP = 0x10a259) (atFlags (condHolds 5) (cmovR64R64Effect 0x10a259 4 9 10)) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[61, 81, 83]
    (.letOp (n := 87) (.out 0x10a25d (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 88) (.exec 0x10a25d (LoadPre 0x10a25d (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x10a25d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a25d 2 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 89) (.out 0x10a261 (testR8R8Effect 0x10a261 2 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[67, 67]
    (.letOp (n := 90) (.exec 0x10a261 (fun s => s.RIP = 0x10a261) (testR8R8Effect 0x10a261 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (b_l10a220_1))))))))))))))))))))))))))))))))))))))

def bytes_l10a220 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x01, 0x48, 0x89, 0xF8, 0x48, 0x8B, 0x3E, 0x4C, 0x8B, 0x46, 0x08, 0x4C, 0x8B,
    0x4E, 0x10, 0x48, 0x8B, 0x76, 0x18, 0x88, 0x0C, 0x24, 0x48, 0x89, 0xE1, 0x0F, 0xB6, 0x0C, 0x24,
    0x4C, 0x8B, 0x12, 0x4C, 0x8B, 0x5A, 0x08, 0x84, 0xC9, 0x49, 0x0F, 0x45, 0xFA, 0x84, 0xC9, 0x4D,
    0x0F, 0x45, 0xC3, 0x4C, 0x8B, 0x52, 0x10, 0x84, 0xC9, 0x4D, 0x0F, 0x45, 0xCA, 0x48, 0x8B, 0x52,
    0x18, 0x84, 0xC9] ++ bytes_l10a220_1

theorem code_l10a220 : ∀ x ∈ codeRange 0x10a220 bytes_l10a220, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa220 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a220_1

@[cfg_block] def b_l10a280 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a280 (pushR64Effect 0x10a280 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a280 (PushPre 0x10a280 1) (pushR64Effect 0x10a280 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a281 (movR64R64Effect 0x10a281 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 56) (.exec 0x10a281 (fun s => s.RIP = 0x10a281) (movR64R64Effect 0x10a281 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a284 (movR32Imm32Effect 0x10a284 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10a284 (fun s => s.RIP = 0x10a284) (movR32Imm32Effect 0x10a284 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a289 (movR32Imm32Effect 0x10a289 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10a289 (fun s => s.RIP = 0x10a289) (movR32Imm32Effect 0x10a289 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10a28e (callEffect (fun _ => 0x127f50) 0x10a293) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 62) (.exec 0x10a28e (PushPre 0x10a28e 5) (callEffect (fun _ => 0x127f50) 0x10a293) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.const ⟨64, 0x10a293⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10a293, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10a280 : List UInt8 :=
  [0x50, 0x48, 0x89, 0xF2, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0xBD,
    0xDC, 0x01, 0x00]

theorem code_l10a280 : ∀ x ∈ codeRange 0x10a280 bytes_l10a280, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa280 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a293 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a293 (andAlImm8Effect 0x10a293 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a293 (fun s => s.RIP = 0x10a293) (andAlImm8Effect 0x10a293 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a295 (movzxR32R8Effect 0x10a295 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10a295 (fun s => s.RIP = 0x10a295) (movzxR32R8Effect 0x10a295 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a298 (popR64Effect 0x10a298 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10a298 (PopPre 0x10a298) (popR64Effect 0x10a298 1 0) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10a293 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0x58, 0xE9, 0xB2, 0xDA, 0x01, 0x00]

theorem code_l10a293 : ∀ x ∈ codeRange 0x10a293 bytes_l10a293, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa293 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2a0 (pushR64Effect 0x10a2a0 1 0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 0]
    (.letOp (n := 54) (.exec 0x10a2a0 (PushPre 0x10a2a0 1) (pushR64Effect 0x10a2a0 1 0) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 0]
    (.letOp (n := 55) (.out 0x10a2a1 (movR64R64Effect 0x10a2a1 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 56) (.exec 0x10a2a1 (fun s => s.RIP = 0x10a2a1) (movR64R64Effect 0x10a2a1 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a2a4 (movR32Imm32Effect 0x10a2a4 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x10a2a4 (fun s => s.RIP = 0x10a2a4) (movR32Imm32Effect 0x10a2a4 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10a2a9 (movR32Imm32Effect 0x10a2a9 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10a2a9 (fun s => s.RIP = 0x10a2a9) (movR32Imm32Effect 0x10a2a9 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10a2ae (callEffect (fun _ => 0x127f50) 0x10a2b3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 62) (.exec 0x10a2ae (PushPre 0x10a2ae 5) (callEffect (fun _ => 0x127f50) 0x10a2b3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 63) (.const ⟨64, 0x10a2b3⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 0), (1, 59), (2, 55), (3, 3), (4, 61), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10a2b3, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10a2a0 : List UInt8 :=
  [0x50, 0x48, 0x89, 0xF2, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0xE8, 0x9D,
    0xDC, 0x01, 0x00]

theorem code_l10a2a0 : ∀ x ∈ codeRange 0x10a2a0 bytes_l10a2a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2a0 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2b3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2b3 (andAlImm8Effect 0x10a2b3 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x10a2b3 (fun s => s.RIP = 0x10a2b3) (andAlImm8Effect 0x10a2b3 0x1) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x10a2b5 (movzxR32R8Effect 0x10a2b5 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x10a2b5 (fun s => s.RIP = 0x10a2b5) (movzxR32R8Effect 0x10a2b5 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x10a2b8 (callEffect (fun _ => 0x127d50) 0x10a2bd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10a2b8 (PushPre 0x10a2b8 5) (callEffect (fun _ => 0x127d50) 0x10a2bd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10a2bd⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10a2bd, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10a2b3 : List UInt8 :=
  [0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0x93, 0xDA, 0x01, 0x00]

theorem code_l10a2b3 : ∀ x ∈ codeRange 0x10a2b3 bytes_l10a2b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2b3 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2bd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2bd (testR8R8Effect 0x10a2bd 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10a2bd (fun s => s.RIP = 0x10a2bd) (testR8R8Effect 0x10a2bd 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x10a2bf (atFlags (condHolds 5) (setccR8Effect 0x10a2bf 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[0, 53]
    (.letOp (n := 56) (.exec 0x10a2bf (fun s => s.RIP = 0x10a2bf) (atFlags (condHolds 5) (setccR8Effect 0x10a2bf 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[0, 53]
    (.letOp (n := 57) (.out 0x10a2c2 (popR64Effect 0x10a2c2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.out 0x10a2c2 (popR64Effect 0x10a2c2 1 1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x10a2c2 (PopPre 0x10a2c2) (popR64Effect 0x10a2c2 1 1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x10a2c3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[58]
    (.letOp (n := 61) (.out 0x10a2c3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10a2c3 (RetPre 0x10a2c3) (retEffect) (Reg.operands [.gpr 4] [])) #v[58]
    (.terminate (.ret (RegMap.args [(0, 55), (1, 57), (2, 2), (3, 3), (4, 61), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 63) (some ⟨60, by decide⟩))))))))))))

def bytes_l10a2bd : List UInt8 :=
  [0x84, 0xC0, 0x0F, 0x95, 0xC0, 0x59, 0xC3]

theorem code_l10a2bd : ∀ x ∈ codeRange 0x10a2bd bytes_l10a2bd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2bd 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2d0 (movR64Imm32Effect 0x10a2d0 2 0x2021a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10a2d0 (fun s => s.RIP = 0x10a2d0) (movR64Imm32Effect 0x10a2d0 2 0x2021a0) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l110b80, RegMap.args [(2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10a2d0 : List UInt8 :=
  [0x48, 0xC7, 0xC2, 0xA0, 0x21, 0x20, 0x00, 0xE9, 0xA4, 0x68, 0x00, 0x00]

theorem code_l10a2d0 : ∀ x ∈ codeRange 0x10a2d0 bytes_l10a2d0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2d0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2e0 (movR64Imm32Effect 0x10a2e0 1 0x2021a0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 54) (.exec 0x10a2e0 (fun s => s.RIP = 0x10a2e0) (movR64Imm32Effect 0x10a2e0 1 0x2021a0) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1109b0, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10a2e0 : List UInt8 :=
  [0x48, 0xC7, 0xC1, 0xA0, 0x21, 0x20, 0x00, 0xE9, 0xC4, 0x66, 0x00, 0x00]

theorem code_l10a2e0 : ∀ x ∈ codeRange 0x10a2e0 bytes_l10a2e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa2e0 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2f0_4 : Block Op Label signature Reg.count 186 :=
  .letOp (n := 186) (.exec 0x10a3ec (StorePre 0x10a3ec 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1b)) s (0x10a3ec + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ec 3 2 (.base 7 (.d8 0x1b))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[184, 7]
    (.letOp (n := 187) (.out 0x10a3ef (movR32R32Effect 0x10a3ef 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 188) (.exec 0x10a3ef (fun s => s.RIP = 0x10a3ef) (movR32R32Effect 0x10a3ef 2 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 189) (.out 0x10a3f1 (shrR32Effect 0x10a3f1 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[187]
    (.letOp (n := 190) (.exec 0x10a3f1 (fun s => s.RIP = 0x10a3f1) (shrR32Effect 0x10a3f1 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.exec 0x10a3f4 (StorePre 0x10a3f4 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1c)) s (0x10a3f4 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3f4 3 2 (.base 7 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[189, 7]
    (.letOp (n := 192) (.out 0x10a3f7 (movR32R32Effect 0x10a3f7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 193) (.exec 0x10a3f7 (fun s => s.RIP = 0x10a3f7) (movR32R32Effect 0x10a3f7 2 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 194) (.out 0x10a3f9 (shrR32Effect 0x10a3f9 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[192]
    (.letOp (n := 195) (.exec 0x10a3f9 (fun s => s.RIP = 0x10a3f9) (shrR32Effect 0x10a3f9 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[192]
    (.letOp (n := 196) (.exec 0x10a3fc (StorePre 0x10a3fc 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1d)) s (0x10a3fc + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3fc 3 2 (.base 7 (.d8 0x1d))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[194, 7]
    (.letOp (n := 197) (.exec 0x10a3ff (StorePre 0x10a3ff 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1e)) s (0x10a3ff + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ff 3 5 (.base 7 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[165, 7]
    (.letOp (n := 198) (.exec 0x10a402 (StorePre 0x10a402 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1f)) s (0x10a402 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a402 3 1 (.base 7 (.d8 0x1f))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[165, 7]
    (.letOp (n := 199) (.out 0x10a405 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 200) (.out 0x10a405 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 201) (.exec 0x10a405 (RetPre 0x10a405) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 165), (2, 194), (3, 3), (4, 200), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 202) (some ⟨199, by decide⟩))))))))))))))))))

def bytes_l10a2f0_4 : List UInt8 :=
  [0x88, 0x57, 0x1B, 0x89, 0xCA, 0xC1, 0xEA, 0x18, 0x88, 0x57, 0x1C, 0x89, 0xCA, 0xC1, 0xEA, 0x10,
    0x88, 0x57, 0x1D, 0x88, 0x6F, 0x1E, 0x88, 0x4F, 0x1F, 0xC3]

theorem code_l10a2f0_4 : ∀ x ∈ codeRange 0x10a3ec bytes_l10a2f0_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa3ec 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10a2f0_3 : Block Op Label signature Reg.count 153 :=
  .letOp (n := 153) (.out 0x10a3ac (shrR32Effect 0x10a3ac 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[151]
    (.letOp (n := 154) (.exec 0x10a3ac (fun s => s.RIP = 0x10a3ac) (shrR32Effect 0x10a3ac 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[151]
    (.letOp (n := 155) (.exec 0x10a3af (StorePre 0x10a3af 3 (fun s => AddrMode.addr (.base 7 (.d8 0x14)) s (0x10a3af + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3af 3 2 (.base 7 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[153, 7]
    (.letOp (n := 156) (.out 0x10a3b2 (movR32R32Effect 0x10a3b2 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 157) (.exec 0x10a3b2 (fun s => s.RIP = 0x10a3b2) (movR32R32Effect 0x10a3b2 2 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 158) (.out 0x10a3b4 (shrR32Effect 0x10a3b4 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[156]
    (.letOp (n := 159) (.exec 0x10a3b4 (fun s => s.RIP = 0x10a3b4) (shrR32Effect 0x10a3b4 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[156]
    (.letOp (n := 160) (.exec 0x10a3b7 (StorePre 0x10a3b7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x15)) s (0x10a3b7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3b7 3 2 (.base 7 (.d8 0x15))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[158, 7]
    (.letOp (n := 161) (.exec 0x10a3ba (StorePre 0x10a3ba 3 (fun s => AddrMode.addr (.base 7 (.d8 0x16)) s (0x10a3ba + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a3ba 3 5 (.base 7 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[129, 7]
    (.letOp (n := 162) (.exec 0x10a3bd (StorePre 0x10a3bd 3 (fun s => AddrMode.addr (.base 7 (.d8 0x17)) s (0x10a3bd + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3bd 3 1 (.base 7 (.d8 0x17))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[129, 7]
    (.letOp (n := 163) (.out 0x10a3c0 (movR64M64Effect 0x10a3c0 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 164) (.exec 0x10a3c0 (LoadPre 0x10a3c0 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x10a3c0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a3c0 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 165) (.out 0x10a3c4 (bswapR64Effect 0x10a3c4 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[163]
    (.letOp (n := 166) (.exec 0x10a3c4 (fun s => s.RIP = 0x10a3c4) (bswapR64Effect 0x10a3c4 3 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 167) (.out 0x10a3c7 (movR64R64Effect 0x10a3c7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 168) (.exec 0x10a3c7 (fun s => s.RIP = 0x10a3c7) (movR64R64Effect 0x10a3c7 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 169) (.out 0x10a3ca (shrR64Effect 0x10a3ca 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[167]
    (.letOp (n := 170) (.exec 0x10a3ca (fun s => s.RIP = 0x10a3ca) (shrR64Effect 0x10a3ca 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[167]
    (.letOp (n := 171) (.exec 0x10a3ce (StorePre 0x10a3ce 3 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10a3ce + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3ce 3 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[169, 7]
    (.letOp (n := 172) (.out 0x10a3d1 (movR64R64Effect 0x10a3d1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 173) (.exec 0x10a3d1 (fun s => s.RIP = 0x10a3d1) (movR64R64Effect 0x10a3d1 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 174) (.out 0x10a3d4 (shrR64Effect 0x10a3d4 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[172]
    (.letOp (n := 175) (.exec 0x10a3d4 (fun s => s.RIP = 0x10a3d4) (shrR64Effect 0x10a3d4 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[172]
    (.letOp (n := 176) (.exec 0x10a3d8 (StorePre 0x10a3d8 3 (fun s => AddrMode.addr (.base 7 (.d8 0x19)) s (0x10a3d8 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3d8 3 2 (.base 7 (.d8 0x19))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[174, 7]
    (.letOp (n := 177) (.out 0x10a3db (movR64R64Effect 0x10a3db 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 178) (.exec 0x10a3db (fun s => s.RIP = 0x10a3db) (movR64R64Effect 0x10a3db 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 179) (.out 0x10a3de (shrR64Effect 0x10a3de 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[177]
    (.letOp (n := 180) (.exec 0x10a3de (fun s => s.RIP = 0x10a3de) (shrR64Effect 0x10a3de 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[177]
    (.letOp (n := 181) (.exec 0x10a3e2 (StorePre 0x10a3e2 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1a)) s (0x10a3e2 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3e2 3 2 (.base 7 (.d8 0x1a))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[179, 7]
    (.letOp (n := 182) (.out 0x10a3e5 (movR64R64Effect 0x10a3e5 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[165]
    (.letOp (n := 183) (.exec 0x10a3e5 (fun s => s.RIP = 0x10a3e5) (movR64R64Effect 0x10a3e5 2 1) (Reg.operands [.gpr 1] [])) #v[165]
    (.letOp (n := 184) (.out 0x10a3e8 (shrR64Effect 0x10a3e8 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[182]
    (.letOp (n := 185) (.exec 0x10a3e8 (fun s => s.RIP = 0x10a3e8) (shrR64Effect 0x10a3e8 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[182]
    (b_l10a2f0_4)))))))))))))))))))))))))))))))))

def bytes_l10a2f0_3 : List UInt8 :=
  [0xC1, 0xEA, 0x18, 0x88, 0x57, 0x14, 0x89, 0xCA, 0xC1, 0xEA, 0x10, 0x88, 0x57, 0x15, 0x88, 0x6F,
    0x16, 0x88, 0x4F, 0x17, 0x48, 0x8B, 0x4E, 0x18, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1,
    0xEA, 0x38, 0x88, 0x57, 0x18, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x19, 0x48,
    0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x28, 0x88, 0x57, 0x1A, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20] ++ bytes_l10a2f0_4

theorem code_l10a2f0_3 : ∀ x ∈ codeRange 0x10a3ac bytes_l10a2f0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa3ac 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_4

@[cfg_block] def b_l10a2f0_2 : Block Op Label signature Reg.count 120 :=
  .letOp (n := 120) (.out 0x10a36d (movR32R32Effect 0x10a36d 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 121) (.exec 0x10a36d (fun s => s.RIP = 0x10a36d) (movR32R32Effect 0x10a36d 2 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 122) (.out 0x10a36f (shrR32Effect 0x10a36f 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[120]
    (.letOp (n := 123) (.exec 0x10a36f (fun s => s.RIP = 0x10a36f) (shrR32Effect 0x10a36f 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 124) (.exec 0x10a372 (StorePre 0x10a372 3 (fun s => AddrMode.addr (.base 7 (.d8 0xd)) s (0x10a372 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a372 3 1 (.base 7 (.d8 0xd))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[122, 7]
    (.letOp (n := 125) (.exec 0x10a375 (StorePre 0x10a375 3 (fun s => AddrMode.addr (.base 7 (.d8 0xe)) s (0x10a375 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a375 3 6 (.base 7 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[91, 7]
    (.letOp (n := 126) (.exec 0x10a378 (StorePre 0x10a378 3 (fun s => AddrMode.addr (.base 7 (.d8 0xf)) s (0x10a378 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a378 3 2 (.base 7 (.d8 0xf))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[91, 7]
    (.letOp (n := 127) (.out 0x10a37b (movR64M64Effect 0x10a37b 1 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 128) (.exec 0x10a37b (LoadPre 0x10a37b (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10a37b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a37b 1 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 129) (.out 0x10a37f (bswapR64Effect 0x10a37f 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[127]
    (.letOp (n := 130) (.exec 0x10a37f (fun s => s.RIP = 0x10a37f) (bswapR64Effect 0x10a37f 3 1) (Reg.operands [.gpr 1] [])) #v[127]
    (.letOp (n := 131) (.out 0x10a382 (movR64R64Effect 0x10a382 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 132) (.exec 0x10a382 (fun s => s.RIP = 0x10a382) (movR64R64Effect 0x10a382 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 133) (.out 0x10a385 (shrR64Effect 0x10a385 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[131]
    (.letOp (n := 134) (.exec 0x10a385 (fun s => s.RIP = 0x10a385) (shrR64Effect 0x10a385 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.exec 0x10a389 (StorePre 0x10a389 3 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10a389 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a389 3 2 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[133, 7]
    (.letOp (n := 136) (.out 0x10a38c (movR64R64Effect 0x10a38c 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 137) (.exec 0x10a38c (fun s => s.RIP = 0x10a38c) (movR64R64Effect 0x10a38c 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 138) (.out 0x10a38f (shrR64Effect 0x10a38f 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[136]
    (.letOp (n := 139) (.exec 0x10a38f (fun s => s.RIP = 0x10a38f) (shrR64Effect 0x10a38f 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.exec 0x10a393 (StorePre 0x10a393 3 (fun s => AddrMode.addr (.base 7 (.d8 0x11)) s (0x10a393 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a393 3 2 (.base 7 (.d8 0x11))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[138, 7]
    (.letOp (n := 141) (.out 0x10a396 (movR64R64Effect 0x10a396 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 142) (.exec 0x10a396 (fun s => s.RIP = 0x10a396) (movR64R64Effect 0x10a396 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 143) (.out 0x10a399 (shrR64Effect 0x10a399 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[141]
    (.letOp (n := 144) (.exec 0x10a399 (fun s => s.RIP = 0x10a399) (shrR64Effect 0x10a399 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[141]
    (.letOp (n := 145) (.exec 0x10a39d (StorePre 0x10a39d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x12)) s (0x10a39d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a39d 3 2 (.base 7 (.d8 0x12))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[143, 7]
    (.letOp (n := 146) (.out 0x10a3a0 (movR64R64Effect 0x10a3a0 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 147) (.exec 0x10a3a0 (fun s => s.RIP = 0x10a3a0) (movR64R64Effect 0x10a3a0 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (.letOp (n := 148) (.out 0x10a3a3 (shrR64Effect 0x10a3a3 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[146]
    (.letOp (n := 149) (.exec 0x10a3a3 (fun s => s.RIP = 0x10a3a3) (shrR64Effect 0x10a3a3 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[146]
    (.letOp (n := 150) (.exec 0x10a3a7 (StorePre 0x10a3a7 3 (fun s => AddrMode.addr (.base 7 (.d8 0x13)) s (0x10a3a7 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a3a7 3 2 (.base 7 (.d8 0x13))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[148, 7]
    (.letOp (n := 151) (.out 0x10a3aa (movR32R32Effect 0x10a3aa 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[129]
    (.letOp (n := 152) (.exec 0x10a3aa (fun s => s.RIP = 0x10a3aa) (movR32R32Effect 0x10a3aa 2 2 1) (Reg.operands [.gpr 1] [])) #v[129]
    (b_l10a2f0_3)))))))))))))))))))))))))))))))))

def bytes_l10a2f0_2 : List UInt8 :=
  [0x89, 0xD1, 0xC1, 0xE9, 0x10, 0x88, 0x4F, 0x0D, 0x88, 0x77, 0x0E, 0x88, 0x57, 0x0F, 0x48, 0x8B,
    0x4E, 0x10, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x38, 0x88, 0x57, 0x10, 0x48,
    0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x11, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x28,
    0x88, 0x57, 0x12, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20, 0x88, 0x57, 0x13, 0x89, 0xCA] ++ bytes_l10a2f0_3

theorem code_l10a2f0_2 : ∀ x ∈ codeRange 0x10a36d bytes_l10a2f0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa36d 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_3

@[cfg_block] def b_l10a2f0_1 : Block Op Label signature Reg.count 88 :=
  .letOp (n := 88) (.exec 0x10a32d (StorePre 0x10a32d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x5)) s (0x10a32d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a32d 3 2 (.base 7 (.d8 0x5))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[86, 7]
    (.letOp (n := 89) (.out 0x10a330 (movR64M64Effect 0x10a330 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 90) (.exec 0x10a330 (LoadPre 0x10a330 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10a330 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10a330 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 91) (.out 0x10a334 (bswapR64Effect 0x10a334 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[89]
    (.letOp (n := 92) (.exec 0x10a334 (fun s => s.RIP = 0x10a334) (bswapR64Effect 0x10a334 3 2) (Reg.operands [.gpr 2] [])) #v[89]
    (.letOp (n := 93) (.exec 0x10a337 (StorePre 0x10a337 3 (fun s => AddrMode.addr (.base 7 (.d8 0x6)) s (0x10a337 + BitVec.ofNat 64 3)) 1) (movM8R8NoRexEffect 0x10a337 3 5 (.base 7 (.d8 0x6))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 94) (.exec 0x10a33a (StorePre 0x10a33a 3 (fun s => AddrMode.addr (.base 7 (.d8 0x7)) s (0x10a33a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a33a 3 1 (.base 7 (.d8 0x7))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[57, 7]
    (.letOp (n := 95) (.out 0x10a33d (movR64R64Effect 0x10a33d 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 96) (.exec 0x10a33d (fun s => s.RIP = 0x10a33d) (movR64R64Effect 0x10a33d 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 97) (.out 0x10a340 (shrR64Effect 0x10a340 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[95]
    (.letOp (n := 98) (.exec 0x10a340 (fun s => s.RIP = 0x10a340) (shrR64Effect 0x10a340 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[95]
    (.letOp (n := 99) (.exec 0x10a344 (StorePre 0x10a344 3 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10a344 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a344 3 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[97, 7]
    (.letOp (n := 100) (.out 0x10a347 (movR64R64Effect 0x10a347 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 101) (.exec 0x10a347 (fun s => s.RIP = 0x10a347) (movR64R64Effect 0x10a347 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 102) (.out 0x10a34a (shrR64Effect 0x10a34a 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[100]
    (.letOp (n := 103) (.exec 0x10a34a (fun s => s.RIP = 0x10a34a) (shrR64Effect 0x10a34a 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[100]
    (.letOp (n := 104) (.exec 0x10a34e (StorePre 0x10a34e 3 (fun s => AddrMode.addr (.base 7 (.d8 0x9)) s (0x10a34e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a34e 3 1 (.base 7 (.d8 0x9))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[102, 7]
    (.letOp (n := 105) (.out 0x10a351 (movR64R64Effect 0x10a351 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 106) (.exec 0x10a351 (fun s => s.RIP = 0x10a351) (movR64R64Effect 0x10a351 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 107) (.out 0x10a354 (shrR64Effect 0x10a354 4 1 40) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[105]
    (.letOp (n := 108) (.exec 0x10a354 (fun s => s.RIP = 0x10a354) (shrR64Effect 0x10a354 4 1 40) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[105]
    (.letOp (n := 109) (.exec 0x10a358 (StorePre 0x10a358 3 (fun s => AddrMode.addr (.base 7 (.d8 0xa)) s (0x10a358 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a358 3 1 (.base 7 (.d8 0xa))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[107, 7]
    (.letOp (n := 110) (.out 0x10a35b (movR64R64Effect 0x10a35b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 111) (.exec 0x10a35b (fun s => s.RIP = 0x10a35b) (movR64R64Effect 0x10a35b 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 112) (.out 0x10a35e (shrR64Effect 0x10a35e 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[110]
    (.letOp (n := 113) (.exec 0x10a35e (fun s => s.RIP = 0x10a35e) (shrR64Effect 0x10a35e 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.exec 0x10a362 (StorePre 0x10a362 3 (fun s => AddrMode.addr (.base 7 (.d8 0xb)) s (0x10a362 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a362 3 1 (.base 7 (.d8 0xb))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[112, 7]
    (.letOp (n := 115) (.out 0x10a365 (movR32R32Effect 0x10a365 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 116) (.exec 0x10a365 (fun s => s.RIP = 0x10a365) (movR32R32Effect 0x10a365 2 1 2) (Reg.operands [.gpr 2] [])) #v[91]
    (.letOp (n := 117) (.out 0x10a367 (shrR32Effect 0x10a367 3 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[115]
    (.letOp (n := 118) (.exec 0x10a367 (fun s => s.RIP = 0x10a367) (shrR32Effect 0x10a367 3 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.exec 0x10a36a (StorePre 0x10a36a 3 (fun s => AddrMode.addr (.base 7 (.d8 0xc)) s (0x10a36a + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a36a 3 1 (.base 7 (.d8 0xc))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[117, 7]
    (b_l10a2f0_2))))))))))))))))))))))))))))))))

def bytes_l10a2f0_1 : List UInt8 :=
  [0x88, 0x57, 0x05, 0x48, 0x8B, 0x56, 0x08, 0x48, 0x0F, 0xCA, 0x88, 0x6F, 0x06, 0x88, 0x4F, 0x07,
    0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x38, 0x88, 0x4F, 0x08, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9,
    0x30, 0x88, 0x4F, 0x09, 0x48, 0x89, 0xD1, 0x48, 0xC1, 0xE9, 0x28, 0x88, 0x4F, 0x0A, 0x48, 0x89,
    0xD1, 0x48, 0xC1, 0xE9, 0x20, 0x88, 0x4F, 0x0B, 0x89, 0xD1, 0xC1, 0xE9, 0x18, 0x88, 0x4F, 0x0C] ++ bytes_l10a2f0_2

theorem code_l10a2f0_1 : ∀ x ∈ codeRange 0x10a32d bytes_l10a2f0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa32d 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_2

@[cfg_block] def b_l10a2f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10a2f0 (movR64R64Effect 0x10a2f0 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x10a2f0 (fun s => s.RIP = 0x10a2f0) (movR64R64Effect 0x10a2f0 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x10a2f3 (movR64M64Effect 0x10a2f3 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 56) (.exec 0x10a2f3 (LoadPre 0x10a2f3 (fun s => AddrMode.addr (.base 6 .none) s (0x10a2f3 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10a2f3 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x10a2f6 (bswapR64Effect 0x10a2f6 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x10a2f6 (fun s => s.RIP = 0x10a2f6) (bswapR64Effect 0x10a2f6 3 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x10a2f9 (movR64R64Effect 0x10a2f9 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x10a2f9 (fun s => s.RIP = 0x10a2f9) (movR64R64Effect 0x10a2f9 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x10a2fc (shrR64Effect 0x10a2fc 4 2 56) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 62) (.exec 0x10a2fc (fun s => s.RIP = 0x10a2fc) (shrR64Effect 0x10a2fc 4 2 56) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.exec 0x10a300 (StorePre 0x10a300 2 (fun s => AddrMode.addr (.base 7 .none) s (0x10a300 + BitVec.ofNat 64 2)) 1) (movM8R8Effect 0x10a300 2 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[61, 7]
    (.letOp (n := 64) (.out 0x10a302 (movR64R64Effect 0x10a302 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 65) (.exec 0x10a302 (fun s => s.RIP = 0x10a302) (movR64R64Effect 0x10a302 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 66) (.out 0x10a305 (shrR64Effect 0x10a305 4 2 48) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[64]
    (.letOp (n := 67) (.exec 0x10a305 (fun s => s.RIP = 0x10a305) (shrR64Effect 0x10a305 4 2 48) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (.letOp (n := 68) (.exec 0x10a309 (StorePre 0x10a309 3 (fun s => AddrMode.addr (.base 7 (.d8 0x1)) s (0x10a309 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a309 3 2 (.base 7 (.d8 0x1))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[66, 7]
    (.letOp (n := 69) (.out 0x10a30c (movR64R64Effect 0x10a30c 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 70) (.exec 0x10a30c (fun s => s.RIP = 0x10a30c) (movR64R64Effect 0x10a30c 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 71) (.out 0x10a30f (shrR64Effect 0x10a30f 4 2 40) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x10a30f (fun s => s.RIP = 0x10a30f) (shrR64Effect 0x10a30f 4 2 40) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.exec 0x10a313 (StorePre 0x10a313 3 (fun s => AddrMode.addr (.base 7 (.d8 0x2)) s (0x10a313 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a313 3 2 (.base 7 (.d8 0x2))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[71, 7]
    (.letOp (n := 74) (.out 0x10a316 (movR64R64Effect 0x10a316 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 75) (.exec 0x10a316 (fun s => s.RIP = 0x10a316) (movR64R64Effect 0x10a316 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 76) (.out 0x10a319 (shrR64Effect 0x10a319 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[74]
    (.letOp (n := 77) (.exec 0x10a319 (fun s => s.RIP = 0x10a319) (shrR64Effect 0x10a319 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.exec 0x10a31d (StorePre 0x10a31d 3 (fun s => AddrMode.addr (.base 7 (.d8 0x3)) s (0x10a31d + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a31d 3 2 (.base 7 (.d8 0x3))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[76, 7]
    (.letOp (n := 79) (.out 0x10a320 (movR32R32Effect 0x10a320 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 80) (.exec 0x10a320 (fun s => s.RIP = 0x10a320) (movR32R32Effect 0x10a320 2 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 81) (.out 0x10a322 (shrR32Effect 0x10a322 3 2 24) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[79]
    (.letOp (n := 82) (.exec 0x10a322 (fun s => s.RIP = 0x10a322) (shrR32Effect 0x10a322 3 2 24) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x10a325 (StorePre 0x10a325 3 (fun s => AddrMode.addr (.base 7 (.d8 0x4)) s (0x10a325 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10a325 3 2 (.base 7 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[81, 7]
    (.letOp (n := 84) (.out 0x10a328 (movR32R32Effect 0x10a328 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 85) (.exec 0x10a328 (fun s => s.RIP = 0x10a328) (movR32R32Effect 0x10a328 2 2 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 86) (.out 0x10a32a (shrR32Effect 0x10a32a 3 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[84]
    (.letOp (n := 87) (.exec 0x10a32a (fun s => s.RIP = 0x10a32a) (shrR32Effect 0x10a32a 3 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[84]
    (b_l10a2f0_1)))))))))))))))))))))))))))))))))))

def bytes_l10a2f0 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x0E, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x38,
    0x88, 0x17, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x30, 0x88, 0x57, 0x01, 0x48, 0x89, 0xCA, 0x48,
    0xC1, 0xEA, 0x28, 0x88, 0x57, 0x02, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x20, 0x88, 0x57, 0x03,
    0x89, 0xCA, 0xC1, 0xEA, 0x18, 0x88, 0x57, 0x04, 0x89, 0xCA, 0xC1, 0xEA, 0x10] ++ bytes_l10a2f0_1

theorem code_l10a2f0 : ∀ x ∈ codeRange 0x10a2f0 bytes_l10a2f0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xa2f0 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10a2f0_1

end K256.Proofs.Verify.LIR
