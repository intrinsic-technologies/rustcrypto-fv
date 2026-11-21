import K256.Proofs.Signing.LIR.Labels
import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.Lift.Generated.Footprints.Part1
import K256.Proofs.Common.Lift.Generated.Footprints.Part2
import K256.Proofs.Common.Lift.Generated.Footprints.Part3
import K256.Proofs.Common.Lift.Generated.Footprints.Part4
import K256.Proofs.Common.Lift.Generated.Footprints.Part5
import K256.Proofs.Signing.LIR.Generated.Footprints

namespace K256.Proofs.Signing.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR K256.Proofs.Verify.LIR

@[cfg_block] def b_l100000_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x100094 (testR64R64Effect 0x100094 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[114, 114]
    (.letOp (n := 130) (.exec 0x100094 (fun s => s.RIP = 0x100094) (testR64R64Effect 0x100094 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[114, 114]
    (.letOp (n := 131) (.out 0x100097 (atFlags (condHolds 5) (cmovR32R32Effect 0x100097 4 9 11)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[112, 108, 129]
    (.letOp (n := 132) (.exec 0x100097 (fun s => s.RIP = 0x100097) (atFlags (condHolds 5) (cmovR32R32Effect 0x100097 4 9 11)) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[112, 108, 129]
    (.letOp (n := 133) (.out 0x10009b (bsrR64M64Effect 0x10009b 4 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[71, 6]
    (.letOp (n := 134) (.exec 0x10009b (LoadPre 0x10009b (fun s => AddrMode.addr (.base 6 .none) s (0x10009b + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x10009b 4 0 (.base 6 .none)) (Reg.operands [.gpr 0, .gpr 6] [])) #v[71, 6]
    (.letOp (n := 135) (.out 0x10009f (xorR32Imm8Effect 0x10009f 3 0 0x3f) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[133]
    (.letOp (n := 136) (.exec 0x10009f (fun s => s.RIP = 0x10009f) (xorR32Imm8Effect 0x10009f 3 0 0x3f) (Reg.operands [.gpr 0] [])) #v[133]
    (.letOp (n := 137) (.exec 0x1000a2 (StorePre 0x1000a2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1000a2 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x1000a2 5 9 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[131, 65]
    (.letOp (n := 138) (.out 0x1000a7 (movzxR32M8Effect 0x1000a7 5 6 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 139) (.exec 0x1000a7 (LoadPre 0x1000a7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1000a7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1000a7 5 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 140) (.out 0x1000ac (negR32Effect 0x1000ac 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[138]
    (.letOp (n := 141) (.exec 0x1000ac (fun s => s.RIP = 0x1000ac) (negR32Effect 0x1000ac 2 6) (Reg.operands [.gpr 6] [])) #v[138]
    (.letOp (n := 142) (.out 0x1000ae (andR32R32Effect 0x1000ae 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[140, 135]
    (.letOp (n := 143) (.exec 0x1000ae (fun s => s.RIP = 0x1000ae) (andR32R32Effect 0x1000ae 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[140, 135]
    (.letOp (n := 144) (.out 0x1000b0 (addR64R64Effect 0x1000b0 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[106, 85]
    (.letOp (n := 145) (.exec 0x1000b0 (fun s => s.RIP = 0x1000b0) (addR64R64Effect 0x1000b0 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[106, 85]
    (.letOp (n := 146) (.out 0x1000b3 (addR64R64Effect 0x1000b3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[144, 127]
    (.letOp (n := 147) (.exec 0x1000b3 (fun s => s.RIP = 0x1000b3) (addR64R64Effect 0x1000b3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[144, 127]
    (.letOp (n := 148) (.out 0x1000b6 (addR64R64Effect 0x1000b6 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[146, 142]
    (.letOp (n := 149) (.exec 0x1000b6 (fun s => s.RIP = 0x1000b6) (addR64R64Effect 0x1000b6 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[146, 142]
    (.letOp (n := 150) (.out 0x1000b9 (movR32Imm32Effect 0x1000b9 5 0 0x107) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 151) (.exec 0x1000b9 (fun s => s.RIP = 0x1000b9) (movR32Imm32Effect 0x1000b9 5 0 0x107) (Reg.operands [] [])) #v[]
    (.letOp (n := 152) (.out 0x1000be (subR64R64Effect 0x1000be 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[150, 148]
    (.letOp (n := 153) (.exec 0x1000be (fun s => s.RIP = 0x1000be) (subR64R64Effect 0x1000be 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[150, 148]
    (.letOp (n := 154) (.out 0x1000c1 (movR32R32Effect 0x1000c1 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[152]
    (.letOp (n := 155) (.exec 0x1000c1 (fun s => s.RIP = 0x1000c1) (movR32R32Effect 0x1000c1 2 2 0) (Reg.operands [.gpr 0] [])) #v[152]
    (.letOp (n := 156) (.out 0x1000c3 (shrR32Effect 0x1000c3 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[154]
    (.letOp (n := 157) (.exec 0x1000c3 (fun s => s.RIP = 0x1000c3) (shrR32Effect 0x1000c3 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[154]
    (.letOp (n := 158) (.out 0x1000c6 (cmpR64R64Effect 0x1000c6 1 2) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 2] []) (.flag .CF)) #v[1, 156]
    (.letOp (n := 159) (.exec 0x1000c6 (fun s => s.RIP = 0x1000c6) (cmpR64R64Effect 0x1000c6 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 156]
    (.letOp (n := 160) (.pure (condOp 2)) #v[158]
    (.terminate (.condBr (Fin.last 160) ⟨.l100162, RegMap.args [(0, 152), (1, 1), (2, 156), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)] 161⟩ ⟨.l1000cf, RegMap.args [(0, 152), (1, 1), (2, 156), (3, 120), (4, 65), (5, 5), (6, 142), (7, 7), (8, 148), (9, 131), (10, 114), (11, 108), (12, 67), (13, 13), (15, 127), (16, 158), (22, 22), (39, 39), (50, 50), (51, 51)] 161⟩)))))))))))))))))))))))))))))))))

def bytes_l100000_2 : List UInt8 :=
  [0x4D, 0x85, 0xD2, 0x45, 0x0F, 0x45, 0xCB, 0x48, 0x0F, 0xBD, 0x06, 0x83, 0xF0, 0x3F, 0x44, 0x88,
    0x4C, 0x24, 0x0F, 0x0F, 0xB6, 0x74, 0x24, 0x0F, 0xF7, 0xDE, 0x21, 0xC6, 0x49, 0x01, 0xD0, 0x4D,
    0x01, 0xF8, 0x49, 0x01, 0xF0, 0xB8, 0x07, 0x01, 0x00, 0x00, 0x4C, 0x29, 0xC0, 0x89, 0xC2, 0xC1,
    0xEA, 0x03, 0x48, 0x39, 0xD1, 0x0F, 0x82, 0x93, 0x00, 0x00, 0x00]

theorem code_l100000_2 : ∀ x ∈ codeRange 0x100094 bytes_l100000_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x94 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100000_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x100046 (bsrR64R64Effect 0x100046 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[89, 87]
    (.letOp (n := 92) (.exec 0x100046 (fun s => s.RIP = 0x100046) (bsrR64R64Effect 0x100046 4 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[89, 87]
    (.letOp (n := 93) (.out 0x10004a (xorR32Imm8Effect 0x10004a 4 11 0x3f) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[91]
    (.letOp (n := 94) (.exec 0x10004a (fun s => s.RIP = 0x10004a) (xorR32Imm8Effect 0x10004a 4 11 0x3f) (Reg.operands [.gpr 11] [])) #v[91]
    (.letOp (n := 95) (.out 0x10004e (xorR32R32Effect 0x10004e 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[77, 77]
    (.letOp (n := 96) (.exec 0x10004e (fun s => s.RIP = 0x10004e) (xorR32R32Effect 0x10004e 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[77, 77]
    (.letOp (n := 97) (.out 0x100051 (testR64R64Effect 0x100051 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[69, 69]
    (.letOp (n := 98) (.exec 0x100051 (fun s => s.RIP = 0x100051) (testR64R64Effect 0x100051 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[69, 69]
    (.letOp (n := 99) (.out 0x100054 (atFlags (condHolds 4) (setccR8Effect 0x100054 4 9)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[95, 97]
    (.letOp (n := 100) (.exec 0x100054 (fun s => s.RIP = 0x100054) (atFlags (condHolds 4) (setccR8Effect 0x100054 4 9)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[95, 97]
    (.letOp (n := 101) (.exec 0x100058 (StorePre 0x100058 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100058 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100058 5 (.sib 4 none 0 (.d8 0xf)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[65, 97]
    (.letOp (n := 102) (.out 0x10005d (movzxR32M8Effect 0x10005d 6 8 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 103) (.exec 0x10005d (LoadPre 0x10005d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x10005d + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x10005d 6 8 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 104) (.out 0x100063 (negR32Effect 0x100063 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[102]
    (.letOp (n := 105) (.exec 0x100063 (fun s => s.RIP = 0x100063) (negR32Effect 0x100063 3 8) (Reg.operands [.gpr 8] [])) #v[102]
    (.letOp (n := 106) (.out 0x100066 (andR32R32Effect 0x100066 3 8 11) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 11] []) (.reg (.gpr 8))) #v[104, 93]
    (.letOp (n := 107) (.exec 0x100066 (fun s => s.RIP = 0x100066) (andR32R32Effect 0x100066 3 8 11) (Reg.operands [.gpr 8, .gpr 11] [])) #v[104, 93]
    (.letOp (n := 108) (.out 0x100069 (xorR32R32Effect 0x100069 3 11 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 11] []) (.reg (.gpr 11))) #v[93, 93]
    (.letOp (n := 109) (.exec 0x100069 (fun s => s.RIP = 0x100069) (xorR32R32Effect 0x100069 3 11 11) (Reg.operands [.gpr 11, .gpr 11] [])) #v[93, 93]
    (.letOp (n := 110) (.out 0x10006c (testR64R64Effect 0x10006c 10 10) (EffectPart.reads (.flag .ZF) [.gpr 10, .gpr 10] []) (.flag .ZF)) #v[87, 87]
    (.letOp (n := 111) (.exec 0x10006c (fun s => s.RIP = 0x10006c) (testR64R64Effect 0x10006c 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[87, 87]
    (.letOp (n := 112) (.out 0x10006f (atFlags (condHolds 5) (cmovR32R32Effect 0x10006f 4 9 11)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 9))) #v[99, 108, 110]
    (.letOp (n := 113) (.exec 0x10006f (fun s => s.RIP = 0x10006f) (atFlags (condHolds 5) (cmovR32R32Effect 0x10006f 4 9 11)) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[99, 108, 110]
    (.letOp (n := 114) (.out 0x100073 (movR64M64Effect 0x100073 10 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 115) (.exec 0x100073 (LoadPre 0x100073 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x100073 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100073 10 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 116) (.out 0x100077 (movR32Imm32Effect 0x100077 5 3 0x7f) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 117) (.exec 0x100077 (fun s => s.RIP = 0x100077) (movR32Imm32Effect 0x100077 5 3 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 118) (.out 0x10007c (bsrR64R64Effect 0x10007c 4 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[116, 114]
    (.letOp (n := 119) (.exec 0x10007c (fun s => s.RIP = 0x10007c) (bsrR64R64Effect 0x10007c 4 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[116, 114]
    (.letOp (n := 120) (.out 0x100080 (xorR32Imm8Effect 0x100080 3 3 0x3f) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[118]
    (.letOp (n := 121) (.exec 0x100080 (fun s => s.RIP = 0x100080) (xorR32Imm8Effect 0x100080 3 3 0x3f) (Reg.operands [.gpr 3] [])) #v[118]
    (.letOp (n := 122) (.exec 0x100083 (StorePre 0x100083 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100083 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100083 5 9 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 123) (.out 0x100088 (movzxR32M8Effect 0x100088 6 15 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 124) (.exec 0x100088 (LoadPre 0x100088 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100088 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100088 6 15 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 125) (.out 0x10008e (negR32Effect 0x10008e 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[123]
    (.letOp (n := 126) (.exec 0x10008e (fun s => s.RIP = 0x10008e) (negR32Effect 0x10008e 3 15) (Reg.operands [.gpr 15] [])) #v[123]
    (.letOp (n := 127) (.out 0x100091 (andR32R32Effect 0x100091 3 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[125, 120]
    (.letOp (n := 128) (.exec 0x100091 (fun s => s.RIP = 0x100091) (andR32R32Effect 0x100091 3 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[125, 120]
    (b_l100000_2))))))))))))))))))))))))))))))))))))))

def bytes_l100000_1 : List UInt8 :=
  [0x4D, 0x0F, 0xBD, 0xDA, 0x41, 0x83, 0xF3, 0x3F, 0x45, 0x31, 0xC9, 0x4D, 0x85, 0xC0, 0x41, 0x0F,
    0x94, 0xC1, 0x0F, 0x94, 0x44, 0x24, 0x0F, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x0F, 0x41, 0xF7, 0xD8,
    0x45, 0x21, 0xD8, 0x45, 0x31, 0xDB, 0x4D, 0x85, 0xD2, 0x45, 0x0F, 0x45, 0xCB, 0x4C, 0x8B, 0x56,
    0x08, 0xBB, 0x7F, 0x00, 0x00, 0x00, 0x49, 0x0F, 0xBD, 0xDA, 0x83, 0xF3, 0x3F, 0x44, 0x88, 0x4C,
    0x24, 0x0F, 0x44, 0x0F, 0xB6, 0x7C, 0x24, 0x0F, 0x41, 0xF7, 0xDF, 0x41, 0x21, 0xDF] ++ bytes_l100000_2

theorem code_l100000_1 : ∀ x ∈ codeRange 0x100046 bytes_l100000_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x46 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_2

@[cfg_block] def b_l100000 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100000 (pushR64Effect 0x100000 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100000 (PushPre 0x100000 1) (pushR64Effect 0x100000 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100001 (pushR64Effect 0x100001 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100001 (PushPre 0x100001 2) (pushR64Effect 0x100001 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100003 (pushR64Effect 0x100003 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100003 (PushPre 0x100003 2) (pushR64Effect 0x100003 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100005 (pushR64Effect 0x100005 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100005 (PushPre 0x100005 2) (pushR64Effect 0x100005 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100007 (pushR64Effect 0x100007 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100007 (PushPre 0x100007 2) (pushR64Effect 0x100007 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100009 (pushR64Effect 0x100009 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100009 (PushPre 0x100009 1) (pushR64Effect 0x100009 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10000a (subR64Imm8Effect 0x10000a 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10000a (fun s => s.RIP = 0x10000a) (subR64Imm8Effect 0x10000a 4 0x18) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10000e (movR64R64Effect 0x10000e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 68) (.exec 0x10000e (fun s => s.RIP = 0x10000e) (movR64R64Effect 0x10000e 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x100011 (movR64M64Effect 0x100011 8 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x100011 (LoadPre 0x100011 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x100011 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100011 8 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x100015 (movR32Imm32Effect 0x100015 5 0 0x7f) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 72) (.exec 0x100015 (fun s => s.RIP = 0x100015) (movR32Imm32Effect 0x100015 5 0 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10001a (movR32Imm32Effect 0x10001a 6 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 74) (.exec 0x10001a (fun s => s.RIP = 0x10001a) (movR32Imm32Effect 0x10001a 6 9 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x100020 (bsrR64R64Effect 0x100020 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[73, 69]
    (.letOp (n := 76) (.exec 0x100020 (fun s => s.RIP = 0x100020) (bsrR64R64Effect 0x100020 4 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[73, 69]
    (.letOp (n := 77) (.out 0x100024 (xorR32Imm8Effect 0x100024 4 9 0x3f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[75]
    (.letOp (n := 78) (.exec 0x100024 (fun s => s.RIP = 0x100024) (xorR32Imm8Effect 0x100024 4 9 0x3f) (Reg.operands [.gpr 9] [])) #v[75]
    (.letOp (n := 79) (.exec 0x100028 (StorePre 0x100028 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100028 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100028 (.sib 4 none 0 (.d8 0xf)) 0x1) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.exec 0x10002d (fun s => s.RIP = 0x10002d) (leaR64Effect 0x10002d 14 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.out 0x100032 (movzxR32M8Effect 0x100032 5 2 (.sib 4 none 0 (.d8 0xf))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 82) (.exec 0x100032 (LoadPre 0x100032 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x100032 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100032 5 2 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 83) (.out 0x100037 (negR32Effect 0x100037 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[81]
    (.letOp (n := 84) (.exec 0x100037 (fun s => s.RIP = 0x100037) (negR32Effect 0x100037 2 2) (Reg.operands [.gpr 2] [])) #v[81]
    (.letOp (n := 85) (.out 0x100039 (andR32R32Effect 0x100039 3 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[83, 77]
    (.letOp (n := 86) (.exec 0x100039 (fun s => s.RIP = 0x100039) (andR32R32Effect 0x100039 3 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[83, 77]
    (.letOp (n := 87) (.out 0x10003c (movR64M64Effect 0x10003c 10 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 88) (.exec 0x10003c (LoadPre 0x10003c (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10003c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10003c 10 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 89) (.out 0x100040 (movR32Imm32Effect 0x100040 6 11 0x7f) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 90) (.exec 0x100040 (fun s => s.RIP = 0x100040) (movR32Imm32Effect 0x100040 6 11 0x7f) (Reg.operands [] [])) #v[]
    (b_l100000_1))))))))))))))))))))))))))))))))))))))

def bytes_l100000 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x18, 0x49, 0x89,
    0xD4, 0x4C, 0x8B, 0x46, 0x18, 0xB8, 0x7F, 0x00, 0x00, 0x00, 0x41, 0xB9, 0x7F, 0x00, 0x00, 0x00,
    0x4D, 0x0F, 0xBD, 0xC8, 0x41, 0x83, 0xF1, 0x3F, 0xC6, 0x44, 0x24, 0x0F, 0x01, 0x4C, 0x8D, 0x74,
    0x24, 0x0F, 0x0F, 0xB6, 0x54, 0x24, 0x0F, 0xF7, 0xDA, 0x44, 0x21, 0xCA, 0x4C, 0x8B, 0x56, 0x10,
    0x41, 0xBB, 0x7F, 0x00, 0x00, 0x00] ++ bytes_l100000_1

theorem code_l100000 : ∀ x ∈ codeRange 0x100000 bytes_l100000, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x0 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100000_1

@[cfg_block] def b_l1000cf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1000cf (testR64R64Effect 0x1000cf 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1000cf (fun s => s.RIP = 0x1000cf) (testR64R64Effect 0x1000cf 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100153, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1000d8, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1000cf : List UInt8 :=
  [0x48, 0x85, 0xD2, 0x0F, 0x84, 0x7B, 0x00, 0x00, 0x00]

theorem code_l1000cf : ∀ x ∈ codeRange 0x1000cf bytes_l1000cf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xcf 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1000d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1000d8 (movR32R32Effect 0x1000d8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 54) (.exec 0x1000d8 (fun s => s.RIP = 0x1000d8) (movR32R32Effect 0x1000d8 2 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1000da (shrR32Effect 0x1000da 3 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x1000da (fun s => s.RIP = 0x1000da) (shrR32Effect 0x1000da 3 1 6) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x1000dd (andR32Imm8Effect 0x1000dd 3 0 0x38) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 58) (.exec 0x1000dd (fun s => s.RIP = 0x1000dd) (andR32Imm8Effect 0x1000dd 3 0 0x38) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 59) (.out 0x1000e0 (cmpR64Imm8Effect 0x1000e0 0 0x1) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[57]
    (.letOp (n := 60) (.exec 0x1000e0 (fun s => s.RIP = 0x1000e0) (cmpR64Imm8Effect 0x1000e0 0 0x1) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 61) (.out 0x1000e4 (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1000e4 1 0xff)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[55, 59]
    (.letOp (n := 62) (.exec 0x1000e4 (fun s => s.RIP = 0x1000e4) (atFlags StatusFlags.CF (sbbR64Imm8Effect 0x1000e4 1 0xff)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 59]
    (.letOp (n := 63) (.out 0x1000e8 (cmpR64Imm8Effect 0x1000e8 1 0x4) (EffectPart.reads (.flag .CF) [.gpr 1] []) (.flag .CF)) #v[61]
    (.letOp (n := 64) (.exec 0x1000e8 (fun s => s.RIP = 0x1000e8) (cmpR64Imm8Effect 0x1000e8 1 0x4) (Reg.operands [.gpr 1] [])) #v[61]
    (.letOp (n := 65) (.out 0x1000ec (movR32Imm32Effect 0x1000ec 6 15 0x4) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 66) (.exec 0x1000ec (fun s => s.RIP = 0x1000ec) (movR32Imm32Effect 0x1000ec 6 15 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x1000f2 (atFlags (condHolds 2) (cmovR64R64Effect 0x1000f2 4 15 1)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[65, 61, 63]
    (.letOp (n := 68) (.exec 0x1000f2 (fun s => s.RIP = 0x1000f2) (atFlags (condHolds 2) (cmovR64R64Effect 0x1000f2 4 15 1)) (Reg.operands [.gpr 15, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[65, 61, 63]
    (.letOp (n := 69) (.out 0x1000f6 (testR64R64Effect 0x1000f6 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[61, 61]
    (.letOp (n := 70) (.exec 0x1000f6 (fun s => s.RIP = 0x1000f6) (testR64R64Effect 0x1000f6 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[61, 61]
    (.letOp (n := 71) (.pure (condOp 4)) #v[69]
    (.terminate (.condBr (Fin.last 71) ⟨.l100153, RegMap.args [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 67), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ ⟨.l1000fb, RegMap.args [(0, 57), (1, 61), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 67), (19, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩))))))))))))))))))))

def bytes_l1000d8 : List UInt8 :=
  [0x89, 0xC1, 0xC1, 0xE9, 0x06, 0x83, 0xE0, 0x38, 0x48, 0x83, 0xF8, 0x01, 0x48, 0x83, 0xD9, 0xFF,
    0x48, 0x83, 0xF9, 0x04, 0x41, 0xBF, 0x04, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0x42, 0xF9, 0x48, 0x85,
    0xC9, 0x74, 0x58]

theorem code_l1000d8 : ∀ x ∈ codeRange 0x1000d8 bytes_l1000d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xd8 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1000fb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1000fb (movR64R64Effect 0x1000fb 13 7) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[7]
    (.letOp (n := 54) (.exec 0x1000fb (fun s => s.RIP = 0x1000fb) (movR64R64Effect 0x1000fb 13 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1000fe (movR64R64Effect 0x1000fe 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 12] []) (.reg (.gpr 14))) #v[12]
    (.letOp (n := 56) (.exec 0x1000fe (fun s => s.RIP = 0x1000fe) (movR64R64Effect 0x1000fe 14 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x100101 (xorR32R32Effect 0x100101 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 58) (.exec 0x100101 (fun s => s.RIP = 0x100101) (xorR32R32Effect 0x100101 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 59) (.out 0x100104 (xorR32R32Effect 0x100104 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 60) (.exec 0x100104 (fun s => s.RIP = 0x100104) (xorR32R32Effect 0x100104 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 61) (.out 0x100106 (movR64R64Effect 0x100106 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 62) (.exec 0x100106 (fun s => s.RIP = 0x100106) (movR64R64Effect 0x100106 3 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 63) (.exec 0x100109 (fun s => s.RIP = 0x100109) (fun _ => nopEffect 0x100109 7) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100110, RegMap.args [(2, 2), (3, 61), (4, 4), (5, 59), (7, 7), (9, 9), (10, 10), (11, 11), (12, 57), (13, 53), (14, 55), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l1000fb : List UInt8 :=
  [0x49, 0x89, 0xFD, 0x4D, 0x89, 0xE6, 0x45, 0x31, 0xE4, 0x31, 0xED, 0x48, 0x89, 0xD3, 0x0F, 0x1F,
    0x80, 0x00, 0x00, 0x00, 0x00]

theorem code_l1000fb : ∀ x ∈ codeRange 0x1000fb bytes_l1000fb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfb 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100110 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100110 (movR64M64Effect 0x100110 0 (.sib 13 (some 5) 3 (.d8 0x0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 5] []) (.reg (.gpr 0))) #v[13, 5]
    (.letOp (n := 54) (.exec 0x100110 (LoadPre 0x100110 (fun s => AddrMode.addr (.sib 13 (some 5) 3 (.d8 0x0)) s (0x100110 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100110 0 (.sib 13 (some 5) 3 (.d8 0x0))) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 55) (.out 0x100115 (bswapR64Effect 0x100115 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x100115 (fun s => s.RIP = 0x100115) (bswapR64Effect 0x100115 3 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100118 (subR64Imm8Effect 0x100118 3 0x8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 58) (.out 0x100118 (subR64Imm8Effect 0x100118 3 0x8) (EffectPart.reads (.flag .CF) [.gpr 3] []) (.flag .CF)) #v[3]
    (.letOp (n := 59) (.exec 0x100118 (fun s => s.RIP = 0x100118) (subR64Imm8Effect 0x100118 3 0x8) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x10011c (movR64R64Effect 0x10011c 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 61) (.exec 0x10011c (fun s => s.RIP = 0x10011c) (movR64R64Effect 0x10011c 7 3) (Reg.operands [.gpr 3] [])) #v[57]
    (.letOp (n := 62) (.out 0x10011f (atFlags (condHolds 2) (cmovR64R64Effect 0x10011f 4 7 12)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[60, 12, 58]
    (.letOp (n := 63) (.exec 0x10011f (fun s => s.RIP = 0x10011f) (atFlags (condHolds 2) (cmovR64R64Effect 0x10011f 4 7 12)) (Reg.operands [.gpr 7, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[60, 12, 58]
    (.letOp (n := 64) (.out 0x100123 (subR64R64Effect 0x100123 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[2, 62]
    (.letOp (n := 65) (.exec 0x100123 (fun s => s.RIP = 0x100123) (subR64R64Effect 0x100123 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[2, 62]
    (.letOp (n := 66) (.out 0x100126 (movR32Imm32Effect 0x100126 5 1 0x8) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 67) (.exec 0x100126 (fun s => s.RIP = 0x100126) (movR32Imm32Effect 0x100126 5 1 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x10012b (subR64R64Effect 0x10012b 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[66, 64]
    (.letOp (n := 69) (.out 0x10012b (subR64R64Effect 0x10012b 1 2) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 2] []) (.flag .CF)) #v[66, 64]
    (.letOp (n := 70) (.exec 0x10012b (fun s => s.RIP = 0x10012b) (subR64R64Effect 0x10012b 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[66, 64]
    (.letOp (n := 71) (.out 0x10012e (atFlags (condHolds 2) (cmovR64R64Effect 0x10012e 4 1 12)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[68, 12, 69]
    (.letOp (n := 72) (.exec 0x10012e (fun s => s.RIP = 0x10012e) (atFlags (condHolds 2) (cmovR64R64Effect 0x10012e 4 1 12)) (Reg.operands [.gpr 1, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[68, 12, 69]
    (.letOp (n := 73) (.exec 0x100132 (StorePre 0x100132 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100132 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100132 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 74) (.out 0x100137 (leaR64Effect 0x100137 6 (.sib 4 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4, .gpr 1] []) (.reg (.gpr 6))) #v[4, 71]
    (.letOp (n := 75) (.exec 0x100137 (fun s => s.RIP = 0x100137) (leaR64Effect 0x100137 6 (.sib 4 (some 1) 0 .none)) (Reg.operands [.gpr 4, .gpr 1] [])) #v[4, 71]
    (.letOp (n := 76) (.out 0x10013b (addR64Imm8Effect 0x10013b 6 0x10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[74]
    (.letOp (n := 77) (.exec 0x10013b (fun s => s.RIP = 0x10013b) (addR64Imm8Effect 0x10013b 6 0x10) (Reg.operands [.gpr 6] [])) #v[74]
    (.letOp (n := 78) (.out 0x10013f (addR64R64Effect 0x10013f 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[62, 14]
    (.letOp (n := 79) (.exec 0x10013f (fun s => s.RIP = 0x10013f) (addR64R64Effect 0x10013f 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[62, 14]
    (.letOp (n := 80) (.out 0x100142 (incR64Effect 0x100142 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 81) (.exec 0x100142 (fun s => s.RIP = 0x100142) (incR64Effect 0x100142 5) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[5]
    (.letOp (n := 82) (.out 0x100145 (callEffect (callMemPtr 0x100145 (.rip 0x103c85)) (0x100145 + BitVec.ofNat 64 (callMemLen (.rip 0x103c85)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 83) (.exec 0x100145 (GoesTo (CallMemPre 0x100145 (.rip 0x103c85)) (callEffect (callMemPtr 0x100145 (.rip 0x103c85)) (0x100145 + BitVec.ofNat 64 (callMemLen (.rip 0x103c85)))) 0x12a820) (callEffect (callMemPtr 0x100145 (.rip 0x103c85)) (0x100145 + BitVec.ofNat 64 (callMemLen (.rip 0x103c85)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.const ⟨64, 0x10014b⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 55), (1, 71), (2, 64), (3, 57), (4, 82), (5, 80), (6, 76), (7, 78), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ { target := .l10014b, kept := #v[], arity := rfl, guard := some (Fin.last 84) })))))))))))))))))))))))))))))))))

def bytes_l100110 : List UInt8 :=
  [0x49, 0x8B, 0x44, 0xED, 0x00, 0x48, 0x0F, 0xC8, 0x48, 0x83, 0xEB, 0x08, 0x48, 0x89, 0xDF, 0x49,
    0x0F, 0x42, 0xFC, 0x48, 0x29, 0xFA, 0xB9, 0x08, 0x00, 0x00, 0x00, 0x48, 0x29, 0xD1, 0x49, 0x0F,
    0x42, 0xCC, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8D, 0x34, 0x0C, 0x48, 0x83, 0xC6, 0x10, 0x4C,
    0x01, 0xF7, 0x48, 0xFF, 0xC5, 0xFF, 0x15, 0x85, 0x3C, 0x10, 0x00]

theorem code_l100110 : ∀ x ∈ codeRange 0x100110 bytes_l100110, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x110 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10014b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10014b (movR64R64Effect 0x10014b 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 54) (.exec 0x10014b (fun s => s.RIP = 0x10014b) (movR64R64Effect 0x10014b 2 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10014e (cmpR64R64Effect 0x10014e 15 5) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 5] []) (.flag .ZF)) #v[15, 5]
    (.letOp (n := 56) (.exec 0x10014e (fun s => s.RIP = 0x10014e) (cmpR64R64Effect 0x10014e 15 5) (Reg.operands [.gpr 15, .gpr 5] [])) #v[15, 5]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100110, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l100153, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10014b : List UInt8 :=
  [0x48, 0x89, 0xDA, 0x49, 0x39, 0xEF, 0x75, 0xBD]

theorem code_l10014b : ∀ x ∈ codeRange 0x10014b bytes_l10014b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14b 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100153 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100153 (addR64Imm8Effect 0x100153 4 0x18) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x100153 (fun s => s.RIP = 0x100153) (addR64Imm8Effect 0x100153 4 0x18) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100157 (popR64Effect 0x100157 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x100157 (popR64Effect 0x100157 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x100157 (PopPre 0x100157) (popR64Effect 0x100157 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x100158 (popR64Effect 0x100158 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x100158 (popR64Effect 0x100158 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x100158 (PopPre 0x100158) (popR64Effect 0x100158 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x10015a (popR64Effect 0x10015a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x10015a (popR64Effect 0x10015a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x10015a (PopPre 0x10015a) (popR64Effect 0x10015a 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x10015c (popR64Effect 0x10015c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x10015c (popR64Effect 0x10015c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x10015c (PopPre 0x10015c) (popR64Effect 0x10015c 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x10015e (popR64Effect 0x10015e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x10015e (popR64Effect 0x10015e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x10015e (PopPre 0x10015e) (popR64Effect 0x10015e 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x100160 (popR64Effect 0x100160 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x100160 (popR64Effect 0x100160 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x100160 (PopPre 0x100160) (popR64Effect 0x100160 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x100161 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x100161 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x100161 (RetPre 0x100161) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l100153 : List UInt8 :=
  [0x48, 0x83, 0xC4, 0x18, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100153 : ∀ x ∈ codeRange 0x100153 bytes_l100153, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x153 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100162 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100162 (xorR32R32Effect 0x100162 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x100162 (fun s => s.RIP = 0x100162) (xorR32R32Effect 0x100162 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x100164 (movR64R64Effect 0x100164 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 56) (.exec 0x100164 (fun s => s.RIP = 0x100164) (movR64R64Effect 0x100164 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 57) (.out 0x100167 (movR64R64Effect 0x100167 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 58) (.exec 0x100167 (fun s => s.RIP = 0x100167) (movR64R64Effect 0x100167 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 59) (.out 0x10016a (movR64Imm32Effect 0x10016a 1 0x202068) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x10016a (fun s => s.RIP = 0x10016a) (movR64Imm32Effect 0x10016a 1 0x202068) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x100171 (callEffect (fun _ => 0x129b60) 0x100176) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x100171 (PushPre 0x100171 5) (callEffect (fun _ => 0x129b60) 0x100176) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x100176⟩) #v[]
    (.terminate (.call ⟨.l129b60, RegMap.args [(1, 59), (2, 57), (4, 61), (5, 5), (6, 55), (7, 53)] 64⟩ { target := .l100176, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l100162 : List UInt8 :=
  [0x31, 0xFF, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xCA, 0x48, 0xC7, 0xC1, 0x68, 0x20, 0x20, 0x00, 0xE8,
    0xEA, 0x99, 0x02, 0x00]

theorem code_l100162 : ∀ x ∈ codeRange 0x100162 bytes_l100162, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x162 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100176 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100176 (fun s => s.RIP = 0x100176) (fun _ => nopEffect 0x100176 10) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100180, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l100176 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l100176 : ∀ x ∈ codeRange 0x100176 bytes_l100176, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x176 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100180 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100180 (cmpM8Imm8Effect 0x100180 3 (.base 7 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 54) (.exec 0x100180 (LoadPre 0x100180 (fun s => AddrMode.addr (.base 7 .none) s (0x100180 + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x100180 3 (.base 7 .none) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10019f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100185, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100180 : List UInt8 :=
  [0x80, 0x3F, 0x00, 0x74, 0x1A]

theorem code_l100180 : ∀ x ∈ codeRange 0x100180 bytes_l100180, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x180 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100185 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100185 (movR64R64Effect 0x100185 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x100185 (fun s => s.RIP = 0x100185) (movR64R64Effect 0x100185 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x100188 (movR64M64Effect 0x100188 7 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x100188 (LoadPre 0x100188 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100188 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100188 7 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10018c (testR64R64Effect 0x10018c 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x10018c (fun s => s.RIP = 0x10018c) (testR64R64Effect 0x10018c 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10019f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100191, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100185 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x7F, 0x08, 0x48, 0x85, 0xFF, 0x74, 0x0E]

theorem code_l100185 : ∀ x ∈ codeRange 0x100185 bytes_l100185, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x185 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100191 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100191 (movR64M64Effect 0x100191 0 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x100191 (LoadPre 0x100191 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x100191 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100191 0 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x100195 (movR64M64Effect 0x100195 0 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x100195 (LoadPre 0x100195 (fun s => AddrMode.addr (.base 0 .none) s (0x100195 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100195 0 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100198 (testR64R64Effect 0x100198 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x100198 (fun s => s.RIP = 0x100198) (testR64R64Effect 0x100198 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10019f, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10019d, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100191 : List UInt8 :=
  [0x48, 0x8B, 0x40, 0x10, 0x48, 0x8B, 0x00, 0x48, 0x85, 0xC0, 0x74, 0x02]

theorem code_l100191 : ∀ x ∈ codeRange 0x100191 bytes_l100191, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x191 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10019d : Block Op Label signature Reg.count 53 :=
  cutBlock 0x10019d

def bytes_l10019d : List UInt8 :=
  [0xFF, 0xE0]

theorem code_l10019d : ∀ x ∈ codeRange 0x10019d bytes_l10019d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19d 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10019f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10019f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x10019f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10019f (RetPre 0x10019f) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l10019f : List UInt8 :=
  [0xC3]

theorem code_l10019f : ∀ x ∈ codeRange 0x10019f bytes_l10019f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x19f 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001a0 (leaR64Effect 0x1001a0 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 54) (.exec 0x1001a0 (fun s => s.RIP = 0x1001a0) (leaR64Effect 0x1001a0 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1001a4 (cmpM8Imm8Effect 0x1001a4 3 (.base 7 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 56) (.exec 0x1001a4 (LoadPre 0x1001a4 (fun s => AddrMode.addr (.base 7 .none) s (0x1001a4 + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x1001a4 3 (.base 7 .none) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1001c3, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1001a9, RegMap.args [(1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1001a0 : List UInt8 :=
  [0x48, 0x8D, 0x4F, 0x08, 0x80, 0x3F, 0x00, 0x74, 0x1A]

theorem code_l1001a0 : ∀ x ∈ codeRange 0x1001a0 bytes_l1001a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a0 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001a9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001a9 (movR64R64Effect 0x1001a9 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x1001a9 (fun s => s.RIP = 0x1001a9) (movR64R64Effect 0x1001a9 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x1001ac (movR64M64Effect 0x1001ac 7 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 56) (.exec 0x1001ac (LoadPre 0x1001ac (fun s => AddrMode.addr (.base 1 .none) s (0x1001ac + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1001ac 7 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x1001af (testR64R64Effect 0x1001af 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x1001af (fun s => s.RIP = 0x1001af) (testR64R64Effect 0x1001af 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1001c2, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1001b4, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1001a9 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x39, 0x48, 0x85, 0xFF, 0x74, 0x0E]

theorem code_l1001a9 : ∀ x ∈ codeRange 0x1001a9 bytes_l1001a9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1a9 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001b4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001b4 (movR64M64Effect 0x1001b4 0 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x1001b4 (LoadPre 0x1001b4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x1001b4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1001b4 0 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x1001b8 (movR64M64Effect 0x1001b8 0 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1001b8 (LoadPre 0x1001b8 (fun s => AddrMode.addr (.base 0 .none) s (0x1001b8 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1001b8 0 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1001bb (testR64R64Effect 0x1001bb 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x1001bb (fun s => s.RIP = 0x1001bb) (testR64R64Effect 0x1001bb 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1001c2, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1001c0, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1001b4 : List UInt8 :=
  [0x48, 0x8B, 0x40, 0x10, 0x48, 0x8B, 0x00, 0x48, 0x85, 0xC0, 0x74, 0x02]

theorem code_l1001b4 : ∀ x ∈ codeRange 0x1001b4 bytes_l1001b4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b4 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001c0 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1001c0

def bytes_l1001c0 : List UInt8 :=
  [0xFF, 0xE0]

theorem code_l1001c0 : ∀ x ∈ codeRange 0x1001c0 bytes_l1001c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c0 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001c2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001c2 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x1001c2 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x1001c2 (RetPre 0x1001c2) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l1001c2 : List UInt8 :=
  [0xC3]

theorem code_l1001c2 : ∀ x ∈ codeRange 0x1001c2 bytes_l1001c2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1c2 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001c3_1 : Block Op Label signature Reg.count 82 :=
  .letOp (n := 82) (.exec 0x100234 (StorePre 0x100234 3 (fun s => AddrMode.addr (.base 1 .none) s (0x100234 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x100234 0 (.base 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[80, 1]
    (.letOp (n := 83) (.out 0x100237 (addR64Imm8Effect 0x100237 4 0x20) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 84) (.exec 0x100237 (fun s => s.RIP = 0x100237) (addR64Imm8Effect 0x100237 4 0x20) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 85) (.out 0x10023b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[83]
    (.letOp (n := 86) (.out 0x10023b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x10023b (RetPre 0x10023b) (retEffect) (Reg.operands [.gpr 4] [])) #v[83]
    (.terminate (.ret (RegMap.args [(0, 80), (1, 1), (2, 2), (3, 3), (4, 86), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 88) (some ⟨85, by decide⟩))))))))

def bytes_l1001c3_1 : List UInt8 :=
  [0x48, 0x89, 0x01, 0x48, 0x83, 0xC4, 0x20, 0xC3]

theorem code_l1001c3_1 : ∀ x ∈ codeRange 0x100234 bytes_l1001c3_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x234 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1001c3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1001c3 (subR64Imm8Effect 0x1001c3 4 0x20) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x1001c3 (fun s => s.RIP = 0x1001c3) (subR64Imm8Effect 0x1001c3 4 0x20) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1001c7 (StorePre 0x1001c7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1001c7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1001c7 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 56) (.exec 0x1001d0 (StorePre 0x1001d0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1001d0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1001d0 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 57) (.exec 0x1001d9 (StorePre 0x1001d9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1001d9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1001d9 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.exec 0x1001e2 (StorePre 0x1001e2 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1001e2 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1001e2 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 59) (.out 0x1001ea (movR64M64Effect 0x1001ea 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 60) (.exec 0x1001ea (LoadPre 0x1001ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1001ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1001ea 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 61) (.exec 0x1001ef (StorePre 0x1001ef 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x1001ef + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1001ef 0 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[59, 1]
    (.letOp (n := 62) (.out 0x1001f3 (movR64M64Effect 0x1001f3 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 63) (.exec 0x1001f3 (LoadPre 0x1001f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1001f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1001f3 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 64) (.exec 0x1001f8 (StorePre 0x1001f8 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x1001f8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1001f8 0 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[62, 1]
    (.letOp (n := 65) (.out 0x1001fc (movR64M64Effect 0x1001fc 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 66) (.exec 0x1001fc (LoadPre 0x1001fc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1001fc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1001fc 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 67) (.exec 0x100201 (StorePre 0x100201 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x100201 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100201 0 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[65, 1]
    (.letOp (n := 68) (.out 0x100205 (movR64M64Effect 0x100205 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 69) (.exec 0x100205 (LoadPre 0x100205 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x100205 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100205 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 70) (.exec 0x100209 (StorePre 0x100209 3 (fun s => AddrMode.addr (.base 1 .none) s (0x100209 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x100209 0 (.base 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[68, 1]
    (.letOp (n := 71) (.out 0x10020c (movR64M64Effect 0x10020c 0 (.rip 0x101f85)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 72) (.exec 0x10020c (LoadPre 0x10020c (fun s => AddrMode.addr (.rip 0x101f85) s (0x10020c + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x10020c 0 (.rip 0x101f85)) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.exec 0x100213 (StorePre 0x100213 4 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x100213 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100213 0 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[71, 1]
    (.letOp (n := 74) (.out 0x100217 (movR64M64Effect 0x100217 0 (.rip 0x101f72)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 75) (.exec 0x100217 (LoadPre 0x100217 (fun s => AddrMode.addr (.rip 0x101f72) s (0x100217 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x100217 0 (.rip 0x101f72)) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.exec 0x10021e (StorePre 0x10021e 4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x10021e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10021e 0 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[74, 1]
    (.letOp (n := 77) (.out 0x100222 (movR64M64Effect 0x100222 0 (.rip 0x101f5f)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 78) (.exec 0x100222 (LoadPre 0x100222 (fun s => AddrMode.addr (.rip 0x101f5f) s (0x100222 + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x100222 0 (.rip 0x101f5f)) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.exec 0x100229 (StorePre 0x100229 4 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x100229 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100229 0 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 1] [])) #v[77, 1]
    (.letOp (n := 80) (.out 0x10022d (movR64M64Effect 0x10022d 0 (.rip 0x101f4c)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 81) (.exec 0x10022d (LoadPre 0x10022d (fun s => AddrMode.addr (.rip 0x101f4c) s (0x10022d + BitVec.ofNat 64 7)) 8) (movR64M64Effect 0x10022d 0 (.rip 0x101f4c)) (Reg.operands [] [])) #v[]
    (b_l1001c3_1)))))))))))))))))))))))))))))

def bytes_l1001c3 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x20, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x41, 0x18,
    0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x41, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x89,
    0x41, 0x08, 0x48, 0x8B, 0x04, 0x24, 0x48, 0x89, 0x01, 0x48, 0x8B, 0x05, 0x85, 0x1F, 0x10, 0x00,
    0x48, 0x89, 0x41, 0x18, 0x48, 0x8B, 0x05, 0x72, 0x1F, 0x10, 0x00, 0x48, 0x89, 0x41, 0x10, 0x48,
    0x8B, 0x05, 0x5F, 0x1F, 0x10, 0x00, 0x48, 0x89, 0x41, 0x08, 0x48, 0x8B, 0x05, 0x4C, 0x1F, 0x10,
    0x00] ++ bytes_l1001c3_1

theorem code_l1001c3 : ∀ x ∈ codeRange 0x1001c3 bytes_l1001c3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1c3 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1001c3_1

@[cfg_block] def b_l100240 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100240 (cmpM8Imm8Effect 0x100240 3 (.base 7 .none) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 7] []) (.flag .ZF)) #v[7]
    (.letOp (n := 54) (.exec 0x100240 (LoadPre 0x100240 (fun s => AddrMode.addr (.base 7 .none) s (0x100240 + BitVec.ofNat 64 3)) 1) (cmpM8Imm8Effect 0x100240 3 (.base 7 .none) 0x0) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10025f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100245, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100240 : List UInt8 :=
  [0x80, 0x3F, 0x00, 0x74, 0x1A]

theorem code_l100240 : ∀ x ∈ codeRange 0x100240 bytes_l100240, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x240 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100245 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100245 (movR64R64Effect 0x100245 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 54) (.exec 0x100245 (fun s => s.RIP = 0x100245) (movR64R64Effect 0x100245 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x100248 (movR64M64Effect 0x100248 7 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 56) (.exec 0x100248 (LoadPre 0x100248 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100248 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100248 7 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.out 0x10024c (testR64R64Effect 0x10024c 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x10024c (fun s => s.RIP = 0x10024c) (testR64R64Effect 0x10024c 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10025f, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100251, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100245 : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x8B, 0x7F, 0x08, 0x48, 0x85, 0xFF, 0x74, 0x0E]

theorem code_l100245 : ∀ x ∈ codeRange 0x100245 bytes_l100245, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x245 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100251 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100251 (movR64M64Effect 0x100251 0 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x100251 (LoadPre 0x100251 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x100251 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100251 0 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x100255 (movR64M64Effect 0x100255 0 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x100255 (LoadPre 0x100255 (fun s => AddrMode.addr (.base 0 .none) s (0x100255 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100255 0 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100258 (testR64R64Effect 0x100258 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x100258 (fun s => s.RIP = 0x100258) (testR64R64Effect 0x100258 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10025f, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10025d, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100251 : List UInt8 :=
  [0x48, 0x8B, 0x40, 0x10, 0x48, 0x8B, 0x00, 0x48, 0x85, 0xC0, 0x74, 0x02]

theorem code_l100251 : ∀ x ∈ codeRange 0x100251 bytes_l100251, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x251 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10025d : Block Op Label signature Reg.count 53 :=
  cutBlock 0x10025d

def bytes_l10025d : List UInt8 :=
  [0xFF, 0xE0]

theorem code_l10025d : ∀ x ∈ codeRange 0x10025d bytes_l10025d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25d 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10025f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10025f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 54) (.out 0x10025f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10025f (RetPre 0x10025f) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 54), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56) (some ⟨53, by decide⟩)))))

def bytes_l10025f : List UInt8 :=
  [0xC3]

theorem code_l10025f : ∀ x ∈ codeRange 0x10025f bytes_l10025f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x25f 1 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1002f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1002f0 (pushR64Effect 0x1002f0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1002f0 (PushPre 0x1002f0 1) (pushR64Effect 0x1002f0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1002f1 (pushR64Effect 0x1002f1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1002f1 (PushPre 0x1002f1 2) (pushR64Effect 0x1002f1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1002f3 (pushR64Effect 0x1002f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1002f3 (PushPre 0x1002f3 2) (pushR64Effect 0x1002f3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1002f5 (pushR64Effect 0x1002f5 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x1002f5 (PushPre 0x1002f5 2) (pushR64Effect 0x1002f5 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x1002f7 (pushR64Effect 0x1002f7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x1002f7 (PushPre 0x1002f7 1) (pushR64Effect 0x1002f7 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x1002f8 (subR64Imm8Effect 0x1002f8 4 0x70) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x1002f8 (fun s => s.RIP = 0x1002f8) (subR64Imm8Effect 0x1002f8 4 0x70) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x1002fc (movR64R64Effect 0x1002fc 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 66) (.exec 0x1002fc (fun s => s.RIP = 0x1002fc) (movR64R64Effect 0x1002fc 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x1002ff (movR64R64Effect 0x1002ff 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x1002ff (fun s => s.RIP = 0x1002ff) (movR64R64Effect 0x1002ff 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x100302 (movR32M32LowEffect 0x100302 5 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[2]
    (.letOp (n := 70) (.exec 0x100302 (LoadPre 0x100302 (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x100302 + BitVec.ofNat 64 3)) 4) (movR32M32LowEffect 0x100302 5 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x100305 (leaR64Effect 0x100305 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 72) (.exec 0x100305 (fun s => s.RIP = 0x100305) (leaR64Effect 0x100305 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 73) (.out 0x10030a (movR32R32Effect 0x10030a 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 74) (.exec 0x10030a (fun s => s.RIP = 0x10030a) (movR32R32Effect 0x10030a 2 2 5) (Reg.operands [.gpr 5] [])) #v[69]
    (.letOp (n := 75) (.out 0x10030c (callEffect (fun _ => 0x127b80) 0x100311) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 76) (.exec 0x10030c (PushPre 0x10030c 5) (callEffect (fun _ => 0x127b80) 0x100311) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 77) (.const ⟨64, 0x100311⟩) #v[]
    (.terminate (.call ⟨.l127b80, RegMap.args [(2, 73), (3, 67), (4, 75), (5, 69), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 65), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l100311, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l1002f0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x70, 0x49, 0x89, 0xF6, 0x48,
    0x89, 0xFB, 0x8B, 0x6A, 0x08, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x89, 0xEA, 0xE8, 0x6F, 0x78, 0x02,
    0x00]

theorem code_l1002f0 : ∀ x ∈ codeRange 0x1002f0 bytes_l1002f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2f0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100311 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100311 (movR32M32LowEffect 0x100311 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100311 (LoadPre 0x100311 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100311 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100311 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100315 (cmpR32Imm8Effect 0x100315 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x100315 (fun s => s.RIP = 0x100315) (cmpR32Imm8Effect 0x100315 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100335, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10031a, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l100311 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x08, 0x83, 0xF8, 0x02, 0x75, 0x1B]

theorem code_l100311 : ∀ x ∈ codeRange 0x100311 bytes_l100311, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x311 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10031a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10031a (movR64M64Effect 0x10031a 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10031a (LoadPre 0x10031a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10031a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10031a 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10031f (movR64R64Effect 0x10031f 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10031f (fun s => s.RIP = 0x10031f) (movR64R64Effect 0x10031f 0 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 57) (.out 0x100322 (shrR64Effect 0x100322 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.out 0x100322 (shrR64Effect 0x100322 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[55]
    (.letOp (n := 59) (.exec 0x100322 (fun s => s.RIP = 0x100322) (shrR64Effect 0x100322 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 60) (.pure (condOp 4)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1003ac, RegMap.args [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l10032c, RegMap.args [(0, 57), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l10031a : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x18, 0x4C, 0x89, 0xF8, 0x48, 0xC1, 0xE8, 0x20, 0x0F, 0x84, 0x80, 0x00,
    0x00, 0x00]

theorem code_l10031a : ∀ x ∈ codeRange 0x10031a bytes_l10031a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x31a 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10032c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10032c (xorR32R32Effect 0x10032c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[0, 0]
    (.letOp (n := 54) (.exec 0x10032c (fun s => s.RIP = 0x10032c) (xorR32R32Effect 0x10032c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[0, 0]
    (.letOp (n := 55) (.out 0x10032e (movR32Imm32Effect 0x10032e 5 1 0xc) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10032e (fun s => s.RIP = 0x10032e) (movR32Imm32Effect 0x10032e 5 1 0xc) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l10036b, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10032c : List UInt8 :=
  [0x31, 0xC0, 0xB9, 0x0C, 0x00, 0x00, 0x00, 0xEB, 0x36]

theorem code_l10032c : ∀ x ∈ codeRange 0x10032c bytes_l10032c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x32c 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100335 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100335 (movR32M32LowEffect 0x100335 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x100335 (LoadPre 0x100335 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100335 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100335 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100339 (movR64M64Effect 0x100339 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x100339 (LoadPre 0x100339 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100339 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100339 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10033e (movR64M64Effect 0x10033e 15 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x10033e (LoadPre 0x10033e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10033e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10033e 15 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100343 (movR64M64Effect 0x100343 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x100343 (LoadPre 0x100343 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100343 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100343 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x100348 (StorePre 0x100348 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100348 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100348 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x10034d (movR64M64Effect 0x10034d 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 63) (.exec 0x10034d (LoadPre 0x10034d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10034d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10034d 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x100352 (StorePre 0x100352 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100352 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100352 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x100357 (movR64M64Effect 0x100357 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x100357 (LoadPre 0x100357 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100357 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100357 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x10035c (StorePre 0x10035c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10035c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10035c 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100361 (movR64M64Effect 0x100361 6 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 69) (.exec 0x100361 (LoadPre 0x100361 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100361 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100361 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x100366 (StorePre 0x100366 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100366 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100366 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[68, 4]
    (.terminate (.br ⟨.l10036b, RegMap.args [(0, 0), (1, 55), (2, 53), (3, 3), (4, 4), (6, 68), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l100335 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x0C, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x4C, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0x8B,
    0x74, 0x24, 0x20, 0x48, 0x89, 0x74, 0x24, 0x40, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x89, 0x74,
    0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x30, 0x48, 0x89, 0x74, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24,
    0x38, 0x48, 0x89, 0x74, 0x24, 0x58]

theorem code_l100335 : ∀ x ∈ codeRange 0x100335 bytes_l100335, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x335 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10036b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10036b (StorePre 0x10036b 2 (fun s => AddrMode.addr (.base 3 .none) s (0x10036b + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x10036b 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 54) (.exec 0x10036d (StorePre 0x10036d 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x10036d + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x10036d 2 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[2, 3]
    (.letOp (n := 55) (.exec 0x100370 (StorePre 0x100370 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100370 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100370 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 56) (.exec 0x100374 (StorePre 0x100374 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100374 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100374 15 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 57) (.out 0x100378 (movR64M64Effect 0x100378 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x100378 (LoadPre 0x100378 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100378 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100378 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10037d (movR64M64Effect 0x10037d 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x10037d (LoadPre 0x10037d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10037d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10037d 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x100382 (StorePre 0x100382 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x100382 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100382 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 62) (.exec 0x100386 (StorePre 0x100386 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x100386 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100386 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x10038a (movR64M64Effect 0x10038a 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x10038a (LoadPre 0x10038a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10038a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10038a 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10038f (StorePre 0x10038f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x10038f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10038f 0 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x100393 (movR64M64Effect 0x100393 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x100393 (LoadPre 0x100393 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100393 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100393 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x100398 (StorePre 0x100398 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x100398 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100398 0 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[66, 3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(0, 66), (1, 59), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l10036b : List UInt8 :=
  [0x89, 0x03, 0x89, 0x53, 0x04, 0x48, 0x89, 0x4B, 0x08, 0x4C, 0x89, 0x7B, 0x10, 0x48, 0x8B, 0x44,
    0x24, 0x40, 0x48, 0x8B, 0x4C, 0x24, 0x48, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4B, 0x20, 0x48,
    0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x43, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x89, 0x43,
    0x30]

theorem code_l10036b : ∀ x ∈ codeRange 0x10036b bytes_l10036b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x36b 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10039c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10039c (movR64R64Effect 0x10039c 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10039c (fun s => s.RIP = 0x10039c) (movR64R64Effect 0x10039c 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10039f (addR64Imm8Effect 0x10039f 4 0x70) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10039f (fun s => s.RIP = 0x10039f) (addR64Imm8Effect 0x10039f 4 0x70) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1003a3 (popR64Effect 0x1003a3 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1003a3 (popR64Effect 0x1003a3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1003a3 (PopPre 0x1003a3) (popR64Effect 0x1003a3 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1003a4 (popR64Effect 0x1003a4 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1003a4 (popR64Effect 0x1003a4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1003a4 (PopPre 0x1003a4) (popR64Effect 0x1003a4 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1003a6 (popR64Effect 0x1003a6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[61]
    (.letOp (n := 64) (.out 0x1003a6 (popR64Effect 0x1003a6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1003a6 (PopPre 0x1003a6) (popR64Effect 0x1003a6 2 14) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1003a8 (popR64Effect 0x1003a8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[64]
    (.letOp (n := 67) (.out 0x1003a8 (popR64Effect 0x1003a8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1003a8 (PopPre 0x1003a8) (popR64Effect 0x1003a8 2 15) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1003aa (popR64Effect 0x1003aa 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 70) (.out 0x1003aa (popR64Effect 0x1003aa 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1003aa (PopPre 0x1003aa) (popR64Effect 0x1003aa 1 5) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1003ab (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[70]
    (.letOp (n := 73) (.out 0x1003ab (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1003ab (RetPre 0x1003ab) (retEffect) (Reg.operands [.gpr 4] [])) #v[70]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 69), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 13), (14, 63), (15, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 75) (some ⟨72, by decide⟩))))))))))))))))))))))))

def bytes_l10039c : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x70, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10039c : ∀ x ∈ codeRange 0x10039c bytes_l10039c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x39c 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003ac (movR64Imm64Effect 0x1003ac 0 0x100000007) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 54) (.exec 0x1003ac (fun s => s.RIP = 0x1003ac) (movR64Imm64Effect 0x1003ac 0 0x100000007) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1003b6 (testR64R64Effect 0x1003b6 15 15) (EffectPart.reads (.flag .ZF) [.gpr 15, .gpr 15] []) (.flag .ZF)) #v[15, 15]
    (.letOp (n := 56) (.exec 0x1003b6 (fun s => s.RIP = 0x1003b6) (testR64R64Effect 0x1003b6 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100484, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1003bf, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1003ac : List UInt8 :=
  [0x48, 0xB8, 0x07, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x4D, 0x85, 0xFF, 0x0F, 0x84, 0xC5,
    0x00, 0x00, 0x00]

theorem code_l1003ac : ∀ x ∈ codeRange 0x1003ac bytes_l1003ac, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ac 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003bf : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003bf (movR64M64Effect 0x1003bf 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1003bf (LoadPre 0x1003bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1003bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1003bf 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1003c4 (cmpR32Imm8Effect 0x1003c4 4 15 0x1) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 56) (.exec 0x1003c4 (fun s => s.RIP = 0x1003c4) (cmpR32Imm8Effect 0x1003c4 4 15 0x1) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1003d9, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1003ca, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1003bf : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x10, 0x41, 0x83, 0xFF, 0x01, 0x75, 0x0F]

theorem code_l1003bf : ∀ x ∈ codeRange 0x1003bf bytes_l1003bf, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3bf 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003ca : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003ca (movzxR32M8Effect 0x1003ca 3 2 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 54) (.exec 0x1003ca (LoadPre 0x1003ca (fun s => AddrMode.addr (.base 1 .none) s (0x1003ca + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1003ca 3 2 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1003cd (testR8R8Effect 0x1003cd 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1003cd (fun s => s.RIP = 0x1003cd) (testR8R8Effect 0x1003cd 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1003e4, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1003d1, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1003ca : List UInt8 :=
  [0x0F, 0xB6, 0x11, 0x84, 0xD2, 0x75, 0x13]

theorem code_l1003ca : ∀ x ∈ codeRange 0x1003ca bytes_l1003ca, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ca 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003d1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003d1 (movR32Imm32Effect 0x1003d1 6 15 0x1) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 54) (.exec 0x1003d1 (fun s => s.RIP = 0x1003d1) (movR32Imm32Effect 0x1003d1 6 15 0x1) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1003ec, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1003d1 : List UInt8 :=
  [0x41, 0xBF, 0x01, 0x00, 0x00, 0x00, 0xEB, 0x13]

theorem code_l1003d1 : ∀ x ∈ codeRange 0x1003d1 bytes_l1003d1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d1 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003d9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003d9 (movzxR32M8Effect 0x1003d9 3 2 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 54) (.exec 0x1003d9 (LoadPre 0x1003d9 (fun s => AddrMode.addr (.base 1 .none) s (0x1003d9 + BitVec.ofNat 64 3)) 1) (movzxR32M8Effect 0x1003d9 3 2 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x1003dc (testR8R8Effect 0x1003dc 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1003dc (fun s => s.RIP = 0x1003dc) (testR8R8Effect 0x1003dc 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10047e, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1003e4, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1003d9 : List UInt8 :=
  [0x0F, 0xB6, 0x11, 0x84, 0xD2, 0x0F, 0x84, 0x9A, 0x00, 0x00, 0x00]

theorem code_l1003d9 : ∀ x ∈ codeRange 0x1003d9 bytes_l1003d9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3d9 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003e4 (testR8R8Effect 0x1003e4 2 2 2) (EffectPart.reads (.flag .SF) [.gpr 2, .gpr 2] []) (.flag .SF)) #v[2, 2]
    (.letOp (n := 54) (.exec 0x1003e4 (fun s => s.RIP = 0x1003e4) (testR8R8Effect 0x1003e4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 55) (.pure (condOp 8)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100478, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1003ec, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1003e4 : List UInt8 :=
  [0x84, 0xD2, 0x0F, 0x88, 0x8C, 0x00, 0x00, 0x00]

theorem code_l1003e4 : ∀ x ∈ codeRange 0x1003e4 bytes_l1003e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3e4 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1003ec : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1003ec (decR64Effect 0x1003ec 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x1003ec (fun s => s.RIP = 0x1003ec) (decR64Effect 0x1003ec 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 55) (.out 0x1003ef (incR64Effect 0x1003ef 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x1003ef (fun s => s.RIP = 0x1003ef) (incR64Effect 0x1003ef 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.letOp (n := 57) (.exec 0x1003f2 (fun s => s.RIP = 0x1003f2) (fun _ => nopEffect 0x1003f2 14) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100400, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1003ec : List UInt8 :=
  [0x48, 0xFF, 0xC9, 0x49, 0xFF, 0xC7, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00,
    0x00, 0x00, 0x00, 0x00]

theorem code_l1003ec : ∀ x ∈ codeRange 0x1003ec bytes_l1003ec, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x3ec 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100400 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100400 (leaR64Effect 0x100400 12 (.base 1 (.d8 0x1))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[1]
    (.letOp (n := 54) (.exec 0x100400 (fun s => s.RIP = 0x100400) (leaR64Effect 0x100400 12 (.base 1 (.d8 0x1))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x100404 (cmpR64Imm8Effect 0x100404 15 0x2) (EffectPart.reads (.flag .ZF) [.gpr 15] []) (.flag .ZF)) #v[15]
    (.letOp (n := 56) (.exec 0x100404 (fun s => s.RIP = 0x100404) (cmpR64Imm8Effect 0x100404 15 0x2) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x100408 (leaR64Effect 0x100408 15 (.base 15 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 58) (.exec 0x100408 (fun s => s.RIP = 0x100408) (leaR64Effect 0x100408 15 (.base 15 (.d8 0xff))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 59) ⟨.l100417, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 57), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l10040e, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 57), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100400 : List UInt8 :=
  [0x4C, 0x8D, 0x61, 0x01, 0x49, 0x83, 0xFF, 0x02, 0x4D, 0x8D, 0x7F, 0xFF, 0x74, 0x09]

theorem code_l100400 : ∀ x ∈ codeRange 0x100400 bytes_l100400, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x400 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10040e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10040e (cmpM8Imm8Effect 0x10040e 4 (.base 1 (.d8 0x1)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[1]
    (.letOp (n := 54) (.exec 0x10040e (LoadPre 0x10040e (fun s => AddrMode.addr (.base 1 (.d8 0x1)) s (0x10040e + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x10040e 4 (.base 1 (.d8 0x1)) 0x0) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x100412 (movR64R64Effect 0x100412 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 56) (.exec 0x100412 (fun s => s.RIP = 0x100412) (movR64R64Effect 0x100412 1 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 57) ⟨.l100400, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l100417, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10040e : List UInt8 :=
  [0x80, 0x79, 0x01, 0x00, 0x4C, 0x89, 0xE1, 0x74, 0xE9]

theorem code_l10040e : ∀ x ∈ codeRange 0x10040e bytes_l10040e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x40e 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100417 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100417 (movR64R64Effect 0x100417 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 54) (.exec 0x100417 (fun s => s.RIP = 0x100417) (movR64R64Effect 0x100417 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 55) (.out 0x10041a (shrR64Effect 0x10041a 4 1 32) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.out 0x10041a (shrR64Effect 0x10041a 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[53]
    (.letOp (n := 57) (.exec 0x10041a (fun s => s.RIP = 0x10041a) (shrR64Effect 0x10041a 4 1 32) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 58) (.pure (condOp 4)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l10043b, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l100420, RegMap.args [(0, 0), (1, 55), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l100417 : List UInt8 :=
  [0x4C, 0x89, 0xF9, 0x48, 0xC1, 0xE9, 0x20, 0x74, 0x1B]

theorem code_l100417 : ∀ x ∈ codeRange 0x100417 bytes_l100417, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x417 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100420 (StorePre 0x100420 6 (fun s => AddrMode.addr (.base 3 .none) s (0x100420 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x100420 6 (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.out 0x100426 (addR64Imm8Effect 0x100426 0 0xfe) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 55) (.exec 0x100426 (fun s => s.RIP = 0x100426) (addR64Imm8Effect 0x100426 0 0xfe) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 56) (.exec 0x10042a (StorePre 0x10042a 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10042a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10042a 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 57) (.exec 0x10042e (StorePre 0x10042e 8 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10042e + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10042e (.base 3 (.d8 0x10)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l100420 : List UInt8 :=
  [0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xC0, 0xFE, 0x48, 0x89, 0x43, 0x08, 0x48, 0xC7,
    0x43, 0x10, 0x00, 0x00, 0x00, 0x00, 0xE9, 0x61, 0xFF, 0xFF, 0xFF]

theorem code_l100420 : ∀ x ∈ codeRange 0x100420 bytes_l100420, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x420 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10043b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10043b (StorePre 0x10043b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10043b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10043b 12 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 54) (.exec 0x100440 (StorePre 0x100440 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100440 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100440 15 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 55) (.out 0x100445 (leaR64Effect 0x100445 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x100445 (fun s => s.RIP = 0x100445) (leaR64Effect 0x100445 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10044a (leaR64Effect 0x10044a 6 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x10044a (fun s => s.RIP = 0x10044a) (leaR64Effect 0x10044a 6 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10044f (callEffect (fun _ => 0x1275f0) 0x100454) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10044f (PushPre 0x10044f 5) (callEffect (fun _ => 0x1275f0) 0x100454) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100454⟩) #v[]
    (.terminate (.call ⟨.l1275f0, RegMap.args [(2, 2), (3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l100454, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10043b : List UInt8 :=
  [0x4C, 0x89, 0x64, 0x24, 0x60, 0x4C, 0x89, 0x7C, 0x24, 0x68, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48,
    0x8D, 0x74, 0x24, 0x60, 0xE8, 0x9C, 0x71, 0x02, 0x00]

theorem code_l10043b : ∀ x ∈ codeRange 0x10043b bytes_l10043b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x43b 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100454 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100454 (movR32M32LowEffect 0x100454 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x100454 (LoadPre 0x100454 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100454 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100454 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100458 (movR32M32LowEffect 0x100458 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x100458 (LoadPre 0x100458 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100458 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100458 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10045c (cmpR32Imm8Effect 0x10045c 3 1 0x2) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x10045c (fun s => s.RIP = 0x10045c) (cmpR32Imm8Effect 0x10045c 3 1 0x2) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10049f, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100461, RegMap.args [(0, 55), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100454 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x08, 0x8B, 0x44, 0x24, 0x0C, 0x83, 0xF9, 0x02, 0x75, 0x3E]

theorem code_l100454 : ∀ x ∈ codeRange 0x100454 bytes_l100454, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x454 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100461 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100461 (cmpR32R32Effect 0x100461 2 0 5) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 5] []) (.flag .ZF)) #v[0, 5]
    (.letOp (n := 54) (.exec 0x100461 (fun s => s.RIP = 0x100461) (cmpR32R32Effect 0x100461 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[0, 5]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1004df, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100465, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100461 : List UInt8 :=
  [0x39, 0xE8, 0x75, 0x7A]

theorem code_l100461 : ∀ x ∈ codeRange 0x100461 bytes_l100461, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x461 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100465 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100465 (StorePre 0x100465 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100465 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100465 12 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 54) (.exec 0x100469 (StorePre 0x100469 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100469 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100469 15 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 55) (.exec 0x10046d (StorePre 0x10046d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10046d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10046d 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100465 : List UInt8 :=
  [0x4C, 0x89, 0x63, 0x08, 0x4C, 0x89, 0x7B, 0x10, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00, 0xE9, 0x24,
    0xFF, 0xFF, 0xFF]

theorem code_l100465 : ∀ x ∈ codeRange 0x100465 bytes_l100465, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x465 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100478 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100478 (addR64Imm8Effect 0x100478 0 0xe) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x100478 (fun s => s.RIP = 0x100478) (addR64Imm8Effect 0x100478 0 0xe) (Reg.operands [.gpr 0] [])) #v[0]
    (.terminate (.br ⟨.l100484, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l100478 : List UInt8 :=
  [0x48, 0x83, 0xC0, 0x0E, 0xEB, 0x06]

theorem code_l100478 : ∀ x ∈ codeRange 0x100478 bytes_l100478, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x478 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10047e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10047e (cmpM8Imm8Effect 0x10047e 4 (.base 1 (.d8 0x1)) 0x0) (EffectPart.reads (.flag .SF) [.gpr 1] []) (.flag .SF)) #v[1]
    (.letOp (n := 54) (.exec 0x10047e (LoadPre 0x10047e (fun s => AddrMode.addr (.base 1 (.d8 0x1)) s (0x10047e + BitVec.ofNat 64 4)) 1) (cmpM8Imm8Effect 0x10047e 4 (.base 1 (.d8 0x1)) 0x0) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.pure (condOp 8)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100502, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100484, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (20, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10047e : List UInt8 :=
  [0x80, 0x79, 0x01, 0x00, 0x78, 0x7E]

theorem code_l10047e : ∀ x ∈ codeRange 0x10047e bytes_l10047e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x47e 6 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100484 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100484 (StorePre 0x100484 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x100484 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x100484 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x100489 (movR32M32Effect 0x100489 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x100489 (LoadPre 0x100489 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x100489 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x100489 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x10048d (StorePre 0x10048d 6 (fun s => AddrMode.addr (.base 3 .none) s (0x10048d + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x10048d 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x100493 (StorePre 0x100493 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x100493 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x100493 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x100496 (StorePre 0x100496 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100496 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100496 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(0, 0), (1, 54), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l100484 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x4B, 0x04, 0x48, 0x89, 0x43, 0x08, 0xE9, 0xFD, 0xFE, 0xFF, 0xFF]

theorem code_l100484 : ∀ x ∈ codeRange 0x100484 bytes_l100484, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x484 27 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10049f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10049f (movR64M64Effect 0x10049f 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x10049f (LoadPre 0x10049f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10049f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10049f 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1004a4 (StorePre 0x1004a4 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1004a4 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004a4 2 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 56) (.out 0x1004a8 (movR64M64Effect 0x1004a8 2 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 57) (.exec 0x1004a8 (LoadPre 0x1004a8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1004a8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004a8 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1004ad (StorePre 0x1004ad 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1004ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004ad 2 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 59) (.out 0x1004b1 (movR64M64Effect 0x1004b1 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x1004b1 (LoadPre 0x1004b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1004b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004b1 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1004b6 (StorePre 0x1004b6 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1004b6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004b6 2 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 62) (.out 0x1004ba (movR64M64Effect 0x1004ba 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x1004ba (LoadPre 0x1004ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1004ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004ba 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1004bf (StorePre 0x1004bf 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1004bf + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004bf 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 65) (.out 0x1004c3 (movR64M64Effect 0x1004c3 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x1004c3 (LoadPre 0x1004c3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1004c3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004c3 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1004c8 (movR64M64Effect 0x1004c8 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x1004c8 (LoadPre 0x1004c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1004c8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1004c8 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1004cd (StorePre 0x1004cd 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x1004cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004cd 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[67, 3]
    (.letOp (n := 70) (.exec 0x1004d1 (StorePre 0x1004d1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1004d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1004d1 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 71) (.exec 0x1004d5 (StorePre 0x1004d5 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1004d5 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1004d5 1 (.base 3 .none)) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 72) (.exec 0x1004d7 (StorePre 0x1004d7 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1004d7 + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1004d7 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(0, 0), (1, 1), (2, 65), (3, 3), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l10049f : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x38, 0x48, 0x89, 0x53, 0x30, 0x48, 0x8B, 0x54, 0x24, 0x30, 0x48, 0x89,
    0x53, 0x28, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0x53, 0x20, 0x48, 0x8B, 0x54, 0x24, 0x20,
    0x48, 0x89, 0x53, 0x18, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x89,
    0x73, 0x10, 0x48, 0x89, 0x53, 0x08, 0x89, 0x0B, 0x89, 0x43, 0x04, 0xE9, 0xBD, 0xFE, 0xFF, 0xFF]

theorem code_l10049f : ∀ x ∈ codeRange 0x10049f bytes_l10049f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x49f 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1004df : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1004df (StorePre 0x1004df 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1004df + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1004df (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1004e4 (movR32M32Effect 0x1004e4 0 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 55) (.exec 0x1004e4 (LoadPre 0x1004e4 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1004e4 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1004e4 0 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.exec 0x1004e8 (StorePre 0x1004e8 6 (fun s => AddrMode.addr (.base 3 .none) s (0x1004e8 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x1004e8 6 (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x1004ee (StorePre 0x1004ee 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1004ee + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1004ee 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[54, 3]
    (.letOp (n := 58) (.exec 0x1004f1 (StorePre 0x1004f1 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1004f1 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x1004f1 (.base 3 (.d8 0x8)) 0x7) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 59) (.exec 0x1004f5 (StorePre 0x1004f5 8 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1004f5 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1004f5 (.base 3 (.d8 0xc)) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l10039c, RegMap.args [(0, 54), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1004df : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x46, 0x1C, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00, 0x89,
    0x43, 0x04, 0xC6, 0x43, 0x08, 0x07, 0x48, 0xC7, 0x43, 0x0C, 0x01, 0x00, 0x00, 0x00, 0xE9, 0x9A,
    0xFE, 0xFF, 0xFF]

theorem code_l1004df : ∀ x ∈ codeRange 0x1004df bytes_l1004df, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x4df 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100502 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100502 (incR64Effect 0x100502 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x100502 (fun s => s.RIP = 0x100502) (incR64Effect 0x100502 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 55) (.out 0x100505 (decR64Effect 0x100505 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 56) (.exec 0x100505 (fun s => s.RIP = 0x100505) (decR64Effect 0x100505 15) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[15]
    (.terminate (.br ⟨.l1003ec, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100502 : List UInt8 :=
  [0x48, 0xFF, 0xC1, 0x49, 0xFF, 0xCF, 0xE9, 0xDF, 0xFE, 0xFF, 0xFF]

theorem code_l100502 : ∀ x ∈ codeRange 0x100502 bytes_l100502, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x502 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100510 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100510 (pushR64Effect 0x100510 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100510 (PushPre 0x100510 1) (pushR64Effect 0x100510 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100511 (pushR64Effect 0x100511 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100511 (PushPre 0x100511 2) (pushR64Effect 0x100511 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100513 (pushR64Effect 0x100513 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100513 (PushPre 0x100513 2) (pushR64Effect 0x100513 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100515 (pushR64Effect 0x100515 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100515 (PushPre 0x100515 2) (pushR64Effect 0x100515 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100517 (pushR64Effect 0x100517 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100517 (PushPre 0x100517 2) (pushR64Effect 0x100517 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100519 (pushR64Effect 0x100519 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100519 (PushPre 0x100519 1) (pushR64Effect 0x100519 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10051a (subR64Imm32Effect 0x10051a 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10051a (fun s => s.RIP = 0x10051a) (subR64Imm32Effect 0x10051a 4 0xb8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100521 (movR64R64Effect 0x100521 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x100521 (fun s => s.RIP = 0x100521) (movR64R64Effect 0x100521 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x100524 (movR64R64Effect 0x100524 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x100524 (fun s => s.RIP = 0x100524) (movR64R64Effect 0x100524 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x100527 (leaR64Effect 0x100527 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 72) (.exec 0x100527 (fun s => s.RIP = 0x100527) (leaR64Effect 0x100527 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 73) (.out 0x10052c (callEffect (fun _ => 0x106900) 0x100531) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 74) (.exec 0x10052c (PushPre 0x10052c 5) (callEffect (fun _ => 0x106900) 0x100531) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.const ⟨64, 0x100531⟩) #v[]
    (.terminate (.call ⟨.l106900, RegMap.args [(3, 69), (4, 73), (5, 5), (6, 6), (7, 71), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ { target := .l100531, kept := #v[], arity := rfl, guard := some (Fin.last 75) }))))))))))))))))))))))))

def bytes_l100510 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0xE8, 0xCF, 0x63, 0x00,
    0x00]

theorem code_l100510 : ∀ x ∈ codeRange 0x100510 bytes_l100510, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x510 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100531 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100531 (movR32M32LowEffect 0x100531 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100531 (LoadPre 0x100531 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100531 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100531 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100535 (movR64M64Effect 0x100535 15 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 56) (.exec 0x100535 (LoadPre 0x100535 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100535 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100535 15 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10053a (movzxR32M8Effect 0x10053a 5 5 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x10053a (LoadPre 0x10053a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10053a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10053a 5 5 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10053f (cmpR32Imm8Effect 0x10053f 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 60) (.exec 0x10053f (fun s => s.RIP = 0x10053f) (cmpR32Imm8Effect 0x10053f 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l100582, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l100544, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 55), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l100531 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x7C, 0x24, 0x14, 0x0F, 0xB6, 0x6C, 0x24, 0x1C, 0x83, 0xF8,
    0x02, 0x75, 0x3E]

theorem code_l100531 : ∀ x ∈ codeRange 0x100531 bytes_l100531, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x531 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100544 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100544 (leaR64Effect 0x100544 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x100544 (fun s => s.RIP = 0x100544) (leaR64Effect 0x100544 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100549 (movR64R64Effect 0x100549 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x100549 (fun s => s.RIP = 0x100549) (movR64R64Effect 0x100549 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x10054c (callEffect (fun _ => 0x106120) 0x100551) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10054c (PushPre 0x10054c 5) (callEffect (fun _ => 0x106120) 0x100551) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x100551⟩) #v[]
    (.terminate (.call ⟨.l106120, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l100551, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l100544 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0xF6, 0xE8, 0xCF, 0x5B, 0x00, 0x00]

theorem code_l100544 : ∀ x ∈ codeRange 0x100544 bytes_l100544, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x544 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100551 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100551 (movR32M32LowEffect 0x100551 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100551 (LoadPre 0x100551 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100551 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100551 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100555 (movR32M32LowEffect 0x100555 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x100555 (LoadPre 0x100555 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100555 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100555 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100559 (cmpR32Imm8Effect 0x100559 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x100559 (fun s => s.RIP = 0x100559) (cmpR32Imm8Effect 0x100559 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1005e6, RegMap.args [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100562, RegMap.args [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100551 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x8B, 0x4C, 0x24, 0x14, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x84, 0x00, 0x00,
    0x00]

theorem code_l100551 : ∀ x ∈ codeRange 0x100551 bytes_l100551, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x551 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100562 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100562 (movR32R32Effect 0x100562 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 54) (.exec 0x100562 (fun s => s.RIP = 0x100562) (movR32R32Effect 0x100562 2 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x100564 (andR8Imm8Effect 0x100564 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x100564 (fun s => s.RIP = 0x100564) (andR8Imm8Effect 0x100564 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x100567 (movR64R64Effect 0x100567 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 58) (.exec 0x100567 (fun s => s.RIP = 0x100567) (movR64R64Effect 0x100567 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10056a (shrR64Effect 0x10056a 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x10056a (fun s => s.RIP = 0x10056a) (shrR64Effect 0x10056a 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x10056e (movR32R32Effect 0x10056e 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 62) (.exec 0x10056e (fun s => s.RIP = 0x10056e) (movR32R32Effect 0x10056e 2 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 63) (.out 0x100570 (movR32R32Effect 0x100570 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 64) (.exec 0x100570 (fun s => s.RIP = 0x100570) (movR32R32Effect 0x100570 2 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x100572 (shrR32Effect 0x100572 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[63]
    (.letOp (n := 66) (.exec 0x100572 (fun s => s.RIP = 0x100572) (shrR32Effect 0x100572 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[63]
    (.letOp (n := 67) (.out 0x100575 (movR32Imm32Effect 0x100575 5 0 0x2) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 68) (.exec 0x100575 (fun s => s.RIP = 0x100575) (movR32Imm32Effect 0x100575 5 0 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x10057a (movR32R32Effect 0x10057a 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 70) (.exec 0x10057a (fun s => s.RIP = 0x10057a) (movR32R32Effect 0x10057a 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l100666, RegMap.args [(0, 67), (1, 69), (2, 55), (3, 3), (4, 4), (5, 61), (7, 65), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l100562 : List UInt8 :=
  [0x89, 0xEA, 0x80, 0xE2, 0x01, 0x4D, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x20, 0x89, 0xCD, 0x89, 0xCF,
    0xC1, 0xEF, 0x08, 0xB8, 0x02, 0x00, 0x00, 0x00, 0x44, 0x89, 0xF9, 0xE9, 0xE4, 0x00, 0x00, 0x00]

theorem code_l100562 : ∀ x ∈ codeRange 0x100562 bytes_l100562, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x562 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100582 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100582 (movzxR32M8Effect 0x100582 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x100582 (LoadPre 0x100582 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x100582 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100582 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100587 (shlR32Effect 0x100587 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x100587 (fun s => s.RIP = 0x100587) (shlR32Effect 0x100587 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10058a (movzxR32M16Effect 0x10058a 5 7 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10058a (LoadPre 0x10058a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10058a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10058a 5 7 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10058f (orR32R32Effect 0x10058f 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10058f (fun s => s.RIP = 0x10058f) (orR32R32Effect 0x10058f 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x100591 (movzxR32M8Effect 0x100591 5 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x100591 (LoadPre 0x100591 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100591 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100591 5 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x100596 (movR64M64Effect 0x100596 1 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x100596 (LoadPre 0x100596 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100596 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100596 1 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10059b (StorePre 0x10059b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10059b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10059b 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x1005a3 (movR64M64Effect 0x1005a3 1 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x1005a3 (LoadPre 0x1005a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x1005a3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005a3 1 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1005a8 (StorePre 0x1005a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1005a8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005a8 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x1005b0 (movR64M64Effect 0x1005b0 1 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x1005b0 (LoadPre 0x1005b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1005b0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005b0 1 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1005b5 (StorePre 0x1005b5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1005b5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005b5 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x1005bd (movR64M64Effect 0x1005bd 1 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x1005bd (LoadPre 0x1005bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1005bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005bd 1 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1005c2 (StorePre 0x1005c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1005c2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005c2 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x1005ca (movR64M64Effect 0x1005ca 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x1005ca (LoadPre 0x1005ca (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1005ca + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1005ca 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x1005cf (StorePre 0x1005cf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1005cf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1005cf 1 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x1005d7 (movR64R64Effect 0x1005d7 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 15] []) (.reg (.gpr 8))) #v[15]
    (.letOp (n := 79) (.exec 0x1005d7 (fun s => s.RIP = 0x1005d7) (movR64R64Effect 0x1005d7 8 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 80) (.out 0x1005da (shrR64Effect 0x1005da 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[78]
    (.letOp (n := 81) (.exec 0x1005da (fun s => s.RIP = 0x1005da) (shrR64Effect 0x1005da 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 82) (.out 0x1005de (movR32R32Effect 0x1005de 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 83) (.exec 0x1005de (fun s => s.RIP = 0x1005de) (movR32R32Effect 0x1005de 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l100666, RegMap.args [(0, 0), (1, 82), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l100582 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0xC1, 0xE1, 0x10, 0x0F, 0xB7, 0x7C, 0x24, 0x1D, 0x09, 0xCF, 0x0F,
    0xB6, 0x54, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x21, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x4C, 0x24, 0x29, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x4C, 0x24, 0x31, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x39,
    0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x89, 0x8C,
    0x24, 0x9F, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x20, 0x44, 0x89, 0xF9, 0xE9,
    0x80, 0x00, 0x00, 0x00]

theorem code_l100582 : ∀ x ∈ codeRange 0x100582 bytes_l100582, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x582 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005e6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1005e6 (movzxR32M8Effect 0x1005e6 5 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1005e6 (LoadPre 0x1005e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1005e6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1005e6 5 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1005eb (cmpR8Imm8Effect 0x1005eb 3 2 0xd) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1005eb (fun s => s.RIP = 0x1005eb) (cmpR8Imm8Effect 0x1005eb 3 2 0xd) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100602, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1005f0, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1005e6 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x18, 0x80, 0xFA, 0x0D, 0x75, 0x12]

theorem code_l1005e6 : ∀ x ∈ codeRange 0x1005e6 bytes_l1005e6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5e6 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1005f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1005f0 (StorePre 0x1005f0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1005f0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1005f0 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1005f5 (movR32M32Effect 0x1005f5 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x1005f5 (LoadPre 0x1005f5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1005f5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1005f5 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1005f9 (movR32Imm32Effect 0x1005f9 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x1005f9 (fun s => s.RIP = 0x1005f9) (movR32Imm32Effect 0x1005f9 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1005fe (movR8Imm8Effect 0x1005fe 2 2 0x5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 59) (.exec 0x1005fe (fun s => s.RIP = 0x1005fe) (movR8Imm8Effect 0x1005fe 2 2 0x5) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l100607, RegMap.args [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1005f0 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xB2, 0x05,
    0xEB, 0x05]

theorem code_l1005f0 : ∀ x ∈ codeRange 0x1005f0 bytes_l1005f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5f0 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100602 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100602 (movR64M64Effect 0x100602 15 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x100602 (LoadPre 0x100602 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100602 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100602 15 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l100607, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l100602 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x1C]

theorem code_l100602 : ∀ x ∈ codeRange 0x100602 bytes_l100602, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x602 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100607 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100607 (StorePre 0x100607 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100607 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100607 4 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.exec 0x10060b (StorePre 0x10060b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10060b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10060b 15 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 55) (.out 0x100610 (movR32M32Effect 0x100610 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x100610 (LoadPre 0x100610 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100610 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100610 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100615 (movR32R32Effect 0x100615 3 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[15]
    (.letOp (n := 58) (.exec 0x100615 (fun s => s.RIP = 0x100615) (movR32R32Effect 0x100615 3 7 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x100618 (shrR32Effect 0x100618 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x100618 (fun s => s.RIP = 0x100618) (shrR32Effect 0x100618 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x10061b (movR64R64Effect 0x10061b 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 62) (.exec 0x10061b (fun s => s.RIP = 0x10061b) (movR64R64Effect 0x10061b 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 63) (.out 0x10061e (shrR64Effect 0x10061e 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x10061e (fun s => s.RIP = 0x10061e) (shrR64Effect 0x10061e 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100622 (movR64M64Effect 0x100622 6 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x100622 (LoadPre 0x100622 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100622 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100622 6 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x100627 (movR64M64Effect 0x100627 9 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 68) (.exec 0x100627 (LoadPre 0x100627 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x100627 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100627 9 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10062c (StorePre 0x10062c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10062c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10062c 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x100634 (StorePre 0x100634 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100634 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100634 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x10063c (movR64M64Effect 0x10063c 6 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x10063c (LoadPre 0x10063c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x10063c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10063c 6 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x100641 (StorePre 0x100641 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100641 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100641 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x100649 (movR64M64Effect 0x100649 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 75) (.exec 0x100649 (LoadPre 0x100649 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100649 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100649 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10064e (StorePre 0x10064e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x10064e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10064e 6 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x100656 (movR64M64Effect 0x100656 6 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x100656 (LoadPre 0x100656 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100656 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100656 6 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10065b (StorePre 0x10065b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10065b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10065b 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x100663 (movR32R32Effect 0x100663 3 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[15]
    (.letOp (n := 81) (.exec 0x100663 (fun s => s.RIP = 0x100663) (movR32R32Effect 0x100663 3 5 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.terminate (.br ⟨.l100666, RegMap.args [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 80), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l100607 : List UInt8 :=
  [0x88, 0x54, 0x24, 0x18, 0x4C, 0x89, 0x7C, 0x24, 0x1C, 0x44, 0x8B, 0x44, 0x24, 0x18, 0x44, 0x89,
    0xFF, 0xC1, 0xEF, 0x08, 0x4C, 0x89, 0xFA, 0x48, 0xC1, 0xEA, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x29,
    0x4C, 0x8B, 0x4C, 0x24, 0x31, 0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x8C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x39, 0x48, 0x89, 0xB4, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x89, 0xB4, 0x24, 0x9F, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x74, 0x24, 0x21, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x89, 0xFD]

theorem code_l100607 : ∀ x ∈ codeRange 0x100607 bytes_l100607, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x607 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100666 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100666 (shlR64Effect 0x100666 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 54) (.exec 0x100666 (fun s => s.RIP = 0x100666) (shlR64Effect 0x100666 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 55) (.out 0x10066a (movR32R32Effect 0x10066a 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 56) (.exec 0x10066a (fun s => s.RIP = 0x10066a) (movR32R32Effect 0x10066a 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x10066c (orR64R64Effect 0x10066c 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x10066c (fun s => s.RIP = 0x10066c) (orR64R64Effect 0x10066c 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x10066f (shlR32Effect 0x10066f 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 60) (.exec 0x10066f (fun s => s.RIP = 0x10066f) (shlR32Effect 0x10066f 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7]
    (.letOp (n := 61) (.out 0x100672 (movzxR32R8Effect 0x100672 4 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 62) (.exec 0x100672 (fun s => s.RIP = 0x100672) (movzxR32R8Effect 0x100672 4 8 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x100676 (orR32R32Effect 0x100676 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x100676 (fun s => s.RIP = 0x100676) (orR32R32Effect 0x100676 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x100679 (movzxR32M16Effect 0x100679 8 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x100679 (LoadPre 0x100679 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100679 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x100679 8 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x100681 (StorePre 0x100681 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100681 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100681 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100686 (movzxR32M8Effect 0x100686 8 7 (.sib 4 none 0 (.d32 0x82))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x100686 (LoadPre 0x100686 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x100686 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100686 8 7 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x10068e (StorePre 0x10068e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10068e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10068e 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x100693 (cmpR32Imm8Effect 0x100693 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 72) (.exec 0x100693 (fun s => s.RIP = 0x100693) (cmpR32Imm8Effect 0x100693 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l10091f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l10069c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l100666 : List UInt8 :=
  [0x49, 0xC1, 0xE0, 0x20, 0x89, 0xCE, 0x4C, 0x09, 0xC6, 0xC1, 0xE7, 0x08, 0x44, 0x0F, 0xB6, 0xC5,
    0x41, 0x09, 0xF8, 0x0F, 0xB7, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x66, 0x89, 0x7C, 0x24, 0x0C,
    0x0F, 0xB6, 0xBC, 0x24, 0x82, 0x00, 0x00, 0x00, 0x40, 0x88, 0x7C, 0x24, 0x0E, 0x83, 0xF8, 0x02,
    0x0F, 0x85, 0x83, 0x02, 0x00, 0x00]

theorem code_l100666 : ∀ x ∈ codeRange 0x100666 bytes_l100666, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x666 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10069c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10069c (StorePre 0x10069c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10069c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10069c 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.exec 0x1006a4 (StorePre 0x1006a4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x1006a4 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x1006a4 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 55) (.exec 0x1006ac (StorePre 0x1006ac 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x1006ac + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1006ac 7 2 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 56) (.out 0x1006b3 (movzxR32M16Effect 0x1006b3 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1006b3 (LoadPre 0x1006b3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1006b3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1006b3 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1006b8 (StorePre 0x1006b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1006b8 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1006b8 8 0 (.sib 4 none 0 (.d32 0xb5))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1006c0 (movzxR32M8Effect 0x1006c0 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1006c0 (LoadPre 0x1006c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1006c0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1006c0 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1006c5 (StorePre 0x1006c5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1006c5 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1006c5 7 0 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1006cc (leaR64Effect 0x1006cc 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1006cc (fun s => s.RIP = 0x1006cc) (leaR64Effect 0x1006cc 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1006d1 (movR32Imm32Effect 0x1006d1 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 65) (.exec 0x1006d1 (fun s => s.RIP = 0x1006d1) (movR32Imm32Effect 0x1006d1 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x1006d6 (callEffect (fun _ => 0x1276d0) 0x1006db) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x1006d6 (PushPre 0x1006d6 5) (callEffect (fun _ => 0x1276d0) 0x1006db) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x1006db⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 59), (1, 1), (2, 64), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l1006db, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l10069c : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x88, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x0C, 0x66, 0x89, 0x84, 0x24,
    0xB5, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x44, 0x24, 0x0E, 0x88, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x7C, 0x24, 0x10, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0xF5, 0x6F, 0x02, 0x00]

theorem code_l10069c : ∀ x ∈ codeRange 0x10069c bytes_l10069c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x69c 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1006db : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1006db (movR32M32LowEffect 0x1006db 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1006db (LoadPre 0x1006db (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1006db + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1006db 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1006df (cmpR32Imm8Effect 0x1006df 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1006df (fun s => s.RIP = 0x1006df) (cmpR32Imm8Effect 0x1006df 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100981, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1006e8, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1006db : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x99, 0x02, 0x00, 0x00]

theorem code_l1006db : ∀ x ∈ codeRange 0x1006db bytes_l1006db, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6db 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1006e8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1006e8 (leaR64Effect 0x1006e8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1006e8 (fun s => s.RIP = 0x1006e8) (leaR64Effect 0x1006e8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1006ed (leaR64Effect 0x1006ed 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1006ed (fun s => s.RIP = 0x1006ed) (leaR64Effect 0x1006ed 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1006f5 (movR64R64Effect 0x1006f5 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x1006f5 (fun s => s.RIP = 0x1006f5) (movR64R64Effect 0x1006f5 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1006f8 (callEffect (fun _ => 0x1038b0) 0x1006fd) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1006f8 (PushPre 0x1006f8 5) (callEffect (fun _ => 0x1038b0) 0x1006fd) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1006fd⟩) #v[]
    (.terminate (.call ⟨.l1038b0, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1006fd, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1006e8 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0xE8, 0xB3, 0x31, 0x00, 0x00]

theorem code_l1006e8 : ∀ x ∈ codeRange 0x1006e8 bytes_l1006e8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6e8 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1006fd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1006fd (movR32M32LowEffect 0x1006fd 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1006fd (LoadPre 0x1006fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1006fd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1006fd 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100701 (cmpR32Imm8Effect 0x100701 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x100701 (fun s => s.RIP = 0x100701) (cmpR32Imm8Effect 0x100701 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1009c7, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l10070a, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1006fd : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xBD, 0x02, 0x00, 0x00]

theorem code_l1006fd : ∀ x ∈ codeRange 0x1006fd bytes_l1006fd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6fd 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10070a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10070a (movR64M64Effect 0x10070a 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10070a (LoadPre 0x10070a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10070a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10070a 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10070f (movR64M64Effect 0x10070f 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x10070f (LoadPre 0x10070f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10070f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10070f 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100714 (leaR64Effect 0x100714 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x100714 (fun s => s.RIP = 0x100714) (leaR64Effect 0x100714 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100719 (movR64R64Effect 0x100719 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 60) (.exec 0x100719 (fun s => s.RIP = 0x100719) (movR64R64Effect 0x100719 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x10071c (callEffect (fun _ => 0x106900) 0x100721) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10071c (PushPre 0x10071c 5) (callEffect (fun _ => 0x106900) 0x100721) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x100721⟩) #v[]
    (.terminate (.call ⟨.l106900, RegMap.args [(3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l100721, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10070a : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x50, 0x4C, 0x8B, 0x64, 0x24, 0x58, 0x48, 0x8D, 0x7C, 0x24, 0x10, 0x4C,
    0x89, 0xF6, 0xE8, 0xDF, 0x61, 0x00, 0x00]

theorem code_l10070a : ∀ x ∈ codeRange 0x10070a bytes_l10070a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x70a 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100721 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100721 (movR32M32LowEffect 0x100721 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100721 (LoadPre 0x100721 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100721 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100721 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100725 (movR64M64Effect 0x100725 13 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x100725 (LoadPre 0x100725 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100725 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100725 13 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10072a (movzxR32M8Effect 0x10072a 5 5 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 58) (.exec 0x10072a (LoadPre 0x10072a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10072a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10072a 5 5 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10072f (cmpR32Imm8Effect 0x10072f 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 60) (.exec 0x10072f (fun s => s.RIP = 0x10072f) (cmpR32Imm8Effect 0x10072f 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.pure (condOp 5)) #v[59]
    (.terminate (.condBr (Fin.last 61) ⟨.l100772, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l100734, RegMap.args [(0, 53), (3, 3), (4, 4), (5, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (19, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l100721 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x6C, 0x24, 0x14, 0x0F, 0xB6, 0x6C, 0x24, 0x1C, 0x83, 0xF8,
    0x02, 0x75, 0x3E]

theorem code_l100721 : ∀ x ∈ codeRange 0x100721 bytes_l100721, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x721 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100734 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100734 (leaR64Effect 0x100734 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x100734 (fun s => s.RIP = 0x100734) (leaR64Effect 0x100734 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100739 (movR64R64Effect 0x100739 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 56) (.exec 0x100739 (fun s => s.RIP = 0x100739) (movR64R64Effect 0x100739 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x10073c (callEffect (fun _ => 0x106120) 0x100741) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10073c (PushPre 0x10073c 5) (callEffect (fun _ => 0x106120) 0x100741) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x100741⟩) #v[]
    (.terminate (.call ⟨.l106120, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l100741, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l100734 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0xF6, 0xE8, 0xDF, 0x59, 0x00, 0x00]

theorem code_l100734 : ∀ x ∈ codeRange 0x100734 bytes_l100734, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x734 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100741 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100741 (movR32M32LowEffect 0x100741 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100741 (LoadPre 0x100741 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100741 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100741 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100745 (movR32M32LowEffect 0x100745 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x100745 (LoadPre 0x100745 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100745 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x100745 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100749 (cmpR32Imm8Effect 0x100749 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 58) (.exec 0x100749 (fun s => s.RIP = 0x100749) (cmpR32Imm8Effect 0x100749 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.pure (condOp 5)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l1007d6, RegMap.args [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l100752, RegMap.args [(0, 53), (1, 55), (3, 3), (4, 4), (5, 5), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l100741 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x8B, 0x4C, 0x24, 0x14, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0x84, 0x00, 0x00,
    0x00]

theorem code_l100741 : ∀ x ∈ codeRange 0x100741 bytes_l100741, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x741 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100752 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100752 (movR32R32Effect 0x100752 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 54) (.exec 0x100752 (fun s => s.RIP = 0x100752) (movR32R32Effect 0x100752 2 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x100754 (andR8Imm8Effect 0x100754 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 56) (.exec 0x100754 (fun s => s.RIP = 0x100754) (andR8Imm8Effect 0x100754 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.out 0x100757 (movR64R64Effect 0x100757 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 58) (.exec 0x100757 (fun s => s.RIP = 0x100757) (movR64R64Effect 0x100757 8 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x10075a (shrR64Effect 0x10075a 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 60) (.exec 0x10075a (fun s => s.RIP = 0x10075a) (shrR64Effect 0x10075a 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x10075e (movR32R32Effect 0x10075e 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 62) (.exec 0x10075e (fun s => s.RIP = 0x10075e) (movR32R32Effect 0x10075e 2 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 63) (.out 0x100760 (shrR32Effect 0x100760 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 64) (.exec 0x100760 (fun s => s.RIP = 0x100760) (shrR32Effect 0x100760 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100763 (movR32Imm32Effect 0x100763 5 0 0x2) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 66) (.exec 0x100763 (fun s => s.RIP = 0x100763) (movR32Imm32Effect 0x100763 5 0 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x100768 (movR32R32Effect 0x100768 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 68) (.exec 0x100768 (fun s => s.RIP = 0x100768) (movR32R32Effect 0x100768 2 5 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x10076a (movR32R32Effect 0x10076a 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 70) (.exec 0x10076a (fun s => s.RIP = 0x10076a) (movR32R32Effect 0x10076a 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l100856, RegMap.args [(0, 65), (1, 69), (2, 55), (3, 3), (4, 4), (5, 67), (7, 63), (8, 59), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l100752 : List UInt8 :=
  [0x89, 0xEA, 0x80, 0xE2, 0x01, 0x4D, 0x89, 0xE8, 0x49, 0xC1, 0xE8, 0x20, 0x89, 0xCF, 0xC1, 0xEF,
    0x08, 0xB8, 0x02, 0x00, 0x00, 0x00, 0x89, 0xCD, 0x44, 0x89, 0xE9, 0xE9, 0xE4, 0x00, 0x00, 0x00]

theorem code_l100752 : ∀ x ∈ codeRange 0x100752 bytes_l100752, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x752 32 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100772 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100772 (movzxR32M8Effect 0x100772 5 1 (.sib 4 none 0 (.d8 0x1f))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x100772 (LoadPre 0x100772 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x100772 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100772 5 1 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100777 (shlR32Effect 0x100777 3 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x100777 (fun s => s.RIP = 0x100777) (shlR32Effect 0x100777 3 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10077a (movzxR32M16Effect 0x10077a 5 7 (.sib 4 none 0 (.d8 0x1d))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10077a (LoadPre 0x10077a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x10077a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10077a 5 7 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10077f (orR32R32Effect 0x10077f 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x10077f (fun s => s.RIP = 0x10077f) (orR32R32Effect 0x10077f 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x100781 (movzxR32M8Effect 0x100781 5 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x100781 (LoadPre 0x100781 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100781 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100781 5 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x100786 (movR64M64Effect 0x100786 1 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 64) (.exec 0x100786 (LoadPre 0x100786 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100786 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100786 1 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10078b (StorePre 0x10078b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10078b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10078b 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x100793 (movR64M64Effect 0x100793 1 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 67) (.exec 0x100793 (LoadPre 0x100793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100793 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100793 1 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x100798 (StorePre 0x100798 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100798 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100798 1 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x1007a0 (movR64M64Effect 0x1007a0 1 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x1007a0 (LoadPre 0x1007a0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x1007a0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007a0 1 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1007a5 (StorePre 0x1007a5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x1007a5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007a5 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x1007ad (movR64M64Effect 0x1007ad 1 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 73) (.exec 0x1007ad (LoadPre 0x1007ad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x1007ad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007ad 1 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x1007b2 (StorePre 0x1007b2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x1007b2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007b2 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x1007ba (movR64M64Effect 0x1007ba 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 76) (.exec 0x1007ba (LoadPre 0x1007ba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1007ba + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007ba 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x1007bf (StorePre 0x1007bf 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x1007bf + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1007bf 1 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x1007c7 (movR64R64Effect 0x1007c7 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 79) (.exec 0x1007c7 (fun s => s.RIP = 0x1007c7) (movR64R64Effect 0x1007c7 8 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 80) (.out 0x1007ca (shrR64Effect 0x1007ca 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[78]
    (.letOp (n := 81) (.exec 0x1007ca (fun s => s.RIP = 0x1007ca) (shrR64Effect 0x1007ca 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 82) (.out 0x1007ce (movR32R32Effect 0x1007ce 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 83) (.exec 0x1007ce (fun s => s.RIP = 0x1007ce) (movR32R32Effect 0x1007ce 3 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l100856, RegMap.args [(0, 0), (1, 82), (2, 61), (3, 3), (4, 4), (5, 5), (7, 59), (8, 80), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l100772 : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x1F, 0xC1, 0xE1, 0x10, 0x0F, 0xB7, 0x7C, 0x24, 0x1D, 0x09, 0xCF, 0x0F,
    0xB6, 0x54, 0x24, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x21, 0x48, 0x89, 0x8C, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x4C, 0x24, 0x29, 0x48, 0x89, 0x8C, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x4C, 0x24, 0x31, 0x48, 0x89, 0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x39,
    0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x4C, 0x24, 0x40, 0x48, 0x89, 0x8C,
    0x24, 0x9F, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xE8, 0x49, 0xC1, 0xE8, 0x20, 0x44, 0x89, 0xE9, 0xE9,
    0x80, 0x00, 0x00, 0x00]

theorem code_l100772 : ∀ x ∈ codeRange 0x100772 bytes_l100772, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x772 100 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1007d6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1007d6 (movzxR32M8Effect 0x1007d6 5 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1007d6 (LoadPre 0x1007d6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1007d6 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1007d6 5 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1007db (cmpR8Imm8Effect 0x1007db 3 2 0xd) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1007db (fun s => s.RIP = 0x1007db) (cmpR8Imm8Effect 0x1007db 3 2 0xd) (Reg.operands [.gpr 2] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1007f2, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1007e0, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1007d6 : List UInt8 :=
  [0x0F, 0xB6, 0x54, 0x24, 0x18, 0x80, 0xFA, 0x0D, 0x75, 0x12]

theorem code_l1007d6 : ∀ x ∈ codeRange 0x1007d6 bytes_l1007d6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7d6 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1007e0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1007e0 (StorePre 0x1007e0 5 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x1007e0 + BitVec.ofNat 64 5)) 1) (movM8Imm8RexEffect 0x1007e0 (.base 14 (.d8 0x20)) 0x1) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 54) (.out 0x1007e5 (movR32M32Effect 0x1007e5 1 (.base 14 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 55) (.exec 0x1007e5 (LoadPre 0x1007e5 (fun s => AddrMode.addr (.base 14 (.d8 0x1c)) s (0x1007e5 + BitVec.ofNat 64 4)) 4) (movR32M32Effect 0x1007e5 1 (.base 14 (.d8 0x1c))) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 56) (.out 0x1007e9 (movR32Imm32Effect 0x1007e9 5 0 0x1) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 57) (.exec 0x1007e9 (fun s => s.RIP = 0x1007e9) (movR32Imm32Effect 0x1007e9 5 0 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x1007ee (movR8Imm8Effect 0x1007ee 2 2 0x5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 59) (.exec 0x1007ee (fun s => s.RIP = 0x1007ee) (movR8Imm8Effect 0x1007ee 2 2 0x5) (Reg.operands [.gpr 2] [])) #v[2]
    (.terminate (.br ⟨.l1007f7, RegMap.args [(0, 56), (1, 54), (2, 58), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1007e0 : List UInt8 :=
  [0x41, 0xC6, 0x46, 0x20, 0x01, 0x41, 0x8B, 0x4E, 0x1C, 0xB8, 0x01, 0x00, 0x00, 0x00, 0xB2, 0x05,
    0xEB, 0x05]

theorem code_l1007e0 : ∀ x ∈ codeRange 0x1007e0 bytes_l1007e0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7e0 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1007f2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1007f2 (movR64M64Effect 0x1007f2 13 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x1007f2 (LoadPre 0x1007f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1007f2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1007f2 13 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1007f7, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1007f2 : List UInt8 :=
  [0x4C, 0x8B, 0x6C, 0x24, 0x1C]

theorem code_l1007f2 : ∀ x ∈ codeRange 0x1007f2 bytes_l1007f2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7f2 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1007f7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1007f7 (StorePre 0x1007f7 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1007f7 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x1007f7 4 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.exec 0x1007fb (StorePre 0x1007fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1007fb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1007fb 13 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 55) (.out 0x100800 (movR32M32Effect 0x100800 8 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 56) (.exec 0x100800 (LoadPre 0x100800 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100800 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100800 8 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100805 (movR32R32Effect 0x100805 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[13]
    (.letOp (n := 58) (.exec 0x100805 (fun s => s.RIP = 0x100805) (movR32R32Effect 0x100805 3 7 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 59) (.out 0x100808 (shrR32Effect 0x100808 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[57]
    (.letOp (n := 60) (.exec 0x100808 (fun s => s.RIP = 0x100808) (shrR32Effect 0x100808 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x10080b (movR64R64Effect 0x10080b 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 62) (.exec 0x10080b (fun s => s.RIP = 0x10080b) (movR64R64Effect 0x10080b 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 63) (.out 0x10080e (shrR64Effect 0x10080e 4 2 32) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x10080e (fun s => s.RIP = 0x10080e) (shrR64Effect 0x10080e 4 2 32) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x100812 (movR64M64Effect 0x100812 6 (.sib 4 none 0 (.d8 0x29))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 66) (.exec 0x100812 (LoadPre 0x100812 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x29)) s (0x100812 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100812 6 (.sib 4 none 0 (.d8 0x29))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x100817 (movR64M64Effect 0x100817 9 (.sib 4 none 0 (.d8 0x31))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 68) (.exec 0x100817 (LoadPre 0x100817 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x31)) s (0x100817 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100817 9 (.sib 4 none 0 (.d8 0x31))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x10081c (StorePre 0x10081c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10081c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10081c 6 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 70) (.exec 0x100824 (StorePre 0x100824 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100824 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100824 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 71) (.out 0x10082c (movR64M64Effect 0x10082c 6 (.sib 4 none 0 (.d8 0x39))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 72) (.exec 0x10082c (LoadPre 0x10082c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x39)) s (0x10082c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10082c 6 (.sib 4 none 0 (.d8 0x39))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x100831 (StorePre 0x100831 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100831 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100831 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x100839 (movR64M64Effect 0x100839 6 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 75) (.exec 0x100839 (LoadPre 0x100839 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100839 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100839 6 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10083e (StorePre 0x10083e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9f)) s (0x10083e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10083e 6 (.sib 4 none 0 (.d32 0x9f))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x100846 (movR64M64Effect 0x100846 6 (.sib 4 none 0 (.d8 0x21))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x100846 (LoadPre 0x100846 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x21)) s (0x100846 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100846 6 (.sib 4 none 0 (.d8 0x21))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x10084b (StorePre 0x10084b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10084b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10084b 6 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[77, 4]
    (.letOp (n := 80) (.out 0x100853 (movR32R32Effect 0x100853 3 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 13] []) (.reg (.gpr 5))) #v[13]
    (.letOp (n := 81) (.exec 0x100853 (fun s => s.RIP = 0x100853) (movR32R32Effect 0x100853 3 5 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.terminate (.br ⟨.l100856, RegMap.args [(0, 0), (1, 1), (2, 63), (3, 3), (4, 4), (5, 80), (6, 77), (7, 59), (8, 55), (9, 67), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l1007f7 : List UInt8 :=
  [0x88, 0x54, 0x24, 0x18, 0x4C, 0x89, 0x6C, 0x24, 0x1C, 0x44, 0x8B, 0x44, 0x24, 0x18, 0x44, 0x89,
    0xEF, 0xC1, 0xEF, 0x08, 0x4C, 0x89, 0xEA, 0x48, 0xC1, 0xEA, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x29,
    0x4C, 0x8B, 0x4C, 0x24, 0x31, 0x48, 0x89, 0xB4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x8C,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x39, 0x48, 0x89, 0xB4, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x74, 0x24, 0x40, 0x48, 0x89, 0xB4, 0x24, 0x9F, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x74, 0x24, 0x21, 0x48, 0x89, 0xB4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x89, 0xED]

theorem code_l1007f7 : ∀ x ∈ codeRange 0x1007f7 bytes_l1007f7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7f7 95 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100856 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100856 (shlR64Effect 0x100856 4 8 32) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 54) (.exec 0x100856 (fun s => s.RIP = 0x100856) (shlR64Effect 0x100856 4 8 32) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[8]
    (.letOp (n := 55) (.out 0x10085a (movR32R32Effect 0x10085a 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 56) (.exec 0x10085a (fun s => s.RIP = 0x10085a) (movR32R32Effect 0x10085a 2 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x10085c (orR64R64Effect 0x10085c 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[55, 53]
    (.letOp (n := 58) (.exec 0x10085c (fun s => s.RIP = 0x10085c) (orR64R64Effect 0x10085c 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[55, 53]
    (.letOp (n := 59) (.out 0x10085f (shlR32Effect 0x10085f 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[7]
    (.letOp (n := 60) (.exec 0x10085f (fun s => s.RIP = 0x10085f) (shlR32Effect 0x10085f 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[7]
    (.letOp (n := 61) (.out 0x100862 (movzxR32R8Effect 0x100862 4 8 5) (EffectPart.reads (.reg (.gpr 8)) [.gpr 5] []) (.reg (.gpr 8))) #v[5]
    (.letOp (n := 62) (.exec 0x100862 (fun s => s.RIP = 0x100862) (movzxR32R8Effect 0x100862 4 8 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 63) (.out 0x100866 (orR32R32Effect 0x100866 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x100866 (fun s => s.RIP = 0x100866) (orR32R32Effect 0x100866 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x100869 (movzxR32M16Effect 0x100869 8 7 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x100869 (LoadPre 0x100869 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100869 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x100869 8 7 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x100871 (StorePre 0x100871 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x100871 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100871 5 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x100876 (movzxR32M8Effect 0x100876 8 7 (.sib 4 none 0 (.d32 0x82))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x100876 (LoadPre 0x100876 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x100876 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x100876 8 7 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x10087e (StorePre 0x10087e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x10087e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x10087e 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x100883 (cmpR32Imm8Effect 0x100883 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 72) (.exec 0x100883 (fun s => s.RIP = 0x100883) (cmpR32Imm8Effect 0x100883 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 73) (.pure (condOp 5)) #v[71]
    (.terminate (.condBr (Fin.last 73) ⟨.l10091f, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ ⟨.l10088c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 57), (7, 68), (8, 63), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l100856 : List UInt8 :=
  [0x49, 0xC1, 0xE0, 0x20, 0x89, 0xCE, 0x4C, 0x09, 0xC6, 0xC1, 0xE7, 0x08, 0x44, 0x0F, 0xB6, 0xC5,
    0x41, 0x09, 0xF8, 0x0F, 0xB7, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x66, 0x89, 0x7C, 0x24, 0x0C,
    0x0F, 0xB6, 0xBC, 0x24, 0x82, 0x00, 0x00, 0x00, 0x40, 0x88, 0x7C, 0x24, 0x0E, 0x83, 0xF8, 0x02,
    0x0F, 0x85, 0x93, 0x00, 0x00, 0x00]

theorem code_l100856 : ∀ x ∈ codeRange 0x100856 bytes_l100856, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x856 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10088c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10088c (StorePre 0x10088c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10088c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10088c 6 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.exec 0x100894 (StorePre 0x100894 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100894 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x100894 8 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 55) (.exec 0x10089c (StorePre 0x10089c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x10089c + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x10089c 7 2 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 56) (.out 0x1008a3 (movzxR32M16Effect 0x1008a3 5 0 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1008a3 (LoadPre 0x1008a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1008a3 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1008a3 5 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1008a8 (StorePre 0x1008a8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb5)) s (0x1008a8 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1008a8 8 0 (.sib 4 none 0 (.d32 0xb5))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1008b0 (movzxR32M8Effect 0x1008b0 5 0 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1008b0 (LoadPre 0x1008b0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1008b0 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x1008b0 5 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1008b5 (StorePre 0x1008b5 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb7)) s (0x1008b5 + BitVec.ofNat 64 7)) 1) (movM8R8Effect 0x1008b5 7 0 (.sib 4 none 0 (.d32 0xb7))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1008bc (leaR64Effect 0x1008bc 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x1008bc (fun s => s.RIP = 0x1008bc) (leaR64Effect 0x1008bc 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x1008c1 (movR32Imm32Effect 0x1008c1 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 65) (.exec 0x1008c1 (fun s => s.RIP = 0x1008c1) (movR32Imm32Effect 0x1008c1 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x1008c6 (callEffect (fun _ => 0x1276d0) 0x1008cb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x1008c6 (PushPre 0x1008c6 5) (callEffect (fun _ => 0x1276d0) 0x1008cb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x1008cb⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 59), (1, 1), (2, 64), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l1008cb, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l10088c : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x44, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x88, 0x94, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x0C, 0x66, 0x89, 0x84, 0x24,
    0xB5, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0x44, 0x24, 0x0E, 0x88, 0x84, 0x24, 0xB7, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x7C, 0x24, 0x10, 0xBA, 0x01, 0x00, 0x00, 0x00, 0xE8, 0x05, 0x6E, 0x02, 0x00]

theorem code_l10088c : ∀ x ∈ codeRange 0x10088c bytes_l10088c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x88c 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1008cb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1008cb (movR32M32LowEffect 0x1008cb 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1008cb (LoadPre 0x1008cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1008cb + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1008cb 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1008cf (cmpR32Imm8Effect 0x1008cf 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1008cf (fun s => s.RIP = 0x1008cf) (cmpR32Imm8Effect 0x1008cf 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l100981, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1008d8, RegMap.args [(0, 53), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1008cb : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x10, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xA9, 0x00, 0x00, 0x00]

theorem code_l1008cb : ∀ x ∈ codeRange 0x1008cb bytes_l1008cb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8cb 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1008d8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1008d8 (leaR64Effect 0x1008d8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1008d8 (fun s => s.RIP = 0x1008d8) (leaR64Effect 0x1008d8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1008dd (leaR64Effect 0x1008dd 2 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x1008dd (fun s => s.RIP = 0x1008dd) (leaR64Effect 0x1008dd 2 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1008e5 (movR64R64Effect 0x1008e5 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x1008e5 (fun s => s.RIP = 0x1008e5) (movR64R64Effect 0x1008e5 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x1008e8 (callEffect (fun _ => 0x1038b0) 0x1008ed) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1008e8 (PushPre 0x1008e8 5) (callEffect (fun _ => 0x1038b0) 0x1008ed) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1008ed⟩) #v[]
    (.terminate (.call ⟨.l1038b0, RegMap.args [(1, 1), (2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1008ed, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1008d8 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0x48, 0x8D, 0x94, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF6,
    0xE8, 0xC3, 0x2F, 0x00, 0x00]

theorem code_l1008d8 : ∀ x ∈ codeRange 0x1008d8 bytes_l1008d8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8d8 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1008ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1008ed (movR32M32LowEffect 0x1008ed 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1008ed (LoadPre 0x1008ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1008ed + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1008ed 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1008f1 (cmpR32Imm8Effect 0x1008f1 3 0 0x2) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[53]
    (.letOp (n := 56) (.exec 0x1008f1 (fun s => s.RIP = 0x1008f1) (cmpR32Imm8Effect 0x1008f1 3 0 0x2) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l1009c7, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1008fa, RegMap.args [(0, 53), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l1008ed : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x48, 0x83, 0xF8, 0x02, 0x0F, 0x85, 0xCD, 0x00, 0x00, 0x00]

theorem code_l1008ed : ∀ x ∈ codeRange 0x1008ed bytes_l1008ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8ed 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1008fa : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1008fa (movR64M64Effect 0x1008fa 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1008fa (LoadPre 0x1008fa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1008fa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1008fa 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1008ff (movR64M64Effect 0x1008ff 1 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1008ff (LoadPre 0x1008ff (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1008ff + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1008ff 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100904 (StorePre 0x100904 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x100904 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100904 15 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 3] [])) #v[15, 3]
    (.letOp (n := 58) (.exec 0x100908 (StorePre 0x100908 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100908 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100908 12 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 59) (.exec 0x10090c (StorePre 0x10090c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x10090c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10090c 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 60) (.exec 0x100910 (StorePre 0x100910 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x100910 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100910 1 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 61) (.exec 0x100914 (StorePre 0x100914 6 (fun s => AddrMode.addr (.base 3 .none) s (0x100914 + BitVec.ofNat 64 6)) 4) (movM32Imm32Effect 0x100914 6 (.base 3 .none) 0x2) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l100a06, RegMap.args [(0, 53), (1, 55), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l1008fa : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x8B, 0x4C, 0x24, 0x58, 0x4C, 0x89, 0x7B, 0x08, 0x4C, 0x89,
    0x63, 0x10, 0x48, 0x89, 0x43, 0x18, 0x48, 0x89, 0x4B, 0x20, 0xC7, 0x03, 0x02, 0x00, 0x00, 0x00,
    0xE9, 0xE7, 0x00, 0x00, 0x00]

theorem code_l1008fa : ∀ x ∈ codeRange 0x1008fa bytes_l1008fa, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x8fa 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10091f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10091f (movR32M32LowEffect 0x10091f 7 (.sib 4 none 0 (.d32 0xa3))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10091f (LoadPre 0x10091f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa3)) s (0x10091f + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x10091f 7 (.sib 4 none 0 (.d32 0xa3))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100926 (StorePre 0x100926 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x100926 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100926 7 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10092a (movR64M64Effect 0x10092a 7 (.sib 4 none 0 (.d32 0x9b))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 57) (.exec 0x10092a (LoadPre 0x10092a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9b)) s (0x10092a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10092a 7 (.sib 4 none 0 (.d32 0x9b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x100932 (StorePre 0x100932 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x100932 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100932 7 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100937 (movR64M64Effect 0x100937 7 (.sib 4 none 0 (.d32 0x93))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 60) (.exec 0x100937 (LoadPre 0x100937 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x93)) s (0x100937 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100937 7 (.sib 4 none 0 (.d32 0x93))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10093f (StorePre 0x10093f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10093f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10093f 7 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x100944 (movR64M64Effect 0x100944 7 (.sib 4 none 0 (.d32 0x83))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x100944 (LoadPre 0x100944 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x83)) s (0x100944 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100944 7 (.sib 4 none 0 (.d32 0x83))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x10094c (movR64M64Effect 0x10094c 9 (.sib 4 none 0 (.d32 0x8b))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 65) (.exec 0x10094c (LoadPre 0x10094c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8b)) s (0x10094c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10094c 9 (.sib 4 none 0 (.d32 0x8b))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x100954 (StorePre 0x100954 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x100954 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100954 9 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.exec 0x100959 (StorePre 0x100959 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x100959 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100959 7 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 68) (.exec 0x10095e (StorePre 0x10095e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x10095e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10095e 6 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 69) (.exec 0x100963 (StorePre 0x100963 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x100963 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100963 8 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 70) (.exec 0x100968 (StorePre 0x100968 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100968 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100968 4 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 71) (.out 0x10096c (movzxR32M16Effect 0x10096c 5 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 72) (.exec 0x10096c (LoadPre 0x10096c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x10096c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10096c 5 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x100971 (StorePre 0x100971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x59)) s (0x100971 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x100971 5 2 (.sib 4 none 0 (.d8 0x59))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x100976 (movzxR32M8Effect 0x100976 5 2 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 75) (.exec 0x100976 (LoadPre 0x100976 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x100976 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100976 5 2 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x10097b (StorePre 0x10097b 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5b)) s (0x10097b + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x10097b 4 2 (.sib 4 none 0 (.d8 0x5b))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[74, 4]
    (.terminate (.br ⟨.l1009cb, RegMap.args [(0, 0), (1, 1), (2, 74), (3, 3), (4, 4), (6, 6), (7, 62), (8, 8), (9, 64), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 77⟩)))))))))))))))))))))))))

def bytes_l10091f : List UInt8 :=
  [0x8B, 0xBC, 0x24, 0xA3, 0x00, 0x00, 0x00, 0x89, 0x7C, 0x24, 0x7C, 0x48, 0x8B, 0xBC, 0x24, 0x9B,
    0x00, 0x00, 0x00, 0x48, 0x89, 0x7C, 0x24, 0x74, 0x48, 0x8B, 0xBC, 0x24, 0x93, 0x00, 0x00, 0x00,
    0x48, 0x89, 0x7C, 0x24, 0x6C, 0x48, 0x8B, 0xBC, 0x24, 0x83, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x8C,
    0x24, 0x8B, 0x00, 0x00, 0x00, 0x4C, 0x89, 0x4C, 0x24, 0x64, 0x48, 0x89, 0x7C, 0x24, 0x5C, 0x48,
    0x89, 0x74, 0x24, 0x4C, 0x44, 0x89, 0x44, 0x24, 0x54, 0x88, 0x54, 0x24, 0x58, 0x0F, 0xB7, 0x54,
    0x24, 0x0C, 0x66, 0x89, 0x54, 0x24, 0x59, 0x0F, 0xB6, 0x54, 0x24, 0x0E, 0x88, 0x54, 0x24, 0x5B,
    0xEB, 0x4A]

theorem code_l10091f : ∀ x ∈ codeRange 0x10091f bytes_l10091f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x91f 98 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100981 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100981 (movR64M64Effect 0x100981 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x100981 (LoadPre 0x100981 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x100981 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100981 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100986 (movR64M64Effect 0x100986 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x100986 (LoadPre 0x100986 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x100986 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100986 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10098b (StorePre 0x10098b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x54)) s (0x10098b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10098b 2 (.sib 4 none 0 (.d8 0x54))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x100990 (movR64M64Effect 0x100990 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x100990 (LoadPre 0x100990 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x100990 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100990 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x100995 (StorePre 0x100995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x100995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100995 2 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x10099a (movR64M64Effect 0x10099a 2 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x10099a (LoadPre 0x10099a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x10099a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10099a 2 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10099f (StorePre 0x10099f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x10099f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10099f 2 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x1009a4 (movR64M64Effect 0x1009a4 2 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x1009a4 (LoadPre 0x1009a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x1009a4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009a4 2 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1009a9 (StorePre 0x1009a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1009a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009a9 2 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x1009ae (movR64M64Effect 0x1009ae 2 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 68) (.exec 0x1009ae (LoadPre 0x1009ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x1009ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009ae 2 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x1009b3 (StorePre 0x1009b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x1009b3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009b3 2 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x1009b8 (movR32M32LowEffect 0x1009b8 2 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 71) (.exec 0x1009b8 (LoadPre 0x1009b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x1009b8 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1009b8 2 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.exec 0x1009bc (StorePre 0x1009bc 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1009bc + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x1009bc 2 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.exec 0x1009c0 (StorePre 0x1009c0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1009c0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1009c0 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l1009cb, RegMap.args [(0, 0), (1, 53), (2, 70), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l100981 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x14, 0x48, 0x8B, 0x54, 0x24, 0x1C, 0x48, 0x89, 0x54, 0x24, 0x54, 0x48,
    0x8B, 0x54, 0x24, 0x24, 0x48, 0x89, 0x54, 0x24, 0x5C, 0x48, 0x8B, 0x54, 0x24, 0x2C, 0x48, 0x89,
    0x54, 0x24, 0x64, 0x48, 0x8B, 0x54, 0x24, 0x34, 0x48, 0x89, 0x54, 0x24, 0x6C, 0x48, 0x8B, 0x54,
    0x24, 0x3C, 0x48, 0x89, 0x54, 0x24, 0x74, 0x8B, 0x54, 0x24, 0x44, 0x89, 0x54, 0x24, 0x7C, 0x48,
    0x89, 0x4C, 0x24, 0x4C, 0xEB, 0x04]

theorem code_l100981 : ∀ x ∈ codeRange 0x100981 bytes_l100981, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x981 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1009c7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1009c7 (movR32M32LowEffect 0x1009c7 1 (.sib 4 none 0 (.d8 0x4c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x1009c7 (LoadPre 0x1009c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x1009c7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1009c7 1 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.br ⟨.l1009cb, RegMap.args [(0, 0), (1, 53), (3, 3), (4, 4), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l1009c7 : List UInt8 :=
  [0x8B, 0x4C, 0x24, 0x4C]

theorem code_l1009c7 : ∀ x ∈ codeRange 0x1009c7 bytes_l1009c7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9c7 4 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1009cb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1009cb (movR64M64Effect 0x1009cb 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 54) (.exec 0x1009cb (LoadPre 0x1009cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1009cb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009cb 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1009d0 (movR64M64Effect 0x1009d0 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1009d0 (LoadPre 0x1009d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1009d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009d0 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1009d5 (movR64M64Effect 0x1009d5 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x1009d5 (LoadPre 0x1009d5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1009d5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009d5 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1009da (StorePre 0x1009da 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x1009da + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009da 7 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 60) (.out 0x1009de (movR64M64Effect 0x1009de 7 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x1009de (LoadPre 0x1009de (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1009de + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009de 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1009e3 (StorePre 0x1009e3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x1009e3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009e3 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[60, 3]
    (.letOp (n := 63) (.out 0x1009e7 (movR64M64Effect 0x1009e7 7 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 64) (.exec 0x1009e7 (LoadPre 0x1009e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1009e7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009e7 7 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1009ec (StorePre 0x1009ec 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x1009ec + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009ec 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[63, 3]
    (.letOp (n := 66) (.out 0x1009f0 (movR64M64Effect 0x1009f0 7 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 67) (.exec 0x1009f0 (LoadPre 0x1009f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1009f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1009f0 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1009f5 (StorePre 0x1009f5 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x1009f5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009f5 7 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[66, 3]
    (.letOp (n := 69) (.exec 0x1009f9 (StorePre 0x1009f9 2 (fun s => AddrMode.addr (.base 3 .none) s (0x1009f9 + BitVec.ofNat 64 2)) 4) (movM32R32LowEffect 0x1009f9 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[0, 3]
    (.letOp (n := 70) (.exec 0x1009fb (StorePre 0x1009fb 3 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1009fb + BitVec.ofNat 64 3)) 4) (movM32R32LowEffect 0x1009fb 1 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[1, 3]
    (.letOp (n := 71) (.exec 0x1009fe (StorePre 0x1009fe 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1009fe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1009fe 2 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[53, 3]
    (.letOp (n := 72) (.exec 0x100a02 (StorePre 0x100a02 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x100a02 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x100a02 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[55, 3]
    (.terminate (.br ⟨.l100a06, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (6, 55), (7, 66), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l1009cb : List UInt8 :=
  [0x48, 0x8B, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x8B, 0x7C, 0x24, 0x78, 0x48,
    0x89, 0x7B, 0x30, 0x48, 0x8B, 0x7C, 0x24, 0x70, 0x48, 0x89, 0x7B, 0x28, 0x48, 0x8B, 0x7C, 0x24,
    0x68, 0x48, 0x89, 0x7B, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x60, 0x48, 0x89, 0x7B, 0x18, 0x89, 0x03,
    0x89, 0x4B, 0x04, 0x48, 0x89, 0x53, 0x08, 0x48, 0x89, 0x73, 0x10]

theorem code_l1009cb : ∀ x ∈ codeRange 0x1009cb bytes_l1009cb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9cb 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100a06 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100a06 (movR64R64Effect 0x100a06 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x100a06 (fun s => s.RIP = 0x100a06) (movR64R64Effect 0x100a06 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x100a09 (addR64Imm32Effect 0x100a09 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x100a09 (fun s => s.RIP = 0x100a09) (addR64Imm32Effect 0x100a09 4 0xb8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100a10 (popR64Effect 0x100a10 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x100a10 (popR64Effect 0x100a10 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x100a10 (PopPre 0x100a10) (popR64Effect 0x100a10 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x100a11 (popR64Effect 0x100a11 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x100a11 (popR64Effect 0x100a11 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x100a11 (PopPre 0x100a11) (popR64Effect 0x100a11 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x100a13 (popR64Effect 0x100a13 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x100a13 (popR64Effect 0x100a13 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x100a13 (PopPre 0x100a13) (popR64Effect 0x100a13 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x100a15 (popR64Effect 0x100a15 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x100a15 (popR64Effect 0x100a15 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x100a15 (PopPre 0x100a15) (popR64Effect 0x100a15 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x100a17 (popR64Effect 0x100a17 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x100a17 (popR64Effect 0x100a17 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x100a17 (PopPre 0x100a17) (popR64Effect 0x100a17 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x100a19 (popR64Effect 0x100a19 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x100a19 (popR64Effect 0x100a19 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x100a19 (PopPre 0x100a19) (popR64Effect 0x100a19 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x100a1a (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x100a1a (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x100a1a (RetPre 0x100a1a) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l100a06 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l100a06 : ∀ x ∈ codeRange 0x100a06 bytes_l100a06, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa06 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

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

@[cfg_block] def b_l100a40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100a40 (pushR64Effect 0x100a40 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100a40 (PushPre 0x100a40 1) (pushR64Effect 0x100a40 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100a41 (pushR64Effect 0x100a41 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100a41 (PushPre 0x100a41 2) (pushR64Effect 0x100a41 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100a43 (pushR64Effect 0x100a43 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100a43 (PushPre 0x100a43 2) (pushR64Effect 0x100a43 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100a45 (pushR64Effect 0x100a45 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100a45 (PushPre 0x100a45 2) (pushR64Effect 0x100a45 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100a47 (pushR64Effect 0x100a47 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100a47 (PushPre 0x100a47 2) (pushR64Effect 0x100a47 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100a49 (pushR64Effect 0x100a49 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100a49 (PushPre 0x100a49 1) (pushR64Effect 0x100a49 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x100a4a (subR64Imm32Effect 0x100a4a 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x100a4a (fun s => s.RIP = 0x100a4a) (subR64Imm32Effect 0x100a4a 4 0xb8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100a51 (movR64R64Effect 0x100a51 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[2]
    (.letOp (n := 68) (.exec 0x100a51 (fun s => s.RIP = 0x100a51) (movR64R64Effect 0x100a51 13 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.exec 0x100a54 (StorePre 0x100a54 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100a54 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a54 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 65]
    (.letOp (n := 70) (.out 0x100a59 (leaR64Effect 0x100a59 1 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[7]
    (.letOp (n := 71) (.exec 0x100a59 (fun s => s.RIP = 0x100a59) (leaR64Effect 0x100a59 1 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 72) (.out 0x100a5d (cmpR64Imm32Effect 0x100a5d 2 0x1fffffff) (EffectPart.reads (.flag .CF) [.gpr 2] []) (.flag .CF)) #v[2]
    (.letOp (n := 73) (.out 0x100a5d (cmpR64Imm32Effect 0x100a5d 2 0x1fffffff) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[2]
    (.letOp (n := 74) (.exec 0x100a5d (fun s => s.RIP = 0x100a5d) (cmpR64Imm32Effect 0x100a5d 2 0x1fffffff) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 75) (.pure (condOp 7)) #v[72, 73]
    (.terminate (.condBr (Fin.last 75) ⟨.l100e6a, RegMap.args [(0, 0), (1, 70), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (16, 72), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩ ⟨.l100a6a, RegMap.args [(0, 0), (1, 70), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 67), (14, 14), (15, 15), (16, 72), (19, 73), (22, 22), (39, 39), (50, 50), (51, 51)] 76⟩))))))))))))))))))))))))

def bytes_l100a40 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xD5, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x8D, 0x4F, 0x08, 0x48, 0x81, 0xFA,
    0xFF, 0xFF, 0xFF, 0x1F, 0x0F, 0x87, 0x00, 0x04, 0x00, 0x00]

theorem code_l100a40 : ∀ x ∈ codeRange 0x100a40 bytes_l100a40, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa40 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100a6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100a6a (leaR32Effect 0x100a6a 8 0 (.abs (some 13) 3 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x100a6a (fun s => s.RIP = 0x100a6a) (leaR32Effect 0x100a6a 8 0 (.abs (some 13) 3 0x0)) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.exec 0x100a72 (StorePre 0x100a72 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100a72 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x100a72 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.exec 0x100a76 (StorePre 0x100a76 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100a76 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100a76 7 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.letOp (n := 57) (.out 0x100a7e (leaR64Effect 0x100a7e 0 (.base 7 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 58) (.exec 0x100a7e (fun s => s.RIP = 0x100a7e) (leaR64Effect 0x100a7e 0 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 59) (.exec 0x100a82 (StorePre 0x100a82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100a82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100a82 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x100a8a (movR64R64Effect 0x100a8a 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 61) (.exec 0x100a8a (fun s => s.RIP = 0x100a8a) (movR64R64Effect 0x100a8a 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 62) (.exec 0x100a8d (StorePre 0x100a8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100a8d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a8d 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 63) (.exec 0x100a92 (StorePre 0x100a92 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100a92 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100a92 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[13, 4]
    (.letOp (n := 64) (.out 0x100a97 (testR64R64Effect 0x100a97 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 65) (.exec 0x100a97 (fun s => s.RIP = 0x100a97) (testR64R64Effect 0x100a97 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 66) (.out 0x100a9a (movR64M64Effect 0x100a9a 12 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 67) (.exec 0x100a9a (LoadPre 0x100a9a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100a9a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100a9a 12 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x100aa2 (leaR64Effect 0x100aa2 3 (.rip 0x29d77)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 69) (.exec 0x100aa2 (fun s => s.RIP = 0x100aa2) (leaR64Effect 0x100aa2 3 (.rip 0x29d77)) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.pure (condOp 4)) #v[64]
    (.terminate (.condBr (Fin.last 70) ⟨.l100aef, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 66), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩ ⟨.l100aab, RegMap.args [(0, 57), (1, 1), (2, 2), (3, 68), (4, 4), (5, 5), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 66), (13, 13), (14, 14), (15, 15), (19, 64), (22, 22), (39, 39), (50, 50), (51, 51)] 71⟩)))))))))))))))))))

def bytes_l100a6a : List UInt8 :=
  [0x42, 0x8D, 0x04, 0xED, 0x00, 0x00, 0x00, 0x00, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0xBC, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x47, 0x28, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xCF, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x4C, 0x89, 0x6C, 0x24, 0x30, 0x4D, 0x85, 0xED,
    0x4C, 0x8B, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x1D, 0x77, 0x9D, 0x02, 0x00, 0x74,
    0x44]

theorem code_l100a6a : ∀ x ∈ codeRange 0x100a6a bytes_l100a6a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xa6a 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100aab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100aab (fun s => s.RIP = 0x100aab) (fun _ => nopEffect 0x100aab 5) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100ab0, RegMap.args [(3, 3), (4, 4), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l100aab : List UInt8 :=
  [0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l100aab : ∀ x ∈ codeRange 0x100aab bytes_l100aab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xaab 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ab0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ab0 (movR64M64Effect 0x100ab0 14 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 54) (.exec 0x100ab0 (LoadPre 0x100ab0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100ab0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ab0 14 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100ab5 (movR64M64Effect 0x100ab5 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 56) (.exec 0x100ab5 (LoadPre 0x100ab5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100ab5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ab5 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100aba (fun s => s.RIP = 0x100aba) (fun _ => nopEffect 0x100aba 6) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100ac0, RegMap.args [(3, 3), (4, 4), (5, 55), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (14, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l100ab0 : List UInt8 :=
  [0x4C, 0x8B, 0x74, 0x24, 0x28, 0x48, 0x8B, 0x6C, 0x24, 0x30, 0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]

theorem code_l100ab0 : ∀ x ∈ codeRange 0x100ab0 bytes_l100ab0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xab0 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ac0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ac0 (cmpR64Imm8Effect 0x100ac0 5 0x20) (EffectPart.reads (.flag .CF) [.gpr 5] []) (.flag .CF)) #v[5]
    (.letOp (n := 54) (.exec 0x100ac0 (fun s => s.RIP = 0x100ac0) (cmpR64Imm8Effect 0x100ac0 5 0x20) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x100ac4 (movR32Imm32Effect 0x100ac4 6 15 0x20) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 56) (.exec 0x100ac4 (fun s => s.RIP = 0x100ac4) (movR32Imm32Effect 0x100ac4 6 15 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100aca (atFlags (condHolds 2) (cmovR64R64Effect 0x100aca 4 15 5)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[55, 5, 53]
    (.letOp (n := 58) (.exec 0x100aca (fun s => s.RIP = 0x100aca) (atFlags (condHolds 2) (cmovR64R64Effect 0x100aca 4 15 5)) (Reg.operands [.gpr 15, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[55, 5, 53]
    (.letOp (n := 59) (.out 0x100ace (leaR64Effect 0x100ace 13 (.sib 14 (some 15) 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14, .gpr 15] []) (.reg (.gpr 13))) #v[14, 57]
    (.letOp (n := 60) (.exec 0x100ace (fun s => s.RIP = 0x100ace) (leaR64Effect 0x100ace 13 (.sib 14 (some 15) 0 .none)) (Reg.operands [.gpr 14, .gpr 15] [])) #v[14, 57]
    (.letOp (n := 61) (.out 0x100ad2 (callEffect (fun _ => 0x104970) 0x100ad7) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x100ad2 (PushPre 0x100ad2 5) (callEffect (fun _ => 0x104970) 0x100ad7) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x100ad7⟩) #v[]
    (.terminate (.call ⟨.l104970, RegMap.args [(3, 3), (4, 61), (5, 5), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 59), (14, 14), (15, 57), (16, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l100ad7, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l100ac0 : List UInt8 :=
  [0x48, 0x83, 0xFD, 0x20, 0x41, 0xBF, 0x20, 0x00, 0x00, 0x00, 0x4C, 0x0F, 0x42, 0xFD, 0x4F, 0x8D,
    0x2C, 0x3E, 0xE8, 0x99, 0x3E, 0x00, 0x00]

theorem code_l100ac0 : ∀ x ∈ codeRange 0x100ac0 bytes_l100ac0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xac0 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ad7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ad7 (movR64R64Effect 0x100ad7 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x100ad7 (fun s => s.RIP = 0x100ad7) (movR64R64Effect 0x100ad7 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x100ada (movR64R64Effect 0x100ada 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x100ada (fun s => s.RIP = 0x100ada) (movR64R64Effect 0x100ada 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x100add (movR64R64Effect 0x100add 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x100add (fun s => s.RIP = 0x100add) (movR64R64Effect 0x100add 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x100ae0 (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x100ae2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[4, 3]
    (.letOp (n := 60) (.exec 0x100ae0 (GoesTo (CallPre 0x100ae0 2 (fun s => (Operand.reg 3 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x100ae2) 0x12a820) (callEffect (fun s => (Operand.reg 3 : Operand 64).read s) 0x100ae2) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 61) (.const ⟨64, 0x100ae2⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l100ae2, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100ad7 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xE6, 0x4C, 0x89, 0xFA, 0xFF, 0xD3]

theorem code_l100ad7 : ∀ x ∈ codeRange 0x100ad7 bytes_l100ad7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xad7 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ae2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ae2 (movR64M64Effect 0x100ae2 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x100ae2 (LoadPre 0x100ae2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100ae2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ae2 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100ae7 (movR64R64Effect 0x100ae7 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 13] []) (.reg (.gpr 14))) #v[13]
    (.letOp (n := 56) (.exec 0x100ae7 (fun s => s.RIP = 0x100ae7) (movR64R64Effect 0x100ae7 14 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x100aea (subR64R64Effect 0x100aea 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[5, 15]
    (.letOp (n := 58) (.out 0x100aea (subR64R64Effect 0x100aea 5 15) (EffectPart.reads (.flag .ZF) [.gpr 5, .gpr 15] []) (.flag .ZF)) #v[5, 15]
    (.letOp (n := 59) (.exec 0x100aea (fun s => s.RIP = 0x100aea) (subR64R64Effect 0x100aea 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[5, 15]
    (.letOp (n := 60) (.pure (condOp 5)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l100ac0, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l100aef, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 57), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 55), (15, 15), (19, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l100ae2 : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x40, 0x4D, 0x89, 0xEE, 0x4C, 0x29, 0xFD, 0x75, 0xD1]

theorem code_l100ae2 : ∀ x ∈ codeRange 0x100ae2 bytes_l100ae2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xae2 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100aef : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100aef (movR32Imm32Effect 0x100aef 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x100aef (fun s => s.RIP = 0x100aef) (movR32Imm32Effect 0x100aef 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100af4 (xorR32R32Effect 0x100af4 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 56) (.exec 0x100af4 (fun s => s.RIP = 0x100af4) (xorR32R32Effect 0x100af4 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 57) (.out 0x100af6 (callEffect (fun _ => 0x103f30) 0x100afb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x100af6 (PushPre 0x100af6 5) (callEffect (fun _ => 0x103f30) 0x100afb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x100afb⟩) #v[]
    (.terminate (.call ⟨.l103f30, RegMap.args [(2, 55), (3, 3), (4, 57), (5, 5), (6, 53), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l100afb, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l100aef : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x31, 0xD2, 0xE8, 0x35, 0x34, 0x00, 0x00]

theorem code_l100aef : ∀ x ∈ codeRange 0x100aef bytes_l100aef, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xaef 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100afb_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x100b98 (negR32Effect 0x100b98 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[127]
    (.letOp (n := 130) (.exec 0x100b98 (fun s => s.RIP = 0x100b98) (negR32Effect 0x100b98 2 2) (Reg.operands [.gpr 2] [])) #v[127]
    (.letOp (n := 131) (.out 0x100b9a (andR32R32Effect 0x100b9a 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[129, 124]
    (.letOp (n := 132) (.exec 0x100b9a (fun s => s.RIP = 0x100b9a) (andR32R32Effect 0x100b9a 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[129, 124]
    (.letOp (n := 133) (.out 0x100b9c (addR32R32Effect 0x100b9c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[93, 72]
    (.letOp (n := 134) (.exec 0x100b9c (fun s => s.RIP = 0x100b9c) (addR32R32Effect 0x100b9c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[93, 72]
    (.letOp (n := 135) (.out 0x100b9e (addR32R32Effect 0x100b9e 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[131, 114]
    (.letOp (n := 136) (.exec 0x100b9e (fun s => s.RIP = 0x100b9e) (addR32R32Effect 0x100b9e 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[131, 114]
    (.letOp (n := 137) (.out 0x100ba1 (addR32R32Effect 0x100ba1 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[135, 133]
    (.letOp (n := 138) (.exec 0x100ba1 (fun s => s.RIP = 0x100ba1) (addR32R32Effect 0x100ba1 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[135, 133]
    (.letOp (n := 139) (.out 0x100ba3 (movR32Imm32Effect 0x100ba3 5 0 0x100) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 140) (.exec 0x100ba3 (fun s => s.RIP = 0x100ba3) (movR32Imm32Effect 0x100ba3 5 0 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 141) (.out 0x100ba8 (subR32R32Effect 0x100ba8 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[139, 137]
    (.letOp (n := 142) (.exec 0x100ba8 (fun s => s.RIP = 0x100ba8) (subR32R32Effect 0x100ba8 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[139, 137]
    (.letOp (n := 143) (.out 0x100baa (movR32M32Effect 0x100baa 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 144) (.exec 0x100baa (LoadPre 0x100baa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x100baa + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x100baa 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 145) (.out 0x100baf (movR32R32Effect 0x100baf 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[143]
    (.letOp (n := 146) (.exec 0x100baf (fun s => s.RIP = 0x100baf) (movR32R32Effect 0x100baf 3 14 8) (Reg.operands [.gpr 8] [])) #v[143]
    (.letOp (n := 147) (.out 0x100bb2 (subR32R32Effect 0x100bb2 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[145, 141]
    (.letOp (n := 148) (.out 0x100bb2 (subR32R32Effect 0x100bb2 3 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[145, 141]
    (.letOp (n := 149) (.exec 0x100bb2 (fun s => s.RIP = 0x100bb2) (subR32R32Effect 0x100bb2 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[145, 141]
    (.letOp (n := 150) (.out 0x100bb5 (movR32Imm32Effect 0x100bb5 5 2 0x0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 151) (.exec 0x100bb5 (fun s => s.RIP = 0x100bb5) (movR32Imm32Effect 0x100bb5 5 2 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 152) (.out 0x100bba (atFlags (condHolds 2) (cmovR32R32Effect 0x100bba 4 14 9)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[147, 97, 148]
    (.letOp (n := 153) (.exec 0x100bba (fun s => s.RIP = 0x100bba) (atFlags (condHolds 2) (cmovR32R32Effect 0x100bba 4 14 9)) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[147, 97, 148]
    (.letOp (n := 154) (.out 0x100bbe (movR32R32Effect 0x100bbe 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[152]
    (.letOp (n := 155) (.exec 0x100bbe (fun s => s.RIP = 0x100bbe) (movR32R32Effect 0x100bbe 3 1 14) (Reg.operands [.gpr 14] [])) #v[152]
    (.letOp (n := 156) (.out 0x100bc1 (shrR32Effect 0x100bc1 3 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[154]
    (.letOp (n := 157) (.out 0x100bc1 (shrR32Effect 0x100bc1 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[154]
    (.letOp (n := 158) (.exec 0x100bc1 (fun s => s.RIP = 0x100bc1) (shrR32Effect 0x100bc1 3 1 3) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[154]
    (.letOp (n := 159) (.pure (condOp 4)) #v[157]
    (.terminate (.condBr (Fin.last 159) ⟨.l100bf0, RegMap.args [(0, 141), (1, 156), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 152), (15, 55), (19, 157), (22, 22), (39, 39), (50, 50), (51, 51)] 160⟩ ⟨.l100bc6, RegMap.args [(0, 141), (1, 156), (2, 150), (3, 3), (4, 4), (5, 5), (6, 124), (7, 107), (8, 143), (9, 97), (10, 10), (11, 11), (12, 66), (14, 152), (15, 55), (19, 157), (22, 22), (39, 39), (50, 50), (51, 51)] 160⟩))))))))))))))))))))))))))))))))

def bytes_l100afb_2 : List UInt8 :=
  [0xF7, 0xDA, 0x21, 0xF2, 0x01, 0xC1, 0x44, 0x01, 0xC2, 0x01, 0xCA, 0xB8, 0x00, 0x01, 0x00, 0x00,
    0x29, 0xD0, 0x44, 0x8B, 0x44, 0x24, 0x38, 0x45, 0x89, 0xC6, 0x41, 0x29, 0xC6, 0xBA, 0x00, 0x00,
    0x00, 0x00, 0x45, 0x0F, 0x42, 0xF1, 0x44, 0x89, 0xF1, 0xC1, 0xE9, 0x03, 0x74, 0x2A]

theorem code_l100afb_2 : ∀ x ∈ codeRange 0x100b98 bytes_l100afb_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xb98 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100afb_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x100b4b (negR32Effect 0x100b4b 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[89]
    (.letOp (n := 92) (.exec 0x100b4b (fun s => s.RIP = 0x100b4b) (negR32Effect 0x100b4b 2 1) (Reg.operands [.gpr 1] [])) #v[89]
    (.letOp (n := 93) (.out 0x100b4d (andR32R32Effect 0x100b4d 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[91, 80]
    (.letOp (n := 94) (.exec 0x100b4d (fun s => s.RIP = 0x100b4d) (andR32R32Effect 0x100b4d 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[91, 80]
    (.letOp (n := 95) (.out 0x100b4f (testR64R64Effect 0x100b4f 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[74, 74]
    (.letOp (n := 96) (.exec 0x100b4f (fun s => s.RIP = 0x100b4f) (testR64R64Effect 0x100b4f 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[74, 74]
    (.letOp (n := 97) (.out 0x100b52 (movR32Imm32Effect 0x100b52 6 9 0x0) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 98) (.exec 0x100b52 (fun s => s.RIP = 0x100b52) (movR32Imm32Effect 0x100b52 6 9 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x100b58 (atFlags (condHolds 5) (cmovR32R32Effect 0x100b58 4 2 9)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[87, 97, 95]
    (.letOp (n := 100) (.exec 0x100b58 (fun s => s.RIP = 0x100b58) (atFlags (condHolds 5) (cmovR32R32Effect 0x100b58 4 2 9)) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[87, 97, 95]
    (.letOp (n := 101) (.out 0x100b5c (movR64M64Effect 0x100b5c 6 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 102) (.exec 0x100b5c (LoadPre 0x100b5c (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x100b5c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b5c 6 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 103) (.out 0x100b60 (movR32Imm32Effect 0x100b60 5 7 0x7f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 104) (.exec 0x100b60 (fun s => s.RIP = 0x100b60) (movR32Imm32Effect 0x100b60 5 7 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 105) (.out 0x100b65 (bsrR64R64Effect 0x100b65 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[103, 101]
    (.letOp (n := 106) (.exec 0x100b65 (fun s => s.RIP = 0x100b65) (bsrR64R64Effect 0x100b65 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[103, 101]
    (.letOp (n := 107) (.out 0x100b69 (xorR32Imm8Effect 0x100b69 3 7 0x3f) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[105]
    (.letOp (n := 108) (.exec 0x100b69 (fun s => s.RIP = 0x100b69) (xorR32Imm8Effect 0x100b69 3 7 0x3f) (Reg.operands [.gpr 7] [])) #v[105]
    (.letOp (n := 109) (.exec 0x100b6c (StorePre 0x100b6c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b6c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b6c 4 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[99, 4]
    (.letOp (n := 110) (.out 0x100b70 (movzxR32M8Effect 0x100b70 6 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 111) (.exec 0x100b70 (LoadPre 0x100b70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b70 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x100b70 6 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 112) (.out 0x100b76 (negR32Effect 0x100b76 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[110]
    (.letOp (n := 113) (.exec 0x100b76 (fun s => s.RIP = 0x100b76) (negR32Effect 0x100b76 3 8) (Reg.operands [.gpr 8] [])) #v[110]
    (.letOp (n := 114) (.out 0x100b79 (andR32R32Effect 0x100b79 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[112, 107]
    (.letOp (n := 115) (.exec 0x100b79 (fun s => s.RIP = 0x100b79) (andR32R32Effect 0x100b79 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[112, 107]
    (.letOp (n := 116) (.out 0x100b7c (testR64R64Effect 0x100b7c 6 6) (EffectPart.reads (.flag .ZF) [.gpr 6, .gpr 6] []) (.flag .ZF)) #v[101, 101]
    (.letOp (n := 117) (.exec 0x100b7c (fun s => s.RIP = 0x100b7c) (testR64R64Effect 0x100b7c 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[101, 101]
    (.letOp (n := 118) (.out 0x100b7f (atFlags (condHolds 5) (cmovR32R32Effect 0x100b7f 4 2 9)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[99, 97, 116]
    (.letOp (n := 119) (.exec 0x100b7f (fun s => s.RIP = 0x100b7f) (atFlags (condHolds 5) (cmovR32R32Effect 0x100b7f 4 2 9)) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[99, 97, 116]
    (.letOp (n := 120) (.out 0x100b83 (movR32Imm32Effect 0x100b83 5 6 0x7f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 121) (.exec 0x100b83 (fun s => s.RIP = 0x100b83) (movR32Imm32Effect 0x100b83 5 6 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 122) (.out 0x100b88 (bsrR64M64Effect 0x100b88 4 6 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[120, 55]
    (.letOp (n := 123) (.exec 0x100b88 (LoadPre 0x100b88 (fun s => AddrMode.addr (.base 15 .none) s (0x100b88 + BitVec.ofNat 64 4)) 8) (bsrR64M64Effect 0x100b88 4 6 (.base 15 .none)) (Reg.operands [.gpr 6, .gpr 15] [])) #v[120, 55]
    (.letOp (n := 124) (.out 0x100b8c (xorR32Imm8Effect 0x100b8c 3 6 0x3f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[122]
    (.letOp (n := 125) (.exec 0x100b8c (fun s => s.RIP = 0x100b8c) (xorR32Imm8Effect 0x100b8c 3 6 0x3f) (Reg.operands [.gpr 6] [])) #v[122]
    (.letOp (n := 126) (.exec 0x100b8f (StorePre 0x100b8f 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b8f + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100b8f 4 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[118, 4]
    (.letOp (n := 127) (.out 0x100b93 (movzxR32M8Effect 0x100b93 5 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 128) (.exec 0x100b93 (LoadPre 0x100b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b93 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b93 5 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l100afb_2))))))))))))))))))))))))))))))))))))))

def bytes_l100afb_1 : List UInt8 :=
  [0xF7, 0xD9, 0x21, 0xF9, 0x48, 0x85, 0xF6, 0x41, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x41, 0x0F, 0x45,
    0xD1, 0x49, 0x8B, 0x77, 0x08, 0xBF, 0x7F, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xBD, 0xFE, 0x83, 0xF7,
    0x3F, 0x88, 0x54, 0x24, 0x08, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x41, 0xF7, 0xD8, 0x41, 0x21,
    0xF8, 0x48, 0x85, 0xF6, 0x41, 0x0F, 0x45, 0xD1, 0xBE, 0x7F, 0x00, 0x00, 0x00, 0x49, 0x0F, 0xBD,
    0x37, 0x83, 0xF6, 0x3F, 0x88, 0x54, 0x24, 0x08, 0x0F, 0xB6, 0x54, 0x24, 0x08] ++ bytes_l100afb_2

theorem code_l100afb_1 : ∀ x ∈ codeRange 0x100b4b bytes_l100afb_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xb4b 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100afb_2

@[cfg_block] def b_l100afb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100afb (movR64M64Effect 0x100afb 0 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100afb (LoadPre 0x100afb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x100afb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100afb 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100b03 (movR64M64Effect 0x100b03 15 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[53]
    (.letOp (n := 56) (.exec 0x100b03 (LoadPre 0x100b03 (fun s => AddrMode.addr (.base 0 .none) s (0x100b03 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100b03 15 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x100b06 (movR64M64Effect 0x100b06 1 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x100b06 (LoadPre 0x100b06 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x100b06 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b06 1 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 59) (.out 0x100b0a (movR32Imm32Effect 0x100b0a 5 2 0x7f) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 60) (.exec 0x100b0a (fun s => s.RIP = 0x100b0a) (movR32Imm32Effect 0x100b0a 5 2 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x100b0f (bsrR64R64Effect 0x100b0f 4 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x100b0f (fun s => s.RIP = 0x100b0f) (bsrR64R64Effect 0x100b0f 4 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x100b13 (xorR32Imm8Effect 0x100b13 3 2 0x3f) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 64) (.exec 0x100b13 (fun s => s.RIP = 0x100b13) (xorR32Imm8Effect 0x100b13 3 2 0x3f) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 65) (.exec 0x100b16 (StorePre 0x100b16 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b16 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100b16 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.out 0x100b1b (leaR64Effect 0x100b1b 12 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 67) (.exec 0x100b1b (fun s => s.RIP = 0x100b1b) (leaR64Effect 0x100b1b 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.out 0x100b20 (movzxR32M8Effect 0x100b20 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x100b20 (LoadPre 0x100b20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b20 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b20 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x100b25 (negR32Effect 0x100b25 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 71) (.exec 0x100b25 (fun s => s.RIP = 0x100b25) (negR32Effect 0x100b25 2 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 72) (.out 0x100b27 (andR32R32Effect 0x100b27 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[70, 63]
    (.letOp (n := 73) (.exec 0x100b27 (fun s => s.RIP = 0x100b27) (andR32R32Effect 0x100b27 2 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[70, 63]
    (.letOp (n := 74) (.out 0x100b29 (movR64M64Effect 0x100b29 6 (.base 15 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 75) (.exec 0x100b29 (LoadPre 0x100b29 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x100b29 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100b29 6 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 15] [])) #v[55]
    (.letOp (n := 76) (.out 0x100b2d (movR32Imm32Effect 0x100b2d 5 7 0x7f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 77) (.exec 0x100b2d (fun s => s.RIP = 0x100b2d) (movR32Imm32Effect 0x100b2d 5 7 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 78) (.out 0x100b32 (bsrR64R64Effect 0x100b32 4 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[76, 74]
    (.letOp (n := 79) (.exec 0x100b32 (fun s => s.RIP = 0x100b32) (bsrR64R64Effect 0x100b32 4 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[76, 74]
    (.letOp (n := 80) (.out 0x100b36 (xorR32Imm8Effect 0x100b36 3 7 0x3f) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x100b36 (fun s => s.RIP = 0x100b36) (xorR32Imm8Effect 0x100b36 3 7 0x3f) (Reg.operands [.gpr 7] [])) #v[78]
    (.letOp (n := 82) (.out 0x100b39 (xorR32R32Effect 0x100b39 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[63, 63]
    (.letOp (n := 83) (.exec 0x100b39 (fun s => s.RIP = 0x100b39) (xorR32R32Effect 0x100b39 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[63, 63]
    (.letOp (n := 84) (.out 0x100b3b (testR64R64Effect 0x100b3b 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[57, 57]
    (.letOp (n := 85) (.exec 0x100b3b (fun s => s.RIP = 0x100b3b) (testR64R64Effect 0x100b3b 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[57, 57]
    (.letOp (n := 86) (.exec 0x100b3e (StorePre 0x100b3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b3e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100b3e 5 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 84]
    (.letOp (n := 87) (.out 0x100b43 (atFlags (condHolds 4) (setccR8Effect 0x100b43 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[82, 84]
    (.letOp (n := 88) (.exec 0x100b43 (fun s => s.RIP = 0x100b43) (atFlags (condHolds 4) (setccR8Effect 0x100b43 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[82, 84]
    (.letOp (n := 89) (.out 0x100b46 (movzxR32M8Effect 0x100b46 5 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 90) (.exec 0x100b46 (LoadPre 0x100b46 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100b46 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100b46 5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l100afb_1))))))))))))))))))))))))))))))))))))))

def bytes_l100afb : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x8B, 0x38, 0x49, 0x8B, 0x4F, 0x18, 0xBA,
    0x7F, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xBD, 0xD1, 0x83, 0xF2, 0x3F, 0xC6, 0x44, 0x24, 0x08, 0x01,
    0x4C, 0x8D, 0x64, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0xF7, 0xD8, 0x21, 0xD0, 0x49, 0x8B,
    0x77, 0x10, 0xBF, 0x7F, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xBD, 0xFE, 0x83, 0xF7, 0x3F, 0x31, 0xD2,
    0x48, 0x85, 0xC9, 0x0F, 0x94, 0x44, 0x24, 0x08, 0x0F, 0x94, 0xC2, 0x0F, 0xB6, 0x4C, 0x24, 0x08] ++ bytes_l100afb_1

theorem code_l100afb : ∀ x ∈ codeRange 0x100afb bytes_l100afb, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xafb 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100afb_1

@[cfg_block] def b_l100bc6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100bc6 (movR32R32Effect 0x100bc6 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 54) (.exec 0x100bc6 (fun s => s.RIP = 0x100bc6) (movR32R32Effect 0x100bc6 2 1 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x100bc8 (movR64M64Effect 0x100bc8 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 56) (.exec 0x100bc8 (LoadPre 0x100bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bc8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100bc8 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x100bcd (movR64R64Effect 0x100bcd 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 58) (.exec 0x100bcd (fun s => s.RIP = 0x100bcd) (movR64R64Effect 0x100bcd 6 13) (Reg.operands [.gpr 13] [])) #v[55]
    (.letOp (n := 59) (.out 0x100bd0 (subR64R64Effect 0x100bd0 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[57, 53]
    (.letOp (n := 60) (.out 0x100bd0 (subR64R64Effect 0x100bd0 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[57, 53]
    (.letOp (n := 61) (.exec 0x100bd0 (fun s => s.RIP = 0x100bd0) (subR64R64Effect 0x100bd0 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[57, 53]
    (.letOp (n := 62) (.pure (condOp 2)) #v[60]
    (.terminate (.condBr (Fin.last 62) ⟨.l100e1c, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ ⟨.l100bd9, RegMap.args [(0, 0), (1, 53), (2, 2), (3, 3), (4, 4), (5, 5), (6, 59), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 55), (14, 14), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩)))))))))))

def bytes_l100bc6 : List UInt8 :=
  [0x89, 0xC9, 0x4C, 0x8B, 0x6C, 0x24, 0x30, 0x4C, 0x89, 0xEE, 0x48, 0x29, 0xCE, 0x0F, 0x82, 0x43,
    0x02, 0x00, 0x00]

theorem code_l100bc6 : ∀ x ∈ codeRange 0x100bc6 bytes_l100bc6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xbc6 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100bd9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100bd9 (andR32Imm8Effect 0x100bd9 4 14 0xf8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 54) (.exec 0x100bd9 (fun s => s.RIP = 0x100bd9) (andR32Imm8Effect 0x100bd9 4 14 0xf8) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x100bdd (subR32R32Effect 0x100bdd 3 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[8, 53]
    (.letOp (n := 56) (.exec 0x100bdd (fun s => s.RIP = 0x100bdd) (subR32R32Effect 0x100bdd 3 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[8, 53]
    (.letOp (n := 57) (.out 0x100be0 (movR32R32Effect 0x100be0 3 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 8] []) (.reg (.gpr 14))) #v[55]
    (.letOp (n := 58) (.exec 0x100be0 (fun s => s.RIP = 0x100be0) (movR32R32Effect 0x100be0 3 14 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 59) (.out 0x100be3 (subR32R32Effect 0x100be3 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[57, 0]
    (.letOp (n := 60) (.out 0x100be3 (subR32R32Effect 0x100be3 3 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[57, 0]
    (.letOp (n := 61) (.exec 0x100be3 (fun s => s.RIP = 0x100be3) (subR32R32Effect 0x100be3 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[57, 0]
    (.letOp (n := 62) (.out 0x100be6 (atFlags (condHolds 2) (cmovR32R32Effect 0x100be6 4 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[59, 2, 60]
    (.letOp (n := 63) (.exec 0x100be6 (fun s => s.RIP = 0x100be6) (atFlags (condHolds 2) (cmovR32R32Effect 0x100be6 4 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[59, 2, 60]
    (.terminate (.br ⟨.l100bf8, RegMap.args [(0, 0), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 55), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 62), (15, 15), (16, 60), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩))))))))))))

def bytes_l100bd9 : List UInt8 :=
  [0x41, 0x83, 0xE6, 0xF8, 0x45, 0x29, 0xF0, 0x45, 0x89, 0xC6, 0x41, 0x29, 0xC6, 0x44, 0x0F, 0x42,
    0xF2, 0xEB, 0x0C]

theorem code_l100bd9 : ∀ x ∈ codeRange 0x100bd9 bytes_l100bd9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xbd9 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100bf0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100bf0 (movR64M64Effect 0x100bf0 13 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x100bf0 (LoadPre 0x100bf0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x100bf0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100bf0 13 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100bf5 (movR64R64Effect 0x100bf5 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 56) (.exec 0x100bf5 (fun s => s.RIP = 0x100bf5) (movR64R64Effect 0x100bf5 6 13) (Reg.operands [.gpr 13] [])) #v[53]
    (.terminate (.br ⟨.l100bf8, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100bf0 : List UInt8 :=
  [0x4C, 0x8B, 0x6C, 0x24, 0x30, 0x4C, 0x89, 0xEE]

theorem code_l100bf0 : ∀ x ∈ codeRange 0x100bf0 bytes_l100bf0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xbf0 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100bf8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100bf8 (StorePre 0x100bf8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x100bf8 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x100bf8 8 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 54) (.exec 0x100bfd (StorePre 0x100bfd 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100bfd + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x100bfd (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100c09 (StorePre 0x100c09 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c09 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c09 (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x100c12 (StorePre 0x100c12 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c12 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c12 (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100c1b (StorePre 0x100c1b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100c1b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100c1b (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x100c24 (movR32Imm32Effect 0x100c24 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 59) (.exec 0x100c24 (fun s => s.RIP = 0x100c24) (movR32Imm32Effect 0x100c24 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x100c29 (movR64M64Effect 0x100c29 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x100c29 (LoadPre 0x100c29 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100c29 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c29 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x100c2e (leaR64Effect 0x100c2e 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 63) (.exec 0x100c2e (fun s => s.RIP = 0x100c2e) (leaR64Effect 0x100c2e 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x100c33 (callEffect (fun _ => 0x127d70) 0x100c38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x100c33 (PushPre 0x100c33 5) (callEffect (fun _ => 0x127d70) 0x100c38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x100c38⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 0), (1, 58), (2, 62), (3, 3), (4, 64), (5, 5), (6, 6), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l100c38, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l100bf8 : List UInt8 :=
  [0x44, 0x89, 0x44, 0x24, 0x3C, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x70, 0x00,
    0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x8D, 0x54, 0x24, 0x68, 0xE8, 0x38, 0x71, 0x02, 0x00]

theorem code_l100bf8 : ∀ x ∈ codeRange 0x100bf8 bytes_l100bf8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xbf8 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100c38 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100c38 (cmpAlImm8Effect 0x100c38 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x100c38 (fun s => s.RIP = 0x100c38) (cmpAlImm8Effect 0x100c38 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l100e2d, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l100c40, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l100c38 : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0xED, 0x01, 0x00, 0x00]

theorem code_l100c38 : ∀ x ∈ codeRange 0x100c38 bytes_l100c38, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xc38 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100c40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100c40 (movR64M64Effect 0x100c40 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100c40 (LoadPre 0x100c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x100c40 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100c40 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100c48 (StorePre 0x100c48 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100c48 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c48 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x100c50 (movR64M64Effect 0x100c50 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x100c50 (LoadPre 0x100c50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x100c50 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c50 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x100c55 (StorePre 0x100c55 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100c55 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c55 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x100c5d (movR64M64Effect 0x100c5d 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x100c5d (LoadPre 0x100c5d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x100c5d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c5d 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x100c62 (movR64M64Effect 0x100c62 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x100c62 (LoadPre 0x100c62 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x100c62 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c62 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x100c67 (StorePre 0x100c67 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x100c67 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c67 1 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x100c6f (StorePre 0x100c6f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100c6f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c6f 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x100c77 (movR64R64Effect 0x100c77 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[12]
    (.letOp (n := 66) (.exec 0x100c77 (fun s => s.RIP = 0x100c77) (movR64R64Effect 0x100c77 7 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 67) (.out 0x100c7a (leaR64Effect 0x100c7a 6 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x100c7a (fun s => s.RIP = 0x100c7a) (leaR64Effect 0x100c7a 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x100c82 (movR32R32Effect 0x100c82 3 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 70) (.exec 0x100c82 (fun s => s.RIP = 0x100c82) (movR32R32Effect 0x100c82 3 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x100c85 (callEffect (fun _ => 0x1065b0) 0x100c8a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x100c85 (PushPre 0x100c85 5) (callEffect (fun _ => 0x1065b0) 0x100c8a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x100c8a⟩) #v[]
    (.terminate (.call ⟨.l1065b0, RegMap.args [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l100c8a, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l100c40 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44,
    0x24, 0x68, 0x48, 0x8B, 0x4C, 0x24, 0x70, 0x48, 0x89, 0x8C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48,
    0x89, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x8D, 0xB4, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x44, 0x89, 0xF2, 0xE8, 0x26, 0x59, 0x00, 0x00]

theorem code_l100c40 : ∀ x ∈ codeRange 0x100c40 bytes_l100c40, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xc40 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100c8a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100c8a (movR64M64Effect 0x100c8a 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x100c8a (LoadPre 0x100c8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100c8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c8a 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100c8f (movR64M64Effect 0x100c8f 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x100c8f (LoadPre 0x100c8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100c8f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c8f 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100c94 (StorePre 0x100c94 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x100c94 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100c94 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.out 0x100c9c (movR64M64Effect 0x100c9c 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x100c9c (LoadPre 0x100c9c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100c9c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100c9c 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x100ca1 (movR64M64Effect 0x100ca1 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x100ca1 (LoadPre 0x100ca1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100ca1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100ca1 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x100ca6 (StorePre 0x100ca6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100ca6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100ca6 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 63) (.exec 0x100cab (StorePre 0x100cab 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100cab + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cab 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 64) (.exec 0x100cb0 (StorePre 0x100cb0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100cb0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cb0 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 65) (.exec 0x100cb5 (StorePre 0x100cb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100cb5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100cb5 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 66) (.exec 0x100cba (StorePre 0x100cba 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100cba + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cba (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x100cc3 (StorePre 0x100cc3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100cc3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cc3 (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x100ccc (StorePre 0x100ccc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100ccc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100ccc (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.exec 0x100cd5 (StorePre 0x100cd5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100cd5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100cd5 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x100cde (movR32Imm32Effect 0x100cde 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 71) (.exec 0x100cde (fun s => s.RIP = 0x100cde) (movR32Imm32Effect 0x100cde 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x100ce3 (movR32Imm32Effect 0x100ce3 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 73) (.exec 0x100ce3 (fun s => s.RIP = 0x100ce3) (movR32Imm32Effect 0x100ce3 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x100ce8 (leaR64Effect 0x100ce8 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 75) (.exec 0x100ce8 (fun s => s.RIP = 0x100ce8) (leaR64Effect 0x100ce8 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.out 0x100ced (movR64R64Effect 0x100ced 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 77) (.exec 0x100ced (fun s => s.RIP = 0x100ced) (movR64R64Effect 0x100ced 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 78) (.out 0x100cf0 (callEffect (fun _ => 0x127f50) 0x100cf5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 79) (.exec 0x100cf0 (PushPre 0x100cf0 5) (callEffect (fun _ => 0x127f50) 0x100cf5) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.const ⟨64, 0x100cf5⟩) #v[]
    (.terminate (.call ⟨.l127f50, RegMap.args [(0, 53), (1, 72), (2, 76), (3, 3), (4, 78), (5, 5), (6, 70), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l100cf5, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l100c8a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00,
    0x00, 0x00, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24,
    0x48, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x74, 0x24, 0x58, 0x48, 0x89, 0x54, 0x24, 0x60,
    0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08,
    0x00, 0x00, 0x00, 0x00, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x8D,
    0x7C, 0x24, 0x48, 0x4C, 0x89, 0xE2, 0xE8, 0x5B, 0x72, 0x02, 0x00]

theorem code_l100c8a : ∀ x ∈ codeRange 0x100c8a bytes_l100c8a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xc8a 107 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100cf5_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x100dc6 (andAlImm8Effect 0x100dc6 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 170) (.exec 0x100dc6 (fun s => s.RIP = 0x100dc6) (andAlImm8Effect 0x100dc6 0x1) (Reg.operands [.gpr 0] [])) #v[167]
    (.letOp (n := 171) (.exec 0x100dc8 (StorePre 0x100dc8 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dc8 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x100dc8 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[169, 4]
    (.letOp (n := 172) (.out 0x100dcc (cmpM8Imm8Effect 0x100dcc 5 (.sib 4 none 0 (.d8 0x8)) 0x0) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 173) (.exec 0x100dcc (LoadPre 0x100dcc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dcc + BitVec.ofNat 64 5)) 1) (cmpM8Imm8Effect 0x100dcc 5 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 174) (.pure (condOp 5)) #v[172]
    (.terminate (.condBr (Fin.last 174) ⟨.l100df5, RegMap.args [(0, 169), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 172), (22, 22), (39, 39), (50, 50), (51, 51)] 175⟩ ⟨.l100dd3, RegMap.args [(0, 169), (1, 164), (2, 150), (3, 3), (4, 4), (5, 5), (6, 144), (7, 156), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 172), (22, 22), (39, 39), (50, 50), (51, 51)] 175⟩)))))))

def bytes_l100cf5_3 : List UInt8 :=
  [0x24, 0x01, 0x88, 0x44, 0x24, 0x08, 0x80, 0x7C, 0x24, 0x08, 0x00, 0x75, 0x22]

theorem code_l100cf5_3 : ∀ x ∈ codeRange 0x100dc6 bytes_l100cf5_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdc6 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100cf5_2 : Block Op Label signature Reg.count 131 :=
  .letOp (n := 131) (.out 0x100d7e (orR64R64Effect 0x100d7e 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[129, 125]
    (.letOp (n := 132) (.exec 0x100d7e (fun s => s.RIP = 0x100d7e) (orR64R64Effect 0x100d7e 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[129, 125]
    (.letOp (n := 133) (.out 0x100d81 (shrR64Effect 0x100d81 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[131]
    (.letOp (n := 134) (.exec 0x100d81 (fun s => s.RIP = 0x100d81) (shrR64Effect 0x100d81 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.exec 0x100d85 (StorePre 0x100d85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d85 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d85 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[133, 4]
    (.letOp (n := 136) (.out 0x100d8a (movR64M64Effect 0x100d8a 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 137) (.exec 0x100d8a (LoadPre 0x100d8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d8a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d8a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 138) (.out 0x100d8f (xorR32R32Effect 0x100d8f 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[133, 133]
    (.letOp (n := 139) (.exec 0x100d8f (fun s => s.RIP = 0x100d8f) (xorR32R32Effect 0x100d8f 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[133, 133]
    (.letOp (n := 140) (.out 0x100d91 (subR64R64Effect 0x100d91 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x100d91 (fun s => s.RIP = 0x100d91) (subR64R64Effect 0x100d91 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[138, 136]
    (.letOp (n := 142) (.out 0x100d94 (movR64M64Effect 0x100d94 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 143) (.exec 0x100d94 (LoadPre 0x100d94 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x100d94 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d94 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 144) (.out 0x100d99 (movR64M64Effect 0x100d99 6 (.base 15 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 145) (.exec 0x100d99 (LoadPre 0x100d99 (fun s => AddrMode.addr (.base 15 (.d8 0x18)) s (0x100d99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d99 6 (.base 15 (.d8 0x18))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 146) (.out 0x100d9d (sarR64Effect 0x100d9d 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[140]
    (.letOp (n := 147) (.exec 0x100d9d (fun s => s.RIP = 0x100d9d) (sarR64Effect 0x100d9d 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[140]
    (.letOp (n := 148) (.out 0x100da1 (addR64R64Effect 0x100da1 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[146, 142]
    (.letOp (n := 149) (.exec 0x100da1 (fun s => s.RIP = 0x100da1) (addR64R64Effect 0x100da1 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[146, 142]
    (.letOp (n := 150) (.out 0x100da4 (subR64R64Effect 0x100da4 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[148, 144]
    (.letOp (n := 151) (.exec 0x100da4 (fun s => s.RIP = 0x100da4) (subR64R64Effect 0x100da4 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[148, 144]
    (.letOp (n := 152) (.out 0x100da7 (notR64Effect 0x100da7 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[142]
    (.letOp (n := 153) (.exec 0x100da7 (fun s => s.RIP = 0x100da7) (notR64Effect 0x100da7 1) (Reg.operands [.gpr 1] [])) #v[142]
    (.letOp (n := 154) (.out 0x100daa (movR64R64Effect 0x100daa 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[144]
    (.letOp (n := 155) (.exec 0x100daa (fun s => s.RIP = 0x100daa) (movR64R64Effect 0x100daa 7 6) (Reg.operands [.gpr 6] [])) #v[144]
    (.letOp (n := 156) (.out 0x100dad (andR64R64Effect 0x100dad 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[154, 152]
    (.letOp (n := 157) (.exec 0x100dad (fun s => s.RIP = 0x100dad) (andR64R64Effect 0x100dad 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[154, 152]
    (.letOp (n := 158) (.out 0x100db0 (orR64R64Effect 0x100db0 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[152, 144]
    (.letOp (n := 159) (.exec 0x100db0 (fun s => s.RIP = 0x100db0) (orR64R64Effect 0x100db0 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[152, 144]
    (.letOp (n := 160) (.out 0x100db3 (andR64R64Effect 0x100db3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[158, 150]
    (.letOp (n := 161) (.exec 0x100db3 (fun s => s.RIP = 0x100db3) (andR64R64Effect 0x100db3 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[158, 150]
    (.letOp (n := 162) (.out 0x100db6 (orR64R64Effect 0x100db6 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[160, 156]
    (.letOp (n := 163) (.exec 0x100db6 (fun s => s.RIP = 0x100db6) (orR64R64Effect 0x100db6 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[160, 156]
    (.letOp (n := 164) (.out 0x100db9 (shrR64Effect 0x100db9 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x100db9 (fun s => s.RIP = 0x100db9) (shrR64Effect 0x100db9 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[162]
    (.letOp (n := 166) (.exec 0x100dbd (StorePre 0x100dbd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dbd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100dbd 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[164, 4]
    (.letOp (n := 167) (.out 0x100dc2 (andR8M8Effect 0x100dc2 4 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[80, 4]
    (.letOp (n := 168) (.exec 0x100dc2 (LoadPre 0x100dc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100dc2 + BitVec.ofNat 64 4)) 1) (andR8M8Effect 0x100dc2 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[80, 4]
    (b_l100cf5_3))))))))))))))))))))))))))))))))))))))

def bytes_l100cf5_2 : List UInt8 :=
  [0x48, 0x09, 0xFA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24,
    0x08, 0x31, 0xD2, 0x48, 0x29, 0xCA, 0x48, 0x8B, 0x4C, 0x24, 0x60, 0x49, 0x8B, 0x77, 0x18, 0x48,
    0xC1, 0xFA, 0x3F, 0x48, 0x01, 0xCA, 0x48, 0x29, 0xF2, 0x48, 0xF7, 0xD1, 0x48, 0x89, 0xF7, 0x48,
    0x21, 0xCF, 0x48, 0x09, 0xF1, 0x48, 0x21, 0xD1, 0x48, 0x09, 0xF9, 0x48, 0xC1, 0xE9, 0x3F, 0x48,
    0x89, 0x4C, 0x24, 0x08, 0x22, 0x44, 0x24, 0x08] ++ bytes_l100cf5_3

theorem code_l100cf5_2 : ∀ x ∈ codeRange 0x100d7e bytes_l100cf5_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd7e 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100cf5_3

@[cfg_block] def b_l100cf5_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x100d3a (notR64Effect 0x100d3a 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[82]
    (.letOp (n := 93) (.exec 0x100d3a (fun s => s.RIP = 0x100d3a) (notR64Effect 0x100d3a 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 94) (.out 0x100d3d (movR64R64Effect 0x100d3d 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[84]
    (.letOp (n := 95) (.exec 0x100d3d (fun s => s.RIP = 0x100d3d) (movR64R64Effect 0x100d3d 7 6) (Reg.operands [.gpr 6] [])) #v[84]
    (.letOp (n := 96) (.out 0x100d40 (andR64R64Effect 0x100d40 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[94, 92]
    (.letOp (n := 97) (.exec 0x100d40 (fun s => s.RIP = 0x100d40) (andR64R64Effect 0x100d40 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[94, 92]
    (.letOp (n := 98) (.out 0x100d43 (orR64R64Effect 0x100d43 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[92, 84]
    (.letOp (n := 99) (.exec 0x100d43 (fun s => s.RIP = 0x100d43) (orR64R64Effect 0x100d43 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[92, 84]
    (.letOp (n := 100) (.out 0x100d46 (andR64R64Effect 0x100d46 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[98, 90]
    (.letOp (n := 101) (.exec 0x100d46 (fun s => s.RIP = 0x100d46) (andR64R64Effect 0x100d46 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[98, 90]
    (.letOp (n := 102) (.out 0x100d49 (orR64R64Effect 0x100d49 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[100, 96]
    (.letOp (n := 103) (.exec 0x100d49 (fun s => s.RIP = 0x100d49) (orR64R64Effect 0x100d49 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[100, 96]
    (.letOp (n := 104) (.out 0x100d4c (shrR64Effect 0x100d4c 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[102]
    (.letOp (n := 105) (.exec 0x100d4c (fun s => s.RIP = 0x100d4c) (shrR64Effect 0x100d4c 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.exec 0x100d50 (StorePre 0x100d50 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d50 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d50 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[104, 4]
    (.letOp (n := 107) (.out 0x100d55 (xorR32R32Effect 0x100d55 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[90, 90]
    (.letOp (n := 108) (.exec 0x100d55 (fun s => s.RIP = 0x100d55) (xorR32R32Effect 0x100d55 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[90, 90]
    (.letOp (n := 109) (.out 0x100d57 (subR64M64Effect 0x100d57 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[107, 4]
    (.letOp (n := 110) (.exec 0x100d57 (LoadPre 0x100d57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d57 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x100d57 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[107, 4]
    (.letOp (n := 111) (.out 0x100d5c (movR64M64Effect 0x100d5c 2 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 112) (.exec 0x100d5c (LoadPre 0x100d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x100d5c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d5c 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x100d61 (movR64M64Effect 0x100d61 6 (.base 15 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 114) (.exec 0x100d61 (LoadPre 0x100d61 (fun s => AddrMode.addr (.base 15 (.d8 0x10)) s (0x100d61 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d61 6 (.base 15 (.d8 0x10))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 115) (.out 0x100d65 (sarR64Effect 0x100d65 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[109]
    (.letOp (n := 116) (.exec 0x100d65 (fun s => s.RIP = 0x100d65) (sarR64Effect 0x100d65 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 117) (.out 0x100d69 (addR64R64Effect 0x100d69 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[115, 111]
    (.letOp (n := 118) (.exec 0x100d69 (fun s => s.RIP = 0x100d69) (addR64R64Effect 0x100d69 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[115, 111]
    (.letOp (n := 119) (.out 0x100d6c (subR64R64Effect 0x100d6c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[117, 113]
    (.letOp (n := 120) (.exec 0x100d6c (fun s => s.RIP = 0x100d6c) (subR64R64Effect 0x100d6c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[117, 113]
    (.letOp (n := 121) (.out 0x100d6f (notR64Effect 0x100d6f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[111]
    (.letOp (n := 122) (.exec 0x100d6f (fun s => s.RIP = 0x100d6f) (notR64Effect 0x100d6f 2) (Reg.operands [.gpr 2] [])) #v[111]
    (.letOp (n := 123) (.out 0x100d72 (movR64R64Effect 0x100d72 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[113]
    (.letOp (n := 124) (.exec 0x100d72 (fun s => s.RIP = 0x100d72) (movR64R64Effect 0x100d72 7 6) (Reg.operands [.gpr 6] [])) #v[113]
    (.letOp (n := 125) (.out 0x100d75 (andR64R64Effect 0x100d75 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x100d75 (fun s => s.RIP = 0x100d75) (andR64R64Effect 0x100d75 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[123, 121]
    (.letOp (n := 127) (.out 0x100d78 (orR64R64Effect 0x100d78 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[121, 113]
    (.letOp (n := 128) (.exec 0x100d78 (fun s => s.RIP = 0x100d78) (orR64R64Effect 0x100d78 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[121, 113]
    (.letOp (n := 129) (.out 0x100d7b (andR64R64Effect 0x100d7b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[127, 119]
    (.letOp (n := 130) (.exec 0x100d7b (fun s => s.RIP = 0x100d7b) (andR64R64Effect 0x100d7b 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[127, 119]
    (b_l100cf5_2)))))))))))))))))))))))))))))))))))))))

def bytes_l100cf5_1 : List UInt8 :=
  [0x48, 0xF7, 0xD2, 0x48, 0x89, 0xF7, 0x48, 0x21, 0xD7, 0x48, 0x09, 0xF2, 0x48, 0x21, 0xCA, 0x48,
    0x09, 0xFA, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x31, 0xC9, 0x48, 0x2B, 0x4C,
    0x24, 0x08, 0x48, 0x8B, 0x54, 0x24, 0x58, 0x49, 0x8B, 0x77, 0x10, 0x48, 0xC1, 0xF9, 0x3F, 0x48,
    0x01, 0xD1, 0x48, 0x29, 0xF1, 0x48, 0xF7, 0xD2, 0x48, 0x89, 0xF7, 0x48, 0x21, 0xD7, 0x48, 0x09,
    0xF2, 0x48, 0x21, 0xCA] ++ bytes_l100cf5_2

theorem code_l100cf5_1 : ∀ x ∈ codeRange 0x100d3a bytes_l100cf5_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xd3a 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100cf5_2

@[cfg_block] def b_l100cf5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100cf5 (movR64M64Effect 0x100cf5 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x100cf5 (LoadPre 0x100cf5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x100cf5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100cf5 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100cfa (movR64M64Effect 0x100cfa 2 (.base 15 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 56) (.exec 0x100cfa (LoadPre 0x100cfa (fun s => AddrMode.addr (.base 15 .none) s (0x100cfa + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100cfa 2 (.base 15 .none)) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x100cfd (movR64R64Effect 0x100cfd 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 58) (.exec 0x100cfd (fun s => s.RIP = 0x100cfd) (movR64R64Effect 0x100cfd 6 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 59) (.out 0x100d00 (subR64R64Effect 0x100d00 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x100d00 (fun s => s.RIP = 0x100d00) (subR64R64Effect 0x100d00 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x100d03 (notR64Effect 0x100d03 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 62) (.exec 0x100d03 (fun s => s.RIP = 0x100d03) (notR64Effect 0x100d03 1) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 63) (.out 0x100d06 (movR64R64Effect 0x100d06 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 64) (.exec 0x100d06 (fun s => s.RIP = 0x100d06) (movR64R64Effect 0x100d06 7 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 65) (.out 0x100d09 (andR64R64Effect 0x100d09 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x100d09 (fun s => s.RIP = 0x100d09) (andR64R64Effect 0x100d09 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x100d0c (orR64R64Effect 0x100d0c 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[61, 55]
    (.letOp (n := 68) (.exec 0x100d0c (fun s => s.RIP = 0x100d0c) (orR64R64Effect 0x100d0c 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[61, 55]
    (.letOp (n := 69) (.out 0x100d0f (andR64R64Effect 0x100d0f 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[67, 59]
    (.letOp (n := 70) (.exec 0x100d0f (fun s => s.RIP = 0x100d0f) (andR64R64Effect 0x100d0f 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[67, 59]
    (.letOp (n := 71) (.out 0x100d12 (orR64R64Effect 0x100d12 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x100d12 (fun s => s.RIP = 0x100d12) (orR64R64Effect 0x100d12 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x100d15 (shrR64Effect 0x100d15 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x100d15 (fun s => s.RIP = 0x100d15) (shrR64Effect 0x100d15 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[71]
    (.letOp (n := 75) (.exec 0x100d19 (StorePre 0x100d19 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d19 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100d19 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x100d1e (xorR32R32Effect 0x100d1e 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[73, 73]
    (.letOp (n := 77) (.exec 0x100d1e (fun s => s.RIP = 0x100d1e) (xorR32R32Effect 0x100d1e 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[73, 73]
    (.letOp (n := 78) (.out 0x100d20 (subR64M64Effect 0x100d20 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[76, 4]
    (.letOp (n := 79) (.exec 0x100d20 (LoadPre 0x100d20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100d20 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x100d20 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 80) (.out 0x100d25 (notR8Effect 0x100d25 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 81) (.exec 0x100d25 (fun s => s.RIP = 0x100d25) (notR8Effect 0x100d25 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 82) (.out 0x100d27 (movR64M64Effect 0x100d27 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 83) (.exec 0x100d27 (LoadPre 0x100d27 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x100d27 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100d27 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 84) (.out 0x100d2c (movR64M64Effect 0x100d2c 6 (.base 15 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 85) (.exec 0x100d2c (LoadPre 0x100d2c (fun s => AddrMode.addr (.base 15 (.d8 0x8)) s (0x100d2c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100d2c 6 (.base 15 (.d8 0x8))) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 86) (.out 0x100d30 (sarR64Effect 0x100d30 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[78]
    (.letOp (n := 87) (.exec 0x100d30 (fun s => s.RIP = 0x100d30) (sarR64Effect 0x100d30 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 88) (.out 0x100d34 (addR64R64Effect 0x100d34 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[86, 82]
    (.letOp (n := 89) (.exec 0x100d34 (fun s => s.RIP = 0x100d34) (addR64R64Effect 0x100d34 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[86, 82]
    (.letOp (n := 90) (.out 0x100d37 (subR64R64Effect 0x100d37 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[88, 84]
    (.letOp (n := 91) (.exec 0x100d37 (fun s => s.RIP = 0x100d37) (subR64R64Effect 0x100d37 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[88, 84]
    (b_l100cf5_1)))))))))))))))))))))))))))))))))))))))

def bytes_l100cf5 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x48, 0x49, 0x8B, 0x17, 0x48, 0x89, 0xCE, 0x48, 0x29, 0xD6, 0x48, 0xF7,
    0xD1, 0x48, 0x89, 0xD7, 0x48, 0x21, 0xCF, 0x48, 0x09, 0xD1, 0x48, 0x21, 0xF1, 0x48, 0x09, 0xF9,
    0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x08, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x08,
    0xF6, 0xD0, 0x48, 0x8B, 0x54, 0x24, 0x50, 0x49, 0x8B, 0x77, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x48,
    0x01, 0xD1, 0x48, 0x29, 0xF1] ++ bytes_l100cf5_1

theorem code_l100cf5 : ∀ x ∈ codeRange 0x100cf5 bytes_l100cf5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xcf5 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100cf5_1

@[cfg_block] def b_l100dd3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100dd3 (movR64M64Effect 0x100dd3 7 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x100dd3 (LoadPre 0x100dd3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x100dd3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100dd3 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100dd8 (testR64R64Effect 0x100dd8 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 56) (.exec 0x100dd8 (fun s => s.RIP = 0x100dd8) (testR64R64Effect 0x100dd8 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 57) (.out 0x100ddb (movR64M64Effect 0x100ddb 12 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 58) (.exec 0x100ddb (LoadPre 0x100ddb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x100ddb + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100ddb 12 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100de3 (leaR64Effect 0x100de3 3 (.rip 0x29a36)) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 60) (.exec 0x100de3 (fun s => s.RIP = 0x100de3) (leaR64Effect 0x100de3 3 (.rip 0x29a36)) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.pure (condOp 5)) #v[55]
    (.terminate (.condBr (Fin.last 61) ⟨.l100ab0, RegMap.args [(2, 2), (3, 59), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ ⟨.l100df0, RegMap.args [(2, 2), (3, 59), (4, 4), (5, 5), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 57), (13, 13), (14, 14), (15, 15), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩))))))))))

def bytes_l100dd3 : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x40, 0x4D, 0x85, 0xED, 0x4C, 0x8B, 0xA4, 0x24, 0x88, 0x00, 0x00, 0x00,
    0x48, 0x8D, 0x1D, 0x36, 0x9A, 0x02, 0x00, 0x0F, 0x85, 0xC0, 0xFC, 0xFF, 0xFF]

theorem code_l100dd3 : ∀ x ∈ codeRange 0x100dd3 bytes_l100dd3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdd3 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100df0 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l100aef, RegMap.args (entryMap (live .l100df0)) 53⟩)

def bytes_l100df0 : List UInt8 :=
  [0xE9, 0xFA, 0xFC, 0xFF, 0xFF]

theorem code_l100df0 : ∀ x ∈ codeRange 0x100df0 bytes_l100df0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdf0 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100df5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100df5 (leaR64Effect 0x100df5 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x100df5 (fun s => s.RIP = 0x100df5) (leaR64Effect 0x100df5 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100dfa (movR64R64Effect 0x100dfa 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 56) (.exec 0x100dfa (fun s => s.RIP = 0x100dfa) (movR64R64Effect 0x100dfa 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 57) (.out 0x100dfd (movR64M64Effect 0x100dfd 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x100dfd (LoadPre 0x100dfd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100dfd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100dfd 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100e02 (movR64R64Effect 0x100e02 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[13]
    (.letOp (n := 60) (.exec 0x100e02 (fun s => s.RIP = 0x100e02) (movR64R64Effect 0x100e02 1 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x100e05 (callEffect (fun _ => 0x100000) 0x100e0a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x100e05 (PushPre 0x100e05 5) (callEffect (fun _ => 0x100000) 0x100e0a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x100e0a⟩) #v[]
    (.terminate (.call ⟨.l100000, RegMap.args [(1, 59), (2, 57), (3, 3), (4, 61), (5, 5), (6, 55), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l100e0a, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l100df5 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x48, 0x4C, 0x89, 0xFE, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x4C, 0x89, 0xE9,
    0xE8, 0xF6, 0xF1, 0xFF, 0xFF]

theorem code_l100df5 : ∀ x ∈ codeRange 0x100df5 bytes_l100df5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xdf5 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e0a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e0a (addR64Imm32Effect 0x100e0a 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x100e0a (fun s => s.RIP = 0x100e0a) (addR64Imm32Effect 0x100e0a 4 0xb8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100e11 (popR64Effect 0x100e11 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[53]
    (.letOp (n := 56) (.out 0x100e11 (popR64Effect 0x100e11 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[53]
    (.letOp (n := 57) (.exec 0x100e11 (PopPre 0x100e11) (popR64Effect 0x100e11 1 3) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x100e12 (popR64Effect 0x100e12 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[56]
    (.letOp (n := 59) (.out 0x100e12 (popR64Effect 0x100e12 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[56]
    (.letOp (n := 60) (.exec 0x100e12 (PopPre 0x100e12) (popR64Effect 0x100e12 2 12) (Reg.operands [.gpr 4] [])) #v[56]
    (.letOp (n := 61) (.out 0x100e14 (popR64Effect 0x100e14 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[59]
    (.letOp (n := 62) (.out 0x100e14 (popR64Effect 0x100e14 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 63) (.exec 0x100e14 (PopPre 0x100e14) (popR64Effect 0x100e14 2 13) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 64) (.out 0x100e16 (popR64Effect 0x100e16 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[62]
    (.letOp (n := 65) (.out 0x100e16 (popR64Effect 0x100e16 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[62]
    (.letOp (n := 66) (.exec 0x100e16 (PopPre 0x100e16) (popR64Effect 0x100e16 2 14) (Reg.operands [.gpr 4] [])) #v[62]
    (.letOp (n := 67) (.out 0x100e18 (popR64Effect 0x100e18 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 68) (.out 0x100e18 (popR64Effect 0x100e18 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 69) (.exec 0x100e18 (PopPre 0x100e18) (popR64Effect 0x100e18 2 15) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 70) (.out 0x100e1a (popR64Effect 0x100e1a 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[68]
    (.letOp (n := 71) (.out 0x100e1a (popR64Effect 0x100e1a 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x100e1a (PopPre 0x100e1a) (popR64Effect 0x100e1a 1 5) (Reg.operands [.gpr 4] [])) #v[68]
    (.letOp (n := 73) (.out 0x100e1b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[71]
    (.letOp (n := 74) (.out 0x100e1b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[71]
    (.letOp (n := 75) (.exec 0x100e1b (RetPre 0x100e1b) (retEffect) (Reg.operands [.gpr 4] [])) #v[71]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 55), (4, 74), (5, 70), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 58), (13, 61), (14, 64), (15, 67), (22, 22), (39, 39), (50, 50), (51, 51)] 76) (some ⟨73, by decide⟩)))))))))))))))))))))))))

def bytes_l100e0a : List UInt8 :=
  [0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l100e0a : ∀ x ∈ codeRange 0x100e0a bytes_l100e0a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe0a 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e1c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e1c (xorR32R32Effect 0x100e1c 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x100e1c (fun s => s.RIP = 0x100e1c) (xorR32R32Effect 0x100e1c 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x100e1e (movR64R64Effect 0x100e1e 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 56) (.exec 0x100e1e (fun s => s.RIP = 0x100e1e) (movR64R64Effect 0x100e1e 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 57) (.out 0x100e21 (movR64Imm32Effect 0x100e21 1 0x202080) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x100e21 (fun s => s.RIP = 0x100e21) (movR64Imm32Effect 0x100e21 1 0x202080) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e28 (callEffect (fun _ => 0x129b60) 0x100e2d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e28 (PushPre 0x100e28 5) (callEffect (fun _ => 0x129b60) 0x100e2d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e2d⟩) #v[]
    (.terminate (.call ⟨.l129b60, RegMap.args [(1, 57), (2, 55), (4, 59), (5, 5), (6, 6), (7, 53), (13, 13)] 62⟩ { target := .l100e2d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e1c : List UInt8 :=
  [0x31, 0xFF, 0x4C, 0x89, 0xEA, 0x48, 0xC7, 0xC1, 0x80, 0x20, 0x20, 0x00, 0xE8, 0x33, 0x8D, 0x02,
    0x00]

theorem code_l100e1c : ∀ x ∈ codeRange 0x100e1c bytes_l100e1c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe1c 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e2d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100e2d (StorePre 0x100e2d 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100e2d + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e2d (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x100e36 (StorePre 0x100e36 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x100e36 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e36 (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x100e3f (leaR64Effect 0x100e3f 0 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x100e3f (fun s => s.RIP = 0x100e3f) (leaR64Effect 0x100e3f 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x100e44 (StorePre 0x100e44 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x100e44 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x100e44 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x100e49 (StorePre 0x100e49 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x100e49 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x100e49 (.sib 4 none 0 (.d8 0x20)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100e52 (leaR64Effect 0x100e52 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x100e52 (fun s => s.RIP = 0x100e52) (leaR64Effect 0x100e52 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x100e57 (movR64Imm32Effect 0x100e57 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 62) (.exec 0x100e57 (fun s => s.RIP = 0x100e57) (movR64Imm32Effect 0x100e57 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x100e5e (movR64Imm32Effect 0x100e5e 2 0x2022a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x100e5e (fun s => s.RIP = 0x100e5e) (movR64Imm32Effect 0x100e5e 2 0x2022a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x100e65 (callEffect (fun _ => 0x129770) 0x100e6a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x100e65 (PushPre 0x100e65 5) (callEffect (fun _ => 0x129770) 0x100e6a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x100e6a⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)] 68⟩ { target := .l100e6a, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l100e2d : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x8D, 0x44, 0x24, 0x3C, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0xC7, 0x44, 0x24,
    0x20, 0x90, 0xA1, 0x12, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0xC7, 0xC7, 0x8F, 0x02, 0x20,
    0x00, 0x48, 0xC7, 0xC2, 0xA0, 0x22, 0x20, 0x00, 0xE8, 0x06, 0x89, 0x02, 0x00]

theorem code_l100e2d : ∀ x ∈ codeRange 0x100e2d bytes_l100e2d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe2d 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e6a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e6a (movR64R64Effect 0x100e6a 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 54) (.exec 0x100e6a (fun s => s.RIP = 0x100e6a) (movR64R64Effect 0x100e6a 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 55) (.out 0x100e6d (movR64R64Effect 0x100e6d 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[1]
    (.letOp (n := 56) (.exec 0x100e6d (fun s => s.RIP = 0x100e6d) (movR64R64Effect 0x100e6d 7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 57) (.out 0x100e70 (movR64M64Effect 0x100e70 6 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x100e70 (LoadPre 0x100e70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x100e70 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x100e70 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x100e75 (movR64R64Effect 0x100e75 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[13]
    (.letOp (n := 60) (.exec 0x100e75 (fun s => s.RIP = 0x100e75) (movR64R64Effect 0x100e75 2 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 61) (.out 0x100e78 (callEffect (fun _ => 0x103ec0) 0x100e7d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x100e78 (PushPre 0x100e78 5) (callEffect (fun _ => 0x103ec0) 0x100e7d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x100e7d⟩) #v[]
    (.terminate (.call ⟨.l103ec0, RegMap.args [(0, 0), (1, 1), (2, 59), (3, 53), (4, 61), (5, 5), (6, 57), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l100e7d, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l100e6a : List UInt8 :=
  [0x48, 0x89, 0xFB, 0x48, 0x89, 0xCF, 0x48, 0x8B, 0x74, 0x24, 0x28, 0x4C, 0x89, 0xEA, 0xE8, 0x43,
    0x30, 0x00, 0x00]

theorem code_l100e6a : ∀ x ∈ codeRange 0x100e6a bytes_l100e6a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe6a 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e7d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e7d (movR64M64Effect 0x100e7d 7 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x100e7d (LoadPre 0x100e7d (fun s => AddrMode.addr (.base 3 .none) s (0x100e7d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100e7d 7 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x100e80 (callEffect (fun _ => 0x1067b0) 0x100e85) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x100e80 (PushPre 0x100e80 5) (callEffect (fun _ => 0x1067b0) 0x100e85) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x100e85⟩) #v[]
    (.terminate (.call ⟨.l1067b0, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (8, 8), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l100e85, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l100e7d : List UInt8 :=
  [0x48, 0x8B, 0x3B, 0xE8, 0x2B, 0x59, 0x00, 0x00]

theorem code_l100e7d : ∀ x ∈ codeRange 0x100e7d bytes_l100e7d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe7d 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e85 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100e85 (movR32Imm32Effect 0x100e85 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x100e85 (fun s => s.RIP = 0x100e85) (movR32Imm32Effect 0x100e85 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x100e8a (movR64Imm32Effect 0x100e8a 7 0x202098) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x100e8a (fun s => s.RIP = 0x100e8a) (movR64Imm32Effect 0x100e8a 7 0x202098) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x100e91 (movR64Imm32Effect 0x100e91 2 0x2020c8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x100e91 (fun s => s.RIP = 0x100e91) (movR64Imm32Effect 0x100e91 2 0x2020c8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x100e98 (callEffect (fun _ => 0x129560) 0x100e9d) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x100e98 (PushPre 0x100e98 5) (callEffect (fun _ => 0x129560) 0x100e9d) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x100e9d⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l100e9d, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l100e85 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x98, 0x20, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0xC8,
    0x20, 0x20, 0x00, 0xE8, 0xC3, 0x86, 0x02, 0x00]

theorem code_l100e85 : ∀ x ∈ codeRange 0x100e85 bytes_l100e85, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe85 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100e9d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100e9d (fun s => s.RIP = 0x100e9d) (fun _ => nopEffect 0x100e9d 3) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l100ea0, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩))

def bytes_l100e9d : List UInt8 :=
  [0x0F, 0x1F, 0x00]

theorem code_l100e9d : ∀ x ∈ codeRange 0x100e9d bytes_l100e9d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xe9d 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ea0_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x100ee4 (movR64M64Effect 0x100ee4 5 (.base 7 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 7] []) (.reg (.gpr 5))) #v[72]
    (.letOp (n := 93) (.exec 0x100ee4 (LoadPre 0x100ee4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x100ee4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100ee4 5 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 7] [])) #v[72]
    (.letOp (n := 94) (.out 0x100ee8 (movR64R64Effect 0x100ee8 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[92]
    (.letOp (n := 95) (.exec 0x100ee8 (fun s => s.RIP = 0x100ee8) (movR64R64Effect 0x100ee8 7 5) (Reg.operands [.gpr 5] [])) #v[92]
    (.letOp (n := 96) (.out 0x100eeb (bswapR64Effect 0x100eeb 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[94]
    (.letOp (n := 97) (.exec 0x100eeb (fun s => s.RIP = 0x100eeb) (bswapR64Effect 0x100eeb 3 7) (Reg.operands [.gpr 7] [])) #v[94]
    (.letOp (n := 98) (.exec 0x100eee (StorePre 0x100eee 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x100eee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100eee 7 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[96, 65]
    (.letOp (n := 99) (.exec 0x100ef6 (StorePre 0x100ef6 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x100ef6 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100ef6 10 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[90, 65]
    (.letOp (n := 100) (.exec 0x100efe (StorePre 0x100efe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x100efe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100efe 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[84, 65]
    (.letOp (n := 101) (.exec 0x100f06 (StorePre 0x100f06 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x100f06 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f06 1 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[80, 65]
    (.letOp (n := 102) (.out 0x100f0e (cmpR64Imm8Effect 0x100f0e 11 0x20) (EffectPart.reads (.flag .CF) [.gpr 11] []) (.flag .CF)) #v[69]
    (.letOp (n := 103) (.out 0x100f0e (cmpR64Imm8Effect 0x100f0e 11 0x20) (EffectPart.reads (.flag .ZF) [.gpr 11] []) (.flag .ZF)) #v[69]
    (.letOp (n := 104) (.exec 0x100f0e (fun s => s.RIP = 0x100f0e) (cmpR64Imm8Effect 0x100f0e 11 0x20) (Reg.operands [.gpr 11] [])) #v[69]
    (.letOp (n := 105) (.pure (condOp 7)) #v[102, 103]
    (.terminate (.condBr (Fin.last 105) ⟨.l10138a, RegMap.args [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (16, 102), (19, 103), (22, 22), (39, 39), (50, 50), (51, 51)] 106⟩ ⟨.l100f18, RegMap.args [(0, 67), (1, 80), (2, 84), (3, 3), (4, 65), (5, 92), (6, 6), (7, 96), (8, 8), (9, 9), (10, 90), (11, 69), (12, 12), (13, 86), (14, 76), (15, 74), (16, 102), (19, 103), (22, 22), (39, 39), (50, 50), (51, 51)] 106⟩)))))))))))))))

def bytes_l100ea0_1 : List UInt8 :=
  [0x48, 0x8B, 0x6F, 0x18, 0x48, 0x89, 0xEF, 0x48, 0x0F, 0xCF, 0x48, 0x89, 0xBC, 0x24, 0xC8, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0x94, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24, 0xD8, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFB, 0x20, 0x0F, 0x87,
    0x72, 0x04, 0x00, 0x00]

theorem code_l100ea0_1 : ∀ x ∈ codeRange 0x100ee4 bytes_l100ea0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xee4 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100ea0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100ea0 (pushR64Effect 0x100ea0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x100ea0 (PushPre 0x100ea0 1) (pushR64Effect 0x100ea0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x100ea1 (pushR64Effect 0x100ea1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x100ea1 (PushPre 0x100ea1 2) (pushR64Effect 0x100ea1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x100ea3 (pushR64Effect 0x100ea3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x100ea3 (PushPre 0x100ea3 2) (pushR64Effect 0x100ea3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x100ea5 (pushR64Effect 0x100ea5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x100ea5 (PushPre 0x100ea5 2) (pushR64Effect 0x100ea5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x100ea7 (pushR64Effect 0x100ea7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x100ea7 (PushPre 0x100ea7 2) (pushR64Effect 0x100ea7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x100ea9 (pushR64Effect 0x100ea9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x100ea9 (PushPre 0x100ea9 1) (pushR64Effect 0x100ea9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x100eaa (subR64Imm32Effect 0x100eaa 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x100eaa (fun s => s.RIP = 0x100eaa) (subR64Imm32Effect 0x100eaa 4 0xe8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x100eb1 (movR64R64Effect 0x100eb1 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 68) (.exec 0x100eb1 (fun s => s.RIP = 0x100eb1) (movR64R64Effect 0x100eb1 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 69) (.out 0x100eb4 (movR64R64Effect 0x100eb4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 70) (.exec 0x100eb4 (fun s => s.RIP = 0x100eb4) (movR64R64Effect 0x100eb4 11 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.exec 0x100eb7 (StorePre 0x100eb7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x100eb7 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100eb7 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 72) (.out 0x100ebf (movR64M64Effect 0x100ebf 7 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 73) (.exec 0x100ebf (LoadPre 0x100ebf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x100ebf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x100ebf 7 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 74) (.out 0x100ec7 (movR64M64Effect 0x100ec7 15 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 7] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 75) (.exec 0x100ec7 (LoadPre 0x100ec7 (fun s => AddrMode.addr (.base 7 .none) s (0x100ec7 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x100ec7 15 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[72]
    (.letOp (n := 76) (.out 0x100eca (movR64M64Effect 0x100eca 14 (.base 7 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 7] []) (.reg (.gpr 14))) #v[72]
    (.letOp (n := 77) (.exec 0x100eca (LoadPre 0x100eca (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x100eca + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eca 14 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 7] [])) #v[72]
    (.letOp (n := 78) (.out 0x100ece (movR64R64Effect 0x100ece 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[74]
    (.letOp (n := 79) (.exec 0x100ece (fun s => s.RIP = 0x100ece) (movR64R64Effect 0x100ece 1 15) (Reg.operands [.gpr 15] [])) #v[74]
    (.letOp (n := 80) (.out 0x100ed1 (bswapR64Effect 0x100ed1 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[78]
    (.letOp (n := 81) (.exec 0x100ed1 (fun s => s.RIP = 0x100ed1) (bswapR64Effect 0x100ed1 3 1) (Reg.operands [.gpr 1] [])) #v[78]
    (.letOp (n := 82) (.out 0x100ed4 (movR64R64Effect 0x100ed4 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[76]
    (.letOp (n := 83) (.exec 0x100ed4 (fun s => s.RIP = 0x100ed4) (movR64R64Effect 0x100ed4 2 14) (Reg.operands [.gpr 14] [])) #v[76]
    (.letOp (n := 84) (.out 0x100ed7 (bswapR64Effect 0x100ed7 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[82]
    (.letOp (n := 85) (.exec 0x100ed7 (fun s => s.RIP = 0x100ed7) (bswapR64Effect 0x100ed7 3 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 86) (.out 0x100eda (movR64M64Effect 0x100eda 13 (.base 7 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 7] []) (.reg (.gpr 13))) #v[72]
    (.letOp (n := 87) (.exec 0x100eda (LoadPre 0x100eda (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x100eda + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x100eda 13 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 7] [])) #v[72]
    (.letOp (n := 88) (.out 0x100ede (movR64R64Effect 0x100ede 10 13) (EffectPart.reads (.reg (.gpr 10)) [.gpr 13] []) (.reg (.gpr 10))) #v[86]
    (.letOp (n := 89) (.exec 0x100ede (fun s => s.RIP = 0x100ede) (movR64R64Effect 0x100ede 10 13) (Reg.operands [.gpr 13] [])) #v[86]
    (.letOp (n := 90) (.out 0x100ee1 (bswapR64Effect 0x100ee1 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[88]
    (.letOp (n := 91) (.exec 0x100ee1 (fun s => s.RIP = 0x100ee1) (bswapR64Effect 0x100ee1 3 10) (Reg.operands [.gpr 10] [])) #v[88]
    (b_l100ea0_1)))))))))))))))))))))))))))))))))))))))

def bytes_l100ea0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xC8, 0x49, 0x89, 0xD3, 0x48, 0x89, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0xBC, 0x24, 0x28, 0x01, 0x00, 0x00, 0x4C, 0x8B, 0x3F, 0x4C, 0x8B, 0x77, 0x08, 0x4C, 0x89,
    0xF9, 0x48, 0x0F, 0xC9, 0x4C, 0x89, 0xF2, 0x48, 0x0F, 0xCA, 0x4C, 0x8B, 0x6F, 0x10, 0x4D, 0x89,
    0xEA, 0x49, 0x0F, 0xCA] ++ bytes_l100ea0_1

theorem code_l100ea0 : ∀ x ∈ codeRange 0x100ea0 bytes_l100ea0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xea0 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100ea0_1

@[cfg_block] def b_l100f18_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x100f6b (shrR64Effect 0x100f6b 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[85]
    (.letOp (n := 88) (.exec 0x100f6b (fun s => s.RIP = 0x100f6b) (shrR64Effect 0x100f6b 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.pure (condOp 5)) #v[87]
    (.terminate (.condBr (Fin.last 89) ⟨.l1013a0, RegMap.args [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ ⟨.l100f75, RegMap.args [(0, 0), (1, 69), (2, 78), (3, 62), (4, 4), (5, 82), (6, 56), (8, 8), (9, 9), (10, 71), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩))))

def bytes_l100f18_1 : List UInt8 :=
  [0x48, 0xC1, 0xEF, 0x20, 0x0F, 0x85, 0x2B, 0x04, 0x00, 0x00]

theorem code_l100f18_1 : ∀ x ∈ codeRange 0x100f6b bytes_l100f18_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf6b 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100f18 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100f18 (StorePre 0x100f18 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x100f18 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f18 6 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.exec 0x100f20 (StorePre 0x100f20 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f20 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x100f20 (.sib 4 none 0 (.d8 0x8)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x100f25 (fun s => s.RIP = 0x100f25) (leaR64Effect 0x100f25 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x100f2a (movzxR32M8Effect 0x100f2a 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x100f2a (LoadPre 0x100f2a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f2a + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f2a 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x100f2f (movR64R64Effect 0x100f2f 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 5] []) (.reg (.gpr 1))) #v[5]
    (.letOp (n := 59) (.exec 0x100f2f (fun s => s.RIP = 0x100f2f) (movR64R64Effect 0x100f2f 1 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 60) (.out 0x100f32 (xorR32R32Effect 0x100f32 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[5, 5]
    (.letOp (n := 61) (.exec 0x100f32 (fun s => s.RIP = 0x100f32) (xorR32R32Effect 0x100f32 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[5, 5]
    (.letOp (n := 62) (.out 0x100f34 (movR64R64Effect 0x100f34 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[58]
    (.letOp (n := 63) (.exec 0x100f34 (fun s => s.RIP = 0x100f34) (movR64R64Effect 0x100f34 3 1) (Reg.operands [.gpr 1] [])) #v[58]
    (.letOp (n := 64) (.out 0x100f37 (testR64R64Effect 0x100f37 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[58, 58]
    (.letOp (n := 65) (.exec 0x100f37 (fun s => s.RIP = 0x100f37) (testR64R64Effect 0x100f37 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[58, 58]
    (.letOp (n := 66) (.out 0x100f3a (atFlags (condHolds 4) (setccR8Effect 0x100f3a 4 5)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[60, 64]
    (.letOp (n := 67) (.exec 0x100f3a (fun s => s.RIP = 0x100f3a) (atFlags (condHolds 4) (setccR8Effect 0x100f3a 4 5)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[60, 64]
    (.letOp (n := 68) (.exec 0x100f3e (StorePre 0x100f3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f3e + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x100f3e 5 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[4, 64]
    (.letOp (n := 69) (.out 0x100f43 (movzxR32M8Effect 0x100f43 5 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 70) (.exec 0x100f43 (LoadPre 0x100f43 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f43 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f43 5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x100f48 (xorR32R32Effect 0x100f48 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 72) (.exec 0x100f48 (fun s => s.RIP = 0x100f48) (xorR32R32Effect 0x100f48 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 73) (.out 0x100f4b (testR64R64Effect 0x100f4b 13 13) (EffectPart.reads (.flag .ZF) [.gpr 13, .gpr 13] []) (.flag .ZF)) #v[13, 13]
    (.letOp (n := 74) (.exec 0x100f4b (fun s => s.RIP = 0x100f4b) (testR64R64Effect 0x100f4b 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[13, 13]
    (.letOp (n := 75) (.out 0x100f4e (atFlags (condHolds 5) (cmovR32R32Effect 0x100f4e 4 5 10)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[66, 71, 73]
    (.letOp (n := 76) (.exec 0x100f4e (fun s => s.RIP = 0x100f4e) (atFlags (condHolds 5) (cmovR32R32Effect 0x100f4e 4 5 10)) (Reg.operands [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[66, 71, 73]
    (.letOp (n := 77) (.exec 0x100f52 (StorePre 0x100f52 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f52 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100f52 5 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x100f57 (movzxR32M8Effect 0x100f57 5 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x100f57 (LoadPre 0x100f57 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f57 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100f57 5 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x100f5c (testR64R64Effect 0x100f5c 14 14) (EffectPart.reads (.flag .ZF) [.gpr 14, .gpr 14] []) (.flag .ZF)) #v[14, 14]
    (.letOp (n := 81) (.exec 0x100f5c (fun s => s.RIP = 0x100f5c) (testR64R64Effect 0x100f5c 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[14, 14]
    (.letOp (n := 82) (.out 0x100f5f (atFlags (condHolds 5) (cmovR32R32Effect 0x100f5f 4 5 10)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 5))) #v[75, 71, 80]
    (.letOp (n := 83) (.exec 0x100f5f (fun s => s.RIP = 0x100f5f) (atFlags (condHolds 5) (cmovR32R32Effect 0x100f5f 4 5 10)) (Reg.operands [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[75, 71, 80]
    (.letOp (n := 84) (.exec 0x100f63 (StorePre 0x100f63 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100f63 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x100f63 5 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 85) (.out 0x100f68 (movR64R64Effect 0x100f68 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[8]
    (.letOp (n := 86) (.exec 0x100f68 (fun s => s.RIP = 0x100f68) (movR64R64Effect 0x100f68 7 8) (Reg.operands [.gpr 8] [])) #v[8]
    (b_l100f18_1))))))))))))))))))))))))))))))))))

def bytes_l100f18 : List UInt8 :=
  [0x48, 0x89, 0xB4, 0x24, 0xB8, 0x00, 0x00, 0x00, 0xC6, 0x44, 0x24, 0x08, 0x01, 0x48, 0x8D, 0x7C,
    0x24, 0x08, 0x0F, 0xB6, 0x74, 0x24, 0x08, 0x48, 0x89, 0xE9, 0x31, 0xED, 0x48, 0x89, 0xCB, 0x48,
    0x85, 0xC9, 0x40, 0x0F, 0x94, 0xC5, 0x0F, 0x94, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x4C, 0x24, 0x08,
    0x45, 0x31, 0xD2, 0x4D, 0x85, 0xED, 0x41, 0x0F, 0x45, 0xEA, 0x40, 0x88, 0x6C, 0x24, 0x08, 0x0F,
    0xB6, 0x54, 0x24, 0x08, 0x4D, 0x85, 0xF6, 0x41, 0x0F, 0x45, 0xEA, 0x40, 0x88, 0x6C, 0x24, 0x08,
    0x4C, 0x89, 0xC7] ++ bytes_l100f18_1

theorem code_l100f18 : ∀ x ∈ codeRange 0x100f18 bytes_l100f18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf18 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100f18_1

@[cfg_block] def b_l100f75 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x100f75 (cmpR64Imm32Effect 0x100f75 8 0x1fffffff) (EffectPart.reads (.flag .CF) [.gpr 8] []) (.flag .CF)) #v[8]
    (.letOp (n := 54) (.out 0x100f75 (cmpR64Imm32Effect 0x100f75 8 0x1fffffff) (EffectPart.reads (.flag .ZF) [.gpr 8] []) (.flag .ZF)) #v[8]
    (.letOp (n := 55) (.exec 0x100f75 (fun s => s.RIP = 0x100f75) (cmpR64Imm32Effect 0x100f75 8 0x1fffffff) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 56) (.pure (condOp 7)) #v[53, 54]
    (.terminate (.condBr (Fin.last 56) ⟨.l1013a0, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l100f82, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 53), (19, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l100f75 : List UInt8 :=
  [0x49, 0x81, 0xF8, 0xFF, 0xFF, 0xFF, 0x1F, 0x0F, 0x87, 0x1E, 0x04, 0x00, 0x00]

theorem code_l100f75 : ∀ x ∈ codeRange 0x100f75 bytes_l100f75, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf75 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100f82_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x100fce (movzxR32M8Effect 0x100fce 5 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 93) (.exec 0x100fce (LoadPre 0x100fce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x100fce + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x100fce 5 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 94) (.out 0x100fd3 (negR32Effect 0x100fd3 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[92]
    (.letOp (n := 95) (.exec 0x100fd3 (fun s => s.RIP = 0x100fd3) (negR32Effect 0x100fd3 2 6) (Reg.operands [.gpr 6] [])) #v[92]
    (.letOp (n := 96) (.out 0x100fd5 (andR32R32Effect 0x100fd5 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[94, 90]
    (.letOp (n := 97) (.exec 0x100fd5 (fun s => s.RIP = 0x100fd5) (andR32R32Effect 0x100fd5 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[94, 90]
    (.letOp (n := 98) (.out 0x100fd7 (addR32R32Effect 0x100fd7 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[96, 86]
    (.letOp (n := 99) (.exec 0x100fd7 (fun s => s.RIP = 0x100fd7) (addR32R32Effect 0x100fd7 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[96, 86]
    (.letOp (n := 100) (.out 0x100fd9 (addR32R32Effect 0x100fd9 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[98, 76]
    (.letOp (n := 101) (.exec 0x100fd9 (fun s => s.RIP = 0x100fd9) (addR32R32Effect 0x100fd9 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[98, 76]
    (.letOp (n := 102) (.out 0x100fdb (movR32Imm32Effect 0x100fdb 5 1 0x100) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 103) (.exec 0x100fdb (fun s => s.RIP = 0x100fdb) (movR32Imm32Effect 0x100fdb 5 1 0x100) (Reg.operands [] [])) #v[]
    (.letOp (n := 104) (.out 0x100fe0 (subR32R32Effect 0x100fe0 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[102, 100]
    (.letOp (n := 105) (.exec 0x100fe0 (fun s => s.RIP = 0x100fe0) (subR32R32Effect 0x100fe0 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[102, 100]
    (.letOp (n := 106) (.out 0x100fe2 (leaR32Effect 0x100fe2 8 9 (.abs (some 8) 3 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 107) (.exec 0x100fe2 (fun s => s.RIP = 0x100fe2) (leaR32Effect 0x100fe2 8 9 (.abs (some 8) 3 0x0)) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 108) (.out 0x100fea (xorR32R32Effect 0x100fea 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[86, 86]
    (.letOp (n := 109) (.exec 0x100fea (fun s => s.RIP = 0x100fea) (xorR32R32Effect 0x100fea 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[86, 86]
    (.letOp (n := 110) (.out 0x100fec (movR32R32Effect 0x100fec 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[106]
    (.letOp (n := 111) (.exec 0x100fec (fun s => s.RIP = 0x100fec) (movR32R32Effect 0x100fec 3 5 9) (Reg.operands [.gpr 9] [])) #v[106]
    (.letOp (n := 112) (.out 0x100fef (subR32R32Effect 0x100fef 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[110, 104]
    (.letOp (n := 113) (.out 0x100fef (subR32R32Effect 0x100fef 2 5 1) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 1] []) (.flag .CF)) #v[110, 104]
    (.letOp (n := 114) (.exec 0x100fef (fun s => s.RIP = 0x100fef) (subR32R32Effect 0x100fef 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[110, 104]
    (.letOp (n := 115) (.out 0x100ff1 (atFlags (condHolds 2) (cmovR32R32Effect 0x100ff1 3 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[112, 108, 113]
    (.letOp (n := 116) (.exec 0x100ff1 (fun s => s.RIP = 0x100ff1) (atFlags (condHolds 2) (cmovR32R32Effect 0x100ff1 3 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[112, 108, 113]
    (.letOp (n := 117) (.out 0x100ff4 (movR32R32Effect 0x100ff4 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[115]
    (.letOp (n := 118) (.exec 0x100ff4 (fun s => s.RIP = 0x100ff4) (movR32R32Effect 0x100ff4 2 2 5) (Reg.operands [.gpr 5] [])) #v[115]
    (.letOp (n := 119) (.out 0x100ff6 (shrR32Effect 0x100ff6 3 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[117]
    (.letOp (n := 120) (.out 0x100ff6 (shrR32Effect 0x100ff6 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.flag .ZF)) #v[117]
    (.letOp (n := 121) (.exec 0x100ff6 (fun s => s.RIP = 0x100ff6) (shrR32Effect 0x100ff6 3 2 3) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[117]
    (.letOp (n := 122) (.exec 0x100ff9 (StorePre 0x100ff9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x100ff9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100ff9 11 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[11, 4]
    (.letOp (n := 123) (.pure (condOp 4)) #v[120]
    (.terminate (.condBr (Fin.last 123) ⟨.l101023, RegMap.args [(0, 0), (1, 104), (2, 119), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 120), (22, 22), (39, 39), (50, 50), (51, 51)] 124⟩ ⟨.l101003, RegMap.args [(0, 0), (1, 104), (2, 119), (3, 3), (4, 4), (5, 115), (6, 100), (7, 90), (8, 8), (9, 106), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 120), (22, 22), (39, 39), (50, 50), (51, 51)] 124⟩)))))))))))))))))))))))))))))))))

def bytes_l100f82_1 : List UInt8 :=
  [0x0F, 0xB6, 0x74, 0x24, 0x08, 0xF7, 0xDE, 0x21, 0xFE, 0x01, 0xD6, 0x01, 0xCE, 0xB9, 0x00, 0x01,
    0x00, 0x00, 0x29, 0xF1, 0x46, 0x8D, 0x0C, 0xC5, 0x00, 0x00, 0x00, 0x00, 0x31, 0xD2, 0x44, 0x89,
    0xCD, 0x29, 0xCD, 0x0F, 0x42, 0xEA, 0x89, 0xEA, 0xC1, 0xEA, 0x03, 0x4C, 0x89, 0x9C, 0x24, 0xB0,
    0x00, 0x00, 0x00, 0x74, 0x20]

theorem code_l100f82_1 : ∀ x ∈ codeRange 0x100fce bytes_l100f82_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfce 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l100f82 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x100f82 (StorePre 0x100f82 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x100f82 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x100f82 9 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x100f8a (movR32Imm32Effect 0x100f8a 5 7 0x7f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 55) (.exec 0x100f8a (fun s => s.RIP = 0x100f8a) (movR32Imm32Effect 0x100f8a 5 7 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 56) (.out 0x100f8f (movR32Imm32Effect 0x100f8f 6 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 57) (.exec 0x100f8f (fun s => s.RIP = 0x100f8f) (movR32Imm32Effect 0x100f8f 6 9 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x100f95 (bsrR64R64Effect 0x100f95 4 9 3) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3] []) (.reg (.gpr 9))) #v[56, 3]
    (.letOp (n := 59) (.exec 0x100f95 (fun s => s.RIP = 0x100f95) (bsrR64R64Effect 0x100f95 4 9 3) (Reg.operands [.gpr 9, .gpr 3] [])) #v[56, 3]
    (.letOp (n := 60) (.out 0x100f99 (xorR32Imm8Effect 0x100f99 4 9 0x3f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[58]
    (.letOp (n := 61) (.exec 0x100f99 (fun s => s.RIP = 0x100f99) (xorR32Imm8Effect 0x100f99 4 9 0x3f) (Reg.operands [.gpr 9] [])) #v[58]
    (.letOp (n := 62) (.out 0x100f9d (negR32Effect 0x100f9d 2 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 63) (.exec 0x100f9d (fun s => s.RIP = 0x100f9d) (negR32Effect 0x100f9d 2 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.out 0x100f9f (andR32R32Effect 0x100f9f 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[62, 60]
    (.letOp (n := 65) (.exec 0x100f9f (fun s => s.RIP = 0x100f9f) (andR32R32Effect 0x100f9f 3 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[62, 60]
    (.letOp (n := 66) (.out 0x100fa2 (movR32Imm32Effect 0x100fa2 6 9 0x7f) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 67) (.exec 0x100fa2 (fun s => s.RIP = 0x100fa2) (movR32Imm32Effect 0x100fa2 6 9 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x100fa8 (bsrR64R64Effect 0x100fa8 4 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[66, 13]
    (.letOp (n := 69) (.exec 0x100fa8 (fun s => s.RIP = 0x100fa8) (bsrR64R64Effect 0x100fa8 4 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[66, 13]
    (.letOp (n := 70) (.out 0x100fac (xorR32Imm8Effect 0x100fac 4 9 0x3f) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[68]
    (.letOp (n := 71) (.exec 0x100fac (fun s => s.RIP = 0x100fac) (xorR32Imm8Effect 0x100fac 4 9 0x3f) (Reg.operands [.gpr 9] [])) #v[68]
    (.letOp (n := 72) (.out 0x100fb0 (negR32Effect 0x100fb0 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 73) (.exec 0x100fb0 (fun s => s.RIP = 0x100fb0) (negR32Effect 0x100fb0 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 74) (.out 0x100fb2 (andR32R32Effect 0x100fb2 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x100fb2 (fun s => s.RIP = 0x100fb2) (andR32R32Effect 0x100fb2 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x100fb5 (addR32R32Effect 0x100fb5 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[74, 64]
    (.letOp (n := 77) (.exec 0x100fb5 (fun s => s.RIP = 0x100fb5) (addR32R32Effect 0x100fb5 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[74, 64]
    (.letOp (n := 78) (.out 0x100fb7 (movR32Imm32Effect 0x100fb7 5 6 0x7f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 79) (.exec 0x100fb7 (fun s => s.RIP = 0x100fb7) (movR32Imm32Effect 0x100fb7 5 6 0x7f) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x100fbc (bsrR64R64Effect 0x100fbc 4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[78, 14]
    (.letOp (n := 81) (.exec 0x100fbc (fun s => s.RIP = 0x100fbc) (bsrR64R64Effect 0x100fbc 4 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[78, 14]
    (.letOp (n := 82) (.out 0x100fc0 (xorR32Imm8Effect 0x100fc0 3 6 0x3f) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[80]
    (.letOp (n := 83) (.exec 0x100fc0 (fun s => s.RIP = 0x100fc0) (xorR32Imm8Effect 0x100fc0 3 6 0x3f) (Reg.operands [.gpr 6] [])) #v[80]
    (.letOp (n := 84) (.out 0x100fc3 (negR32Effect 0x100fc3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 85) (.exec 0x100fc3 (fun s => s.RIP = 0x100fc3) (negR32Effect 0x100fc3 2 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 86) (.out 0x100fc5 (andR32R32Effect 0x100fc5 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[84, 82]
    (.letOp (n := 87) (.exec 0x100fc5 (fun s => s.RIP = 0x100fc5) (andR32R32Effect 0x100fc5 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[84, 82]
    (.letOp (n := 88) (.out 0x100fc7 (bsrR64R64Effect 0x100fc7 4 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 15] []) (.reg (.gpr 7))) #v[54, 15]
    (.letOp (n := 89) (.exec 0x100fc7 (fun s => s.RIP = 0x100fc7) (bsrR64R64Effect 0x100fc7 4 7 15) (Reg.operands [.gpr 7, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 90) (.out 0x100fcb (xorR32Imm8Effect 0x100fcb 3 7 0x3f) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[88]
    (.letOp (n := 91) (.exec 0x100fcb (fun s => s.RIP = 0x100fcb) (xorR32Imm8Effect 0x100fcb 3 7 0x3f) (Reg.operands [.gpr 7] [])) #v[88]
    (b_l100f82_1)))))))))))))))))))))))))))))))))))))))

def bytes_l100f82 : List UInt8 :=
  [0x4C, 0x89, 0x8C, 0x24, 0xA8, 0x00, 0x00, 0x00, 0xBF, 0x7F, 0x00, 0x00, 0x00, 0x41, 0xB9, 0x7F,
    0x00, 0x00, 0x00, 0x4C, 0x0F, 0xBD, 0xCB, 0x41, 0x83, 0xF1, 0x3F, 0xF7, 0xDE, 0x44, 0x21, 0xCE,
    0x41, 0xB9, 0x7F, 0x00, 0x00, 0x00, 0x4D, 0x0F, 0xBD, 0xCD, 0x41, 0x83, 0xF1, 0x3F, 0xF7, 0xD9,
    0x44, 0x21, 0xC9, 0x01, 0xF1, 0xBE, 0x7F, 0x00, 0x00, 0x00, 0x49, 0x0F, 0xBD, 0xF6, 0x83, 0xF6,
    0x3F, 0xF7, 0xDA, 0x21, 0xF2, 0x49, 0x0F, 0xBD, 0xFF, 0x83, 0xF7, 0x3F] ++ bytes_l100f82_1

theorem code_l100f82 : ∀ x ∈ codeRange 0x100f82 bytes_l100f82, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xf82 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l100f82_1

@[cfg_block] def b_l101003 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101003 (movR32R32Effect 0x101003 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 54) (.exec 0x101003 (fun s => s.RIP = 0x101003) (movR32R32Effect 0x101003 2 2 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.out 0x101005 (movR64R64Effect 0x101005 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[8]
    (.letOp (n := 56) (.exec 0x101005 (fun s => s.RIP = 0x101005) (movR64R64Effect 0x101005 6 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x101008 (subR64R64Effect 0x101008 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[55, 53]
    (.letOp (n := 58) (.out 0x101008 (subR64R64Effect 0x101008 6 2) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 2] []) (.flag .CF)) #v[55, 53]
    (.letOp (n := 59) (.exec 0x101008 (fun s => s.RIP = 0x101008) (subR64R64Effect 0x101008 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[55, 53]
    (.letOp (n := 60) (.pure (condOp 2)) #v[58]
    (.terminate (.condBr (Fin.last 60) ⟨.l1013b8, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ ⟨.l101011, RegMap.args [(0, 0), (1, 1), (2, 53), (3, 3), (4, 4), (5, 5), (6, 57), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩)))))))))

def bytes_l101003 : List UInt8 :=
  [0x89, 0xD2, 0x4C, 0x89, 0xC6, 0x48, 0x29, 0xD6, 0x0F, 0x82, 0xA7, 0x03, 0x00, 0x00]

theorem code_l101003 : ∀ x ∈ codeRange 0x101003 bytes_l101003, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1003 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101011 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101011 (andR32Imm8Effect 0x101011 3 5 0xf8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 54) (.exec 0x101011 (fun s => s.RIP = 0x101011) (andR32Imm8Effect 0x101011 3 5 0xf8) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 55) (.out 0x101014 (subR32R32Effect 0x101014 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[9, 53]
    (.letOp (n := 56) (.exec 0x101014 (fun s => s.RIP = 0x101014) (subR32R32Effect 0x101014 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[9, 53]
    (.letOp (n := 57) (.out 0x101017 (xorR32R32Effect 0x101017 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 58) (.exec 0x101017 (fun s => s.RIP = 0x101017) (xorR32R32Effect 0x101017 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 59) (.out 0x101019 (movR32R32Effect 0x101019 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 60) (.exec 0x101019 (fun s => s.RIP = 0x101019) (movR32R32Effect 0x101019 3 5 9) (Reg.operands [.gpr 9] [])) #v[55]
    (.letOp (n := 61) (.out 0x10101c (subR32R32Effect 0x10101c 2 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 1] []) (.reg (.gpr 5))) #v[59, 1]
    (.letOp (n := 62) (.out 0x10101c (subR32R32Effect 0x10101c 2 5 1) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 1] []) (.flag .CF)) #v[59, 1]
    (.letOp (n := 63) (.exec 0x10101c (fun s => s.RIP = 0x10101c) (subR32R32Effect 0x10101c 2 5 1) (Reg.operands [.gpr 5, .gpr 1] [])) #v[59, 1]
    (.letOp (n := 64) (.out 0x10101e (atFlags (condHolds 2) (cmovR32R32Effect 0x10101e 3 5 2)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[61, 57, 62]
    (.letOp (n := 65) (.exec 0x10101e (fun s => s.RIP = 0x10101e) (atFlags (condHolds 2) (cmovR32R32Effect 0x10101e 3 5 2)) (Reg.operands [.gpr 5, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[61, 57, 62]
    (.terminate (.br ⟨.l101026, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 4), (5, 64), (6, 6), (9, 55), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 62), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l101011 : List UInt8 :=
  [0x83, 0xE5, 0xF8, 0x41, 0x29, 0xE9, 0x31, 0xD2, 0x44, 0x89, 0xCD, 0x29, 0xCD, 0x0F, 0x42, 0xEA,
    0xEB, 0x03]

theorem code_l101011 : ∀ x ∈ codeRange 0x101011 bytes_l101011, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1011 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101023 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101023 (movR64R64Effect 0x101023 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[8]
    (.letOp (n := 54) (.exec 0x101023 (fun s => s.RIP = 0x101023) (movR64R64Effect 0x101023 6 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.terminate (.br ⟨.l101026, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (6, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101023 : List UInt8 :=
  [0x4C, 0x89, 0xC6]

theorem code_l101023 : ∀ x ∈ codeRange 0x101023 bytes_l101023, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1023 3 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101026 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101026 (StorePre 0x101026 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x101026 + BitVec.ofNat 64 8)) 4) (movM32R32Effect 0x101026 9 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.exec 0x10102e (StorePre 0x10102e 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10102e + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10102e (.sib 4 none 0 (.d32 0x80)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10103a (StorePre 0x10103a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10103a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10103a (.sib 4 none 0 (.d8 0x78)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x101043 (StorePre 0x101043 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101043 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101043 (.sib 4 none 0 (.d8 0x70)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10104c (StorePre 0x10104c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10104c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10104c (.sib 4 none 0 (.d8 0x68)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x101055 (leaR64Effect 0x101055 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x101055 (fun s => s.RIP = 0x101055) (leaR64Effect 0x101055 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.out 0x10105a (movR32Imm32Effect 0x10105a 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 61) (.exec 0x10105a (fun s => s.RIP = 0x10105a) (movR32Imm32Effect 0x10105a 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x10105f (movR64R64Effect 0x10105f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[0]
    (.letOp (n := 63) (.exec 0x10105f (fun s => s.RIP = 0x10105f) (movR64R64Effect 0x10105f 7 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 64) (.out 0x101062 (movR32R32Effect 0x101062 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[9]
    (.letOp (n := 65) (.exec 0x101062 (fun s => s.RIP = 0x101062) (movR32R32Effect 0x101062 3 8 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 66) (.out 0x101065 (callEffect (fun _ => 0x127d70) 0x10106a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x101065 (PushPre 0x101065 5) (callEffect (fun _ => 0x127d70) 0x10106a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x10106a⟩) #v[]
    (.terminate (.call ⟨.l127d70, RegMap.args [(0, 0), (1, 60), (2, 58), (3, 3), (4, 66), (5, 5), (6, 6), (7, 62), (8, 64), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l10106a, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l101026 : List UInt8 :=
  [0x44, 0x89, 0x8C, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x70, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48,
    0x8D, 0x54, 0x24, 0x68, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7, 0x45, 0x89, 0xC8, 0xE8,
    0x06, 0x6D, 0x02, 0x00]

theorem code_l101026 : ∀ x ∈ codeRange 0x101026 bytes_l101026, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1026 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10106a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10106a (cmpAlImm8Effect 0x10106a 0xff) (EffectPart.reads (.flag .ZF) [.gpr 0] []) (.flag .ZF)) #v[0]
    (.letOp (n := 54) (.exec 0x10106a (fun s => s.RIP = 0x10106a) (cmpAlImm8Effect 0x10106a 0xff) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1013c9, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101072, RegMap.args [(0, 0), (3, 3), (4, 4), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l10106a : List UInt8 :=
  [0x3C, 0xFF, 0x0F, 0x85, 0x57, 0x03, 0x00, 0x00]

theorem code_l10106a : ∀ x ∈ codeRange 0x10106a bytes_l10106a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x106a 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101072 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101072 (movR64M64Effect 0x101072 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x101072 (LoadPre 0x101072 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101072 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101072 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10107a (StorePre 0x10107a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10107a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10107a 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10107f (movR64M64Effect 0x10107f 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x10107f (LoadPre 0x10107f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10107f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10107f 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101084 (StorePre 0x101084 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x101084 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101084 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x101089 (movR64M64Effect 0x101089 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x101089 (LoadPre 0x101089 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101089 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101089 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10108e (movR64M64Effect 0x10108e 1 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x10108e (LoadPre 0x10108e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10108e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10108e 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x101093 (StorePre 0x101093 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101093 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101093 1 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x101098 (StorePre 0x101098 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101098 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101098 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x10109d (leaR64Effect 0x10109d 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x10109d (fun s => s.RIP = 0x10109d) (leaR64Effect 0x10109d 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x1010a2 (leaR64Effect 0x1010a2 6 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x1010a2 (fun s => s.RIP = 0x1010a2) (leaR64Effect 0x1010a2 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x1010a7 (movR32R32Effect 0x1010a7 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5] []) (.reg (.gpr 2))) #v[5]
    (.letOp (n := 70) (.exec 0x1010a7 (fun s => s.RIP = 0x1010a7) (movR32R32Effect 0x1010a7 2 2 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 71) (.out 0x1010a9 (callEffect (fun _ => 0x1065b0) 0x1010ae) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x1010a9 (PushPre 0x1010a9 5) (callEffect (fun _ => 0x1065b0) 0x1010ae) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x1010ae⟩) #v[]
    (.terminate (.call ⟨.l1065b0, RegMap.args [(0, 59), (1, 61), (2, 69), (3, 3), (4, 71), (5, 5), (6, 67), (7, 65), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l1010ae, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l101072 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x44,
    0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x4C, 0x24,
    0x70, 0x48, 0x89, 0x4C, 0x24, 0x50, 0x48, 0x89, 0x44, 0x24, 0x48, 0x48, 0x8D, 0x7C, 0x24, 0x08,
    0x48, 0x8D, 0x74, 0x24, 0x48, 0x89, 0xEA, 0xE8, 0x02, 0x55, 0x00, 0x00]

theorem code_l101072 : ∀ x ∈ codeRange 0x101072 bytes_l101072, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1072 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1010ae_5 : Block Op Label signature Reg.count 233 :=
  .letOp (n := 233) (.out 0x101239 (orR64R64Effect 0x101239 1 5) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5] []) (.reg (.gpr 1))) #v[231, 161]
    (.letOp (n := 234) (.exec 0x101239 (fun s => s.RIP = 0x101239) (orR64R64Effect 0x101239 1 5) (Reg.operands [.gpr 1, .gpr 5] [])) #v[231, 161]
    (.letOp (n := 235) (.out 0x10123c (shrR64Effect 0x10123c 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[233]
    (.letOp (n := 236) (.exec 0x10123c (fun s => s.RIP = 0x10123c) (shrR64Effect 0x10123c 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[233]
    (.letOp (n := 237) (.exec 0x101240 (StorePre 0x101240 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101240 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101240 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[235, 4]
    (.letOp (n := 238) (.out 0x101245 (movzxR32M8Effect 0x101245 5 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 239) (.exec 0x101245 (LoadPre 0x101245 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101245 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x101245 5 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 240) (.out 0x10124a (andAlImm8Effect 0x10124a 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[238]
    (.letOp (n := 241) (.exec 0x10124a (fun s => s.RIP = 0x10124a) (andAlImm8Effect 0x10124a 0x1) (Reg.operands [.gpr 0] [])) #v[238]
    (.letOp (n := 242) (.out 0x10124c (movzxR32R8Effect 0x10124c 4 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[240]
    (.letOp (n := 243) (.exec 0x10124c (fun s => s.RIP = 0x10124c) (movzxR32R8Effect 0x10124c 4 8 0) (Reg.operands [.gpr 0] [])) #v[240]
    (.letOp (n := 244) (.out 0x101250 (leaR64Effect 0x101250 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 245) (.exec 0x101250 (fun s => s.RIP = 0x101250) (leaR64Effect 0x101250 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 246) (.out 0x101255 (leaR64Effect 0x101255 2 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 247) (.exec 0x101255 (fun s => s.RIP = 0x101255) (leaR64Effect 0x101255 2 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 248) (.out 0x10125a (movR32Imm32Effect 0x10125a 5 6 0x4) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 249) (.exec 0x10125a (fun s => s.RIP = 0x10125a) (movR32Imm32Effect 0x10125a 5 6 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 250) (.out 0x10125f (movR32Imm32Effect 0x10125f 5 1 0x4) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 251) (.exec 0x10125f (fun s => s.RIP = 0x10125f) (movR32Imm32Effect 0x10125f 5 1 0x4) (Reg.operands [] [])) #v[]
    (.letOp (n := 252) (.out 0x101264 (movR64R64Effect 0x101264 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 253) (.exec 0x101264 (fun s => s.RIP = 0x101264) (movR64R64Effect 0x101264 7 5) (Reg.operands [.gpr 5] [])) #v[244]
    (.letOp (n := 254) (.out 0x101267 (callEffect (fun _ => 0x127ea0) 0x10126c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 255) (.exec 0x101267 (PushPre 0x101267 5) (callEffect (fun _ => 0x127ea0) 0x10126c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 256) (.const ⟨64, 0x10126c⟩) #v[]
    (.terminate (.call ⟨.l127ea0, RegMap.args [(0, 240), (1, 250), (2, 246), (3, 185), (4, 254), (5, 244), (6, 248), (7, 252), (8, 242), (9, 140), (10, 101), (11, 128), (12, 132), (13, 155), (14, 173), (15, 163), (22, 22), (39, 39), (50, 50), (51, 51)] 257⟩ { target := .l10126c, kept := #v[], arity := rfl, guard := some (Fin.last 256) })))))))))))))))))))))))))

def bytes_l1010ae_5 : List UInt8 :=
  [0x48, 0x09, 0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x0F, 0xB6, 0x44, 0x24,
    0x48, 0x24, 0x01, 0x44, 0x0F, 0xB6, 0xC0, 0x48, 0x8D, 0x6C, 0x24, 0x08, 0x48, 0x8D, 0x54, 0x24,
    0x68, 0xBE, 0x04, 0x00, 0x00, 0x00, 0xB9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0xE8, 0x34,
    0x6C, 0x02, 0x00]

theorem code_l1010ae_5 : ∀ x ∈ codeRange 0x101239 bytes_l1010ae_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1239 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1010ae_4 : Block Op Label signature Reg.count 195 :=
  .letOp (n := 195) (.out 0x1011f0 (subR64M64Effect 0x1011f0 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[193, 4]
    (.letOp (n := 196) (.exec 0x1011f0 (LoadPre 0x1011f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1011f0 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x1011f0 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[193, 4]
    (.letOp (n := 197) (.out 0x1011f5 (sarR64Effect 0x1011f5 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[195]
    (.letOp (n := 198) (.exec 0x1011f5 (fun s => s.RIP = 0x1011f5) (sarR64Effect 0x1011f5 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 199) (.out 0x1011f9 (addR64R64Effect 0x1011f9 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[197, 97]
    (.letOp (n := 200) (.exec 0x1011f9 (fun s => s.RIP = 0x1011f9) (addR64R64Effect 0x1011f9 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[197, 97]
    (.letOp (n := 201) (.out 0x1011fc (andR64R64Effect 0x1011fc 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[199, 109]
    (.letOp (n := 202) (.exec 0x1011fc (fun s => s.RIP = 0x1011fc) (andR64R64Effect 0x1011fc 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[199, 109]
    (.letOp (n := 203) (.out 0x1011ff (orR64R64Effect 0x1011ff 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[201, 107]
    (.letOp (n := 204) (.exec 0x1011ff (fun s => s.RIP = 0x1011ff) (orR64R64Effect 0x1011ff 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[201, 107]
    (.letOp (n := 205) (.out 0x101202 (shrR64Effect 0x101202 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[203]
    (.letOp (n := 206) (.exec 0x101202 (fun s => s.RIP = 0x101202) (shrR64Effect 0x101202 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[203]
    (.letOp (n := 207) (.exec 0x101206 (StorePre 0x101206 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101206 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101206 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[205, 4]
    (.letOp (n := 208) (.out 0x10120b (xorR32R32Effect 0x10120b 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[205, 205]
    (.letOp (n := 209) (.exec 0x10120b (fun s => s.RIP = 0x10120b) (xorR32R32Effect 0x10120b 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[205, 205]
    (.letOp (n := 210) (.out 0x10120d (subR64M64Effect 0x10120d 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[208, 4]
    (.letOp (n := 211) (.exec 0x10120d (LoadPre 0x10120d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10120d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10120d 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[208, 4]
    (.letOp (n := 212) (.out 0x101212 (sarR64Effect 0x101212 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[210]
    (.letOp (n := 213) (.exec 0x101212 (fun s => s.RIP = 0x101212) (sarR64Effect 0x101212 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[210]
    (.letOp (n := 214) (.out 0x101216 (addR64R64Effect 0x101216 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[212, 128]
    (.letOp (n := 215) (.exec 0x101216 (fun s => s.RIP = 0x101216) (addR64R64Effect 0x101216 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[212, 128]
    (.letOp (n := 216) (.out 0x101219 (andR64R64Effect 0x101219 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[214, 140]
    (.letOp (n := 217) (.exec 0x101219 (fun s => s.RIP = 0x101219) (andR64R64Effect 0x101219 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[214, 140]
    (.letOp (n := 218) (.out 0x10121c (orR64R64Effect 0x10121c 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[216, 138]
    (.letOp (n := 219) (.exec 0x10121c (fun s => s.RIP = 0x10121c) (orR64R64Effect 0x10121c 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[216, 138]
    (.letOp (n := 220) (.out 0x10121f (shrR64Effect 0x10121f 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[218]
    (.letOp (n := 221) (.exec 0x10121f (fun s => s.RIP = 0x10121f) (shrR64Effect 0x10121f 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.exec 0x101223 (StorePre 0x101223 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x101223 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101223 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[220, 4]
    (.letOp (n := 223) (.out 0x101228 (xorR32R32Effect 0x101228 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[220, 220]
    (.letOp (n := 224) (.exec 0x101228 (fun s => s.RIP = 0x101228) (xorR32R32Effect 0x101228 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[220, 220]
    (.letOp (n := 225) (.out 0x10122a (subR64M64Effect 0x10122a 1 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[223, 4]
    (.letOp (n := 226) (.exec 0x10122a (LoadPre 0x10122a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10122a + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10122a 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[223, 4]
    (.letOp (n := 227) (.out 0x10122f (sarR64Effect 0x10122f 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[225]
    (.letOp (n := 228) (.exec 0x10122f (fun s => s.RIP = 0x10122f) (sarR64Effect 0x10122f 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[225]
    (.letOp (n := 229) (.out 0x101233 (addR64R64Effect 0x101233 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[227, 155]
    (.letOp (n := 230) (.exec 0x101233 (fun s => s.RIP = 0x101233) (addR64R64Effect 0x101233 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[227, 155]
    (.letOp (n := 231) (.out 0x101236 (andR64R64Effect 0x101236 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[229, 163]
    (.letOp (n := 232) (.exec 0x101236 (fun s => s.RIP = 0x101236) (andR64R64Effect 0x101236 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[229, 163]
    (b_l1010ae_5))))))))))))))))))))))))))))))))))))))

def bytes_l1010ae_4 : List UInt8 :=
  [0x48, 0x2B, 0x4C, 0x24, 0x48, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xC1, 0x48, 0x21, 0xD1, 0x48,
    0x09, 0xF9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x31, 0xC9, 0x48, 0x2B, 0x4C,
    0x24, 0x48, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xD9, 0x4C, 0x21, 0xC9, 0x48, 0x09, 0xF1, 0x48,
    0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x31, 0xC9, 0x48, 0x2B, 0x4C, 0x24, 0x48, 0x48,
    0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xE9, 0x4C, 0x21, 0xF9] ++ bytes_l1010ae_5

theorem code_l1010ae_4 : ∀ x ∈ codeRange 0x1011f0 bytes_l1010ae_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x11f0 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1010ae_5

@[cfg_block] def b_l1010ae_3 : Block Op Label signature Reg.count 163 :=
  .letOp (n := 163) (.out 0x101198 (orR64R64Effect 0x101198 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[157, 3]
    (.letOp (n := 164) (.exec 0x101198 (fun s => s.RIP = 0x101198) (orR64R64Effect 0x101198 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[157, 3]
    (.letOp (n := 165) (.out 0x10119b (xorR32R32Effect 0x10119b 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[87, 87]
    (.letOp (n := 166) (.exec 0x10119b (fun s => s.RIP = 0x10119b) (xorR32R32Effect 0x10119b 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[87, 87]
    (.letOp (n := 167) (.out 0x10119d (subR64M64Effect 0x10119d 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[165, 4]
    (.letOp (n := 168) (.exec 0x10119d (LoadPre 0x10119d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10119d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10119d 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[165, 4]
    (.letOp (n := 169) (.out 0x1011a2 (sarR64Effect 0x1011a2 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 170) (.exec 0x1011a2 (fun s => s.RIP = 0x1011a2) (sarR64Effect 0x1011a2 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[167]
    (.letOp (n := 171) (.out 0x1011a6 (addR64R64Effect 0x1011a6 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[169, 155]
    (.letOp (n := 172) (.exec 0x1011a6 (fun s => s.RIP = 0x1011a6) (addR64R64Effect 0x1011a6 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[169, 155]
    (.letOp (n := 173) (.out 0x1011a9 (movR64M64Effect 0x1011a9 14 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 174) (.exec 0x1011a9 (LoadPre 0x1011a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x1011a9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1011a9 14 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 175) (.out 0x1011b1 (movR64R64Effect 0x1011b1 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[171]
    (.letOp (n := 176) (.exec 0x1011b1 (fun s => s.RIP = 0x1011b1) (movR64R64Effect 0x1011b1 3 0) (Reg.operands [.gpr 0] [])) #v[171]
    (.letOp (n := 177) (.out 0x1011b4 (andR64R64Effect 0x1011b4 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[175, 163]
    (.letOp (n := 178) (.exec 0x1011b4 (fun s => s.RIP = 0x1011b4) (andR64R64Effect 0x1011b4 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[175, 163]
    (.letOp (n := 179) (.out 0x1011b7 (orR64R64Effect 0x1011b7 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[177, 161]
    (.letOp (n := 180) (.exec 0x1011b7 (fun s => s.RIP = 0x1011b7) (orR64R64Effect 0x1011b7 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[177, 161]
    (.letOp (n := 181) (.out 0x1011ba (shrR64Effect 0x1011ba 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[179]
    (.letOp (n := 182) (.exec 0x1011ba (fun s => s.RIP = 0x1011ba) (shrR64Effect 0x1011ba 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.exec 0x1011be (StorePre 0x1011be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1011be + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011be 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[181, 4]
    (.letOp (n := 184) (.exec 0x1011c3 (fun s => s.RIP = 0x1011c3) (leaR64Effect 0x1011c3 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 185) (.out 0x1011c8 (movR64M64Effect 0x1011c8 3 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 186) (.exec 0x1011c8 (LoadPre 0x1011c8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1011c8 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1011c8 3 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 187) (.exec 0x1011d0 (StorePre 0x1011d0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1011d0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011d0 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[185, 4]
    (.letOp (n := 188) (.exec 0x1011d5 (StorePre 0x1011d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1011d5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011d5 10 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[101, 4]
    (.letOp (n := 189) (.exec 0x1011da (StorePre 0x1011da 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1011da + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011da 12 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[132, 4]
    (.letOp (n := 190) (.exec 0x1011df (StorePre 0x1011df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1011df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011df 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[171, 4]
    (.letOp (n := 191) (.exec 0x1011e4 (StorePre 0x1011e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1011e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1011e4 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 192) (.exec 0x1011e9 (fun s => s.RIP = 0x1011e9) (leaR64Effect 0x1011e9 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 193) (.out 0x1011ee (xorR32R32Effect 0x1011ee 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[84, 84]
    (.letOp (n := 194) (.exec 0x1011ee (fun s => s.RIP = 0x1011ee) (xorR32R32Effect 0x1011ee 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[84, 84]
    (b_l1010ae_4))))))))))))))))))))))))))))))))

def bytes_l1010ae_3 : List UInt8 :=
  [0x49, 0x09, 0xDF, 0x31, 0xC0, 0x48, 0x2B, 0x44, 0x24, 0x08, 0x48, 0xC1, 0xF8, 0x3F, 0x4C, 0x01,
    0xE8, 0x4C, 0x8B, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC3, 0x4C, 0x21, 0xFB, 0x48,
    0x09, 0xEB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x48, 0x8D, 0x5C, 0x24, 0x08,
    0x48, 0x8B, 0x9C, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x4C, 0x89, 0x54,
    0x24, 0x10, 0x4C, 0x89, 0x64, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0x4C, 0x24,
    0x48, 0x48, 0x8D, 0x44, 0x24, 0x48, 0x31, 0xC9] ++ bytes_l1010ae_4

theorem code_l1010ae_3 : ∀ x ∈ codeRange 0x101198 bytes_l1010ae_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1198 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1010ae_4

@[cfg_block] def b_l1010ae_2 : Block Op Label signature Reg.count 124 :=
  .letOp (n := 124) (.out 0x101151 (movR64M64Effect 0x101151 9 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 125) (.exec 0x101151 (LoadPre 0x101151 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x101151 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101151 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 126) (.out 0x101156 (movR64R64Effect 0x101156 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[124]
    (.letOp (n := 127) (.exec 0x101156 (fun s => s.RIP = 0x101156) (movR64R64Effect 0x101156 11 9) (Reg.operands [.gpr 9] [])) #v[124]
    (.letOp (n := 128) (.out 0x101159 (subR64R64Effect 0x101159 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[126, 13]
    (.letOp (n := 129) (.exec 0x101159 (fun s => s.RIP = 0x101159) (subR64R64Effect 0x101159 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[126, 13]
    (.letOp (n := 130) (.out 0x10115c (sarR64Effect 0x10115c 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[122]
    (.letOp (n := 131) (.exec 0x10115c (fun s => s.RIP = 0x10115c) (sarR64Effect 0x10115c 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 132) (.out 0x101160 (addR64R64Effect 0x101160 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[130, 128]
    (.letOp (n := 133) (.exec 0x101160 (fun s => s.RIP = 0x101160) (addR64R64Effect 0x101160 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[130, 128]
    (.letOp (n := 134) (.out 0x101163 (notR64Effect 0x101163 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[124]
    (.letOp (n := 135) (.exec 0x101163 (fun s => s.RIP = 0x101163) (notR64Effect 0x101163 9) (Reg.operands [.gpr 9] [])) #v[124]
    (.letOp (n := 136) (.out 0x101166 (movR64R64Effect 0x101166 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 13] []) (.reg (.gpr 6))) #v[13]
    (.letOp (n := 137) (.exec 0x101166 (fun s => s.RIP = 0x101166) (movR64R64Effect 0x101166 6 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 138) (.out 0x101169 (andR64R64Effect 0x101169 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[136, 134]
    (.letOp (n := 139) (.exec 0x101169 (fun s => s.RIP = 0x101169) (andR64R64Effect 0x101169 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[136, 134]
    (.letOp (n := 140) (.out 0x10116c (orR64R64Effect 0x10116c 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[134, 13]
    (.letOp (n := 141) (.exec 0x10116c (fun s => s.RIP = 0x10116c) (orR64R64Effect 0x10116c 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[134, 13]
    (.letOp (n := 142) (.out 0x10116f (movR64R64Effect 0x10116f 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 12] []) (.reg (.gpr 15))) #v[132]
    (.letOp (n := 143) (.exec 0x10116f (fun s => s.RIP = 0x10116f) (movR64R64Effect 0x10116f 15 12) (Reg.operands [.gpr 12] [])) #v[132]
    (.letOp (n := 144) (.out 0x101172 (andR64R64Effect 0x101172 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[142, 140]
    (.letOp (n := 145) (.exec 0x101172 (fun s => s.RIP = 0x101172) (andR64R64Effect 0x101172 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[142, 140]
    (.letOp (n := 146) (.out 0x101175 (orR64R64Effect 0x101175 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[144, 138]
    (.letOp (n := 147) (.exec 0x101175 (fun s => s.RIP = 0x101175) (orR64R64Effect 0x101175 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[144, 138]
    (.letOp (n := 148) (.out 0x101178 (shrR64Effect 0x101178 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[146]
    (.letOp (n := 149) (.exec 0x101178 (fun s => s.RIP = 0x101178) (shrR64Effect 0x101178 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[146]
    (.letOp (n := 150) (.exec 0x10117c (StorePre 0x10117c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10117c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10117c 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[148, 4]
    (.letOp (n := 151) (.out 0x101181 (movR64M64Effect 0x101181 15 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 152) (.exec 0x101181 (LoadPre 0x101181 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x101181 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101181 15 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 153) (.out 0x101189 (movR64R64Effect 0x101189 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[151]
    (.letOp (n := 154) (.exec 0x101189 (fun s => s.RIP = 0x101189) (movR64R64Effect 0x101189 13 15) (Reg.operands [.gpr 15] [])) #v[151]
    (.letOp (n := 155) (.out 0x10118c (subR64R64Effect 0x10118c 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[153, 3]
    (.letOp (n := 156) (.exec 0x10118c (fun s => s.RIP = 0x10118c) (subR64R64Effect 0x10118c 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[153, 3]
    (.letOp (n := 157) (.out 0x10118f (notR64Effect 0x10118f 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[151]
    (.letOp (n := 158) (.exec 0x10118f (fun s => s.RIP = 0x10118f) (notR64Effect 0x10118f 15) (Reg.operands [.gpr 15] [])) #v[151]
    (.letOp (n := 159) (.out 0x101192 (movR64R64Effect 0x101192 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[3]
    (.letOp (n := 160) (.exec 0x101192 (fun s => s.RIP = 0x101192) (movR64R64Effect 0x101192 5 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 161) (.out 0x101195 (andR64R64Effect 0x101195 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x101195 (fun s => s.RIP = 0x101195) (andR64R64Effect 0x101195 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[159, 157]
    (b_l1010ae_3)))))))))))))))))))))))))))))))))))))))

def bytes_l1010ae_2 : List UInt8 :=
  [0x4C, 0x8B, 0x4C, 0x24, 0x78, 0x4D, 0x89, 0xCB, 0x4D, 0x29, 0xEB, 0x49, 0xC1, 0xFC, 0x3F, 0x4D,
    0x01, 0xDC, 0x49, 0xF7, 0xD1, 0x4C, 0x89, 0xEE, 0x4C, 0x21, 0xCE, 0x4D, 0x09, 0xE9, 0x4D, 0x89,
    0xE7, 0x4D, 0x21, 0xCF, 0x49, 0x09, 0xF7, 0x49, 0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24, 0x08,
    0x4C, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4D, 0x89, 0xFD, 0x49, 0x29, 0xDD, 0x49, 0xF7,
    0xD7, 0x48, 0x89, 0xDD, 0x4C, 0x21, 0xFD] ++ bytes_l1010ae_3

theorem code_l1010ae_2 : ∀ x ∈ codeRange 0x101151 bytes_l1010ae_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1151 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1010ae_3

@[cfg_block] def b_l1010ae_1 : Block Op Label signature Reg.count 86 :=
  .letOp (n := 86) (.exec 0x101107 (StorePre 0x101107 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101107 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101107 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 87) (.out 0x10110c (leaR64Effect 0x10110c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 88) (.exec 0x10110c (fun s => s.RIP = 0x10110c) (leaR64Effect 0x10110c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.out 0x101111 (xorR32R32Effect 0x101111 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 90) (.exec 0x101111 (fun s => s.RIP = 0x101111) (xorR32R32Effect 0x101111 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 91) (.out 0x101114 (subR64M64Effect 0x101114 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[89, 4]
    (.letOp (n := 92) (.exec 0x101114 (LoadPre 0x101114 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101114 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x101114 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[89, 4]
    (.letOp (n := 93) (.out 0x101119 (movR64M64Effect 0x101119 2 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 94) (.exec 0x101119 (LoadPre 0x101119 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101119 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101119 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x10111e (movR64R64Effect 0x10111e 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[93]
    (.letOp (n := 96) (.exec 0x10111e (fun s => s.RIP = 0x10111e) (movR64R64Effect 0x10111e 8 2) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 97) (.out 0x101121 (subR64R64Effect 0x101121 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[95, 14]
    (.letOp (n := 98) (.exec 0x101121 (fun s => s.RIP = 0x101121) (subR64R64Effect 0x101121 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[95, 14]
    (.letOp (n := 99) (.out 0x101124 (sarR64Effect 0x101124 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[91]
    (.letOp (n := 100) (.exec 0x101124 (fun s => s.RIP = 0x101124) (sarR64Effect 0x101124 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 101) (.out 0x101128 (addR64R64Effect 0x101128 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x101128 (fun s => s.RIP = 0x101128) (addR64R64Effect 0x101128 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x10112b (notR64Effect 0x10112b 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 104) (.exec 0x10112b (fun s => s.RIP = 0x10112b) (notR64Effect 0x10112b 2) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 105) (.out 0x10112e (movR64R64Effect 0x10112e 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 106) (.exec 0x10112e (fun s => s.RIP = 0x10112e) (movR64R64Effect 0x10112e 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 107) (.out 0x101131 (andR64R64Effect 0x101131 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x101131 (fun s => s.RIP = 0x101131) (andR64R64Effect 0x101131 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x101134 (orR64R64Effect 0x101134 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[103, 14]
    (.letOp (n := 110) (.exec 0x101134 (fun s => s.RIP = 0x101134) (orR64R64Effect 0x101134 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[103, 14]
    (.letOp (n := 111) (.out 0x101137 (movR64R64Effect 0x101137 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 10] []) (.reg (.gpr 9))) #v[101]
    (.letOp (n := 112) (.exec 0x101137 (fun s => s.RIP = 0x101137) (movR64R64Effect 0x101137 9 10) (Reg.operands [.gpr 10] [])) #v[101]
    (.letOp (n := 113) (.out 0x10113a (andR64R64Effect 0x10113a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x10113a (fun s => s.RIP = 0x10113a) (andR64R64Effect 0x10113a 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[111, 109]
    (.letOp (n := 115) (.out 0x10113d (orR64R64Effect 0x10113d 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[113, 107]
    (.letOp (n := 116) (.exec 0x10113d (fun s => s.RIP = 0x10113d) (orR64R64Effect 0x10113d 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[113, 107]
    (.letOp (n := 117) (.out 0x101140 (shrR64Effect 0x101140 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[115]
    (.letOp (n := 118) (.exec 0x101140 (fun s => s.RIP = 0x101140) (shrR64Effect 0x101140 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.exec 0x101144 (StorePre 0x101144 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101144 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101144 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[117, 4]
    (.letOp (n := 120) (.out 0x101149 (xorR32R32Effect 0x101149 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[12, 12]
    (.letOp (n := 121) (.exec 0x101149 (fun s => s.RIP = 0x101149) (xorR32R32Effect 0x101149 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[12, 12]
    (.letOp (n := 122) (.out 0x10114c (subR64M64Effect 0x10114c 12 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[120, 4]
    (.letOp (n := 123) (.exec 0x10114c (LoadPre 0x10114c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10114c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x10114c 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[120, 4]
    (b_l1010ae_2))))))))))))))))))))))))))))))))))))))

def bytes_l1010ae_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x54,
    0x24, 0x08, 0x48, 0x8B, 0x54, 0x24, 0x70, 0x49, 0x89, 0xD0, 0x4D, 0x29, 0xF0, 0x49, 0xC1, 0xFA,
    0x3F, 0x4D, 0x01, 0xC2, 0x48, 0xF7, 0xD2, 0x4C, 0x89, 0xF7, 0x48, 0x21, 0xD7, 0x4C, 0x09, 0xF2,
    0x4D, 0x89, 0xD1, 0x49, 0x21, 0xD1, 0x49, 0x09, 0xF9, 0x49, 0xC1, 0xE9, 0x3F, 0x4C, 0x89, 0x4C,
    0x24, 0x08, 0x45, 0x31, 0xE4, 0x4C, 0x2B, 0x64, 0x24, 0x08] ++ bytes_l1010ae_2

theorem code_l1010ae_1 : ∀ x ∈ codeRange 0x101107 bytes_l1010ae_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1107 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1010ae_2

@[cfg_block] def b_l1010ae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1010ae (movR64M64Effect 0x1010ae 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1010ae (LoadPre 0x1010ae (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1010ae + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010ae 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1010b3 (StorePre 0x1010b3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1010b3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010b3 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1010b8 (movR64M64Effect 0x1010b8 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x1010b8 (LoadPre 0x1010b8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1010b8 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010b8 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1010bd (movR64M64Effect 0x1010bd 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 59) (.exec 0x1010bd (LoadPre 0x1010bd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1010bd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010bd 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1010c2 (StorePre 0x1010c2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x1010c2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010c2 1 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 61) (.out 0x1010c7 (movR64M64Effect 0x1010c7 6 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 62) (.exec 0x1010c7 (LoadPre 0x1010c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1010c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1010c7 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x1010cc (StorePre 0x1010cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1010cc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010cc 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 64) (.exec 0x1010d1 (StorePre 0x1010d1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1010d1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d1 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 65) (.exec 0x1010d6 (StorePre 0x1010d6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1010d6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1010d6 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 66) (.exec 0x1010db (StorePre 0x1010db 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1010db + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1010db 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 67) (.out 0x1010e3 (movR64R64Effect 0x1010e3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 68) (.exec 0x1010e3 (fun s => s.RIP = 0x1010e3) (movR64R64Effect 0x1010e3 0 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 69) (.out 0x1010e6 (subR64R64Effect 0x1010e6 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[67, 15]
    (.letOp (n := 70) (.exec 0x1010e6 (fun s => s.RIP = 0x1010e6) (subR64R64Effect 0x1010e6 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[67, 15]
    (.letOp (n := 71) (.exec 0x1010e9 (StorePre 0x1010e9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1010e9 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1010e9 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x1010f1 (notR64Effect 0x1010f1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[56]
    (.letOp (n := 73) (.exec 0x1010f1 (fun s => s.RIP = 0x1010f1) (notR64Effect 0x1010f1 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 74) (.out 0x1010f4 (movR64R64Effect 0x1010f4 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 75) (.exec 0x1010f4 (fun s => s.RIP = 0x1010f4) (movR64R64Effect 0x1010f4 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 76) (.out 0x1010f7 (andR64R64Effect 0x1010f7 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[74, 72]
    (.letOp (n := 77) (.exec 0x1010f7 (fun s => s.RIP = 0x1010f7) (andR64R64Effect 0x1010f7 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[74, 72]
    (.letOp (n := 78) (.out 0x1010fa (orR64R64Effect 0x1010fa 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[72, 15]
    (.letOp (n := 79) (.exec 0x1010fa (fun s => s.RIP = 0x1010fa) (orR64R64Effect 0x1010fa 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[72, 15]
    (.letOp (n := 80) (.out 0x1010fd (andR64R64Effect 0x1010fd 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[78, 69]
    (.letOp (n := 81) (.exec 0x1010fd (fun s => s.RIP = 0x1010fd) (andR64R64Effect 0x1010fd 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[78, 69]
    (.letOp (n := 82) (.out 0x101100 (orR64R64Effect 0x101100 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[80, 76]
    (.letOp (n := 83) (.exec 0x101100 (fun s => s.RIP = 0x101100) (orR64R64Effect 0x101100 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[80, 76]
    (.letOp (n := 84) (.out 0x101103 (shrR64Effect 0x101103 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[82]
    (.letOp (n := 85) (.exec 0x101103 (fun s => s.RIP = 0x101103) (shrR64Effect 0x101103 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82]
    (b_l1010ae_1)))))))))))))))))))))))))))))))))

def bytes_l1010ae : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x4C, 0x24, 0x08, 0x48,
    0x8B, 0x54, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x48, 0x48, 0x8B, 0x74, 0x24, 0x18, 0x48, 0x89,
    0x4C, 0x24, 0x68, 0x48, 0x89, 0x54, 0x24, 0x70, 0x48, 0x89, 0x74, 0x24, 0x78, 0x48, 0x89, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC8, 0x4C, 0x29, 0xF8, 0x48, 0x89, 0x84, 0x24, 0xA0,
    0x00, 0x00, 0x00, 0x48, 0xF7, 0xD1, 0x4C, 0x89, 0xFA, 0x48, 0x21, 0xCA, 0x4C, 0x09, 0xF9, 0x48,
    0x21, 0xC1, 0x48, 0x09, 0xD1, 0x48, 0xC1, 0xE9, 0x3F] ++ bytes_l1010ae_1

theorem code_l1010ae : ∀ x ∈ codeRange 0x1010ae bytes_l1010ae, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10ae 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1010ae_1

@[cfg_block] def b_l10126c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10126c (leaR64Effect 0x10126c 12 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x10126c (fun s => s.RIP = 0x10126c) (leaR64Effect 0x10126c 12 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101274 (movR64R64Effect 0x101274 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[5]
    (.letOp (n := 56) (.exec 0x101274 (fun s => s.RIP = 0x101274) (movR64R64Effect 0x101274 7 5) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.out 0x101277 (movR64M64Effect 0x101277 15 (.sib 4 none 0 (.d32 0x128))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 58) (.exec 0x101277 (LoadPre 0x101277 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x101277 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101277 15 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10127f (movR64R64Effect 0x10127f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[57]
    (.letOp (n := 60) (.exec 0x10127f (fun s => s.RIP = 0x10127f) (movR64R64Effect 0x10127f 6 15) (Reg.operands [.gpr 15] [])) #v[57]
    (.letOp (n := 61) (.out 0x101282 (movR64R64Effect 0x101282 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[53]
    (.letOp (n := 62) (.exec 0x101282 (fun s => s.RIP = 0x101282) (movR64R64Effect 0x101282 2 12) (Reg.operands [.gpr 12] [])) #v[53]
    (.letOp (n := 63) (.out 0x101285 (movR64M64Effect 0x101285 3 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 64) (.exec 0x101285 (LoadPre 0x101285 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x101285 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101285 3 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10128d (movR64R64Effect 0x10128d 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 66) (.exec 0x10128d (fun s => s.RIP = 0x10128d) (movR64R64Effect 0x10128d 1 3) (Reg.operands [.gpr 3] [])) #v[63]
    (.letOp (n := 67) (.out 0x101290 (callEffect (fun _ => 0x100000) 0x101295) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x101290 (PushPre 0x101290 5) (callEffect (fun _ => 0x100000) 0x101295) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x101295⟩) #v[]
    (.terminate (.call ⟨.l100000, RegMap.args [(1, 65), (2, 61), (3, 63), (4, 67), (5, 5), (6, 59), (7, 55), (12, 53), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l101295, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l10126c : List UInt8 :=
  [0x4C, 0x8D, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0xEF, 0x4C, 0x8B, 0xBC, 0x24, 0x28,
    0x01, 0x00, 0x00, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xE2, 0x48, 0x8B, 0x9C, 0x24, 0xB0, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xD9, 0xE8, 0x6B, 0xED, 0xFF, 0xFF]

theorem code_l10126c : ∀ x ∈ codeRange 0x10126c bytes_l10126c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x126c 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101295_1 : Block Op Label signature Reg.count 79 :=
  .letOp (n := 79) (.out 0x101320 (movR32Imm32Effect 0x101320 5 2 0x3) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x101320 (fun s => s.RIP = 0x101320) (movR32Imm32Effect 0x101320 5 2 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x101325 (callEffect (fun _ => 0x103f30) 0x10132a) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x101325 (PushPre 0x101325 5) (callEffect (fun _ => 0x103f30) 0x10132a) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x10132a⟩) #v[]
    (.terminate (.call ⟨.l103f30, RegMap.args [(0, 72), (2, 79), (3, 3), (4, 81), (5, 5), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l10132a, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))

def bytes_l101295_1 : List UInt8 :=
  [0xBA, 0x03, 0x00, 0x00, 0x00, 0xE8, 0x06, 0x2C, 0x00, 0x00]

theorem code_l101295_1 : ∀ x ∈ codeRange 0x101320 bytes_l101295_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1320 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101295 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101295 (StorePre 0x101295 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x101295 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101295 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10129e (StorePre 0x10129e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10129e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10129e (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1012a7 (StorePre 0x1012a7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1012a7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1012a7 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1012b0 (StorePre 0x1012b0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1012b0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1012b0 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1012b9 (movR64Imm64Effect 0x1012b9 0 0x101010101010101) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 58) (.exec 0x1012b9 (fun s => s.RIP = 0x1012b9) (movR64Imm64Effect 0x1012b9 0 0x101010101010101) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x1012c3 (StorePre 0x1012c3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1012c3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012c3 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x1012c8 (StorePre 0x1012c8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1012c8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012c8 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 61) (.exec 0x1012cd (StorePre 0x1012cd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1012cd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012cd 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 62) (.exec 0x1012d2 (StorePre 0x1012d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1012d2 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012d2 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 63) (.out 0x1012d7 (movR64M64Effect 0x1012d7 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x1012d7 (LoadPre 0x1012d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1012d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1012d7 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x1012df (StorePre 0x1012df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1012df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012df 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.exec 0x1012e4 (StorePre 0x1012e4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1012e4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012e4 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 67) (.exec 0x1012e9 (StorePre 0x1012e9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1012e9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1012e9 12 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 68) (.exec 0x1012ee (StorePre 0x1012ee 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1012ee + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1012ee 3 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 69) (.out 0x1012f6 (movR64M64Effect 0x1012f6 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x1012f6 (LoadPre 0x1012f6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1012f6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1012f6 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x1012fe (StorePre 0x1012fe 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1012fe + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1012fe 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x101306 (movR64M64Effect 0x101306 0 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x101306 (LoadPre 0x101306 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x101306 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101306 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x10130e (StorePre 0x10130e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10130e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10130e 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x101316 (leaR64Effect 0x101316 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 76) (.exec 0x101316 (fun s => s.RIP = 0x101316) (leaR64Effect 0x101316 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x10131b (leaR64Effect 0x10131b 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 78) (.exec 0x10131b (fun s => s.RIP = 0x10131b) (leaR64Effect 0x10131b 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l101295_1))))))))))))))))))))))))))

def bytes_l101295 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xB8, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x48, 0x89,
    0x44, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44,
    0x24, 0x40, 0x48, 0x8B, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48,
    0x89, 0x5C, 0x24, 0x70, 0x4C, 0x89, 0x64, 0x24, 0x78, 0x48, 0x89, 0x9C, 0x24, 0x80, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x90, 0x00, 0x00,
    0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x74, 0x24, 0x68] ++ bytes_l101295_1

theorem code_l101295 : ∀ x ∈ codeRange 0x101295 bytes_l101295, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1295 139 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l101295_1

@[cfg_block] def b_l10132a_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x101380 (popR64Effect 0x101380 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[83]
    (.letOp (n := 86) (.out 0x101380 (popR64Effect 0x101380 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[83]
    (.letOp (n := 87) (.exec 0x101380 (PopPre 0x101380) (popR64Effect 0x101380 2 12) (Reg.operands [.gpr 4] [])) #v[83]
    (.letOp (n := 88) (.out 0x101382 (popR64Effect 0x101382 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[86]
    (.letOp (n := 89) (.out 0x101382 (popR64Effect 0x101382 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[86]
    (.letOp (n := 90) (.exec 0x101382 (PopPre 0x101382) (popR64Effect 0x101382 2 13) (Reg.operands [.gpr 4] [])) #v[86]
    (.letOp (n := 91) (.out 0x101384 (popR64Effect 0x101384 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[89]
    (.letOp (n := 92) (.out 0x101384 (popR64Effect 0x101384 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[89]
    (.letOp (n := 93) (.exec 0x101384 (PopPre 0x101384) (popR64Effect 0x101384 2 14) (Reg.operands [.gpr 4] [])) #v[89]
    (.letOp (n := 94) (.out 0x101386 (popR64Effect 0x101386 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[92]
    (.letOp (n := 95) (.out 0x101386 (popR64Effect 0x101386 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[92]
    (.letOp (n := 96) (.exec 0x101386 (PopPre 0x101386) (popR64Effect 0x101386 2 15) (Reg.operands [.gpr 4] [])) #v[92]
    (.letOp (n := 97) (.out 0x101388 (popR64Effect 0x101388 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[95]
    (.letOp (n := 98) (.out 0x101388 (popR64Effect 0x101388 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[95]
    (.letOp (n := 99) (.exec 0x101388 (PopPre 0x101388) (popR64Effect 0x101388 1 5) (Reg.operands [.gpr 4] [])) #v[95]
    (.letOp (n := 100) (.out 0x101389 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[98]
    (.letOp (n := 101) (.out 0x101389 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[98]
    (.letOp (n := 102) (.exec 0x101389 (RetPre 0x101389) (retEffect) (Reg.operands [.gpr 4] [])) #v[98]
    (.terminate (.ret (RegMap.args [(0, 78), (1, 73), (2, 2), (3, 82), (4, 101), (5, 97), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 85), (13, 88), (14, 91), (15, 94), (22, 22), (39, 39), (50, 50), (51, 51)] 103) (some ⟨100, by decide⟩))))))))))))))))))))

def bytes_l10132a_1 : List UInt8 :=
  [0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10132a_1 : ∀ x ∈ codeRange 0x101380 bytes_l10132a_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1380 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10132a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10132a (movR64M64Effect 0x10132a 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10132a (LoadPre 0x10132a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10132a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10132a 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10132f (StorePre 0x10132f 4 (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x10132f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10132f 0 (.base 14 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 56) (.out 0x101333 (movR64M64Effect 0x101333 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x101333 (LoadPre 0x101333 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x101333 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101333 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x101338 (StorePre 0x101338 4 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x101338 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101338 0 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 59) (.out 0x10133c (movR64M64Effect 0x10133c 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x10133c (LoadPre 0x10133c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10133c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10133c 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x101341 (StorePre 0x101341 4 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x101341 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101341 0 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[59, 14]
    (.letOp (n := 62) (.out 0x101345 (movR64M64Effect 0x101345 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x101345 (LoadPre 0x101345 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101345 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101345 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x10134a (StorePre 0x10134a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10134a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10134a 0 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[62, 14]
    (.letOp (n := 65) (.out 0x10134e (movR64M64Effect 0x10134e 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x10134e (LoadPre 0x10134e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10134e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10134e 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x101353 (StorePre 0x101353 4 (fun s => AddrMode.addr (.base 14 (.d8 0x20)) s (0x101353 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101353 0 (.base 14 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[65, 14]
    (.letOp (n := 68) (.out 0x101357 (movR64M64Effect 0x101357 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x101357 (LoadPre 0x101357 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101357 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101357 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x10135c (StorePre 0x10135c 4 (fun s => AddrMode.addr (.base 14 (.d8 0x18)) s (0x10135c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10135c 0 (.base 14 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[68, 14]
    (.letOp (n := 71) (.out 0x101360 (movR64M64Effect 0x101360 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x101360 (LoadPre 0x101360 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x101360 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101360 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.out 0x101365 (movR64M64Effect 0x101365 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 74) (.exec 0x101365 (LoadPre 0x101365 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101365 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101365 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.exec 0x10136a (StorePre 0x10136a 4 (fun s => AddrMode.addr (.base 14 (.d8 0x10)) s (0x10136a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10136a 1 (.base 14 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 14] [])) #v[73, 14]
    (.letOp (n := 76) (.exec 0x10136e (StorePre 0x10136e 4 (fun s => AddrMode.addr (.base 14 (.d8 0x8)) s (0x10136e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10136e 0 (.base 14 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 14] [])) #v[71, 14]
    (.letOp (n := 77) (.exec 0x101372 (StorePre 0x101372 3 (fun s => AddrMode.addr (.base 14 .none) s (0x101372 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x101372 15 (.base 14 .none)) (Reg.operands [.gpr 15, .gpr 14] [])) #v[15, 14]
    (.letOp (n := 78) (.out 0x101375 (movR64R64Effect 0x101375 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 79) (.exec 0x101375 (fun s => s.RIP = 0x101375) (movR64R64Effect 0x101375 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 80) (.out 0x101378 (addR64Imm32Effect 0x101378 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 81) (.exec 0x101378 (fun s => s.RIP = 0x101378) (addR64Imm32Effect 0x101378 4 0xe8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 82) (.out 0x10137f (popR64Effect 0x10137f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[80]
    (.letOp (n := 83) (.out 0x10137f (popR64Effect 0x10137f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[80]
    (.letOp (n := 84) (.exec 0x10137f (PopPre 0x10137f) (popR64Effect 0x10137f 1 3) (Reg.operands [.gpr 4] [])) #v[80]
    (b_l10132a_1))))))))))))))))))))))))))))))))

def bytes_l10132a : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x49, 0x89, 0x46, 0x40, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x49, 0x89,
    0x46, 0x38, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x49, 0x89, 0x46, 0x30, 0x48, 0x8B, 0x44, 0x24, 0x28,
    0x49, 0x89, 0x46, 0x28, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x49, 0x89, 0x46, 0x20, 0x48, 0x8B, 0x44,
    0x24, 0x18, 0x49, 0x89, 0x46, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10,
    0x49, 0x89, 0x4E, 0x10, 0x49, 0x89, 0x46, 0x08, 0x4D, 0x89, 0x3E, 0x4C, 0x89, 0xF0, 0x48, 0x81,
    0xC4, 0xE8, 0x00, 0x00, 0x00, 0x5B] ++ bytes_l10132a_1

theorem code_l10132a : ∀ x ∈ codeRange 0x10132a bytes_l10132a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x132a 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10132a_1

@[cfg_block] def b_l10138a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10138a (movR32Imm32Effect 0x10138a 5 2 0x20) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x10138a (fun s => s.RIP = 0x10138a) (movR32Imm32Effect 0x10138a 5 2 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10138f (xorR32R32Effect 0x10138f 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x10138f (fun s => s.RIP = 0x10138f) (xorR32R32Effect 0x10138f 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x101391 (movR64R64Effect 0x101391 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[11]
    (.letOp (n := 58) (.exec 0x101391 (fun s => s.RIP = 0x101391) (movR64R64Effect 0x101391 6 11) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 59) (.out 0x101394 (movR64Imm32Effect 0x101394 1 0x2020e0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x101394 (fun s => s.RIP = 0x101394) (movR64Imm32Effect 0x101394 1 0x2020e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x10139b (callEffect (fun _ => 0x129b60) 0x1013a0) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x10139b (PushPre 0x10139b 5) (callEffect (fun _ => 0x129b60) 0x1013a0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1013a0⟩) #v[]
    (.terminate (.call ⟨.l129b60, RegMap.args [(1, 59), (2, 53), (4, 61), (5, 5), (6, 57), (7, 55), (11, 11)] 64⟩ { target := .l1013a0, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10138a : List UInt8 :=
  [0xBA, 0x20, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x4C, 0x89, 0xDE, 0x48, 0xC7, 0xC1, 0xE0, 0x20, 0x20,
    0x00, 0xE8, 0xC0, 0x87, 0x02, 0x00]

theorem code_l10138a : ∀ x ∈ codeRange 0x10138a bytes_l10138a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x138a 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013a0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013a0 (movR32Imm32Effect 0x1013a0 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x1013a0 (fun s => s.RIP = 0x1013a0) (movR32Imm32Effect 0x1013a0 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1013a5 (movR64Imm32Effect 0x1013a5 7 0x202098) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 56) (.exec 0x1013a5 (fun s => s.RIP = 0x1013a5) (movR64Imm32Effect 0x1013a5 7 0x202098) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1013ac (movR64Imm32Effect 0x1013ac 2 0x2020c8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 58) (.exec 0x1013ac (fun s => s.RIP = 0x1013ac) (movR64Imm32Effect 0x1013ac 2 0x2020c8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1013b3 (callEffect (fun _ => 0x129560) 0x1013b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1013b3 (PushPre 0x1013b3 5) (callEffect (fun _ => 0x129560) 0x1013b8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1013b8⟩) #v[]
    (.terminate (.call ⟨.l129560, RegMap.args [(2, 57), (4, 59), (5, 5), (6, 53), (7, 55)] 62⟩ { target := .l1013b8, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1013a0 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC7, 0x98, 0x20, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0xC8,
    0x20, 0x20, 0x00, 0xE8, 0xA8, 0x81, 0x02, 0x00]

theorem code_l1013a0 : ∀ x ∈ codeRange 0x1013a0 bytes_l1013a0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13a0 24 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1013b8 (xorR32R32Effect 0x1013b8 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 54) (.exec 0x1013b8 (fun s => s.RIP = 0x1013b8) (xorR32R32Effect 0x1013b8 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 55) (.out 0x1013ba (movR64R64Effect 0x1013ba 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8] []) (.reg (.gpr 2))) #v[8]
    (.letOp (n := 56) (.exec 0x1013ba (fun s => s.RIP = 0x1013ba) (movR64R64Effect 0x1013ba 2 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 57) (.out 0x1013bd (movR64Imm32Effect 0x1013bd 1 0x202080) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 58) (.exec 0x1013bd (fun s => s.RIP = 0x1013bd) (movR64Imm32Effect 0x1013bd 1 0x202080) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1013c4 (callEffect (fun _ => 0x129b60) 0x1013c9) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1013c4 (PushPre 0x1013c4 5) (callEffect (fun _ => 0x129b60) 0x1013c9) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1013c9⟩) #v[]
    (.terminate (.call ⟨.l129b60, RegMap.args [(1, 57), (2, 55), (4, 59), (5, 5), (6, 6), (7, 53), (8, 8)] 62⟩ { target := .l1013c9, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1013b8 : List UInt8 :=
  [0x31, 0xFF, 0x4C, 0x89, 0xC2, 0x48, 0xC7, 0xC1, 0x80, 0x20, 0x20, 0x00, 0xE8, 0x97, 0x87, 0x02,
    0x00]

theorem code_l1013b8 : ∀ x ∈ codeRange 0x1013b8 bytes_l1013b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13b8 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1013c9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1013c9 (StorePre 0x1013c9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1013c9 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013c9 (.sib 4 none 0 (.d8 0x8)) 0x202498) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x1013d2 (StorePre 0x1013d2 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1013d2 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013d2 (.sib 4 none 0 (.d8 0x10)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1013db (leaR64Effect 0x1013db 0 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x1013db (fun s => s.RIP = 0x1013db) (leaR64Effect 0x1013db 0 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1013e3 (StorePre 0x1013e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1013e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1013e3 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x1013e8 (StorePre 0x1013e8 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1013e8 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1013e8 (.sib 4 none 0 (.d8 0x20)) 0x12a190) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1013f1 (leaR64Effect 0x1013f1 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1013f1 (fun s => s.RIP = 0x1013f1) (leaR64Effect 0x1013f1 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1013f6 (movR64Imm32Effect 0x1013f6 7 0x20028f) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 62) (.exec 0x1013f6 (fun s => s.RIP = 0x1013f6) (movR64Imm32Effect 0x1013f6 7 0x20028f) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x1013fd (movR64Imm32Effect 0x1013fd 2 0x2022a0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 64) (.exec 0x1013fd (fun s => s.RIP = 0x1013fd) (movR64Imm32Effect 0x1013fd 2 0x2022a0) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x101404 (callEffect (fun _ => 0x129770) 0x101409) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x101404 (PushPre 0x101404 5) (callEffect (fun _ => 0x129770) 0x101409) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x101409⟩) #v[]
    (.terminate (.call ⟨.l129770, RegMap.args [(0, 55), (2, 63), (4, 65), (5, 5), (6, 59), (7, 61)] 68⟩ { target := .l101409, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l1013c9 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x98, 0x24, 0x20, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x90, 0xA1,
    0x12, 0x00, 0x48, 0x8D, 0x84, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48,
    0xC7, 0x44, 0x24, 0x20, 0x90, 0xA1, 0x12, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x08, 0x48, 0xC7, 0xC7,
    0x8F, 0x02, 0x20, 0x00, 0x48, 0xC7, 0xC2, 0xA0, 0x22, 0x20, 0x00, 0xE8, 0x67, 0x83, 0x02, 0x00]

theorem code_l1013c9 : ∀ x ∈ codeRange 0x1013c9 bytes_l1013c9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x13c9 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101409 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101409 (fun s => s.RIP = 0x101409) (fun _ => nopEffect 0x101409 7) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x101410 (pushR64Effect 0x101410 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x101410 (PushPre 0x101410 1) (pushR64Effect 0x101410 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x101411 (pushR64Effect 0x101411 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x101411 (PushPre 0x101411 2) (pushR64Effect 0x101411 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x101413 (pushR64Effect 0x101413 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x101413 (PushPre 0x101413 2) (pushR64Effect 0x101413 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x101415 (pushR64Effect 0x101415 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x101415 (PushPre 0x101415 2) (pushR64Effect 0x101415 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x101417 (pushR64Effect 0x101417 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x101417 (PushPre 0x101417 2) (pushR64Effect 0x101417 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x101419 (pushR64Effect 0x101419 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x101419 (PushPre 0x101419 1) (pushR64Effect 0x101419 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x10141a (subR64Imm32Effect 0x10141a 4 0xf8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x10141a (fun s => s.RIP = 0x10141a) (subR64Imm32Effect 0x10141a 4 0xf8) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.out 0x101421 (movR64R64Effect 0x101421 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 69) (.exec 0x101421 (fun s => s.RIP = 0x101421) (movR64R64Effect 0x101421 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 70) (.out 0x101424 (movR64R64Effect 0x101424 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 71) (.exec 0x101424 (fun s => s.RIP = 0x101424) (movR64R64Effect 0x101424 15 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 72) (.out 0x101427 (movR64R64Effect 0x101427 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 73) (.exec 0x101427 (fun s => s.RIP = 0x101427) (movR64R64Effect 0x101427 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 74) (.out 0x10142a (movR64R64Effect 0x10142a 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[66]
    (.letOp (n := 75) (.exec 0x10142a (fun s => s.RIP = 0x10142a) (movR64R64Effect 0x10142a 7 4) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 76) (.out 0x10142d (callEffect (fun _ => 0x127690) 0x101432) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 77) (.exec 0x10142d (PushPre 0x10142d 5) (callEffect (fun _ => 0x127690) 0x101432) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 78) (.const ⟨64, 0x101432⟩) #v[]
    (.terminate (.call ⟨.l127690, RegMap.args [(2, 2), (3, 72), (4, 76), (5, 5), (6, 6), (7, 74), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 68), (15, 70), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l101432, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l101409 : List UInt8 :=
  [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54,
    0x53, 0x48, 0x81, 0xEC, 0xF8, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x49, 0x89, 0xF7, 0x48, 0x89,
    0xFB, 0x48, 0x89, 0xE7, 0xE8, 0x5E, 0x62, 0x02, 0x00]

theorem code_l101409 : ∀ x ∈ codeRange 0x101409 bytes_l101409, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1409 41 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101432 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101432 (cmpMImm8Effect 0x101432 4 32 (.sib 4 none 0 .none) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101432 (LoadPre 0x101432 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101432 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x101432 4 32 (.sib 4 none 0 .none) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10143c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101432 : List UInt8 :=
  [0x83, 0x3C, 0x24, 0x02, 0x0F, 0x85, 0xE8, 0x01, 0x00, 0x00]

theorem code_l101432 : ∀ x ∈ codeRange 0x101432 bytes_l101432, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1432 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10143c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10143c (movR64M64Effect 0x10143c 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10143c (LoadPre 0x10143c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10143c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10143c 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101441 (movR64M64Effect 0x101441 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x101441 (LoadPre 0x101441 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x101441 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101441 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101446 (movR64M64Effect 0x101446 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x101446 (LoadPre 0x101446 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x101446 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101446 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10144b (movR64M64Effect 0x10144b 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x10144b (LoadPre 0x10144b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10144b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10144b 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x101450 (movR64M64Effect 0x101450 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x101450 (LoadPre 0x101450 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x101450 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x101450 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x101455 (StorePre 0x101455 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x101455 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101455 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 64) (.exec 0x10145a (StorePre 0x10145a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10145a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10145a 1 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 65) (.exec 0x10145f (StorePre 0x10145f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10145f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10145f 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 66) (.exec 0x101464 (StorePre 0x101464 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101464 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101464 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 67) (.exec 0x101469 (StorePre 0x101469 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101469 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101469 7 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 68) (.out 0x10146e (leaR64Effect 0x10146e 7 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x10146e (fun s => s.RIP = 0x10146e) (leaR64Effect 0x10146e 7 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x101476 (leaR64Effect 0x101476 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 71) (.exec 0x101476 (fun s => s.RIP = 0x101476) (leaR64Effect 0x101476 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.out 0x10147b (callEffect (fun _ => 0x106900) 0x101480) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 73) (.exec 0x10147b (PushPre 0x10147b 5) (callEffect (fun _ => 0x106900) 0x101480) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.const ⟨64, 0x101480⟩) #v[]
    (.terminate (.call ⟨.l106900, RegMap.args [(0, 53), (1, 55), (2, 57), (3, 3), (4, 72), (5, 5), (6, 70), (7, 68), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ { target := .l101480, kept := #v[], arity := rfl, guard := some (Fin.last 74) })))))))))))))))))))))))

def bytes_l10143c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48,
    0x8B, 0x74, 0x24, 0x20, 0x48, 0x8B, 0x7C, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x50, 0x48, 0x89,
    0x4C, 0x24, 0x58, 0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x74, 0x24, 0x68, 0x48, 0x89, 0x7C,
    0x24, 0x70, 0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x50, 0xE8,
    0x80, 0x54, 0x00, 0x00]

theorem code_l10143c : ∀ x ∈ codeRange 0x10143c bytes_l10143c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x143c 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101480 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101480 (cmpMImm8Effect 0x101480 8 32 (.sib 4 none 0 (.d32 0xc0)) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101480 (LoadPre 0x101480 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x101480 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x101480 8 32 (.sib 4 none 0 (.d32 0xc0)) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10148e, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101480 : List UInt8 :=
  [0x83, 0xBC, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x02, 0x0F, 0x85, 0x96, 0x01, 0x00, 0x00]

theorem code_l101480 : ∀ x ∈ codeRange 0x101480 bytes_l101480, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1480 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10148e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10148e (movR64M64Effect 0x10148e 12 (.sib 4 none 0 (.d32 0xc4))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x10148e (LoadPre 0x10148e (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x10148e + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10148e 12 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101496 (movzxR32M8Effect 0x101496 8 5 (.sib 4 none 0 (.d32 0xcc))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 56) (.exec 0x101496 (LoadPre 0x101496 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x101496 + BitVec.ofNat 64 8)) 1) (movzxR32M8Effect 0x101496 8 5 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10149e (movR64R64Effect 0x10149e 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 58) (.exec 0x10149e (fun s => s.RIP = 0x10149e) (movR64R64Effect 0x10149e 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1014a1 (leaR64Effect 0x1014a1 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 60) (.exec 0x1014a1 (fun s => s.RIP = 0x1014a1) (leaR64Effect 0x1014a1 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x1014a6 (callEffect (fun _ => 0x106120) 0x1014ab) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x1014a6 (PushPre 0x1014a6 5) (callEffect (fun _ => 0x106120) 0x1014ab) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x1014ab⟩) #v[]
    (.terminate (.call ⟨.l106120, RegMap.args [(3, 3), (4, 61), (5, 55), (6, 59), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 53), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l1014ab, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10148e : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x0F, 0xB6, 0xAC, 0x24, 0xCC, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xE7, 0x48, 0x8D, 0x74, 0x24, 0x50, 0xE8, 0x75, 0x4C, 0x00, 0x00]

theorem code_l10148e : ∀ x ∈ codeRange 0x10148e bytes_l10148e, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x148e 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014ab : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014ab (cmpMImm8Effect 0x1014ab 4 32 (.sib 4 none 0 .none) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1014ab (LoadPre 0x1014ab (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014ab + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x1014ab 4 32 (.sib 4 none 0 .none) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1014b5, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1014ab : List UInt8 :=
  [0x83, 0x3C, 0x24, 0x02, 0x0F, 0x85, 0x6F, 0x01, 0x00, 0x00]

theorem code_l1014ab : ∀ x ∈ codeRange 0x1014ab bytes_l1014ab, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14ab 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014b5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014b5 (movR32M32LowEffect 0x1014b5 0 (.sib 4 none 0 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1014b5 (LoadPre 0x1014b5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x1014b5 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x1014b5 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1014b9 (andR8Imm8Effect 0x1014b9 4 5 0x1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[5]
    (.letOp (n := 56) (.exec 0x1014b9 (fun s => s.RIP = 0x1014b9) (andR8Imm8Effect 0x1014b9 4 5 0x1) (Reg.operands [.gpr 5] [])) #v[5]
    (.letOp (n := 57) (.exec 0x1014bd (StorePre 0x1014bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1014bd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1014bd 12 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 58) (.exec 0x1014c2 (StorePre 0x1014c2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1014c2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x1014c2 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.exec 0x1014c9 (StorePre 0x1014c9 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x1014c9 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x1014c9 8 5 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 60) (.out 0x1014d1 (movR64R64Effect 0x1014d1 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 61) (.exec 0x1014d1 (fun s => s.RIP = 0x1014d1) (movR64R64Effect 0x1014d1 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x1014d4 (movR32Imm32Effect 0x1014d4 5 2 0xa) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 63) (.exec 0x1014d4 (fun s => s.RIP = 0x1014d4) (movR32Imm32Effect 0x1014d4 5 2 0xa) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1014d9 (movR64R64Effect 0x1014d9 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 65) (.exec 0x1014d9 (fun s => s.RIP = 0x1014d9) (movR64R64Effect 0x1014d9 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 66) (.out 0x1014dc (callEffect (fun _ => 0x1276d0) 0x1014e1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 67) (.exec 0x1014dc (PushPre 0x1014dc 5) (callEffect (fun _ => 0x1276d0) 0x1014e1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.const ⟨64, 0x1014e1⟩) #v[]
    (.terminate (.call ⟨.l1276d0, RegMap.args [(0, 53), (1, 1), (2, 62), (3, 3), (4, 66), (5, 55), (6, 64), (7, 60), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ { target := .l1014e1, kept := #v[], arity := rfl, guard := some (Fin.last 68) })))))))))))))))))

def bytes_l1014b5 : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x04, 0x40, 0x80, 0xE5, 0x01, 0x4C, 0x89, 0x64, 0x24, 0x78, 0x89, 0x84, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x40, 0x88, 0xAC, 0x24, 0x84, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE7, 0xBA,
    0x0A, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0xE8, 0xEF, 0x61, 0x02, 0x00]

theorem code_l1014b5 : ∀ x ∈ codeRange 0x1014b5 bytes_l1014b5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14b5 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014e1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014e1 (cmpMImm8Effect 0x1014e1 4 32 (.sib 4 none 0 .none) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x1014e1 (LoadPre 0x1014e1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1014e1 + BitVec.ofNat 64 4)) 4) (cmpMImm8Effect 0x1014e1 4 32 (.sib 4 none 0 .none) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1014eb, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1014e1 : List UInt8 :=
  [0x83, 0x3C, 0x24, 0x02, 0x0F, 0x85, 0x39, 0x01, 0x00, 0x00]

theorem code_l1014e1 : ∀ x ∈ codeRange 0x1014e1 bytes_l1014e1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14e1 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1014eb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1014eb (leaR64Effect 0x1014eb 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1014eb (fun s => s.RIP = 0x1014eb) (leaR64Effect 0x1014eb 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1014f3 (leaR64Effect 0x1014f3 6 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x1014f3 (fun s => s.RIP = 0x1014f3) (leaR64Effect 0x1014f3 6 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1014f8 (leaR64Effect 0x1014f8 2 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x1014f8 (fun s => s.RIP = 0x1014f8) (leaR64Effect 0x1014f8 2 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1014fd (callEffect (fun _ => 0x103670) 0x101502) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1014fd (PushPre 0x1014fd 5) (callEffect (fun _ => 0x103670) 0x101502) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x101502⟩) #v[]
    (.terminate (.call ⟨.l103670, RegMap.args [(1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 55), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l101502, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1014eb : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x50, 0x48, 0x8D, 0x54,
    0x24, 0x78, 0xE8, 0x6E, 0x21, 0x00, 0x00]

theorem code_l1014eb : ∀ x ∈ codeRange 0x1014eb bytes_l1014eb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14eb 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101502 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101502 (cmpMImm8Effect 0x101502 8 32 (.sib 4 none 0 (.d32 0x88)) 0x2) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101502 (LoadPre 0x101502 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x101502 + BitVec.ofNat 64 8)) 4) (cmpMImm8Effect 0x101502 8 32 (.sib 4 none 0 (.d32 0x88)) 0x2) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l101510, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101502 : List UInt8 :=
  [0x83, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x02, 0x0F, 0x85, 0x14, 0x01, 0x00, 0x00]

theorem code_l101502 : ∀ x ∈ codeRange 0x101502 bytes_l101502, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1502 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101510 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101510 (testM8Imm8Effect 0x101510 5 (.sib 4 none 0 (.d8 0x70)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x101510 (LoadPre 0x101510 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x101510 + BitVec.ofNat 64 5)) 1) (testM8Imm8Effect 0x101510 5 (.sib 4 none 0 (.d8 0x70)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10151b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101510 : List UInt8 :=
  [0xF6, 0x44, 0x24, 0x70, 0x01, 0x0F, 0x85, 0x09, 0x01, 0x00, 0x00]

theorem code_l101510 : ∀ x ∈ codeRange 0x101510 bytes_l101510, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1510 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10151b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10151b (movR32M32LowEffect 0x10151b 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10151b (LoadPre 0x10151b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10151b + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10151b 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10151f (cmpR32M32Effect 0x10151f 4 0 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[53, 4]
    (.letOp (n := 56) (.out 0x10151f (cmpR32M32Effect 0x10151f 4 0 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 4] []) (.flag .ZF)) #v[53, 4]
    (.letOp (n := 57) (.exec 0x10151f (LoadPre 0x10151f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x10151f + BitVec.ofNat 64 4)) 4) (cmpR32M32Effect 0x10151f 4 0 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.pure (condOp 7)) #v[55, 56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101624, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101529, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (14, 14), (15, 15), (16, 55), (19, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10151b : List UInt8 :=
  [0x8B, 0x44, 0x24, 0x68, 0x3B, 0x44, 0x24, 0x6C, 0x0F, 0x87, 0xFB, 0x00, 0x00, 0x00]

theorem code_l10151b : ∀ x ∈ codeRange 0x10151b bytes_l10151b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x151b 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101529 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101529 (movR64M64Effect 0x101529 13 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 54) (.exec 0x101529 (LoadPre 0x101529 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x101529 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101529 13 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101531 (movR64M64Effect 0x101531 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x101531 (LoadPre 0x101531 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x101531 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101531 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x101539 (cmpR64Imm8Effect 0x101539 13 0x21) (EffectPart.reads (.flag .CF) [.gpr 13] []) (.flag .CF)) #v[53]
    (.letOp (n := 58) (.exec 0x101539 (fun s => s.RIP = 0x101539) (cmpR64Imm8Effect 0x101539 13 0x21) (Reg.operands [.gpr 13] [])) #v[53]
    (.letOp (n := 59) (.out 0x10153d (atFlags (condHolds 3) (setccR8Effect 0x10153d 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1, 57]
    (.letOp (n := 60) (.exec 0x10153d (fun s => s.RIP = 0x10153d) (atFlags (condHolds 3) (setccR8Effect 0x10153d 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1, 57]
    (.letOp (n := 61) (.out 0x101540 (cmpR64Imm8Effect 0x101540 0 0x21) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[55]
    (.letOp (n := 62) (.exec 0x101540 (fun s => s.RIP = 0x101540) (cmpR64Imm8Effect 0x101540 0 0x21) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 63) (.out 0x101544 (atFlags (condHolds 3) (setccR8Effect 0x101544 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[2, 61]
    (.letOp (n := 64) (.exec 0x101544 (fun s => s.RIP = 0x101544) (atFlags (condHolds 3) (setccR8Effect 0x101544 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[2, 61]
    (.letOp (n := 65) (.out 0x101547 (orR8R8Effect 0x101547 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[63, 59]
    (.letOp (n := 66) (.out 0x101547 (orR8R8Effect 0x101547 2 2 1) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 1] []) (.flag .ZF)) #v[63, 59]
    (.letOp (n := 67) (.exec 0x101547 (fun s => s.RIP = 0x101547) (orR8R8Effect 0x101547 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[63, 59]
    (.letOp (n := 68) (.pure (condOp 5)) #v[66]
    (.terminate (.condBr (Fin.last 68) ⟨.l101624, RegMap.args [(0, 55), (1, 59), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩ ⟨.l10154f, RegMap.args [(0, 55), (1, 59), (2, 65), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (19, 66), (22, 22), (39, 39), (50, 50), (51, 51)] 69⟩)))))))))))))))))

def bytes_l101529 : List UInt8 :=
  [0x4C, 0x8B, 0xAC, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x49, 0x83, 0xFD, 0x21, 0x0F, 0x93, 0xC1, 0x48, 0x83, 0xF8, 0x21, 0x0F, 0x93, 0xC2, 0x08, 0xCA,
    0x0F, 0x85, 0xD5, 0x00, 0x00, 0x00]

theorem code_l101529 : ∀ x ∈ codeRange 0x101529 bytes_l101529, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1529 38 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10154f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10154f (movR64M64Effect 0x10154f 5 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x10154f (LoadPre 0x10154f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10154f + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10154f 5 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101557 (subR64R64Effect 0x101557 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[53, 15]
    (.letOp (n := 56) (.out 0x101557 (subR64R64Effect 0x101557 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[53, 15]
    (.letOp (n := 57) (.exec 0x101557 (fun s => s.RIP = 0x101557) (subR64R64Effect 0x101557 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 58) (.pure (condOp 2)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101624, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l101560, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 55), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l10154f : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0x90, 0x00, 0x00, 0x00, 0x4C, 0x29, 0xFD, 0x0F, 0x82, 0xC4, 0x00, 0x00,
    0x00]

theorem code_l10154f : ∀ x ∈ codeRange 0x10154f bytes_l10154f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x154f 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101560 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101560 (addR64R64Effect 0x101560 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[13, 5]
    (.letOp (n := 54) (.out 0x101560 (addR64R64Effect 0x101560 13 5) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 5] []) (.flag .CF)) #v[13, 5]
    (.letOp (n := 55) (.exec 0x101560 (fun s => s.RIP = 0x101560) (addR64R64Effect 0x101560 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[13, 5]
    (.letOp (n := 56) (.pure (condOp 2)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l101624, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l101569, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 53), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l101560 : List UInt8 :=
  [0x49, 0x01, 0xED, 0x0F, 0x82, 0xBB, 0x00, 0x00, 0x00]

theorem code_l101560 : ∀ x ∈ codeRange 0x101560 bytes_l101560, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1560 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101569 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101569 (movR64M64Effect 0x101569 12 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 54) (.exec 0x101569 (LoadPre 0x101569 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x101569 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x101569 12 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x101571 (subR64R64Effect 0x101571 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[53, 15]
    (.letOp (n := 56) (.out 0x101571 (subR64R64Effect 0x101571 12 15) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 15] []) (.flag .CF)) #v[53, 15]
    (.letOp (n := 57) (.exec 0x101571 (fun s => s.RIP = 0x101571) (subR64R64Effect 0x101571 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 58) (.pure (condOp 2)) #v[56]
    (.terminate (.condBr (Fin.last 58) ⟨.l101624, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩ ⟨.l10157a, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 13), (14, 14), (15, 15), (16, 56), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l101569 : List UInt8 :=
  [0x4C, 0x8B, 0xA4, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x4D, 0x29, 0xFC, 0x0F, 0x82, 0xAA, 0x00, 0x00,
    0x00]

theorem code_l101569 : ∀ x ∈ codeRange 0x101569 bytes_l101569, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1569 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10157a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10157a (addR64R64Effect 0x10157a 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[0, 12]
    (.letOp (n := 54) (.out 0x10157a (addR64R64Effect 0x10157a 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[0, 12]
    (.letOp (n := 55) (.exec 0x10157a (fun s => s.RIP = 0x10157a) (addR64R64Effect 0x10157a 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[0, 12]
    (.letOp (n := 56) (.pure (condOp 2)) #v[54]
    (.terminate (.condBr (Fin.last 56) ⟨.l101624, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩ ⟨.l101583, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 54), (22, 22), (39, 39), (50, 50), (51, 51)] 57⟩)))))

def bytes_l10157a : List UInt8 :=
  [0x4C, 0x01, 0xE0, 0x0F, 0x82, 0xA1, 0x00, 0x00, 0x00]

theorem code_l10157a : ∀ x ∈ codeRange 0x10157a bytes_l10157a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x157a 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101583 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101583 (cmpR64R64Effect 0x101583 0 14) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 14] []) (.flag .ZF)) #v[0, 14]
    (.letOp (n := 54) (.exec 0x101583 (fun s => s.RIP = 0x101583) (cmpR64R64Effect 0x101583 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[0, 14]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l101624, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10158c, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l101583 : List UInt8 :=
  [0x4C, 0x39, 0xF0, 0x0F, 0x85, 0x98, 0x00, 0x00, 0x00]

theorem code_l101583 : ∀ x ∈ codeRange 0x101583 bytes_l101583, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1583 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10158c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10158c (StorePre 0x10158c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10158c + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x10158c (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x101591 (StorePre 0x101591 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x101591 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x101591 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10159a (StorePre 0x10159a 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10159a + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10159a (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x1015a3 (StorePre 0x1015a3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1015a3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015a3 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1015ac (StorePre 0x1015ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1015ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015ac (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1015b5 (StorePre 0x1015b5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1015b5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015b5 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x1015be (StorePre 0x1015be 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1015be + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015be (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x1015c7 (StorePre 0x1015c7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1015c7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015c7 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1015d0 (StorePre 0x1015d0 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1015d0 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x1015d0 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x1015d9 (StorePre 0x1015d9 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1015d9 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x1015d9 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1015e1 (cmpR64Imm8Effect 0x1015e1 14 0x4a) (EffectPart.reads (.flag .CF) [.gpr 14] []) (.flag .CF)) #v[14]
    (.letOp (n := 64) (.exec 0x1015e1 (fun s => s.RIP = 0x1015e1) (cmpR64Imm8Effect 0x1015e1 14 0x4a) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.pure (condOp 3)) #v[63]
    (.terminate (.condBr (Fin.last 65) ⟨.l101648, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ ⟨.l1015e7, RegMap.args [(3, 3), (4, 4), (5, 5), (7, 7), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (16, 63), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩))))))))))))))

def bytes_l10158c : List UInt8 :=
  [0xC6, 0x44, 0x24, 0x48, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x10,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x04,
    0x24, 0x00, 0x00, 0x00, 0x00, 0x49, 0x83, 0xFE, 0x4A, 0x73, 0x61]

theorem code_l10158c : ∀ x ∈ codeRange 0x10158c bytes_l10158c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x158c 91 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015e7 (movR64R64Effect 0x1015e7 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x1015e7 (fun s => s.RIP = 0x1015e7) (movR64R64Effect 0x1015e7 7 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1015ea (leaR64Effect 0x1015ea 0 (.rip 0x2922f)) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 56) (.exec 0x1015ea (fun s => s.RIP = 0x1015ea) (leaR64Effect 0x1015ea 0 (.rip 0x2922f)) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x1015f1 (movR64R64Effect 0x1015f1 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x1015f1 (fun s => s.RIP = 0x1015f1) (movR64R64Effect 0x1015f1 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1015f4 (movR64R64Effect 0x1015f4 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14] []) (.reg (.gpr 2))) #v[14]
    (.letOp (n := 60) (.exec 0x1015f4 (fun s => s.RIP = 0x1015f4) (movR64R64Effect 0x1015f4 2 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 61) (.out 0x1015f7 (movR64R64Effect 0x1015f7 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[55]
    (.letOp (n := 62) (.exec 0x1015f7 (fun s => s.RIP = 0x1015f7) (movR64R64Effect 0x1015f7 15 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 63) (.out 0x1015fa (callEffect (fun s => (Operand.reg 0 : Operand 64).read s) 0x1015fc) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 0] []) (.reg (.gpr 4))) #v[4, 55]
    (.letOp (n := 64) (.exec 0x1015fa (GoesTo (CallPre 0x1015fa 2 (fun s => (Operand.reg 0 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 0 : Operand 64).read s) 0x1015fc) 0x12a820) (callEffect (fun s => (Operand.reg 0 : Operand 64).read s) 0x1015fc) (Reg.operands [.gpr 4, .gpr 0] [])) #v[4, 55]
    (.letOp (n := 65) (.const ⟨64, 0x1015fc⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 55), (2, 59), (3, 3), (4, 63), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 61), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l1015fc, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l1015e7 : List UInt8 :=
  [0x48, 0x89, 0xE7, 0x48, 0x8D, 0x05, 0x2F, 0x92, 0x02, 0x00, 0x4C, 0x89, 0xFE, 0x4C, 0x89, 0xF2,
    0x49, 0x89, 0xC7, 0xFF, 0xD0]

theorem code_l1015e7 : ∀ x ∈ codeRange 0x1015e7 bytes_l1015e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15e7 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1015fc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1015fc (leaR64Effect 0x1015fc 7 (.base 3 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x1015fc (fun s => s.RIP = 0x1015fc) (leaR64Effect 0x1015fc 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101600 (movR32Imm32Effect 0x101600 5 2 0x49) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x101600 (fun s => s.RIP = 0x101600) (movR32Imm32Effect 0x101600 5 2 0x49) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x101605 (movR64R64Effect 0x101605 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 58) (.exec 0x101605 (fun s => s.RIP = 0x101605) (movR64R64Effect 0x101605 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x101608 (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x10160b) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 60) (.exec 0x101608 (GoesTo (CallPre 0x101608 3 (fun s => (Operand.reg 15 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x10160b) 0x12a820) (callEffect (fun s => (Operand.reg 15 : Operand 64).read s) 0x10160b) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 61) (.const ⟨64, 0x10160b⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10160b, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1015fc : List UInt8 :=
  [0x48, 0x8D, 0x7B, 0x28, 0xBA, 0x49, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE6, 0x41, 0xFF, 0xD7]

theorem code_l1015fc : ∀ x ∈ codeRange 0x1015fc bytes_l1015fc, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x15fc 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10160b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10160b (StorePre 0x10160b 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x10160b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10160b 5 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 3] [])) #v[5, 3]
    (.letOp (n := 54) (.exec 0x10160f (StorePre 0x10160f 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10160f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10160f 13 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 3] [])) #v[13, 3]
    (.letOp (n := 55) (.exec 0x101613 (StorePre 0x101613 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x101613 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101613 12 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 12, .gpr 3] [])) #v[12, 3]
    (.letOp (n := 56) (.exec 0x101617 (StorePre 0x101617 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x101617 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x101617 14 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 3] [])) #v[14, 3]
    (.letOp (n := 57) (.exec 0x10161b (StorePre 0x10161b 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10161b + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10161b (.base 3 .none) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l101633, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10160b : List UInt8 :=
  [0x48, 0x89, 0x6B, 0x08, 0x4C, 0x89, 0x6B, 0x10, 0x4C, 0x89, 0x63, 0x18, 0x4C, 0x89, 0x73, 0x20,
    0x48, 0xC7, 0x03, 0x00, 0x00, 0x00, 0x00, 0xEB, 0x0F]

theorem code_l10160b : ∀ x ∈ codeRange 0x10160b bytes_l10160b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x160b 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101624 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x101624 (StorePre 0x101624 8 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x101624 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101624 (.base 3 (.d8 0x8)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.exec 0x10162c (StorePre 0x10162c 7 (fun s => AddrMode.addr (.base 3 .none) s (0x10162c + BitVec.ofNat 64 7)) 8) (movM64Imm32Effect 0x10162c (.base 3 .none) 0x1) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l101633, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l101624 : List UInt8 :=
  [0x48, 0xC7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x03, 0x01, 0x00, 0x00, 0x00]

theorem code_l101624 : ∀ x ∈ codeRange 0x101624 bytes_l101624, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1624 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101633 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101633 (movR64R64Effect 0x101633 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x101633 (fun s => s.RIP = 0x101633) (movR64R64Effect 0x101633 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x101636 (addR64Imm32Effect 0x101636 4 0xf8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x101636 (fun s => s.RIP = 0x101636) (addR64Imm32Effect 0x101636 4 0xf8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10163d (popR64Effect 0x10163d 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x10163d (popR64Effect 0x10163d 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x10163d (PopPre 0x10163d) (popR64Effect 0x10163d 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x10163e (popR64Effect 0x10163e 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x10163e (popR64Effect 0x10163e 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10163e (PopPre 0x10163e) (popR64Effect 0x10163e 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x101640 (popR64Effect 0x101640 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x101640 (popR64Effect 0x101640 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x101640 (PopPre 0x101640) (popR64Effect 0x101640 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x101642 (popR64Effect 0x101642 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x101642 (popR64Effect 0x101642 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x101642 (PopPre 0x101642) (popR64Effect 0x101642 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x101644 (popR64Effect 0x101644 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x101644 (popR64Effect 0x101644 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x101644 (PopPre 0x101644) (popR64Effect 0x101644 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x101646 (popR64Effect 0x101646 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x101646 (popR64Effect 0x101646 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x101646 (PopPre 0x101646) (popR64Effect 0x101646 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x101647 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x101647 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x101647 (RetPre 0x101647) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l101633 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xF8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l101633 : ∀ x ∈ codeRange 0x101633 bytes_l101633, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1633 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l101648 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x101648 (movR32Imm32Effect 0x101648 5 2 0x49) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x101648 (fun s => s.RIP = 0x101648) (movR32Imm32Effect 0x101648 5 2 0x49) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10164d (xorR32R32Effect 0x10164d 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 56) (.exec 0x10164d (fun s => s.RIP = 0x10164d) (xorR32R32Effect 0x10164d 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 57) (.out 0x10164f (movR64R64Effect 0x10164f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 58) (.exec 0x10164f (fun s => s.RIP = 0x10164f) (movR64R64Effect 0x10164f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 59) (.out 0x101652 (movR64Imm32Effect 0x101652 1 0x2020f8) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 60) (.exec 0x101652 (fun s => s.RIP = 0x101652) (movR64Imm32Effect 0x101652 1 0x2020f8) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x101659 (callEffect (fun _ => 0x129b60) 0x10165e) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 62) (.exec 0x101659 (PushPre 0x101659 5) (callEffect (fun _ => 0x129b60) 0x10165e) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.const ⟨64, 0x10165e⟩) #v[]
    (.terminate (.call ⟨.l129b60, RegMap.args [(1, 59), (2, 53), (4, 61), (5, 5), (6, 57), (7, 55), (14, 14)] 64⟩ { target := .l10165e, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l101648 : List UInt8 :=
  [0xBA, 0x49, 0x00, 0x00, 0x00, 0x31, 0xFF, 0x4C, 0x89, 0xF6, 0x48, 0xC7, 0xC1, 0xF8, 0x20, 0x20,
    0x00, 0xE8, 0x02, 0x85, 0x02, 0x00]

theorem code_l101648 : ∀ x ∈ codeRange 0x101648 bytes_l101648, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1648 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10165e_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x1016a9 (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 88) (.exec 0x1016a9 (fun s => s.RIP = 0x1016a9) (leaR64Effect 0x1016a9 15 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 89) (.out 0x1016b1 (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 90) (.exec 0x1016b1 (fun s => s.RIP = 0x1016b1) (leaR64Effect 0x1016b1 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 91) (.out 0x1016b6 (movR64R64Effect 0x1016b6 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[87]
    (.letOp (n := 92) (.exec 0x1016b6 (fun s => s.RIP = 0x1016b6) (movR64R64Effect 0x1016b6 7 15) (Reg.operands [.gpr 15] [])) #v[87]
    (.letOp (n := 93) (.out 0x1016b9 (callEffect (fun _ => 0x109e60) 0x1016be) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 94) (.exec 0x1016b9 (PushPre 0x1016b9 5) (callEffect (fun _ => 0x109e60) 0x1016be) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 95) (.const ⟨64, 0x1016be⟩) #v[]
    (.terminate (.call ⟨.l109e60, RegMap.args [(0, 81), (1, 83), (2, 2), (3, 73), (4, 93), (5, 5), (6, 89), (7, 91), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 87), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ { target := .l1016be, kept := #v[], arity := rfl, guard := some (Fin.last 95) }))))))))))

def bytes_l10165e_1 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x58, 0x4C, 0x89, 0xFF,
    0xE8, 0xA2, 0x87, 0x00, 0x00]

theorem code_l10165e_1 : ∀ x ∈ codeRange 0x1016a9 bytes_l10165e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x16a9 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10165e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10165e (fun s => s.RIP = 0x10165e) (fun _ => nopEffect 0x10165e 2) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.out 0x101660 (pushR64Effect 0x101660 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 55) (.exec 0x101660 (PushPre 0x101660 1) (pushR64Effect 0x101660 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 56) (.out 0x101661 (pushR64Effect 0x101661 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[54, 15]
    (.letOp (n := 57) (.exec 0x101661 (PushPre 0x101661 2) (pushR64Effect 0x101661 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[54, 15]
    (.letOp (n := 58) (.out 0x101663 (pushR64Effect 0x101663 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[56, 14]
    (.letOp (n := 59) (.exec 0x101663 (PushPre 0x101663 2) (pushR64Effect 0x101663 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[56, 14]
    (.letOp (n := 60) (.out 0x101665 (pushR64Effect 0x101665 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[58, 13]
    (.letOp (n := 61) (.exec 0x101665 (PushPre 0x101665 2) (pushR64Effect 0x101665 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[58, 13]
    (.letOp (n := 62) (.out 0x101667 (pushR64Effect 0x101667 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[60, 12]
    (.letOp (n := 63) (.exec 0x101667 (PushPre 0x101667 2) (pushR64Effect 0x101667 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[60, 12]
    (.letOp (n := 64) (.out 0x101669 (pushR64Effect 0x101669 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x101669 (PushPre 0x101669 1) (pushR64Effect 0x101669 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x10166a (subR64Imm32Effect 0x10166a 4 0x1000) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 67) (.exec 0x10166a (fun s => s.RIP = 0x10166a) (subR64Imm32Effect 0x10166a 4 0x1000) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 68) (.exec 0x101671 (StorePre 0x101671 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x101671 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x101671 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 69) (.out 0x101679 (subR64Imm32Effect 0x101679 4 0x7d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x101679 (fun s => s.RIP = 0x101679) (subR64Imm32Effect 0x101679 4 0x7d8) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x101680 (movR64R64Effect 0x101680 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 72) (.exec 0x101680 (fun s => s.RIP = 0x101680) (movR64R64Effect 0x101680 14 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x101683 (movR64R64Effect 0x101683 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 74) (.exec 0x101683 (fun s => s.RIP = 0x101683) (movR64R64Effect 0x101683 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x101686 (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x101686 (LoadPre 0x101686 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x101686 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x101686 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.exec 0x10168a (StorePre 0x10168a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10168a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10168a 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 69]
    (.letOp (n := 78) (.out 0x10168f (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 79) (.exec 0x10168f (LoadPre 0x10168f (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10168f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10168f 0 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 80) (.exec 0x101693 (StorePre 0x101693 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x101693 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x101693 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 69]
    (.letOp (n := 81) (.out 0x101698 (movR64M64Effect 0x101698 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 82) (.exec 0x101698 (LoadPre 0x101698 (fun s => AddrMode.addr (.base 6 .none) s (0x101698 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x101698 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 83) (.out 0x10169b (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 84) (.exec 0x10169b (LoadPre 0x10169b (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10169b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10169b 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 85) (.exec 0x10169f (StorePre 0x10169f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10169f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10169f 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[83, 69]
    (.letOp (n := 86) (.exec 0x1016a4 (StorePre 0x1016a4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1016a4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1016a4 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 69]
    (b_l10165e_1))))))))))))))))))))))))))))))))))

def bytes_l10165e : List UInt8 :=
  [0x66, 0x90, 0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x00,
    0x10, 0x00, 0x00, 0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xEC, 0xD8, 0x07,
    0x00, 0x00, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xFB, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24,
    0x70, 0x48, 0x8B, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E,
    0x08, 0x48, 0x89, 0x4C, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x58] ++ bytes_l10165e_1

theorem code_l10165e : ∀ x ∈ codeRange 0x10165e bytes_l10165e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x165e 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10165e_1

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

@[cfg_block] def b_l102630 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102630 (pushR64Effect 0x102630 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x102630 (PushPre 0x102630 2) (pushR64Effect 0x102630 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x102632 (pushR64Effect 0x102632 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x102632 (PushPre 0x102632 2) (pushR64Effect 0x102632 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x102634 (pushR64Effect 0x102634 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x102634 (PushPre 0x102634 2) (pushR64Effect 0x102634 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x102636 (pushR64Effect 0x102636 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x102636 (PushPre 0x102636 1) (pushR64Effect 0x102636 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x102637 (subR64Imm32Effect 0x102637 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x102637 (fun s => s.RIP = 0x102637) (subR64Imm32Effect 0x102637 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x10263e (movR64R64Effect 0x10263e 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 64) (.exec 0x10263e (fun s => s.RIP = 0x10263e) (movR64R64Effect 0x10263e 14 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 65) (.out 0x102641 (movR64R64Effect 0x102641 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 66) (.exec 0x102641 (fun s => s.RIP = 0x102641) (movR64R64Effect 0x102641 15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 67) (.out 0x102644 (movR64R64Effect 0x102644 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 68) (.exec 0x102644 (fun s => s.RIP = 0x102644) (movR64R64Effect 0x102644 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 69) (.out 0x102647 (leaR64Effect 0x102647 7 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[61]
    (.letOp (n := 70) (.exec 0x102647 (fun s => s.RIP = 0x102647) (leaR64Effect 0x102647 7 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 71) (.out 0x10264c (callEffect (fun _ => 0x106dd0) 0x102651) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 72) (.exec 0x10264c (PushPre 0x10264c 5) (callEffect (fun _ => 0x106dd0) 0x102651) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 73) (.const ⟨64, 0x102651⟩) #v[]
    (.terminate (.call ⟨.l106dd0, RegMap.args [(1, 1), (2, 2), (3, 67), (4, 71), (5, 5), (6, 6), (7, 69), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 63), (15, 65), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l102651, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l102630 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x01, 0x00, 0x00, 0x49, 0x89,
    0xCE, 0x49, 0x89, 0xD7, 0x48, 0x89, 0xFB, 0x48, 0x8D, 0x7C, 0x24, 0x20, 0xE8, 0x7F, 0x47, 0x00,
    0x00]

theorem code_l102630 : ∀ x ∈ codeRange 0x102630 bytes_l102630, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2630 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102651 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102651 (cmpMImm8Effect 0x102651 5 32 (.sib 4 none 0 (.d8 0x20)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x102651 (LoadPre 0x102651 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x102651 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x102651 5 32 (.sib 4 none 0 (.d8 0x20)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l102883, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10265c, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l102651 : List UInt8 :=
  [0x83, 0x7C, 0x24, 0x20, 0x01, 0x0F, 0x84, 0x27, 0x02, 0x00, 0x00]

theorem code_l102651 : ∀ x ∈ codeRange 0x102651 bytes_l102651, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2651 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10265c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10265c (movR64M64Effect 0x10265c 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10265c (LoadPre 0x10265c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10265c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10265c 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x102661 (StorePre 0x102661 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102661 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102661 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x102666 (movR64M64Effect 0x102666 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x102666 (LoadPre 0x102666 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x102666 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102666 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10266b (StorePre 0x10266b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10266b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10266b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x102670 (movR64M64Effect 0x102670 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x102670 (LoadPre 0x102670 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x102670 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102670 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x102675 (movR64M64Effect 0x102675 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 62) (.exec 0x102675 (LoadPre 0x102675 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x102675 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102675 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.exec 0x10267a (StorePre 0x10267a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10267a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10267a 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x10267f (StorePre 0x10267f 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10267f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10267f 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 65) (.out 0x102683 (leaR64Effect 0x102683 12 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 66) (.exec 0x102683 (fun s => s.RIP = 0x102683) (leaR64Effect 0x102683 12 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10268b (movR64R64Effect 0x10268b 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 68) (.exec 0x10268b (fun s => s.RIP = 0x10268b) (movR64R64Effect 0x10268b 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10268e (movR64R64Effect 0x10268e 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 70) (.exec 0x10268e (fun s => s.RIP = 0x10268e) (movR64R64Effect 0x10268e 7 12) (Reg.operands [.gpr 12] [])) #v[65]
    (.letOp (n := 71) (.out 0x102691 (callEffect (fun _ => 0x10ee80) 0x102696) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x102691 (PushPre 0x102691 5) (callEffect (fun _ => 0x10ee80) 0x102696) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x102696⟩) #v[]
    (.terminate (.call ⟨.l10ee80, RegMap.args [(0, 59), (1, 61), (3, 3), (4, 71), (5, 5), (6, 67), (7, 69), (9, 9), (10, 10), (11, 11), (12, 65), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l102696, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10265c : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48,
    0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89,
    0x4C, 0x24, 0x08, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x8D, 0xA4, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48,
    0x89, 0xE6, 0x4C, 0x89, 0xE7, 0xE8, 0xEA, 0xC7, 0x00, 0x00]

theorem code_l10265c : ∀ x ∈ codeRange 0x10265c bytes_l10265c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x265c 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102696 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102696 (leaR64Effect 0x102696 7 (.sib 4 none 0 (.d32 0x160))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x102696 (fun s => s.RIP = 0x102696) (leaR64Effect 0x102696 7 (.sib 4 none 0 (.d32 0x160))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10269e (movR64R64Effect 0x10269e 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 56) (.exec 0x10269e (fun s => s.RIP = 0x10269e) (movR64R64Effect 0x10269e 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1026a1 (callEffect (fun _ => 0x10fe50) 0x1026a6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x1026a1 (PushPre 0x1026a1 5) (callEffect (fun _ => 0x10fe50) 0x1026a6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x1026a6⟩) #v[]
    (.terminate (.call ⟨.l10fe50, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l1026a6, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l102696 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0x60, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xE6, 0xE8, 0xAA, 0xD7, 0x00, 0x00]

theorem code_l102696 : ∀ x ∈ codeRange 0x102696 bytes_l102696, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2696 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1026a6_1 : Block Op Label signature Reg.count 81 :=
  .letOp (n := 81) (.out 0x10273d (leaR64Effect 0x10273d 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 82) (.exec 0x10273d (fun s => s.RIP = 0x10273d) (leaR64Effect 0x10273d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x102742 (leaR64Effect 0x102742 6 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 84) (.exec 0x102742 (fun s => s.RIP = 0x102742) (leaR64Effect 0x102742 6 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10274a (movR32Imm32Effect 0x10274a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 86) (.exec 0x10274a (fun s => s.RIP = 0x10274a) (movR32Imm32Effect 0x10274a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x10274f (movR64R64Effect 0x10274f 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[81]
    (.letOp (n := 88) (.exec 0x10274f (fun s => s.RIP = 0x10274f) (movR64R64Effect 0x10274f 7 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 89) (.exec 0x102752 (RepPre 0x102752 (RepMovsqPre 0x102752)) (repMovsqEffect 0x102752) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[83, 87, 85, 22]
    (.letOp (n := 90) (.out 0x102755 (leaR64Effect 0x102755 8 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 91) (.exec 0x102755 (fun s => s.RIP = 0x102755) (leaR64Effect 0x102755 8 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x10275d (movR32Imm32Effect 0x10275d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 93) (.exec 0x10275d (fun s => s.RIP = 0x10275d) (movR32Imm32Effect 0x10275d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 94) (.out 0x102762 (movR64R64Effect 0x102762 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[90]
    (.letOp (n := 95) (.exec 0x102762 (fun s => s.RIP = 0x102762) (movR64R64Effect 0x102762 7 8) (Reg.operands [.gpr 8] [])) #v[90]
    (.letOp (n := 96) (.out 0x102765 (movR64R64Effect 0x102765 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 97) (.exec 0x102765 (fun s => s.RIP = 0x102765) (movR64R64Effect 0x102765 6 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 98) (.exec 0x102768 (RepPre 0x102768 (RepMovsqPre 0x102768)) (repMovsqEffect 0x102768) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[96, 94, 92, 22]
    (.letOp (n := 99) (.exec 0x10276b (StorePre 0x10276b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10276b + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10276b 15 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 100) (.exec 0x102773 (StorePre 0x102773 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x102773 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102773 14 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[14, 4]
    (.letOp (n := 101) (.out 0x10277b (leaR64Effect 0x10277b 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 102) (.exec 0x10277b (fun s => s.RIP = 0x10277b) (leaR64Effect 0x10277b 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 103) (.out 0x102780 (leaR64Effect 0x102780 2 (.sib 4 none 0 (.d32 0x140))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 104) (.exec 0x102780 (fun s => s.RIP = 0x102780) (leaR64Effect 0x102780 2 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.out 0x102788 (movR32Imm32Effect 0x102788 5 1 0x1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 106) (.exec 0x102788 (fun s => s.RIP = 0x102788) (movR32Imm32Effect 0x102788 5 1 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 107) (.out 0x10278d (movR64R64Effect 0x10278d 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[90]
    (.letOp (n := 108) (.exec 0x10278d (fun s => s.RIP = 0x10278d) (movR64R64Effect 0x10278d 6 8) (Reg.operands [.gpr 8] [])) #v[90]
    (.letOp (n := 109) (.out 0x102790 (callEffect (fun _ => 0x105420) 0x102795) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 110) (.exec 0x102790 (PushPre 0x102790 5) (callEffect (fun _ => 0x105420) 0x102795) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 111) (.const ⟨64, 0x102795⟩) #v[]
    (.terminate (.call ⟨.l105420, RegMap.args [(0, 81), (1, 105), (2, 103), (3, 3), (4, 109), (5, 5), (6, 107), (7, 101), (8, 90), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 112⟩ { target := .l102795, kept := #v[], arity := rfl, guard := some (Fin.last 111) }))))))))))))))))))))))))))))))))

def bytes_l1026a6_1 : List UInt8 :=
  [0x48, 0x8D, 0x44, 0x24, 0x50, 0x48, 0x8D, 0xB4, 0x24, 0x40, 0x01, 0x00, 0x00, 0xB9, 0x0F, 0x00,
    0x00, 0x00, 0x48, 0x89, 0xC7, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xC7, 0x48, 0x89, 0xC6, 0xF3, 0x48, 0xA5, 0x4C, 0x89,
    0xBC, 0x24, 0x40, 0x01, 0x00, 0x00, 0x4C, 0x89, 0xB4, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8D,
    0x7C, 0x24, 0x48, 0x48, 0x8D, 0x94, 0x24, 0x40, 0x01, 0x00, 0x00, 0xB9, 0x01, 0x00, 0x00, 0x00,
    0x4C, 0x89, 0xC6, 0xE8, 0x8B, 0x2C, 0x00, 0x00]

theorem code_l1026a6_1 : ∀ x ∈ codeRange 0x10273d bytes_l1026a6_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x273d 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1026a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1026a6 (movR64M64Effect 0x1026a6 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1026a6 (LoadPre 0x1026a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1026a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026a6 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1026ab (movR64M64Effect 0x1026ab 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x1026ab (LoadPre 0x1026ab (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1026ab + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026ab 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x1026b0 (StorePre 0x1026b0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x1026b0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026b0 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 58) (.exec 0x1026b8 (StorePre 0x1026b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x1026b8 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026b8 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x1026c0 (movR64M64Effect 0x1026c0 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1026c0 (LoadPre 0x1026c0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1026c0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026c0 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1026c5 (StorePre 0x1026c5 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1026c5 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026c5 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1026cd (movR64M64Effect 0x1026cd 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1026cd (LoadPre 0x1026cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1026cd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1026cd 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1026d2 (StorePre 0x1026d2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x158)) s (0x1026d2 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1026d2 0 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.exec 0x1026da (StorePre 0x1026da 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1026da + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026da (.sib 4 none 0 (.d32 0xc8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x1026e6 (StorePre 0x1026e6 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x1026e6 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026e6 (.sib 4 none 0 (.d32 0xd0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1026f2 (StorePre 0x1026f2 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1026f2 + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026f2 (.sib 4 none 0 (.d32 0xd8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x1026fe (StorePre 0x1026fe 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1026fe + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x1026fe (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.out 0x10270a (movR64M64Effect 0x10270a 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 70) (.exec 0x10270a (LoadPre 0x10270a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10270a + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10270a 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.exec 0x102712 (StorePre 0x102712 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x102712 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102712 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 72) (.out 0x102716 (movR64M64Effect 0x102716 0 (.sib 4 none 0 (.d32 0xd0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 73) (.exec 0x102716 (LoadPre 0x102716 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102716 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102716 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.exec 0x10271e (StorePre 0x10271e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10271e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10271e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x102723 (movR64M64Effect 0x102723 0 (.sib 4 none 0 (.d32 0xd8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 76) (.exec 0x102723 (LoadPre 0x102723 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x102723 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102723 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.exec 0x10272b (StorePre 0x10272b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10272b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10272b 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x102730 (movR64M64Effect 0x102730 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 79) (.exec 0x102730 (LoadPre 0x102730 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x102730 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x102730 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.exec 0x102738 (StorePre 0x102738 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x102738 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x102738 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[78, 4]
    (b_l1026a6_1))))))))))))))))))))))))))))

def bytes_l1026a6 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x8B, 0x4C, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x40, 0x01,
    0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x48,
    0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24,
    0x58, 0x01, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x04, 0x24,
    0x48, 0x8B, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xE0, 0x00,
    0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18] ++ bytes_l1026a6_1

theorem code_l1026a6 : ∀ x ∈ codeRange 0x1026a6 bytes_l1026a6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x26a6 151 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1026a6_1

@[cfg_block] def b_l102795 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x102795 (cmpMImm8Effect 0x102795 5 32 (.sib 4 none 0 (.d8 0x48)) 0x1) (EffectPart.reads (.flag .ZF) [.gpr 4] []) (.flag .ZF)) #v[4]
    (.letOp (n := 54) (.exec 0x102795 (LoadPre 0x102795 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102795 + BitVec.ofNat 64 5)) 4) (cmpMImm8Effect 0x102795 5 32 (.sib 4 none 0 (.d8 0x48)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.pure (condOp 5)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l1027b7, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l10279c, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l102795 : List UInt8 :=
  [0x83, 0x7C, 0x24, 0x48, 0x01, 0x75, 0x1B]

theorem code_l102795 : ∀ x ∈ codeRange 0x102795 bytes_l102795, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2795 7 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10279c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10279c (movR64M64Effect 0x10279c 7 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10279c (LoadPre 0x10279c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10279c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10279c 7 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1027a1 (testR64R64Effect 0x1027a1 7 7) (EffectPart.reads (.flag .ZF) [.gpr 7, .gpr 7] []) (.flag .ZF)) #v[53, 53]
    (.letOp (n := 56) (.exec 0x1027a1 (fun s => s.RIP = 0x1027a1) (testR64R64Effect 0x1027a1 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[53, 53]
    (.letOp (n := 57) (.pure (condOp 4)) #v[55]
    (.terminate (.condBr (Fin.last 57) ⟨.l10281c, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ ⟨.l1027a6, RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 53), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 55), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩))))))

def bytes_l10279c : List UInt8 :=
  [0x48, 0x8B, 0x7C, 0x24, 0x50, 0x48, 0x85, 0xFF, 0x74, 0x76]

theorem code_l10279c : ∀ x ∈ codeRange 0x10279c bytes_l10279c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x279c 10 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027a6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1027a6 (movR64M64Effect 0x1027a6 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1027a6 (LoadPre 0x1027a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1027a6 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027a6 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1027ab (movR64M64Effect 0x1027ab 0 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1027ab (LoadPre 0x1027ab (fun s => AddrMode.addr (.base 0 .none) s (0x1027ab + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1027ab 0 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1027ae (testR64R64Effect 0x1027ae 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 58) (.exec 0x1027ae (fun s => s.RIP = 0x1027ae) (testR64R64Effect 0x1027ae 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 59) (.pure (condOp 4)) #v[57]
    (.terminate (.condBr (Fin.last 59) ⟨.l10281c, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ ⟨.l1027b3, RegMap.args [(0, 55), (1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (13, 13), (19, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l1027a6 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x00, 0x48, 0x85, 0xC0, 0x74, 0x69]

theorem code_l1027a6 : ∀ x ∈ codeRange 0x1027a6 bytes_l1027a6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27a6 13 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027b3 : Block Op Label signature Reg.count 53 :=
  cutBlock 0x1027b3

def bytes_l1027b3 : List UInt8 :=
  [0xFF, 0xD0]

theorem code_l1027b3 : ∀ x ∈ codeRange 0x1027b3 bytes_l1027b3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b3 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027b5 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l10281c, RegMap.args (entryMap (live .l1027b5)) 53⟩)

def bytes_l1027b5 : List UInt8 :=
  [0xEB, 0x65]

theorem code_l1027b5 : ∀ x ∈ codeRange 0x1027b5 bytes_l1027b5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x27b5 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027b7_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x10280c (StorePre 0x10280c 4 (fun s => AddrMode.addr (.base 3 (.d8 0x20)) s (0x10280c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10280c 7 (.base 3 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 90) (.exec 0x102810 (StorePre 0x102810 4 (fun s => AddrMode.addr (.base 3 (.d8 0x28)) s (0x102810 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102810 8 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 3] [])) #v[75, 3]
    (.letOp (n := 91) (.exec 0x102814 (StorePre 0x102814 4 (fun s => AddrMode.addr (.base 3 (.d8 0x30)) s (0x102814 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102814 9 (.base 3 (.d8 0x30))) (Reg.operands [.gpr 9, .gpr 3] [])) #v[79, 3]
    (.letOp (n := 92) (.exec 0x102818 (StorePre 0x102818 4 (fun s => AddrMode.addr (.base 3 (.d8 0x38)) s (0x102818 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102818 10 (.base 3 (.d8 0x38))) (Reg.operands [.gpr 10, .gpr 3] [])) #v[83, 3]
    (.terminate (.br ⟨.l10281c, RegMap.args [(0, 55), (1, 59), (2, 67), (3, 3), (4, 4), (5, 5), (6, 65), (7, 71), (8, 75), (9, 79), (10, 83), (11, 11), (13, 13), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩)))))

def bytes_l1027b7_1 : List UInt8 :=
  [0x48, 0x89, 0x7B, 0x20, 0x4C, 0x89, 0x43, 0x28, 0x4C, 0x89, 0x4B, 0x30, 0x4C, 0x89, 0x53, 0x38]

theorem code_l1027b7_1 : ∀ x ∈ codeRange 0x10280c bytes_l1027b7_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x280c 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1027b7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1027b7 (movR64M64Effect 0x1027b7 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x1027b7 (LoadPre 0x1027b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x1027b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027b7 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1027bc (bswapR64Effect 0x1027bc 3 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x1027bc (fun s => s.RIP = 0x1027bc) (bswapR64Effect 0x1027bc 3 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x1027bf (movR64M64Effect 0x1027bf 1 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x1027bf (LoadPre 0x1027bf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x1027bf + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027bf 1 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x1027c4 (bswapR64Effect 0x1027c4 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x1027c4 (fun s => s.RIP = 0x1027c4) (bswapR64Effect 0x1027c4 3 1) (Reg.operands [.gpr 1] [])) #v[57]
    (.letOp (n := 61) (.out 0x1027c7 (movR64M64Effect 0x1027c7 2 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x1027c7 (LoadPre 0x1027c7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x1027c7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027c7 2 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x1027cc (movR64M64Effect 0x1027cc 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 64) (.exec 0x1027cc (LoadPre 0x1027cc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x1027cc + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027cc 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x1027d1 (bswapR64Effect 0x1027d1 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 66) (.exec 0x1027d1 (fun s => s.RIP = 0x1027d1) (bswapR64Effect 0x1027d1 3 6) (Reg.operands [.gpr 6] [])) #v[63]
    (.letOp (n := 67) (.out 0x1027d4 (bswapR64Effect 0x1027d4 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 68) (.exec 0x1027d4 (fun s => s.RIP = 0x1027d4) (bswapR64Effect 0x1027d4 3 2) (Reg.operands [.gpr 2] [])) #v[61]
    (.letOp (n := 69) (.out 0x1027d7 (movR64M64Effect 0x1027d7 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x1027d7 (LoadPre 0x1027d7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1027d7 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027d7 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x1027df (bswapR64Effect 0x1027df 3 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[69]
    (.letOp (n := 72) (.exec 0x1027df (fun s => s.RIP = 0x1027df) (bswapR64Effect 0x1027df 3 7) (Reg.operands [.gpr 7] [])) #v[69]
    (.letOp (n := 73) (.out 0x1027e2 (movR64M64Effect 0x1027e2 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 74) (.exec 0x1027e2 (LoadPre 0x1027e2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x1027e2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1027e2 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x1027ea (bswapR64Effect 0x1027ea 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 76) (.exec 0x1027ea (fun s => s.RIP = 0x1027ea) (bswapR64Effect 0x1027ea 3 8) (Reg.operands [.gpr 8] [])) #v[73]
    (.letOp (n := 77) (.out 0x1027ed (movR64M64Effect 0x1027ed 9 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 78) (.exec 0x1027ed (LoadPre 0x1027ed (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1027ed + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027ed 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.out 0x1027f2 (bswapR64Effect 0x1027f2 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[77]
    (.letOp (n := 80) (.exec 0x1027f2 (fun s => s.RIP = 0x1027f2) (bswapR64Effect 0x1027f2 3 9) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 81) (.out 0x1027f5 (movR64M64Effect 0x1027f5 10 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 82) (.exec 0x1027f5 (LoadPre 0x1027f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x1027f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1027f5 10 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1027fa (bswapR64Effect 0x1027fa 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 84) (.exec 0x1027fa (fun s => s.RIP = 0x1027fa) (bswapR64Effect 0x1027fa 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (.letOp (n := 85) (.exec 0x1027fd (StorePre 0x1027fd 3 (fun s => AddrMode.addr (.base 3 .none) s (0x1027fd + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1027fd 0 (.base 3 .none)) (Reg.operands [.gpr 0, .gpr 3] [])) #v[55, 3]
    (.letOp (n := 86) (.exec 0x102800 (StorePre 0x102800 4 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x102800 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102800 1 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 87) (.exec 0x102804 (StorePre 0x102804 4 (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x102804 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102804 6 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 3] [])) #v[65, 3]
    (.letOp (n := 88) (.exec 0x102808 (StorePre 0x102808 4 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x102808 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x102808 2 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3] [])) #v[67, 3]
    (b_l1027b7_1))))))))))))))))))))))))))))))))))))

def bytes_l1027b7 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x68, 0x48, 0x0F, 0xC8, 0x48, 0x8B, 0x4C, 0x24, 0x60, 0x48, 0x0F, 0xC9,
    0x48, 0x8B, 0x54, 0x24, 0x50, 0x48, 0x8B, 0x74, 0x24, 0x58, 0x48, 0x0F, 0xCE, 0x48, 0x0F, 0xCA,
    0x48, 0x8B, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x0F, 0xCF, 0x4C, 0x8B, 0x84, 0x24, 0x80,
    0x00, 0x00, 0x00, 0x49, 0x0F, 0xC8, 0x4C, 0x8B, 0x4C, 0x24, 0x78, 0x49, 0x0F, 0xC9, 0x4C, 0x8B,
    0x54, 0x24, 0x70, 0x49, 0x0F, 0xCA, 0x48, 0x89, 0x03, 0x48, 0x89, 0x4B, 0x08, 0x48, 0x89, 0x73,
    0x10, 0x48, 0x89, 0x53, 0x18] ++ bytes_l1027b7_1

theorem code_l1027b7 : ∀ x ∈ codeRange 0x1027b7 bytes_l1027b7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x27b7 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1027b7_1

@[cfg_block] def b_l10281c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10281c (StorePre 0x10281c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10281c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10281c (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x102825 (StorePre 0x102825 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102825 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102825 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10282e (StorePre 0x10282e 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10282e + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10282e (.sib 4 none 0 (.d8 0x58)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x102837 (StorePre 0x102837 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102837 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102837 (.sib 4 none 0 (.d8 0x60)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x102840 (movR64M64Effect 0x102840 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x102840 (LoadPre 0x102840 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x102840 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102840 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x102845 (StorePre 0x102845 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x102845 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102845 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x10284d (movR64M64Effect 0x10284d 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 61) (.exec 0x10284d (LoadPre 0x10284d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10284d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10284d 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x102852 (StorePre 0x102852 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x102852 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x102852 0 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x10285a (movR64M64Effect 0x10285a 0 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 64) (.exec 0x10285a (LoadPre 0x10285a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10285a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10285a 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.exec 0x10285f (StorePre 0x10285f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10285f + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10285f 0 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 66) (.out 0x102867 (movR64M64Effect 0x102867 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 67) (.exec 0x102867 (LoadPre 0x102867 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x102867 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x102867 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 68) (.exec 0x10286c (StorePre 0x10286c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10286c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10286c 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[66, 4]
    (.letOp (n := 69) (.out 0x102874 (addR64Imm32Effect 0x102874 4 0x1b8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x102874 (fun s => s.RIP = 0x102874) (addR64Imm32Effect 0x102874 4 0x1b8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x10287b (popR64Effect 0x10287b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[69]
    (.letOp (n := 72) (.out 0x10287b (popR64Effect 0x10287b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x10287b (PopPre 0x10287b) (popR64Effect 0x10287b 1 3) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x10287c (popR64Effect 0x10287c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[72]
    (.letOp (n := 75) (.out 0x10287c (popR64Effect 0x10287c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x10287c (PopPre 0x10287c) (popR64Effect 0x10287c 2 12) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x10287e (popR64Effect 0x10287e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[75]
    (.letOp (n := 78) (.out 0x10287e (popR64Effect 0x10287e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x10287e (PopPre 0x10287e) (popR64Effect 0x10287e 2 14) (Reg.operands [.gpr 4] [])) #v[75]
    (.letOp (n := 80) (.out 0x102880 (popR64Effect 0x102880 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[78]
    (.letOp (n := 81) (.out 0x102880 (popR64Effect 0x102880 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[78]
    (.letOp (n := 82) (.exec 0x102880 (PopPre 0x102880) (popR64Effect 0x102880 2 15) (Reg.operands [.gpr 4] [])) #v[78]
    (.letOp (n := 83) (.out 0x102882 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[81]
    (.letOp (n := 84) (.out 0x102882 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[81]
    (.letOp (n := 85) (.exec 0x102882 (RetPre 0x102882) (retEffect) (Reg.operands [.gpr 4] [])) #v[81]
    (.terminate (.ret (RegMap.args [(0, 66), (1, 1), (2, 2), (3, 71), (4, 84), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 74), (13, 13), (14, 77), (15, 80), (22, 22), (39, 39), (50, 50), (51, 51)] 86) (some ⟨83, by decide⟩)))))))))))))))))))))))))))))))))))

def bytes_l10281c : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x60,
    0x00, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xC8, 0x00, 0x00,
    0x00, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x8B,
    0x44, 0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0xD8, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x60,
    0x48, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x81, 0xC4, 0xB8, 0x01, 0x00, 0x00, 0x5B,
    0x41, 0x5C, 0x41, 0x5E, 0x41, 0x5F, 0xC3]

theorem code_l10281c : ∀ x ∈ codeRange 0x10281c bytes_l10281c, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x281c 103 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l102883 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x102883 (StorePre 0x102883 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x102883 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x102883 (.sib 4 none 0 (.d8 0x50)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10288c (StorePre 0x10288c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10288c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10288c (.sib 4 none 0 (.d8 0x48)) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x102895 (leaR64Effect 0x102895 7 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x102895 (fun s => s.RIP = 0x102895) (leaR64Effect 0x102895 7 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10289a (callEffect (fun _ => 0x1001a0) 0x10289f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10289a (PushPre 0x10289a 5) (callEffect (fun _ => 0x1001a0) 0x10289f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10289f⟩) #v[]
    (.terminate (.call ⟨.l1001a0, RegMap.args [(2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10289f, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l102883 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x50, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x48, 0x01, 0x00,
    0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x48, 0xE8, 0x01, 0xD9, 0xFF, 0xFF]

theorem code_l102883 : ∀ x ∈ codeRange 0x102883 bytes_l102883, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x2883 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10289f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10289f (PushPre 0x10289f 5) (callEffect (fun _ => 0x100a30) 0x1028a4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.const ⟨64, 0x1028a4⟩) #v[]
    (.terminate (.call ⟨.l100a30, RegMap.args [] 55⟩ { target := .l1028a4, kept := #v[], arity := rfl, guard := some (Fin.last 54) })))

def bytes_l10289f : List UInt8 :=
  [0xE8, 0x8C, 0xE1, 0xFF, 0xFF]

theorem code_l10289f : ∀ x ∈ codeRange 0x10289f bytes_l10289f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x289f 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1028a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1028a4 (fun s => s.RIP = 0x1028a4) (fun _ => nopEffect 0x1028a4 10) (Reg.operands [] [])) #v[]
    (.letOp (n := 54) (.exec 0x1028ae (fun s => s.RIP = 0x1028ae) (fun _ => nopEffect 0x1028ae 2) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1028b0 (pushR64Effect 0x1028b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 56) (.exec 0x1028b0 (PushPre 0x1028b0 1) (pushR64Effect 0x1028b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 57) (.out 0x1028b1 (pushR64Effect 0x1028b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[55, 15]
    (.letOp (n := 58) (.exec 0x1028b1 (PushPre 0x1028b1 2) (pushR64Effect 0x1028b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[55, 15]
    (.letOp (n := 59) (.out 0x1028b3 (pushR64Effect 0x1028b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[57, 14]
    (.letOp (n := 60) (.exec 0x1028b3 (PushPre 0x1028b3 2) (pushR64Effect 0x1028b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[57, 14]
    (.letOp (n := 61) (.out 0x1028b5 (pushR64Effect 0x1028b5 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1028b5 (PushPre 0x1028b5 2) (pushR64Effect 0x1028b5 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1028b7 (pushR64Effect 0x1028b7 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1028b7 (PushPre 0x1028b7 1) (pushR64Effect 0x1028b7 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1028b8 (subR64Imm32Effect 0x1028b8 4 0x390) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1028b8 (fun s => s.RIP = 0x1028b8) (subR64Imm32Effect 0x1028b8 4 0x390) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1028bf (movR32R32Effect 0x1028bf 3 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 8] []) (.reg (.gpr 5))) #v[8]
    (.letOp (n := 68) (.exec 0x1028bf (fun s => s.RIP = 0x1028bf) (movR32R32Effect 0x1028bf 3 5 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 69) (.out 0x1028c2 (movR64R64Effect 0x1028c2 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 70) (.exec 0x1028c2 (fun s => s.RIP = 0x1028c2) (movR64R64Effect 0x1028c2 15 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x1028c5 (movR64R64Effect 0x1028c5 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 72) (.exec 0x1028c5 (fun s => s.RIP = 0x1028c5) (movR64R64Effect 0x1028c5 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x1028c8 (movR64R64Effect 0x1028c8 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 74) (.exec 0x1028c8 (fun s => s.RIP = 0x1028c8) (movR64R64Effect 0x1028c8 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 75) (.out 0x1028cb (movR64R64Effect 0x1028cb 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 76) (.exec 0x1028cb (fun s => s.RIP = 0x1028cb) (movR64R64Effect 0x1028cb 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.out 0x1028ce (movR64R64Effect 0x1028ce 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 78) (.exec 0x1028ce (fun s => s.RIP = 0x1028ce) (movR64R64Effect 0x1028ce 6 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 79) (.out 0x1028d1 (callEffect (fun _ => 0x103ac0) 0x1028d6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 80) (.exec 0x1028d1 (PushPre 0x1028d1 5) (callEffect (fun _ => 0x103ac0) 0x1028d6) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 81) (.const ⟨64, 0x1028d6⟩) #v[]
    (.terminate (.call ⟨.l103ac0, RegMap.args [(1, 1), (2, 2), (3, 73), (4, 79), (5, 67), (6, 77), (7, 75), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 71), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 82⟩ { target := .l1028d6, kept := #v[], arity := rfl, guard := some (Fin.last 81) }))))))))))))))))))))))))))))))

def bytes_l1028a4 : List UInt8 :=
  [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90, 0x55, 0x41, 0x57, 0x41,
    0x56, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x90, 0x03, 0x00, 0x00, 0x44, 0x89, 0xC5, 0x49, 0x89,
    0xD7, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x89, 0xE7, 0x48, 0x89, 0xCE, 0xE8, 0xEA, 0x11,
    0x00, 0x00]

theorem code_l1028a4 : ∀ x ∈ codeRange 0x1028a4 bytes_l1028a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x28a4 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end K256.Proofs.Signing.LIR
