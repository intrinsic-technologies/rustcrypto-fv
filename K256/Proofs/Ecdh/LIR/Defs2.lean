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

@[cfg_block] def b_l109c00_5 : Block Op Label signature Reg.count 243 :=
  .letOp (n := 243) (.out 0x109d52 (andR64R64Effect 0x109d52 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[241, 239]
    (.letOp (n := 244) (.exec 0x109d52 (fun s => s.RIP = 0x109d52) (andR64R64Effect 0x109d52 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[241, 239]
    (.letOp (n := 245) (.out 0x109d55 (xorR64R64Effect 0x109d55 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[243, 71]
    (.letOp (n := 246) (.exec 0x109d55 (fun s => s.RIP = 0x109d55) (xorR64R64Effect 0x109d55 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[243, 71]
    (.letOp (n := 247) (.exec 0x109d58 (StorePre 0x109d58 3 (fun s => AddrMode.addr (.base 7 .none) s (0x109d58 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x109d58 1 (.base 7 .none)) (Reg.operands [.gpr 1, .gpr 7] [])) #v[212, 7]
    (.letOp (n := 248) (.exec 0x109d5b (StorePre 0x109d5b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x109d5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5b 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[223, 7]
    (.letOp (n := 249) (.exec 0x109d5f (StorePre 0x109d5f 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x109d5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d5f 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[234, 7]
    (.letOp (n := 250) (.exec 0x109d63 (StorePre 0x109d63 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x109d63 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x109d63 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[245, 7]
    (.letOp (n := 251) (.out 0x109d67 (addR64Imm8Effect 0x109d67 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 252) (.exec 0x109d67 (fun s => s.RIP = 0x109d67) (addR64Imm8Effect 0x109d67 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 253) (.out 0x109d6b (popR64Effect 0x109d6b 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[251]
    (.letOp (n := 254) (.out 0x109d6b (popR64Effect 0x109d6b 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[251]
    (.letOp (n := 255) (.exec 0x109d6b (PopPre 0x109d6b) (popR64Effect 0x109d6b 1 3) (Reg.operands [.gpr 4] [])) #v[251]
    (.letOp (n := 256) (.out 0x109d6c (popR64Effect 0x109d6c 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[254]
    (.letOp (n := 257) (.out 0x109d6c (popR64Effect 0x109d6c 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[254]
    (.letOp (n := 258) (.exec 0x109d6c (PopPre 0x109d6c) (popR64Effect 0x109d6c 2 12) (Reg.operands [.gpr 4] [])) #v[254]
    (.letOp (n := 259) (.out 0x109d6e (popR64Effect 0x109d6e 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[257]
    (.letOp (n := 260) (.out 0x109d6e (popR64Effect 0x109d6e 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[257]
    (.letOp (n := 261) (.exec 0x109d6e (PopPre 0x109d6e) (popR64Effect 0x109d6e 2 13) (Reg.operands [.gpr 4] [])) #v[257]
    (.letOp (n := 262) (.out 0x109d70 (popR64Effect 0x109d70 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[260]
    (.letOp (n := 263) (.out 0x109d70 (popR64Effect 0x109d70 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[260]
    (.letOp (n := 264) (.exec 0x109d70 (PopPre 0x109d70) (popR64Effect 0x109d70 2 14) (Reg.operands [.gpr 4] [])) #v[260]
    (.letOp (n := 265) (.out 0x109d72 (popR64Effect 0x109d72 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[263]
    (.letOp (n := 266) (.out 0x109d72 (popR64Effect 0x109d72 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[263]
    (.letOp (n := 267) (.exec 0x109d72 (PopPre 0x109d72) (popR64Effect 0x109d72 2 15) (Reg.operands [.gpr 4] [])) #v[263]
    (.letOp (n := 268) (.out 0x109d74 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[266]
    (.letOp (n := 269) (.out 0x109d74 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[266]
    (.letOp (n := 270) (.exec 0x109d74 (RetPre 0x109d74) (retEffect) (Reg.operands [.gpr 4] [])) #v[266]
    (.terminate (.ret (RegMap.args [(0, 71), (1, 212), (2, 245), (3, 253), (4, 269), (5, 5), (6, 234), (7, 7), (8, 69), (9, 67), (10, 223), (11, 206), (12, 256), (13, 259), (14, 262), (15, 265), (22, 22), (39, 39), (50, 50), (51, 51)] 271) (some ⟨268, by decide⟩))))))))))))))))))))))))))))))

def bytes_l109c00_5 : List UInt8 :=
  [0x4C, 0x21, 0xFA, 0x48, 0x31, 0xC2, 0x48, 0x89, 0x0F, 0x4C, 0x89, 0x57, 0x08, 0x48, 0x89, 0x77,
    0x10, 0x48, 0x89, 0x57, 0x18, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E,
    0x41, 0x5F, 0xC3]

theorem code_l109c00_5 : ∀ x ∈ codeRange 0x109d52 bytes_l109c00_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x9d52 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l109c00_4 : Block Op Label signature Reg.count 206 :=
  .letOp (n := 206) (.out 0x109d0c (xorR64R64Effect 0x109d0c 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[77, 65]
    (.letOp (n := 207) (.exec 0x109d0c (fun s => s.RIP = 0x109d0c) (xorR64R64Effect 0x109d0c 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[77, 65]
    (.letOp (n := 208) (.out 0x109d0f (negR64Effect 0x109d0f 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[204]
    (.letOp (n := 209) (.exec 0x109d0f (fun s => s.RIP = 0x109d0f) (negR64Effect 0x109d0f 1) (Reg.operands [.gpr 1] [])) #v[204]
    (.letOp (n := 210) (.out 0x109d12 (andR64R64Effect 0x109d12 1 11) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 11] []) (.reg (.gpr 1))) #v[208, 206]
    (.letOp (n := 211) (.exec 0x109d12 (fun s => s.RIP = 0x109d12) (andR64R64Effect 0x109d12 1 11) (Reg.operands [.gpr 1, .gpr 11] [])) #v[208, 206]
    (.letOp (n := 212) (.out 0x109d15 (xorR64R64Effect 0x109d15 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[210, 65]
    (.letOp (n := 213) (.exec 0x109d15 (fun s => s.RIP = 0x109d15) (xorR64R64Effect 0x109d15 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[210, 65]
    (.letOp (n := 214) (.exec 0x109d18 (StorePre 0x109d18 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d18 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d18 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 215) (.out 0x109d1c (movzxR32M8Effect 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[63]
    (.letOp (n := 216) (.exec 0x109d1c (LoadPre 0x109d1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d1c + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x109d1c 6 10 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 217) (.out 0x109d22 (xorR64R64Effect 0x109d22 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[111, 67]
    (.letOp (n := 218) (.exec 0x109d22 (fun s => s.RIP = 0x109d22) (xorR64R64Effect 0x109d22 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[111, 67]
    (.letOp (n := 219) (.out 0x109d25 (negR64Effect 0x109d25 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[215]
    (.letOp (n := 220) (.exec 0x109d25 (fun s => s.RIP = 0x109d25) (negR64Effect 0x109d25 10) (Reg.operands [.gpr 10] [])) #v[215]
    (.letOp (n := 221) (.out 0x109d28 (andR64R64Effect 0x109d28 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[219, 217]
    (.letOp (n := 222) (.exec 0x109d28 (fun s => s.RIP = 0x109d28) (andR64R64Effect 0x109d28 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[219, 217]
    (.letOp (n := 223) (.out 0x109d2b (xorR64R64Effect 0x109d2b 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[221, 67]
    (.letOp (n := 224) (.exec 0x109d2b (fun s => s.RIP = 0x109d2b) (xorR64R64Effect 0x109d2b 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[221, 67]
    (.letOp (n := 225) (.exec 0x109d2e (StorePre 0x109d2e 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d2e + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d2e 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 226) (.out 0x109d32 (movzxR32M8Effect 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 227) (.exec 0x109d32 (LoadPre 0x109d32 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d32 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d32 5 6 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 228) (.out 0x109d37 (xorR64R64Effect 0x109d37 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[140, 69]
    (.letOp (n := 229) (.exec 0x109d37 (fun s => s.RIP = 0x109d37) (xorR64R64Effect 0x109d37 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[140, 69]
    (.letOp (n := 230) (.out 0x109d3a (negR64Effect 0x109d3a 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[226]
    (.letOp (n := 231) (.exec 0x109d3a (fun s => s.RIP = 0x109d3a) (negR64Effect 0x109d3a 6) (Reg.operands [.gpr 6] [])) #v[226]
    (.letOp (n := 232) (.out 0x109d3d (andR64R64Effect 0x109d3d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[230, 228]
    (.letOp (n := 233) (.exec 0x109d3d (fun s => s.RIP = 0x109d3d) (andR64R64Effect 0x109d3d 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[230, 228]
    (.letOp (n := 234) (.out 0x109d40 (xorR64R64Effect 0x109d40 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[232, 69]
    (.letOp (n := 235) (.exec 0x109d40 (fun s => s.RIP = 0x109d40) (xorR64R64Effect 0x109d40 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[232, 69]
    (.letOp (n := 236) (.exec 0x109d43 (StorePre 0x109d43 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d43 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109d43 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 237) (.out 0x109d47 (movzxR32M8Effect 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 238) (.exec 0x109d47 (LoadPre 0x109d47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d47 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d47 5 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 239) (.out 0x109d4c (xorR64R64Effect 0x109d4c 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[171, 71]
    (.letOp (n := 240) (.exec 0x109d4c (fun s => s.RIP = 0x109d4c) (xorR64R64Effect 0x109d4c 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[171, 71]
    (.letOp (n := 241) (.out 0x109d4f (negR64Effect 0x109d4f 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[237]
    (.letOp (n := 242) (.exec 0x109d4f (fun s => s.RIP = 0x109d4f) (negR64Effect 0x109d4f 2) (Reg.operands [.gpr 2] [])) #v[237]
    (b_l109c00_5)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_4 : List UInt8 :=
  [0x4D, 0x31, 0xD3, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xD9, 0x4C, 0x31, 0xD1, 0x88, 0x54, 0x24, 0x07,
    0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x4C, 0x31, 0xCE, 0x49, 0xF7, 0xDA, 0x49, 0x21, 0xF2, 0x4D,
    0x31, 0xCA, 0x88, 0x54, 0x24, 0x07, 0x0F, 0xB6, 0x74, 0x24, 0x07, 0x4C, 0x31, 0xC3, 0x48, 0xF7,
    0xDE, 0x48, 0x21, 0xDE, 0x4C, 0x31, 0xC6, 0x88, 0x54, 0x24, 0x07, 0x0F, 0xB6, 0x54, 0x24, 0x07,
    0x49, 0x31, 0xC7, 0x48, 0xF7, 0xDA] ++ bytes_l109c00_5

theorem code_l109c00_4 : ∀ x ∈ codeRange 0x109d0c bytes_l109c00_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9d0c 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_5

@[cfg_block] def b_l109c00_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x109cc6 (sarR64Effect 0x109cc6 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[161]
    (.letOp (n := 170) (.exec 0x109cc6 (fun s => s.RIP = 0x109cc6) (sarR64Effect 0x109cc6 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[161]
    (.letOp (n := 171) (.out 0x109cca (addR64R64Effect 0x109cca 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[169, 167]
    (.letOp (n := 172) (.exec 0x109cca (fun s => s.RIP = 0x109cca) (addR64R64Effect 0x109cca 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[169, 167]
    (.letOp (n := 173) (.out 0x109ccd (notR64Effect 0x109ccd 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[163]
    (.letOp (n := 174) (.exec 0x109ccd (fun s => s.RIP = 0x109ccd) (notR64Effect 0x109ccd 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 175) (.out 0x109cd0 (movR64R64Effect 0x109cd0 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[71]
    (.letOp (n := 176) (.exec 0x109cd0 (fun s => s.RIP = 0x109cd0) (movR64R64Effect 0x109cd0 13 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 177) (.out 0x109cd3 (andR64R64Effect 0x109cd3 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[175, 173]
    (.letOp (n := 178) (.exec 0x109cd3 (fun s => s.RIP = 0x109cd3) (andR64R64Effect 0x109cd3 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[175, 173]
    (.letOp (n := 179) (.out 0x109cd6 (orR64R64Effect 0x109cd6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[173, 71]
    (.letOp (n := 180) (.exec 0x109cd6 (fun s => s.RIP = 0x109cd6) (orR64R64Effect 0x109cd6 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[173, 71]
    (.letOp (n := 181) (.out 0x109cd9 (andR64R64Effect 0x109cd9 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[179, 171]
    (.letOp (n := 182) (.exec 0x109cd9 (fun s => s.RIP = 0x109cd9) (andR64R64Effect 0x109cd9 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[179, 171]
    (.letOp (n := 183) (.out 0x109cdc (orR64R64Effect 0x109cdc 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[181, 177]
    (.letOp (n := 184) (.exec 0x109cdc (fun s => s.RIP = 0x109cdc) (orR64R64Effect 0x109cdc 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[181, 177]
    (.letOp (n := 185) (.out 0x109cdf (shrR64Effect 0x109cdf 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[183]
    (.letOp (n := 186) (.exec 0x109cdf (fun s => s.RIP = 0x109cdf) (shrR64Effect 0x109cdf 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[183]
    (.letOp (n := 187) (.exec 0x109ce3 (StorePre 0x109ce3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109ce3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109ce3 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[185, 63]
    (.letOp (n := 188) (.out 0x109ce8 (movR64R64Effect 0x109ce8 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 189) (.exec 0x109ce8 (fun s => s.RIP = 0x109ce8) (movR64R64Effect 0x109ce8 1 9) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 190) (.out 0x109ceb (orR64R64Effect 0x109ceb 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[188, 65]
    (.letOp (n := 191) (.exec 0x109ceb (fun s => s.RIP = 0x109ceb) (orR64R64Effect 0x109ceb 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[188, 65]
    (.letOp (n := 192) (.out 0x109cee (orR64R64Effect 0x109cee 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[190, 69]
    (.letOp (n := 193) (.exec 0x109cee (fun s => s.RIP = 0x109cee) (orR64R64Effect 0x109cee 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[190, 69]
    (.letOp (n := 194) (.out 0x109cf1 (andR8Imm8Effect 0x109cf1 3 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[93]
    (.letOp (n := 195) (.exec 0x109cf1 (fun s => s.RIP = 0x109cf1) (andR8Imm8Effect 0x109cf1 3 2 0x1) (Reg.operands [.gpr 2] [])) #v[93]
    (.letOp (n := 196) (.out 0x109cf4 (orR64R64Effect 0x109cf4 1 0) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 0] []) (.flag .ZF)) #v[192, 71]
    (.letOp (n := 197) (.exec 0x109cf4 (fun s => s.RIP = 0x109cf4) (orR64R64Effect 0x109cf4 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[192, 71]
    (.letOp (n := 198) (.out 0x109cf7 (movzxR32R8Effect 0x109cf7 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[194]
    (.letOp (n := 199) (.exec 0x109cf7 (fun s => s.RIP = 0x109cf7) (movzxR32R8Effect 0x109cf7 3 2 2) (Reg.operands [.gpr 2] [])) #v[194]
    (.letOp (n := 200) (.out 0x109cfa (atFlags (condHolds 4) (cmovR32R32Effect 0x109cfa 4 2 14)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[198, 97, 196]
    (.letOp (n := 201) (.exec 0x109cfa (fun s => s.RIP = 0x109cfa) (atFlags (condHolds 4) (cmovR32R32Effect 0x109cfa 4 2 14)) (Reg.operands [.gpr 2, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[198, 97, 196]
    (.letOp (n := 202) (.exec 0x109cfe (StorePre 0x109cfe 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109cfe + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x109cfe 4 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[200, 63]
    (.letOp (n := 203) (.exec 0x109d02 (fun s => s.RIP = 0x109d02) (leaR64Effect 0x109d02 14 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 204) (.out 0x109d07 (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[63]
    (.letOp (n := 205) (.exec 0x109d07 (LoadPre 0x109d07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x109d07 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x109d07 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[63]
    (b_l109c00_4)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_3 : List UInt8 :=
  [0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x01, 0xEF, 0x48, 0xF7, 0xD1, 0x49, 0x89, 0xC5, 0x49, 0x21, 0xCD,
    0x48, 0x09, 0xC1, 0x4C, 0x21, 0xF9, 0x4C, 0x09, 0xE9, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0x4C,
    0x24, 0x08, 0x4C, 0x89, 0xC9, 0x4C, 0x09, 0xD1, 0x4C, 0x09, 0xC1, 0x80, 0xE2, 0x01, 0x48, 0x09,
    0xC1, 0x0F, 0xB6, 0xD2, 0x41, 0x0F, 0x44, 0xD6, 0x88, 0x54, 0x24, 0x07, 0x4C, 0x8D, 0x74, 0x24,
    0x07, 0x0F, 0xB6, 0x4C, 0x24, 0x07] ++ bytes_l109c00_4

theorem code_l109c00_3 : ∀ x ∈ codeRange 0x109cc6 bytes_l109c00_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9cc6 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_4

@[cfg_block] def b_l109c00_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x109c80 (subR64M64Effect 0x109c80 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[128, 63]
    (.letOp (n := 131) (.exec 0x109c80 (LoadPre 0x109c80 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c80 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c80 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[128, 63]
    (.letOp (n := 132) (.out 0x109c85 (movR64M64Effect 0x109c85 15 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1]
    (.letOp (n := 133) (.exec 0x109c85 (LoadPre 0x109c85 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x109c85 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c85 15 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 134) (.out 0x109c89 (movR64R64Effect 0x109c89 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 15] []) (.reg (.gpr 13))) #v[132]
    (.letOp (n := 135) (.exec 0x109c89 (fun s => s.RIP = 0x109c89) (movR64R64Effect 0x109c89 13 15) (Reg.operands [.gpr 15] [])) #v[132]
    (.letOp (n := 136) (.out 0x109c8c (subR64R64Effect 0x109c8c 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8] []) (.reg (.gpr 13))) #v[134, 69]
    (.letOp (n := 137) (.exec 0x109c8c (fun s => s.RIP = 0x109c8c) (subR64R64Effect 0x109c8c 13 8) (Reg.operands [.gpr 13, .gpr 8] [])) #v[134, 69]
    (.letOp (n := 138) (.out 0x109c8f (sarR64Effect 0x109c8f 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[130]
    (.letOp (n := 139) (.exec 0x109c8f (fun s => s.RIP = 0x109c8f) (sarR64Effect 0x109c8f 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130]
    (.letOp (n := 140) (.out 0x109c93 (addR64R64Effect 0x109c93 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x109c93 (fun s => s.RIP = 0x109c93) (addR64R64Effect 0x109c93 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[138, 136]
    (.letOp (n := 142) (.out 0x109c96 (notR64Effect 0x109c96 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[132]
    (.letOp (n := 143) (.exec 0x109c96 (fun s => s.RIP = 0x109c96) (notR64Effect 0x109c96 15) (Reg.operands [.gpr 15] [])) #v[132]
    (.letOp (n := 144) (.out 0x109c99 (movR64R64Effect 0x109c99 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 145) (.exec 0x109c99 (fun s => s.RIP = 0x109c99) (movR64R64Effect 0x109c99 13 8) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 146) (.out 0x109c9c (andR64R64Effect 0x109c9c 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[144, 142]
    (.letOp (n := 147) (.exec 0x109c9c (fun s => s.RIP = 0x109c9c) (andR64R64Effect 0x109c9c 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[144, 142]
    (.letOp (n := 148) (.out 0x109c9f (orR64R64Effect 0x109c9f 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[142, 69]
    (.letOp (n := 149) (.exec 0x109c9f (fun s => s.RIP = 0x109c9f) (orR64R64Effect 0x109c9f 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[142, 69]
    (.letOp (n := 150) (.out 0x109ca2 (andR64R64Effect 0x109ca2 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[148, 140]
    (.letOp (n := 151) (.exec 0x109ca2 (fun s => s.RIP = 0x109ca2) (andR64R64Effect 0x109ca2 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[148, 140]
    (.letOp (n := 152) (.out 0x109ca5 (orR64R64Effect 0x109ca5 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[150, 146]
    (.letOp (n := 153) (.exec 0x109ca5 (fun s => s.RIP = 0x109ca5) (orR64R64Effect 0x109ca5 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[150, 146]
    (.letOp (n := 154) (.out 0x109ca8 (shrR64Effect 0x109ca8 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[152]
    (.letOp (n := 155) (.exec 0x109ca8 (fun s => s.RIP = 0x109ca8) (shrR64Effect 0x109ca8 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[152]
    (.letOp (n := 156) (.exec 0x109cac (StorePre 0x109cac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cac + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109cac 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[154, 63]
    (.letOp (n := 157) (.out 0x109cb1 (movR64M64Effect 0x109cb1 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 158) (.exec 0x109cb1 (LoadPre 0x109cb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109cb1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x109cb1 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 159) (.out 0x109cb6 (xorR32R32Effect 0x109cb6 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[154, 154]
    (.letOp (n := 160) (.exec 0x109cb6 (fun s => s.RIP = 0x109cb6) (xorR32R32Effect 0x109cb6 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[154, 154]
    (.letOp (n := 161) (.out 0x109cb9 (subR64R64Effect 0x109cb9 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x109cb9 (fun s => s.RIP = 0x109cb9) (subR64R64Effect 0x109cb9 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[159, 157]
    (.letOp (n := 163) (.out 0x109cbc (movR64M64Effect 0x109cbc 1 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 164) (.exec 0x109cbc (LoadPre 0x109cbc (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x109cbc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109cbc 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 165) (.out 0x109cc0 (movR64R64Effect 0x109cc0 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[163]
    (.letOp (n := 166) (.exec 0x109cc0 (fun s => s.RIP = 0x109cc0) (movR64R64Effect 0x109cc0 13 1) (Reg.operands [.gpr 1] [])) #v[163]
    (.letOp (n := 167) (.out 0x109cc3 (subR64R64Effect 0x109cc3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[165, 71]
    (.letOp (n := 168) (.exec 0x109cc3 (fun s => s.RIP = 0x109cc3) (subR64R64Effect 0x109cc3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[165, 71]
    (b_l109c00_3)))))))))))))))))))))))))))))))))))))))

def bytes_l109c00_2 : List UInt8 :=
  [0x48, 0x2B, 0x5C, 0x24, 0x08, 0x4C, 0x8B, 0x79, 0x10, 0x4D, 0x89, 0xFD, 0x4D, 0x29, 0xC5, 0x48,
    0xC1, 0xFB, 0x3F, 0x4C, 0x01, 0xEB, 0x49, 0xF7, 0xD7, 0x4D, 0x89, 0xC5, 0x4D, 0x21, 0xFD, 0x4D,
    0x09, 0xC7, 0x49, 0x21, 0xDF, 0x4D, 0x09, 0xEF, 0x49, 0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24,
    0x08, 0x4C, 0x8B, 0x6C, 0x24, 0x08, 0x45, 0x31, 0xFF, 0x4D, 0x29, 0xEF, 0x48, 0x8B, 0x49, 0x18,
    0x49, 0x89, 0xCD, 0x49, 0x29, 0xC5] ++ bytes_l109c00_3

theorem code_l109c00_2 : ∀ x ∈ codeRange 0x109c80 bytes_l109c00_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c80 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_3

@[cfg_block] def b_l109c00_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x109c3b (xorR8M8Effect 0x109c3b 3 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 6]
    (.letOp (n := 94) (.exec 0x109c3b (LoadPre 0x109c3b (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x109c3b + BitVec.ofNat 64 3)) 1) (xorR8M8Effect 0x109c3b 3 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 6]
    (.letOp (n := 95) (.exec 0x109c3e (StorePre 0x109c3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c3e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c3e 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[91, 63]
    (.letOp (n := 96) (.exec 0x109c43 (fun s => s.RIP = 0x109c43) (leaR64Effect 0x109c43 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 97) (.out 0x109c48 (xorR32R32Effect 0x109c48 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[83, 83]
    (.letOp (n := 98) (.exec 0x109c48 (fun s => s.RIP = 0x109c48) (xorR32R32Effect 0x109c48 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[83, 83]
    (.letOp (n := 99) (.out 0x109c4b (xorR32R32Effect 0x109c4b 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 100) (.exec 0x109c4b (fun s => s.RIP = 0x109c4b) (xorR32R32Effect 0x109c4b 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 101) (.out 0x109c4d (subR64M64Effect 0x109c4d 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[99, 63]
    (.letOp (n := 102) (.exec 0x109c4d (LoadPre 0x109c4d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c4d + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x109c4d 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[99, 63]
    (.letOp (n := 103) (.out 0x109c52 (movR64M64Effect 0x109c52 3 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 104) (.exec 0x109c52 (LoadPre 0x109c52 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x109c52 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c52 3 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 105) (.out 0x109c56 (movR64R64Effect 0x109c56 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[103]
    (.letOp (n := 106) (.exec 0x109c56 (fun s => s.RIP = 0x109c56) (movR64R64Effect 0x109c56 15 3) (Reg.operands [.gpr 3] [])) #v[103]
    (.letOp (n := 107) (.out 0x109c59 (subR64R64Effect 0x109c59 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[105, 67]
    (.letOp (n := 108) (.exec 0x109c59 (fun s => s.RIP = 0x109c59) (subR64R64Effect 0x109c59 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[105, 67]
    (.letOp (n := 109) (.out 0x109c5c (sarR64Effect 0x109c5c 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[101]
    (.letOp (n := 110) (.exec 0x109c5c (fun s => s.RIP = 0x109c5c) (sarR64Effect 0x109c5c 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 111) (.out 0x109c60 (addR64R64Effect 0x109c60 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[109, 107]
    (.letOp (n := 112) (.exec 0x109c60 (fun s => s.RIP = 0x109c60) (addR64R64Effect 0x109c60 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[109, 107]
    (.letOp (n := 113) (.out 0x109c63 (notR64Effect 0x109c63 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[103]
    (.letOp (n := 114) (.exec 0x109c63 (fun s => s.RIP = 0x109c63) (notR64Effect 0x109c63 3) (Reg.operands [.gpr 3] [])) #v[103]
    (.letOp (n := 115) (.out 0x109c66 (movR64R64Effect 0x109c66 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 116) (.exec 0x109c66 (fun s => s.RIP = 0x109c66) (movR64R64Effect 0x109c66 15 9) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 117) (.out 0x109c69 (andR64R64Effect 0x109c69 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x109c69 (fun s => s.RIP = 0x109c69) (andR64R64Effect 0x109c69 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x109c6c (orR64R64Effect 0x109c6c 3 9) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 9] []) (.reg (.gpr 3))) #v[113, 67]
    (.letOp (n := 120) (.exec 0x109c6c (fun s => s.RIP = 0x109c6c) (orR64R64Effect 0x109c6c 3 9) (Reg.operands [.gpr 3, .gpr 9] [])) #v[113, 67]
    (.letOp (n := 121) (.out 0x109c6f (andR64R64Effect 0x109c6f 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[119, 111]
    (.letOp (n := 122) (.exec 0x109c6f (fun s => s.RIP = 0x109c6f) (andR64R64Effect 0x109c6f 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[119, 111]
    (.letOp (n := 123) (.out 0x109c72 (orR64R64Effect 0x109c72 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[121, 117]
    (.letOp (n := 124) (.exec 0x109c72 (fun s => s.RIP = 0x109c72) (orR64R64Effect 0x109c72 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[121, 117]
    (.letOp (n := 125) (.out 0x109c75 (shrR64Effect 0x109c75 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 126) (.exec 0x109c75 (fun s => s.RIP = 0x109c75) (shrR64Effect 0x109c75 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[123]
    (.letOp (n := 127) (.exec 0x109c79 (StorePre 0x109c79 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x109c79 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x109c79 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[125, 63]
    (.letOp (n := 128) (.out 0x109c7e (xorR32R32Effect 0x109c7e 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[125, 125]
    (.letOp (n := 129) (.exec 0x109c7e (fun s => s.RIP = 0x109c7e) (xorR32R32Effect 0x109c7e 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[125, 125]
    (b_l109c00_2)))))))))))))))))))))))))))))))))))))

def bytes_l109c00_1 : List UInt8 :=
  [0x32, 0x56, 0x20, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x4C, 0x8D, 0x64, 0x24, 0x08, 0x45, 0x31, 0xF6,
    0x31, 0xF6, 0x48, 0x2B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x59, 0x08, 0x49, 0x89, 0xDF, 0x4D, 0x29,
    0xCF, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xCF, 0x49, 0x21,
    0xDF, 0x4C, 0x09, 0xCB, 0x48, 0x21, 0xF3, 0x4C, 0x09, 0xFB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89,
    0x5C, 0x24, 0x08, 0x31, 0xDB] ++ bytes_l109c00_2

theorem code_l109c00_1 : ∀ x ∈ codeRange 0x109c3b bytes_l109c00_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c3b 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_2

@[cfg_block] def b_l109c00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x109c00 (pushR64Effect 0x109c00 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x109c00 (PushPre 0x109c00 2) (pushR64Effect 0x109c00 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x109c02 (pushR64Effect 0x109c02 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x109c02 (PushPre 0x109c02 2) (pushR64Effect 0x109c02 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x109c04 (pushR64Effect 0x109c04 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x109c04 (PushPre 0x109c04 2) (pushR64Effect 0x109c04 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x109c06 (pushR64Effect 0x109c06 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x109c06 (PushPre 0x109c06 2) (pushR64Effect 0x109c06 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x109c08 (pushR64Effect 0x109c08 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x109c08 (PushPre 0x109c08 1) (pushR64Effect 0x109c08 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x109c09 (subR64Imm8Effect 0x109c09 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x109c09 (fun s => s.RIP = 0x109c09) (subR64Imm8Effect 0x109c09 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.out 0x109c0d (movR64M64Effect 0x109c0d 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 66) (.exec 0x109c0d (LoadPre 0x109c0d (fun s => AddrMode.addr (.base 6 .none) s (0x109c0d + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c0d 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x109c10 (movR64M64Effect 0x109c10 9 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 68) (.exec 0x109c10 (LoadPre 0x109c10 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x109c10 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c10 9 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x109c14 (movR64M64Effect 0x109c14 8 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x109c14 (LoadPre 0x109c14 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x109c14 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c14 8 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x109c18 (movR64M64Effect 0x109c18 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 72) (.exec 0x109c18 (LoadPre 0x109c18 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x109c18 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x109c18 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x109c1c (movR64M64Effect 0x109c1c 3 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[1]
    (.letOp (n := 74) (.exec 0x109c1c (LoadPre 0x109c1c (fun s => AddrMode.addr (.base 1 .none) s (0x109c1c + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x109c1c 3 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 75) (.out 0x109c1f (movR64R64Effect 0x109c1f 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[73]
    (.letOp (n := 76) (.exec 0x109c1f (fun s => s.RIP = 0x109c1f) (movR64R64Effect 0x109c1f 11 3) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 77) (.out 0x109c22 (subR64R64Effect 0x109c22 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[75, 65]
    (.letOp (n := 78) (.exec 0x109c22 (fun s => s.RIP = 0x109c22) (subR64R64Effect 0x109c22 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[75, 65]
    (.letOp (n := 79) (.out 0x109c25 (notR64Effect 0x109c25 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[73]
    (.letOp (n := 80) (.exec 0x109c25 (fun s => s.RIP = 0x109c25) (notR64Effect 0x109c25 3) (Reg.operands [.gpr 3] [])) #v[73]
    (.letOp (n := 81) (.out 0x109c28 (movR64R64Effect 0x109c28 14 10) (EffectPart.reads (.reg (.gpr 14)) [.gpr 10] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 82) (.exec 0x109c28 (fun s => s.RIP = 0x109c28) (movR64R64Effect 0x109c28 14 10) (Reg.operands [.gpr 10] [])) #v[65]
    (.letOp (n := 83) (.out 0x109c2b (andR64R64Effect 0x109c2b 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[81, 79]
    (.letOp (n := 84) (.exec 0x109c2b (fun s => s.RIP = 0x109c2b) (andR64R64Effect 0x109c2b 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[81, 79]
    (.letOp (n := 85) (.out 0x109c2e (orR64R64Effect 0x109c2e 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[79, 65]
    (.letOp (n := 86) (.exec 0x109c2e (fun s => s.RIP = 0x109c2e) (orR64R64Effect 0x109c2e 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[79, 65]
    (.letOp (n := 87) (.out 0x109c31 (andR64R64Effect 0x109c31 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[85, 77]
    (.letOp (n := 88) (.exec 0x109c31 (fun s => s.RIP = 0x109c31) (andR64R64Effect 0x109c31 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[85, 77]
    (.letOp (n := 89) (.out 0x109c34 (orR64R64Effect 0x109c34 3 14) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14] []) (.reg (.gpr 3))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x109c34 (fun s => s.RIP = 0x109c34) (orR64R64Effect 0x109c34 3 14) (Reg.operands [.gpr 3, .gpr 14] [])) #v[87, 83]
    (.letOp (n := 91) (.out 0x109c37 (shrR64Effect 0x109c37 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[89]
    (.letOp (n := 92) (.exec 0x109c37 (fun s => s.RIP = 0x109c37) (shrR64Effect 0x109c37 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (b_l109c00_1))))))))))))))))))))))))))))))))))))))))

def bytes_l109c00 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B, 0x16,
    0x4C, 0x8B, 0x4E, 0x08, 0x4C, 0x8B, 0x46, 0x10, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x8B, 0x19, 0x49,
    0x89, 0xDB, 0x4D, 0x29, 0xD3, 0x48, 0xF7, 0xD3, 0x4D, 0x89, 0xD6, 0x49, 0x21, 0xDE, 0x4C, 0x09,
    0xD3, 0x4C, 0x21, 0xDB, 0x4C, 0x09, 0xF3, 0x48, 0xC1, 0xEB, 0x3F] ++ bytes_l109c00_1

theorem code_l109c00 : ∀ x ∈ codeRange 0x109c00 bytes_l109c00, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x9c00 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l109c00_1

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

end K256.Proofs.Ecdh.LIR
