import AesGcm.Proofs.Machine.Instructions.Memory16
import AesGcm.Proofs.Machine.Instructions.HighByteStore
import AesGcm.Proofs.Machine.LIR.Labels
import AesGcm.Proofs.Copied.X86Proofs.CFG.EvalAttr
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Footprints

namespace AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Instructions
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift

@[cfg_block] def b_l105636_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x105719 (xorR32R32Effect 0x105719 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[0, 164]
    (.letOp (n := 167) (.exec 0x105719 (fun s => s.RIP = 0x105719) (xorR32R32Effect 0x105719 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 164]
    (.letOp (n := 168) (.out 0x10571b (shlR32Effect 0x10571b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[164]
    (.letOp (n := 169) (.exec 0x10571b (fun s => s.RIP = 0x10571b) (shlR32Effect 0x10571b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 170) (.out 0x10571e (xorR32R32Effect 0x10571e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[168, 166]
    (.letOp (n := 171) (.exec 0x10571e (fun s => s.RIP = 0x10571e) (xorR32R32Effect 0x10571e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[168, 166]
    (.letOp (n := 172) (.exec 0x105720 (StorePre 0x105720 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105720 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105720 5 1 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 173) (.out 0x105725 (movR64R64Effect 0x105725 15 4) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 174) (.exec 0x105725 (fun s => s.RIP = 0x105725) (movR64R64Effect 0x105725 15 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 175) (.out 0x105728 (movR32Imm32Effect 0x105728 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 176) (.exec 0x105728 (fun s => s.RIP = 0x105728) (movR32Imm32Effect 0x105728 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 177) (.out 0x10572d (movR64R64Effect 0x10572d 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[173]
    (.letOp (n := 178) (.exec 0x10572d (fun s => s.RIP = 0x10572d) (movR64R64Effect 0x10572d 7 15) (Reg.operands [.gpr 15] [])) #v[173]
    (.letOp (n := 179) (.out 0x105730 (callEffect (fun _ => 0x100b10) 0x105735) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 180) (.exec 0x105730 (PushPre 0x105730 5) (callEffect (fun _ => 0x100b10) 0x105735) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 181) (.const ⟨64, 0x105735⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 166), (1, 170), (2, 155), (3, 3), (4, 179), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)] 182⟩ { target := .l105735, kept := #v[], arity := rfl, guard := some (Fin.last 181) })))))))))))))))))

def bytes_l105636_3 : List UInt8 :=
  [0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x0E, 0x49, 0x89, 0xE7, 0xBE,
    0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8, 0xDB, 0xB3, 0xFF, 0xFF]

theorem code_l105636_3 : ∀ x ∈ codeRange 0x105719 bytes_l105636_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5719 28 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105636_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x1056d7 (movzxR32R16Effect 0x1056d7 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 129) (.exec 0x1056d7 (fun s => s.RIP = 0x1056d7) (movzxR32R16Effect 0x1056d7 3 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 130) (.out 0x1056da (shrR32Effect 0x1056da 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[128]
    (.letOp (n := 131) (.exec 0x1056da (fun s => s.RIP = 0x1056da) (shrR32Effect 0x1056da 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 132) (.out 0x1056dd (xorR32R32Effect 0x1056dd 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[130, 2]
    (.letOp (n := 133) (.exec 0x1056dd (fun s => s.RIP = 0x1056dd) (xorR32R32Effect 0x1056dd 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[130, 2]
    (.letOp (n := 134) (.out 0x1056df (andR32Imm32Effect 0x1056df 6 6 0x3030) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[132]
    (.letOp (n := 135) (.exec 0x1056df (fun s => s.RIP = 0x1056df) (andR32Imm32Effect 0x1056df 6 6 0x3030) (Reg.operands [.gpr 6] [])) #v[132]
    (.letOp (n := 136) (.out 0x1056e5 (xorR32R32Effect 0x1056e5 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 134]
    (.letOp (n := 137) (.exec 0x1056e5 (fun s => s.RIP = 0x1056e5) (xorR32R32Effect 0x1056e5 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 134]
    (.letOp (n := 138) (.out 0x1056e7 (shlR32Effect 0x1056e7 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[134]
    (.letOp (n := 139) (.exec 0x1056e7 (fun s => s.RIP = 0x1056e7) (shlR32Effect 0x1056e7 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 140) (.out 0x1056ea (xorR32R32Effect 0x1056ea 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x1056ea (fun s => s.RIP = 0x1056ea) (xorR32R32Effect 0x1056ea 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[138, 136]
    (.letOp (n := 142) (.exec 0x1056ec (StorePre 0x1056ec 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1056ec + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1056ec 5 6 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[140, 4]
    (.letOp (n := 143) (.out 0x1056f1 (movzxR32R16Effect 0x1056f1 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 144) (.exec 0x1056f1 (fun s => s.RIP = 0x1056f1) (movzxR32R16Effect 0x1056f1 3 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 145) (.out 0x1056f4 (shrR32Effect 0x1056f4 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[143]
    (.letOp (n := 146) (.exec 0x1056f4 (fun s => s.RIP = 0x1056f4) (shrR32Effect 0x1056f4 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x1056f7 (xorR32R32Effect 0x1056f7 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[145, 1]
    (.letOp (n := 148) (.exec 0x1056f7 (fun s => s.RIP = 0x1056f7) (xorR32R32Effect 0x1056f7 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[145, 1]
    (.letOp (n := 149) (.out 0x1056f9 (andR32Imm32Effect 0x1056f9 6 2 0x3030) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 150) (.exec 0x1056f9 (fun s => s.RIP = 0x1056f9) (andR32Imm32Effect 0x1056f9 6 2 0x3030) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x1056ff (xorR32R32Effect 0x1056ff 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1, 149]
    (.letOp (n := 152) (.exec 0x1056ff (fun s => s.RIP = 0x1056ff) (xorR32R32Effect 0x1056ff 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 149]
    (.letOp (n := 153) (.out 0x105701 (shlR32Effect 0x105701 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[149]
    (.letOp (n := 154) (.exec 0x105701 (fun s => s.RIP = 0x105701) (shlR32Effect 0x105701 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 155) (.out 0x105704 (xorR32R32Effect 0x105704 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[153, 151]
    (.letOp (n := 156) (.exec 0x105704 (fun s => s.RIP = 0x105704) (xorR32R32Effect 0x105704 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[153, 151]
    (.letOp (n := 157) (.exec 0x105706 (StorePre 0x105706 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105706 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105706 5 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[155, 4]
    (.letOp (n := 158) (.out 0x10570b (movzxR32R16Effect 0x10570b 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 159) (.exec 0x10570b (fun s => s.RIP = 0x10570b) (movzxR32R16Effect 0x10570b 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 160) (.out 0x10570e (shrR32Effect 0x10570e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[158]
    (.letOp (n := 161) (.exec 0x10570e (fun s => s.RIP = 0x10570e) (shrR32Effect 0x10570e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[158]
    (.letOp (n := 162) (.out 0x105711 (xorR32R32Effect 0x105711 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[160, 0]
    (.letOp (n := 163) (.exec 0x105711 (fun s => s.RIP = 0x105711) (xorR32R32Effect 0x105711 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[160, 0]
    (.letOp (n := 164) (.out 0x105713 (andR32Imm32Effect 0x105713 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x105713 (fun s => s.RIP = 0x105713) (andR32Imm32Effect 0x105713 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[162]
    (b_l105636_3))))))))))))))))))))))))))))))))))))))

def bytes_l105636_2 : List UInt8 :=
  [0x0F, 0xB7, 0xF2, 0xC1, 0xEE, 0x02, 0x31, 0xD6, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00, 0x31, 0xF2,
    0xC1, 0xE6, 0x02, 0x31, 0xD6, 0x66, 0x89, 0x74, 0x24, 0x0A, 0x0F, 0xB7, 0xD1, 0xC1, 0xEA, 0x02,
    0x31, 0xCA, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA, 0x66,
    0x89, 0x54, 0x24, 0x0C, 0x0F, 0xB7, 0xC8, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30,
    0x00, 0x00] ++ bytes_l105636_3

theorem code_l105636_2 : ∀ x ∈ codeRange 0x1056d7 bytes_l105636_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x56d7 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105636_3

@[cfg_block] def b_l105636_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10568b (xorR32R32Effect 0x10568b 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[8, 89]
    (.letOp (n := 92) (.exec 0x10568b (fun s => s.RIP = 0x10568b) (xorR32R32Effect 0x10568b 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[8, 89]
    (.letOp (n := 93) (.out 0x10568e (shlR32Effect 0x10568e 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[89]
    (.letOp (n := 94) (.exec 0x10568e (fun s => s.RIP = 0x10568e) (shlR32Effect 0x10568e 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 95) (.out 0x105692 (xorR32R32Effect 0x105692 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[93, 91]
    (.letOp (n := 96) (.exec 0x105692 (fun s => s.RIP = 0x105692) (xorR32R32Effect 0x105692 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[93, 91]
    (.letOp (n := 97) (.exec 0x105695 (StorePre 0x105695 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105695 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105695 6 9 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x10569b (movzxR32R16Effect 0x10569b 4 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 99) (.exec 0x10569b (fun s => s.RIP = 0x10569b) (movzxR32R16Effect 0x10569b 4 8 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 100) (.out 0x10569f (shrR32Effect 0x10569f 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[98]
    (.letOp (n := 101) (.exec 0x10569f (fun s => s.RIP = 0x10569f) (shrR32Effect 0x10569f 4 8 2) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x1056a3 (xorR32R32Effect 0x1056a3 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[100, 7]
    (.letOp (n := 103) (.exec 0x1056a3 (fun s => s.RIP = 0x1056a3) (xorR32R32Effect 0x1056a3 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[100, 7]
    (.letOp (n := 104) (.out 0x1056a6 (andR32Imm32Effect 0x1056a6 7 8 0x3030) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[102]
    (.letOp (n := 105) (.exec 0x1056a6 (fun s => s.RIP = 0x1056a6) (andR32Imm32Effect 0x1056a6 7 8 0x3030) (Reg.operands [.gpr 8] [])) #v[102]
    (.letOp (n := 106) (.out 0x1056ad (xorR32R32Effect 0x1056ad 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[7, 104]
    (.letOp (n := 107) (.exec 0x1056ad (fun s => s.RIP = 0x1056ad) (xorR32R32Effect 0x1056ad 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 104]
    (.letOp (n := 108) (.out 0x1056b0 (shlR32Effect 0x1056b0 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[104]
    (.letOp (n := 109) (.exec 0x1056b0 (fun s => s.RIP = 0x1056b0) (shlR32Effect 0x1056b0 4 8 2) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[104]
    (.letOp (n := 110) (.out 0x1056b4 (xorR32R32Effect 0x1056b4 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[108, 106]
    (.letOp (n := 111) (.exec 0x1056b4 (fun s => s.RIP = 0x1056b4) (xorR32R32Effect 0x1056b4 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[108, 106]
    (.letOp (n := 112) (.exec 0x1056b7 (StorePre 0x1056b7 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x1056b7 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1056b7 6 8 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[110, 4]
    (.letOp (n := 113) (.out 0x1056bd (movzxR32R16Effect 0x1056bd 3 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 114) (.exec 0x1056bd (fun s => s.RIP = 0x1056bd) (movzxR32R16Effect 0x1056bd 3 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 115) (.out 0x1056c0 (shrR32Effect 0x1056c0 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[113]
    (.letOp (n := 116) (.exec 0x1056c0 (fun s => s.RIP = 0x1056c0) (shrR32Effect 0x1056c0 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x1056c3 (xorR32R32Effect 0x1056c3 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[115, 6]
    (.letOp (n := 118) (.exec 0x1056c3 (fun s => s.RIP = 0x1056c3) (xorR32R32Effect 0x1056c3 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[115, 6]
    (.letOp (n := 119) (.out 0x1056c5 (andR32Imm32Effect 0x1056c5 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[117]
    (.letOp (n := 120) (.exec 0x1056c5 (fun s => s.RIP = 0x1056c5) (andR32Imm32Effect 0x1056c5 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[117]
    (.letOp (n := 121) (.out 0x1056cb (xorR32R32Effect 0x1056cb 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[6, 119]
    (.letOp (n := 122) (.exec 0x1056cb (fun s => s.RIP = 0x1056cb) (xorR32R32Effect 0x1056cb 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 119]
    (.letOp (n := 123) (.out 0x1056cd (shlR32Effect 0x1056cd 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 124) (.exec 0x1056cd (fun s => s.RIP = 0x1056cd) (shlR32Effect 0x1056cd 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 125) (.out 0x1056d0 (xorR32R32Effect 0x1056d0 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x1056d0 (fun s => s.RIP = 0x1056d0) (xorR32R32Effect 0x1056d0 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[123, 121]
    (.letOp (n := 127) (.exec 0x1056d2 (StorePre 0x1056d2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1056d2 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1056d2 5 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[125, 4]
    (b_l105636_2)))))))))))))))))))))))))))))))))))))

def bytes_l105636_1 : List UInt8 :=
  [0x45, 0x31, 0xC8, 0x41, 0xC1, 0xE1, 0x02, 0x45, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x04,
    0x44, 0x0F, 0xB7, 0xC7, 0x41, 0xC1, 0xE8, 0x02, 0x41, 0x31, 0xF8, 0x41, 0x81, 0xE0, 0x30, 0x30,
    0x00, 0x00, 0x44, 0x31, 0xC7, 0x41, 0xC1, 0xE0, 0x02, 0x41, 0x31, 0xF8, 0x66, 0x44, 0x89, 0x44,
    0x24, 0x06, 0x0F, 0xB7, 0xFE, 0xC1, 0xEF, 0x02, 0x31, 0xF7, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00,
    0x31, 0xFE, 0xC1, 0xE7, 0x02, 0x31, 0xF7, 0x66, 0x89, 0x7C, 0x24, 0x08] ++ bytes_l105636_2

theorem code_l105636_1 : ∀ x ∈ codeRange 0x10568b bytes_l105636_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x568b 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105636_2

@[cfg_block] def b_l105636 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105636 (movzxR32R16Effect 0x105636 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x105636 (fun s => s.RIP = 0x105636) (movzxR32R16Effect 0x105636 4 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x10563a (shrR32Effect 0x10563a 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 56) (.exec 0x10563a (fun s => s.RIP = 0x10563a) (shrR32Effect 0x10563a 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x10563e (xorR32R32Effect 0x10563e 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[55, 10]
    (.letOp (n := 58) (.exec 0x10563e (fun s => s.RIP = 0x10563e) (xorR32R32Effect 0x10563e 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[55, 10]
    (.letOp (n := 59) (.out 0x105641 (andR32Imm32Effect 0x105641 7 11 0x3030) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x105641 (fun s => s.RIP = 0x105641) (andR32Imm32Effect 0x105641 7 11 0x3030) (Reg.operands [.gpr 11] [])) #v[57]
    (.letOp (n := 61) (.out 0x105648 (xorR32R32Effect 0x105648 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[10, 59]
    (.letOp (n := 62) (.exec 0x105648 (fun s => s.RIP = 0x105648) (xorR32R32Effect 0x105648 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 59]
    (.letOp (n := 63) (.out 0x10564b (shlR32Effect 0x10564b 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[59]
    (.letOp (n := 64) (.exec 0x10564b (fun s => s.RIP = 0x10564b) (shlR32Effect 0x10564b 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 65) (.out 0x10564f (xorR32R32Effect 0x10564f 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x10564f (fun s => s.RIP = 0x10564f) (xorR32R32Effect 0x10564f 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[63, 61]
    (.letOp (n := 67) (.exec 0x105652 (StorePre 0x105652 5 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105652 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105652 5 11 (.sib 4 none 0 .none)) (Reg.operands [.gpr 11, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x105657 (movzxR32R16Effect 0x105657 4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 69) (.exec 0x105657 (fun s => s.RIP = 0x105657) (movzxR32R16Effect 0x105657 4 10 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 70) (.out 0x10565b (shrR32Effect 0x10565b 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[68]
    (.letOp (n := 71) (.exec 0x10565b (fun s => s.RIP = 0x10565b) (shrR32Effect 0x10565b 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x10565f (xorR32R32Effect 0x10565f 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[70, 9]
    (.letOp (n := 73) (.exec 0x10565f (fun s => s.RIP = 0x10565f) (xorR32R32Effect 0x10565f 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[70, 9]
    (.letOp (n := 74) (.out 0x105662 (andR32Imm32Effect 0x105662 7 10 0x3030) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[72]
    (.letOp (n := 75) (.exec 0x105662 (fun s => s.RIP = 0x105662) (andR32Imm32Effect 0x105662 7 10 0x3030) (Reg.operands [.gpr 10] [])) #v[72]
    (.letOp (n := 76) (.out 0x105669 (xorR32R32Effect 0x105669 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[9, 74]
    (.letOp (n := 77) (.exec 0x105669 (fun s => s.RIP = 0x105669) (xorR32R32Effect 0x105669 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 74]
    (.letOp (n := 78) (.out 0x10566c (shlR32Effect 0x10566c 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[74]
    (.letOp (n := 79) (.exec 0x10566c (fun s => s.RIP = 0x10566c) (shlR32Effect 0x10566c 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 80) (.out 0x105670 (xorR32R32Effect 0x105670 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[78, 76]
    (.letOp (n := 81) (.exec 0x105670 (fun s => s.RIP = 0x105670) (xorR32R32Effect 0x105670 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[78, 76]
    (.letOp (n := 82) (.exec 0x105673 (StorePre 0x105673 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x105673 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x105673 6 10 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x105679 (movzxR32R16Effect 0x105679 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 84) (.exec 0x105679 (fun s => s.RIP = 0x105679) (movzxR32R16Effect 0x105679 4 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 85) (.out 0x10567d (shrR32Effect 0x10567d 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[83]
    (.letOp (n := 86) (.exec 0x10567d (fun s => s.RIP = 0x10567d) (shrR32Effect 0x10567d 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x105681 (xorR32R32Effect 0x105681 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[85, 8]
    (.letOp (n := 88) (.exec 0x105681 (fun s => s.RIP = 0x105681) (xorR32R32Effect 0x105681 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[85, 8]
    (.letOp (n := 89) (.out 0x105684 (andR32Imm32Effect 0x105684 7 9 0x3030) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[87]
    (.letOp (n := 90) (.exec 0x105684 (fun s => s.RIP = 0x105684) (andR32Imm32Effect 0x105684 7 9 0x3030) (Reg.operands [.gpr 9] [])) #v[87]
    (b_l105636_1))))))))))))))))))))))))))))))))))))))

def bytes_l105636 : List UInt8 :=
  [0x45, 0x0F, 0xB7, 0xDA, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x30, 0x30,
    0x00, 0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x66, 0x44, 0x89, 0x1C,
    0x24, 0x45, 0x0F, 0xB7, 0xD1, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41, 0x81, 0xE2, 0x30,
    0x30, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA, 0x66, 0x44, 0x89,
    0x54, 0x24, 0x02, 0x45, 0x0F, 0xB7, 0xC8, 0x41, 0xC1, 0xE9, 0x02, 0x45, 0x31, 0xC1, 0x41, 0x81,
    0xE1, 0x30, 0x30, 0x00, 0x00] ++ bytes_l105636_1

theorem code_l105636 : ∀ x ∈ codeRange 0x105636 bytes_l105636, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5636 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105636_1

@[cfg_block] def b_l105735_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x1057a6 (movR64R64Effect 0x1057a6 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 86) (.exec 0x1057a6 (fun s => s.RIP = 0x1057a6) (movR64R64Effect 0x1057a6 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 87) (.out 0x1057a9 (callEffect (fun _ => 0x109d90) 0x1057ae) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x1057a9 (PushPre 0x1057a9 5) (callEffect (fun _ => 0x109d90) 0x1057ae) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x1057ae⟩) #v[]
    (.terminate (.call ⟨.l109d90, RegMap.args [(0, 76), (1, 53), (2, 79), (3, 81), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l1057ae, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))

def bytes_l105735_1 : List UInt8 :=
  [0x4C, 0x89, 0xFE, 0xE8, 0xE2, 0x45, 0x00, 0x00]

theorem code_l105735_1 : ∀ x ∈ codeRange 0x1057a6 bytes_l105735_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x57a6 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105735 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105735 (movR64M64Effect 0x105735 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x105735 (LoadPre 0x105735 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105735 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x105735 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10573a (movzxR32M16Effect 0x10573a 7 0 (.base 1 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x10573a (LoadPre 0x10573a (fun s => AddrMode.addr (.base 1 (.d32 0xa0)) s (0x10573a + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10573a 7 0 (.base 1 (.d32 0xa0))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.exec 0x105741 (StorePre 0x105741 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x105741 + BitVec.ofNat 64 4)) 2) (xorMREffect 0x105741 4 16 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x105745 (movzxR32M16Effect 0x105745 7 0 (.base 1 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x105745 (LoadPre 0x105745 (fun s => AddrMode.addr (.base 1 (.d32 0xa2)) s (0x105745 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105745 7 0 (.base 1 (.d32 0xa2))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 60) (.exec 0x10574c (StorePre 0x10574c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x10574c + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10574c 5 16 0 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x105751 (movzxR32M16Effect 0x105751 7 0 (.base 1 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x105751 (LoadPre 0x105751 (fun s => AddrMode.addr (.base 1 (.d32 0xa4)) s (0x105751 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105751 7 0 (.base 1 (.d32 0xa4))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 63) (.exec 0x105758 (StorePre 0x105758 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x105758 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105758 5 16 0 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x10575d (movzxR32M16Effect 0x10575d 7 0 (.base 1 (.d32 0xa6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x10575d (LoadPre 0x10575d (fun s => AddrMode.addr (.base 1 (.d32 0xa6)) s (0x10575d + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10575d 7 0 (.base 1 (.d32 0xa6))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 66) (.exec 0x105764 (StorePre 0x105764 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x105764 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105764 5 16 0 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x105769 (movzxR32M16Effect 0x105769 7 0 (.base 1 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x105769 (LoadPre 0x105769 (fun s => AddrMode.addr (.base 1 (.d32 0xa8)) s (0x105769 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105769 7 0 (.base 1 (.d32 0xa8))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 69) (.exec 0x105770 (StorePre 0x105770 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x105770 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105770 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x105775 (movzxR32M16Effect 0x105775 7 0 (.base 1 (.d32 0xaa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 71) (.exec 0x105775 (LoadPre 0x105775 (fun s => AddrMode.addr (.base 1 (.d32 0xaa)) s (0x105775 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105775 7 0 (.base 1 (.d32 0xaa))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 72) (.exec 0x10577c (StorePre 0x10577c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x10577c + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10577c 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x105781 (movzxR32M16Effect 0x105781 7 0 (.base 1 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 74) (.exec 0x105781 (LoadPre 0x105781 (fun s => AddrMode.addr (.base 1 (.d32 0xac)) s (0x105781 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x105781 7 0 (.base 1 (.d32 0xac))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 75) (.exec 0x105788 (StorePre 0x105788 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x105788 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105788 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x10578d (movzxR32M16Effect 0x10578d 7 0 (.base 1 (.d32 0xae))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 77) (.exec 0x10578d (LoadPre 0x10578d (fun s => AddrMode.addr (.base 1 (.d32 0xae)) s (0x10578d + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10578d 7 0 (.base 1 (.d32 0xae))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 78) (.exec 0x105794 (StorePre 0x105794 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x105794 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x105794 5 16 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x105799 (movR32Imm32Effect 0x105799 5 2 0x8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x105799 (fun s => s.RIP = 0x105799) (movR32Imm32Effect 0x105799 5 2 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x10579e (movR64M64Effect 0x10579e 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 82) (.exec 0x10579e (LoadPre 0x10579e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10579e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10579e 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x1057a3 (movR64R64Effect 0x1057a3 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[81]
    (.letOp (n := 84) (.exec 0x1057a3 (fun s => s.RIP = 0x1057a3) (movR64R64Effect 0x1057a3 7 3) (Reg.operands [.gpr 3] [])) #v[81]
    (b_l105735_1))))))))))))))))))))))))))))))))

def bytes_l105735 : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x28, 0x0F, 0xB7, 0x81, 0xA0, 0x00, 0x00, 0x00, 0x66, 0x31, 0x04, 0x24,
    0x0F, 0xB7, 0x81, 0xA2, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x02, 0x0F, 0xB7, 0x81, 0xA4,
    0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x04, 0x0F, 0xB7, 0x81, 0xA6, 0x00, 0x00, 0x00, 0x66,
    0x31, 0x44, 0x24, 0x06, 0x0F, 0xB7, 0x81, 0xA8, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x08,
    0x0F, 0xB7, 0x81, 0xAA, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x0A, 0x0F, 0xB7, 0x81, 0xAC,
    0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x0C, 0x0F, 0xB7, 0x81, 0xAE, 0x00, 0x00, 0x00, 0x66,
    0x31, 0x44, 0x24, 0x0E, 0xBA, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x30, 0x48, 0x89,
    0xDF] ++ bytes_l105735_1

theorem code_l105735 : ∀ x ∈ codeRange 0x105735 bytes_l105735, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5735 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l105735_1

@[cfg_block] def b_l1057ae : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1057ae (movR64R64Effect 0x1057ae 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x1057ae (fun s => s.RIP = 0x1057ae) (movR64R64Effect 0x1057ae 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x1057b1 (addR64Imm8Effect 0x1057b1 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x1057b1 (fun s => s.RIP = 0x1057b1) (addR64Imm8Effect 0x1057b1 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x1057b5 (popR64Effect 0x1057b5 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x1057b5 (popR64Effect 0x1057b5 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x1057b5 (PopPre 0x1057b5) (popR64Effect 0x1057b5 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x1057b6 (popR64Effect 0x1057b6 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x1057b6 (popR64Effect 0x1057b6 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x1057b6 (PopPre 0x1057b6) (popR64Effect 0x1057b6 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x1057b8 (popR64Effect 0x1057b8 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x1057b8 (popR64Effect 0x1057b8 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x1057b8 (PopPre 0x1057b8) (popR64Effect 0x1057b8 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x1057ba (popR64Effect 0x1057ba 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x1057ba (popR64Effect 0x1057ba 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x1057ba (PopPre 0x1057ba) (popR64Effect 0x1057ba 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x1057bc (popR64Effect 0x1057bc 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x1057bc (popR64Effect 0x1057bc 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x1057bc (PopPre 0x1057bc) (popR64Effect 0x1057bc 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x1057be (popR64Effect 0x1057be 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x1057be (popR64Effect 0x1057be 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x1057be (PopPre 0x1057be) (popR64Effect 0x1057be 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x1057bf (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x1057bf (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x1057bf (RetPre 0x1057bf) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l1057ae : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l1057ae : ∀ x ∈ codeRange 0x1057ae bytes_l1057ae, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x57ae 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1057c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1057c0 (pushR64Effect 0x1057c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1057c0 (PushPre 0x1057c0 1) (pushR64Effect 0x1057c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1057c1 (pushR64Effect 0x1057c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1057c1 (PushPre 0x1057c1 2) (pushR64Effect 0x1057c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1057c3 (pushR64Effect 0x1057c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1057c3 (PushPre 0x1057c3 2) (pushR64Effect 0x1057c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1057c5 (pushR64Effect 0x1057c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1057c5 (PushPre 0x1057c5 2) (pushR64Effect 0x1057c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1057c7 (pushR64Effect 0x1057c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1057c7 (PushPre 0x1057c7 2) (pushR64Effect 0x1057c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1057c9 (pushR64Effect 0x1057c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1057c9 (PushPre 0x1057c9 1) (pushR64Effect 0x1057c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1057ca (subR64Imm32Effect 0x1057ca 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1057ca (fun s => s.RIP = 0x1057ca) (subR64Imm32Effect 0x1057ca 4 0x138) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1057d1 (movR64R64Effect 0x1057d1 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 6] []) (.reg (.gpr 12))) #v[6]
    (.letOp (n := 68) (.exec 0x1057d1 (fun s => s.RIP = 0x1057d1) (movR64R64Effect 0x1057d1 12 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x1057d4 (StorePre 0x1057d4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x1057d4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057d4 7 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.out 0x1057dc (leaR64Effect 0x1057dc 14 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 71) (.exec 0x1057dc (fun s => s.RIP = 0x1057dc) (leaR64Effect 0x1057dc 14 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.out 0x1057e1 (movR32Imm32Effect 0x1057e1 5 2 0xf0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 73) (.exec 0x1057e1 (fun s => s.RIP = 0x1057e1) (movR32Imm32Effect 0x1057e1 5 2 0xf0) (Reg.operands [] [])) #v[]
    (.letOp (n := 74) (.out 0x1057e6 (movR64R64Effect 0x1057e6 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[70]
    (.letOp (n := 75) (.exec 0x1057e6 (fun s => s.RIP = 0x1057e6) (movR64R64Effect 0x1057e6 7 14) (Reg.operands [.gpr 14] [])) #v[70]
    (.letOp (n := 76) (.out 0x1057e9 (xorR32R32Effect 0x1057e9 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 77) (.exec 0x1057e9 (fun s => s.RIP = 0x1057e9) (xorR32R32Effect 0x1057e9 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 78) (.out 0x1057eb (callEffect (callMemPtr 0x1057eb (.rip 0xfba37)) (0x1057eb + BitVec.ofNat 64 (callMemLen (.rip 0xfba37)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 79) (.exec 0x1057eb (GoesTo (CallMemPre 0x1057eb (.rip 0xfba37)) (callEffect (callMemPtr 0x1057eb (.rip 0xfba37)) (0x1057eb + BitVec.ofNat 64 (callMemLen (.rip 0xfba37)))) 0x103eb0) (callEffect (callMemPtr 0x1057eb (.rip 0xfba37)) (0x1057eb + BitVec.ofNat 64 (callMemLen (.rip 0xfba37)))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 80) (.const ⟨64, 0x1057f1⟩) #v[]
    (.terminate (.call ⟨.l103eb0, RegMap.args [(2, 72), (3, 3), (4, 78), (5, 5), (6, 76), (7, 74), (9, 9), (11, 11), (12, 67), (13, 13), (14, 70), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 81⟩ { target := .l1057f1, kept := #v[], arity := rfl, guard := some (Fin.last 80) })))))))))))))))))))))))))))))

def bytes_l1057c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x38, 0x01, 0x00,
    0x00, 0x49, 0x89, 0xF4, 0x48, 0x89, 0xBC, 0x24, 0x30, 0x01, 0x00, 0x00, 0x4C, 0x8D, 0x74, 0x24,
    0x0C, 0xBA, 0xF0, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x31, 0xF6, 0xFF, 0x15, 0x37, 0xBA, 0x0F,
    0x00]

theorem code_l1057c0 : ∀ x ∈ codeRange 0x1057c0 bytes_l1057c0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x57c0 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1057f1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1057f1 (movR64M64Effect 0x1057f1 0 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 54) (.exec 0x1057f1 (LoadPre 0x1057f1 (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1057f1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1057f1 0 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1057f5 (movR64M64Effect 0x1057f5 1 (.sib 12 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 56) (.exec 0x1057f5 (LoadPre 0x1057f5 (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x8)) s (0x1057f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1057f5 1 (.sib 12 none 0 (.d8 0x8))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.exec 0x1057fa (StorePre 0x1057fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x1057fa + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1057fa 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.exec 0x105802 (StorePre 0x105802 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x105802 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105802 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 59) (.out 0x10580a (movR32Imm32Effect 0x10580a 6 15 0x8) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 60) (.exec 0x10580a (fun s => s.RIP = 0x10580a) (movR32Imm32Effect 0x10580a 6 15 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x105810 (leaR64Effect 0x105810 2 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x105810 (fun s => s.RIP = 0x105810) (leaR64Effect 0x105810 2 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x105818 (movR32Imm32Effect 0x105818 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 64) (.exec 0x105818 (fun s => s.RIP = 0x105818) (movR32Imm32Effect 0x105818 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x10581d (movR64R64Effect 0x10581d 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 66) (.exec 0x10581d (fun s => s.RIP = 0x10581d) (movR64R64Effect 0x10581d 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 67) (.out 0x105820 (callEffect (fun _ => 0x109ff0) 0x105825) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 68) (.exec 0x105820 (PushPre 0x105820 5) (callEffect (fun _ => 0x109ff0) 0x105825) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 69) (.const ⟨64, 0x105825⟩) #v[]
    (.terminate (.call ⟨.l109ff0, RegMap.args [(0, 53), (1, 55), (2, 61), (3, 3), (4, 67), (5, 5), (6, 63), (7, 65), (12, 12), (13, 13), (14, 14), (15, 59), (22, 22), (39, 39), (50, 50), (51, 51)] 70⟩ { target := .l105825, kept := #v[], arity := rfl, guard := some (Fin.last 69) }))))))))))))))))))

def bytes_l1057f1 : List UInt8 :=
  [0x49, 0x8B, 0x04, 0x24, 0x49, 0x8B, 0x4C, 0x24, 0x08, 0x48, 0x89, 0x8C, 0x24, 0x28, 0x01, 0x00,
    0x00, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x41, 0xBF, 0x08, 0x00, 0x00, 0x00, 0x48,
    0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0xE8,
    0xCB, 0x47, 0x00, 0x00]

theorem code_l1057f1 : ∀ x ∈ codeRange 0x1057f1 bytes_l1057f1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x57f1 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105825 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105825 (leaR64Effect 0x105825 7 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x105825 (fun s => s.RIP = 0x105825) (leaR64Effect 0x105825 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10582a (movR64M64Effect 0x10582a 0 (.sib 12 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 56) (.exec 0x10582a (LoadPre 0x10582a (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x10)) s (0x10582a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10582a 0 (.sib 12 none 0 (.d8 0x10))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x10582f (movR64M64Effect 0x10582f 1 (.sib 12 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 58) (.exec 0x10582f (LoadPre 0x10582f (fun s => AddrMode.addr (.sib 12 none 0 (.d8 0x18)) s (0x10582f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10582f 1 (.sib 12 none 0 (.d8 0x18))) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 59) (.exec 0x105834 (StorePre 0x105834 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x128)) s (0x105834 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x105834 1 (.sib 4 none 0 (.d32 0x128))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.exec 0x10583c (StorePre 0x10583c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x120)) s (0x10583c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10583c 0 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 61) (.out 0x105844 (leaR64Effect 0x105844 2 (.sib 4 none 0 (.d32 0x120))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 62) (.exec 0x105844 (fun s => s.RIP = 0x105844) (leaR64Effect 0x105844 2 (.sib 4 none 0 (.d32 0x120))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10584c (movR32Imm32Effect 0x10584c 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 64) (.exec 0x10584c (fun s => s.RIP = 0x10584c) (movR32Imm32Effect 0x10584c 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x105851 (callEffect (fun _ => 0x109ff0) 0x105856) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 66) (.exec 0x105851 (PushPre 0x105851 5) (callEffect (fun _ => 0x109ff0) 0x105856) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.const ⟨64, 0x105856⟩) #v[]
    (.terminate (.call ⟨.l109ff0, RegMap.args [(0, 55), (1, 57), (2, 61), (3, 3), (4, 65), (5, 5), (6, 63), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 68⟩ { target := .l105856, kept := #v[], arity := rfl, guard := some (Fin.last 67) }))))))))))))))))

def bytes_l105825 : List UInt8 :=
  [0x48, 0x8D, 0x7C, 0x24, 0x1C, 0x49, 0x8B, 0x44, 0x24, 0x10, 0x49, 0x8B, 0x4C, 0x24, 0x18, 0x48,
    0x89, 0x8C, 0x24, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x20, 0x01, 0x00, 0x00, 0x48,
    0x8D, 0x94, 0x24, 0x20, 0x01, 0x00, 0x00, 0xBE, 0x08, 0x00, 0x00, 0x00, 0xE8, 0x9A, 0x47, 0x00,
    0x00]

theorem code_l105825 : ∀ x ∈ codeRange 0x105825 bytes_l105825, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5825 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105856 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105856 (movR32Imm32Effect 0x105856 5 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [] []) (.reg (.gpr 3))) #v[]
    (.letOp (n := 54) (.exec 0x105856 (fun s => s.RIP = 0x105856) (movR32Imm32Effect 0x105856 5 3 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x10585b (movR32Imm32Effect 0x10585b 6 12 0x30) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 56) (.exec 0x10585b (fun s => s.RIP = 0x10585b) (movR32Imm32Effect 0x10585b 6 12 0x30) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x105861 (movR32Imm32Effect 0x105861 6 13 0x20) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 58) (.exec 0x105861 (fun s => s.RIP = 0x105861) (movR32Imm32Effect 0x105861 6 13 0x20) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.exec 0x105867 (fun s => s.RIP = 0x105867) (fun _ => nopEffect 0x105867 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l105870, RegMap.args [(0, 0), (1, 1), (3, 53), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 55), (13, 57), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩))))))))

def bytes_l105856 : List UInt8 :=
  [0xBB, 0x20, 0x00, 0x00, 0x00, 0x41, 0xBC, 0x30, 0x00, 0x00, 0x00, 0x41, 0xBD, 0x20, 0x00, 0x00,
    0x00, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l105856 : ∀ x ∈ codeRange 0x105856 bytes_l105856, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5856 26 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105870 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105870 (movR32Imm32Effect 0x105870 5 6 0x78) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x105870 (fun s => s.RIP = 0x105870) (movR32Imm32Effect 0x105870 5 6 0x78) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x105875 (movR64R64Effect 0x105875 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x105875 (fun s => s.RIP = 0x105875) (movR64R64Effect 0x105875 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x105878 (movR64R64Effect 0x105878 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x105878 (fun s => s.RIP = 0x105878) (movR64R64Effect 0x105878 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10587b (callEffect (fun _ => 0x103f30) 0x105880) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10587b (PushPre 0x10587b 5) (callEffect (fun _ => 0x103f30) 0x105880) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105880⟩) #v[]
    (.terminate (.call ⟨.l103f30, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105880, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105870 : List UInt8 :=
  [0xBE, 0x78, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0xE8, 0xB0, 0xE6, 0xFF, 0xFF]

theorem code_l105870 : ∀ x ∈ codeRange 0x105870 bytes_l105870, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5870 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105880 (leaR64Effect 0x105880 7 (.sib 4 (some 3) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 3] []) (.reg (.gpr 7))) #v[4, 3]
    (.letOp (n := 54) (.exec 0x105880 (fun s => s.RIP = 0x105880) (leaR64Effect 0x105880 7 (.sib 4 (some 3) 0 .none)) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.out 0x105884 (addR64Imm8Effect 0x105884 7 0xc) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x105884 (fun s => s.RIP = 0x105884) (addR64Imm8Effect 0x105884 7 0xc) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x105888 (movR32Imm32Effect 0x105888 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x105888 (fun s => s.RIP = 0x105888) (movR32Imm32Effect 0x105888 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x10588d (callEffect (fun _ => 0x100b10) 0x105892) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x10588d (PushPre 0x10588d 5) (callEffect (fun _ => 0x100b10) 0x105892) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x105892⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l105892, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l105880 : List UInt8 :=
  [0x48, 0x8D, 0x3C, 0x1C, 0x48, 0x83, 0xC7, 0x0C, 0xBE, 0x08, 0x00, 0x00, 0x00, 0xE8, 0x7E, 0xB2,
    0xFF, 0xFF]

theorem code_l105880 : ∀ x ∈ codeRange 0x105880 bytes_l105880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5880 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105892 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x105892 (StorePre 0x105892 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0xc)) s (0x105892 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105892 5 16 (.sib 4 (some 3) 0 (.d8 0xc))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 54) (.exec 0x105897 (StorePre 0x105897 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0xe)) s (0x105897 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105897 5 16 (.sib 4 (some 3) 0 (.d8 0xe))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.exec 0x10589c (StorePre 0x10589c 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x16)) s (0x10589c + BitVec.ofNat 64 5)) 2) (notMEffect 0x10589c 5 16 (.sib 4 (some 3) 0 (.d8 0x16))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 56) (.exec 0x1058a1 (StorePre 0x1058a1 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x18)) s (0x1058a1 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058a1 5 16 (.sib 4 (some 3) 0 (.d8 0x18))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 57) (.exec 0x1058a6 (StorePre 0x1058a6 6 (fun s => AddrMode.addr (.sib 4 (some 13) 0 (.d8 0xc)) s (0x1058a6 + BitVec.ofNat 64 6)) 1) (xorM8Imm8Effect 0x1058a6 6 (.sib 4 (some 13) 0 (.d8 0xc)) 0x80) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 58) (.out 0x1058ac (addR64Imm8Effect 0x1058ac 15 0x8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 59) (.exec 0x1058ac (fun s => s.RIP = 0x1058ac) (addR64Imm8Effect 0x1058ac 15 0x8) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 60) (.out 0x1058b0 (movR32Imm32Effect 0x1058b0 5 6 0x78) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 61) (.exec 0x1058b0 (fun s => s.RIP = 0x1058b0) (movR32Imm32Effect 0x1058b0 5 6 0x78) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.out 0x1058b5 (movR32Imm32Effect 0x1058b5 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 63) (.exec 0x1058b5 (fun s => s.RIP = 0x1058b5) (movR32Imm32Effect 0x1058b5 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x1058ba (movR64R64Effect 0x1058ba 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 65) (.exec 0x1058ba (fun s => s.RIP = 0x1058ba) (movR64R64Effect 0x1058ba 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 66) (.out 0x1058bd (movR64R64Effect 0x1058bd 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[58]
    (.letOp (n := 67) (.exec 0x1058bd (fun s => s.RIP = 0x1058bd) (movR64R64Effect 0x1058bd 2 15) (Reg.operands [.gpr 15] [])) #v[58]
    (.letOp (n := 68) (.out 0x1058c0 (movR32Imm32Effect 0x1058c0 6 8 0x7) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 69) (.exec 0x1058c0 (fun s => s.RIP = 0x1058c0) (movR32Imm32Effect 0x1058c0 6 8 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x1058c6 (callEffect (fun _ => 0x104010) 0x1058cb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 71) (.exec 0x1058c6 (PushPre 0x1058c6 5) (callEffect (fun _ => 0x104010) 0x1058cb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 72) (.const ⟨64, 0x1058cb⟩) #v[]
    (.terminate (.call ⟨.l104010, RegMap.args [(0, 0), (1, 62), (2, 66), (3, 3), (4, 70), (5, 5), (6, 60), (7, 64), (8, 68), (11, 11), (12, 12), (13, 13), (14, 14), (15, 58), (22, 22), (39, 39), (50, 50), (51, 51)] 73⟩ { target := .l1058cb, kept := #v[], arity := rfl, guard := some (Fin.last 72) })))))))))))))))))))))

def bytes_l105892 : List UInt8 :=
  [0x66, 0xF7, 0x54, 0x1C, 0x0C, 0x66, 0xF7, 0x54, 0x1C, 0x0E, 0x66, 0xF7, 0x54, 0x1C, 0x16, 0x66,
    0xF7, 0x54, 0x1C, 0x18, 0x42, 0x80, 0x74, 0x2C, 0x0C, 0x80, 0x49, 0x83, 0xC7, 0x08, 0xBE, 0x78,
    0x00, 0x00, 0x00, 0xB9, 0x10, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0x41, 0xB8,
    0x07, 0x00, 0x00, 0x00, 0xE8, 0x45, 0xE7, 0xFF, 0xFF]

theorem code_l105892 : ∀ x ∈ codeRange 0x105892 bytes_l105892, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5892 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1058cb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1058cb (cmpR64Imm32Effect 0x1058cb 13 0xec) (EffectPart.reads (.flag .ZF) [.gpr 13] []) (.flag .ZF)) #v[13]
    (.letOp (n := 54) (.exec 0x1058cb (fun s => s.RIP = 0x1058cb) (cmpR64Imm32Effect 0x1058cb 13 0xec) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.pure (condOp 4)) #v[53]
    (.terminate (.condBr (Fin.last 55) ⟨.l10593a, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩ ⟨.l1058d4, RegMap.args [(0, 0), (1, 1), (3, 3), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l1058cb : List UInt8 :=
  [0x49, 0x81, 0xFD, 0xEC, 0x00, 0x00, 0x00, 0x74, 0x66]

theorem code_l1058cb : ∀ x ∈ codeRange 0x1058cb bytes_l1058cb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x58cb 9 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1058d4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1058d4 (movR32Imm32Effect 0x1058d4 5 6 0x78) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x1058d4 (fun s => s.RIP = 0x1058d4) (movR32Imm32Effect 0x1058d4 5 6 0x78) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1058d9 (movR64R64Effect 0x1058d9 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 56) (.exec 0x1058d9 (fun s => s.RIP = 0x1058d9) (movR64R64Effect 0x1058d9 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 57) (.out 0x1058dc (movR64R64Effect 0x1058dc 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[15]
    (.letOp (n := 58) (.exec 0x1058dc (fun s => s.RIP = 0x1058dc) (movR64R64Effect 0x1058dc 2 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x1058df (callEffect (fun _ => 0x103f30) 0x1058e4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1058df (PushPre 0x1058df 5) (callEffect (fun _ => 0x103f30) 0x1058e4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1058e4⟩) #v[]
    (.terminate (.call ⟨.l103f30, RegMap.args [(0, 0), (1, 1), (2, 57), (3, 3), (4, 59), (5, 5), (6, 53), (7, 55), (8, 8), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1058e4, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1058d4 : List UInt8 :=
  [0xBE, 0x78, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0xE8, 0x4C, 0xE6, 0xFF, 0xFF]

theorem code_l1058d4 : ∀ x ∈ codeRange 0x1058d4 bytes_l1058d4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x58d4 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1058e4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1058e4 (leaR64Effect 0x1058e4 7 (.sib 4 (some 12) 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4, .gpr 12] []) (.reg (.gpr 7))) #v[4, 12]
    (.letOp (n := 54) (.exec 0x1058e4 (fun s => s.RIP = 0x1058e4) (leaR64Effect 0x1058e4 7 (.sib 4 (some 12) 0 .none)) (Reg.operands [.gpr 4, .gpr 12] [])) #v[4, 12]
    (.letOp (n := 55) (.out 0x1058e8 (addR64Imm8Effect 0x1058e8 7 0xc) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x1058e8 (fun s => s.RIP = 0x1058e8) (addR64Imm8Effect 0x1058e8 7 0xc) (Reg.operands [.gpr 7] [])) #v[53]
    (.letOp (n := 57) (.out 0x1058ec (movR32Imm32Effect 0x1058ec 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 58) (.exec 0x1058ec (fun s => s.RIP = 0x1058ec) (movR32Imm32Effect 0x1058ec 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 59) (.out 0x1058f1 (callEffect (fun _ => 0x100b10) 0x1058f6) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x1058f1 (PushPre 0x1058f1 5) (callEffect (fun _ => 0x100b10) 0x1058f6) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x1058f6⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(3, 3), (4, 59), (5, 5), (6, 57), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l1058f6, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l1058e4 : List UInt8 :=
  [0x4A, 0x8D, 0x3C, 0x24, 0x48, 0x83, 0xC7, 0x0C, 0xBE, 0x08, 0x00, 0x00, 0x00, 0xE8, 0x1A, 0xB2,
    0xFF, 0xFF]

theorem code_l1058e4 : ∀ x ∈ codeRange 0x1058e4 bytes_l1058e4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x58e4 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1058f6 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1058f6 (StorePre 0x1058f6 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x1c)) s (0x1058f6 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058f6 5 16 (.sib 4 (some 3) 0 (.d8 0x1c))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 54) (.exec 0x1058fb (StorePre 0x1058fb 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x1e)) s (0x1058fb + BitVec.ofNat 64 5)) 2) (notMEffect 0x1058fb 5 16 (.sib 4 (some 3) 0 (.d8 0x1e))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 55) (.exec 0x105900 (StorePre 0x105900 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x26)) s (0x105900 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105900 5 16 (.sib 4 (some 3) 0 (.d8 0x26))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 56) (.exec 0x105905 (StorePre 0x105905 5 (fun s => AddrMode.addr (.sib 4 (some 3) 0 (.d8 0x28)) s (0x105905 + BitVec.ofNat 64 5)) 2) (notMEffect 0x105905 5 16 (.sib 4 (some 3) 0 (.d8 0x28))) (Reg.operands [.gpr 4, .gpr 3] [])) #v[4, 3]
    (.letOp (n := 57) (.out 0x10590a (addR64Imm8Effect 0x10590a 15 0x8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[15]
    (.letOp (n := 58) (.exec 0x10590a (fun s => s.RIP = 0x10590a) (addR64Imm8Effect 0x10590a 15 0x8) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10590e (movR32Imm32Effect 0x10590e 5 6 0x78) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x10590e (fun s => s.RIP = 0x10590e) (movR32Imm32Effect 0x10590e 5 6 0x78) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.out 0x105913 (movR32Imm32Effect 0x105913 5 1 0x10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 62) (.exec 0x105913 (fun s => s.RIP = 0x105913) (movR32Imm32Effect 0x105913 5 1 0x10) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x105918 (movR64R64Effect 0x105918 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 64) (.exec 0x105918 (fun s => s.RIP = 0x105918) (movR64R64Effect 0x105918 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 65) (.out 0x10591b (movR64R64Effect 0x10591b 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 66) (.exec 0x10591b (fun s => s.RIP = 0x10591b) (movR64R64Effect 0x10591b 2 15) (Reg.operands [.gpr 15] [])) #v[57]
    (.letOp (n := 67) (.out 0x10591e (movR32Imm32Effect 0x10591e 6 8 0x3) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 68) (.exec 0x10591e (fun s => s.RIP = 0x10591e) (movR32Imm32Effect 0x10591e 6 8 0x3) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x105924 (callEffect (fun _ => 0x104010) 0x105929) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 70) (.exec 0x105924 (PushPre 0x105924 5) (callEffect (fun _ => 0x104010) 0x105929) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.const ⟨64, 0x105929⟩) #v[]
    (.terminate (.call ⟨.l104010, RegMap.args [(0, 0), (1, 61), (2, 65), (3, 3), (4, 69), (5, 5), (6, 59), (7, 63), (8, 67), (11, 11), (12, 12), (13, 13), (14, 14), (15, 57), (22, 22), (39, 39), (50, 50), (51, 51)] 72⟩ { target := .l105929, kept := #v[], arity := rfl, guard := some (Fin.last 71) }))))))))))))))))))))

def bytes_l1058f6 : List UInt8 :=
  [0x66, 0xF7, 0x54, 0x1C, 0x1C, 0x66, 0xF7, 0x54, 0x1C, 0x1E, 0x66, 0xF7, 0x54, 0x1C, 0x26, 0x66,
    0xF7, 0x54, 0x1C, 0x28, 0x49, 0x83, 0xC7, 0x08, 0xBE, 0x78, 0x00, 0x00, 0x00, 0xB9, 0x10, 0x00,
    0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xFA, 0x41, 0xB8, 0x03, 0x00, 0x00, 0x00, 0xE8, 0xE7,
    0xE6, 0xFF, 0xFF]

theorem code_l1058f6 : ∀ x ∈ codeRange 0x1058f6 bytes_l1058f6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x58f6 51 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l105929 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x105929 (addR64Imm8Effect 0x105929 13 0x22) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 54) (.exec 0x105929 (fun s => s.RIP = 0x105929) (addR64Imm8Effect 0x105929 13 0x22) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x10592d (addR64Imm8Effect 0x10592d 3 0x20) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 56) (.exec 0x10592d (fun s => s.RIP = 0x10592d) (addR64Imm8Effect 0x10592d 3 0x20) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.out 0x105931 (addR64Imm8Effect 0x105931 12 0x20) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[12]
    (.letOp (n := 58) (.exec 0x105931 (fun s => s.RIP = 0x105931) (addR64Imm8Effect 0x105931 12 0x20) (Reg.operands [.gpr 12] [])) #v[12]
    (.terminate (.br ⟨.l105870, RegMap.args [(0, 0), (1, 1), (3, 55), (4, 4), (5, 5), (8, 8), (9, 9), (11, 11), (12, 57), (13, 53), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 59⟩)))))))

def bytes_l105929 : List UInt8 :=
  [0x49, 0x83, 0xC5, 0x22, 0x48, 0x83, 0xC3, 0x20, 0x49, 0x83, 0xC4, 0x20, 0xE9, 0x36, 0xFF, 0xFF,
    0xFF]

theorem code_l105929 : ∀ x ∈ codeRange 0x105929 bytes_l105929, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x5929 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10593a_59 : Block Op Label signature Reg.count 2295 :=
  .letOp (n := 2295) (.exec 0x1068ef (StorePre 0x1068ef 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe6)) s (0x1068ef + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1068ef 9 9 (.sib 4 none 0 (.d32 0xe6))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2293, 4]
    (.letOp (n := 2296) (.out 0x1068f8 (notR32Effect 0x1068f8 2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2285]
    (.letOp (n := 2297) (.exec 0x1068f8 (fun s => s.RIP = 0x1068f8) (notR32Effect 0x1068f8 2 1) (Reg.operands [.gpr 1] [])) #v[2285]
    (.letOp (n := 2298) (.exec 0x1068fa (StorePre 0x1068fa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1068fa + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1068fa 8 1 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[2296, 4]
    (.letOp (n := 2299) (.exec 0x106902 (StorePre 0x106902 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xec)) s (0x106902 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106902 8 16 (.sib 4 none 0 (.d32 0xec))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2300) (.exec 0x10690a (StorePre 0x10690a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xee)) s (0x10690a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10690a 8 16 (.sib 4 none 0 (.d32 0xee))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2301) (.exec 0x106912 (StorePre 0x106912 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf6)) s (0x106912 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106912 8 16 (.sib 4 none 0 (.d32 0xf6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2302) (.exec 0x10691a (StorePre 0x10691a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10691a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10691a 8 16 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2303) (.out 0x106922 (leaR64Effect 0x106922 6 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2304) (.exec 0x106922 (fun s => s.RIP = 0x106922) (leaR64Effect 0x106922 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2305) (.out 0x106927 (movR32Imm32Effect 0x106927 5 2 0xf0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 2306) (.exec 0x106927 (fun s => s.RIP = 0x106927) (movR32Imm32Effect 0x106927 5 2 0xf0) (Reg.operands [] [])) #v[]
    (.letOp (n := 2307) (.out 0x10692c (movR64M64Effect 0x10692c 3 (.sib 4 none 0 (.d32 0x130))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 2308) (.exec 0x10692c (LoadPre 0x10692c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x130)) s (0x10692c + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10692c 3 (.sib 4 none 0 (.d32 0x130))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2309) (.out 0x106934 (movR64R64Effect 0x106934 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[2307]
    (.letOp (n := 2310) (.exec 0x106934 (fun s => s.RIP = 0x106934) (movR64R64Effect 0x106934 7 3) (Reg.operands [.gpr 3] [])) #v[2307]
    (.letOp (n := 2311) (.out 0x106937 (callEffect (callMemPtr 0x106937 (.rip 0xfa8cb)) (0x106937 + BitVec.ofNat 64 (callMemLen (.rip 0xfa8cb)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 2312) (.exec 0x106937 (GoesTo (CallMemPre 0x106937 (.rip 0xfa8cb)) (callEffect (callMemPtr 0x106937 (.rip 0xfa8cb)) (0x106937 + BitVec.ofNat 64 (callMemLen (.rip 0xfa8cb)))) 0x103f00) (callEffect (callMemPtr 0x106937 (.rip 0xfa8cb)) (0x106937 + BitVec.ofNat 64 (callMemLen (.rip 0xfa8cb)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2313) (.const ⟨64, 0x10693d⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 2279), (1, 2296), (2, 2305), (3, 2307), (4, 2311), (5, 2254), (6, 2303), (7, 2309), (8, 2287), (9, 2293), (10, 2263), (11, 2260), (12, 2231), (13, 2251), (14, 2204), (15, 2207), (22, 22), (39, 39), (50, 50), (51, 51)] 2314⟩ { target := .l10693d, kept := #v[], arity := rfl, guard := some (Fin.last 2313) }))))))))))))))))))))

def bytes_l10593a_59 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x8C, 0x24, 0xE6, 0x00, 0x00, 0x00, 0xF7, 0xD1, 0x66, 0x89, 0x8C, 0x24, 0xE8,
    0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xEC, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xEE,
    0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xF6, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xF8,
    0x00, 0x00, 0x00, 0x48, 0x8D, 0x74, 0x24, 0x0C, 0xBA, 0xF0, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x9C,
    0x24, 0x30, 0x01, 0x00, 0x00, 0x48, 0x89, 0xDF, 0xFF, 0x15, 0xCB, 0xA8, 0x0F, 0x00]

theorem code_l10593a_59 : ∀ x ∈ codeRange 0x1068ef bytes_l10593a_59, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x68ef 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10593a_58 : Block Op Label signature Reg.count 2265 :=
  .letOp (n := 2265) (.exec 0x106883 (StorePre 0x106883 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x106883 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106883 9 10 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[2263, 4]
    (.letOp (n := 2266) (.exec 0x10688c (StorePre 0x10688c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x10688c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10688c 8 16 (.sib 4 none 0 (.d32 0xbe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2267) (.out 0x106894 (movR32R32Effect 0x106894 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2247]
    (.letOp (n := 2268) (.exec 0x106894 (fun s => s.RIP = 0x106894) (movR32R32Effect 0x106894 2 1 0) (Reg.operands [.gpr 0] [])) #v[2247]
    (.letOp (n := 2269) (.exec 0x106896 (StorePre 0x106896 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x106896 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106896 8 16 (.sib 4 none 0 (.d32 0xc6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2270) (.out 0x10689e (shrR32Effect 0x10689e 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2267]
    (.letOp (n := 2271) (.exec 0x10689e (fun s => s.RIP = 0x10689e) (shrR32Effect 0x10689e 2 1 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2267]
    (.letOp (n := 2272) (.exec 0x1068a0 (StorePre 0x1068a0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x1068a0 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068a0 8 16 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2273) (.out 0x1068a8 (xorR32R32Effect 0x1068a8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2270, 2247]
    (.letOp (n := 2274) (.exec 0x1068a8 (fun s => s.RIP = 0x1068a8) (xorR32R32Effect 0x1068a8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2270, 2247]
    (.letOp (n := 2275) (.exec 0x1068aa (StorePre 0x1068aa 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xcc)) s (0x1068aa + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068aa 8 16 (.sib 4 none 0 (.d32 0xcc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2276) (.out 0x1068b2 (andR32Imm32Effect 0x1068b2 6 1 0x5050) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2273]
    (.letOp (n := 2277) (.exec 0x1068b2 (fun s => s.RIP = 0x1068b2) (andR32Imm32Effect 0x1068b2 6 1 0x5050) (Reg.operands [.gpr 1] [])) #v[2273]
    (.letOp (n := 2278) (.exec 0x1068b8 (StorePre 0x1068b8 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xce)) s (0x1068b8 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068b8 8 16 (.sib 4 none 0 (.d32 0xce))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2279) (.out 0x1068c0 (xorR32R32Effect 0x1068c0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2247, 2276]
    (.letOp (n := 2280) (.exec 0x1068c0 (fun s => s.RIP = 0x1068c0) (xorR32R32Effect 0x1068c0 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2247, 2276]
    (.letOp (n := 2281) (.exec 0x1068c2 (StorePre 0x1068c2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd6)) s (0x1068c2 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068c2 8 16 (.sib 4 none 0 (.d32 0xd6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2282) (.out 0x1068ca (addR32R32Effect 0x1068ca 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[2276, 2276]
    (.letOp (n := 2283) (.exec 0x1068ca (fun s => s.RIP = 0x1068ca) (addR32R32Effect 0x1068ca 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[2276, 2276]
    (.letOp (n := 2284) (.exec 0x1068cc (StorePre 0x1068cc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x1068cc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1068cc 8 16 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2285) (.out 0x1068d4 (xorR32R32Effect 0x1068d4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2282, 2279]
    (.letOp (n := 2286) (.exec 0x1068d4 (fun s => s.RIP = 0x1068d4) (xorR32R32Effect 0x1068d4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2282, 2279]
    (.letOp (n := 2287) (.out 0x1068d6 (notR32Effect 0x1068d6 3 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[1969]
    (.letOp (n := 2288) (.exec 0x1068d6 (fun s => s.RIP = 0x1068d6) (notR32Effect 0x1068d6 3 8) (Reg.operands [.gpr 8] [])) #v[1969]
    (.letOp (n := 2289) (.exec 0x1068d9 (StorePre 0x1068d9 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x1068d9 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x1068d9 9 8 (.sib 4 none 0 (.d32 0xdc))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[2287, 4]
    (.letOp (n := 2290) (.out 0x1068e2 (notR32Effect 0x1068e2 2 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[2167]
    (.letOp (n := 2291) (.exec 0x1068e2 (fun s => s.RIP = 0x1068e2) (notR32Effect 0x1068e2 2 7) (Reg.operands [.gpr 7] [])) #v[2167]
    (.letOp (n := 2292) (.exec 0x1068e4 (StorePre 0x1068e4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xde)) s (0x1068e4 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1068e4 8 7 (.sib 4 none 0 (.d32 0xde))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[2290, 4]
    (.letOp (n := 2293) (.out 0x1068ec (notR32Effect 0x1068ec 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[2229]
    (.letOp (n := 2294) (.exec 0x1068ec (fun s => s.RIP = 0x1068ec) (notR32Effect 0x1068ec 3 9) (Reg.operands [.gpr 9] [])) #v[2229]
    (b_l10593a_59))))))))))))))))))))))))))))))

def bytes_l10593a_58 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x94, 0x24, 0xBC, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xBE, 0x00, 0x00,
    0x00, 0x89, 0xC1, 0x66, 0xF7, 0x94, 0x24, 0xC6, 0x00, 0x00, 0x00, 0xD1, 0xE9, 0x66, 0xF7, 0x94,
    0x24, 0xC8, 0x00, 0x00, 0x00, 0x31, 0xC1, 0x66, 0xF7, 0x94, 0x24, 0xCC, 0x00, 0x00, 0x00, 0x81,
    0xE1, 0x50, 0x50, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0xCE, 0x00, 0x00, 0x00, 0x31, 0xC8, 0x66,
    0xF7, 0x94, 0x24, 0xD6, 0x00, 0x00, 0x00, 0x01, 0xC9, 0x66, 0xF7, 0x94, 0x24, 0xD8, 0x00, 0x00,
    0x00, 0x31, 0xC1, 0x41, 0xF7, 0xD0, 0x66, 0x44, 0x89, 0x84, 0x24, 0xDC, 0x00, 0x00, 0x00, 0xF7,
    0xD7, 0x66, 0x89, 0xBC, 0x24, 0xDE, 0x00, 0x00, 0x00, 0x41, 0xF7, 0xD1] ++ bytes_l10593a_59

theorem code_l10593a_58 : ∀ x ∈ codeRange 0x106883 bytes_l10593a_58, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6883 108 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_59

def b_l10593a_57 : Block Op Label signature Reg.count 2233 :=
  .letOp (n := 2233) (.exec 0x106820 (StorePre 0x106820 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x106820 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106820 9 12 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[2231, 4]
    (.letOp (n := 2234) (.out 0x106829 (movR32R32Effect 0x106829 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[2098]
    (.letOp (n := 2235) (.exec 0x106829 (fun s => s.RIP = 0x106829) (movR32R32Effect 0x106829 2 0 6) (Reg.operands [.gpr 6] [])) #v[2098]
    (.letOp (n := 2236) (.out 0x10682b (shrR32Effect 0x10682b 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2234]
    (.letOp (n := 2237) (.exec 0x10682b (fun s => s.RIP = 0x10682b) (shrR32Effect 0x10682b 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2234]
    (.letOp (n := 2238) (.out 0x10682e (xorR32R32Effect 0x10682e 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2236, 2098]
    (.letOp (n := 2239) (.exec 0x10682e (fun s => s.RIP = 0x10682e) (xorR32R32Effect 0x10682e 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2236, 2098]
    (.letOp (n := 2240) (.out 0x106830 (andEaxImm32Effect 0x106830 0x1320) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2238]
    (.letOp (n := 2241) (.exec 0x106830 (fun s => s.RIP = 0x106830) (andEaxImm32Effect 0x106830 0x1320) (Reg.operands [.gpr 0] [])) #v[2238]
    (.letOp (n := 2242) (.out 0x106835 (xorR32R32Effect 0x106835 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[2098, 2240]
    (.letOp (n := 2243) (.exec 0x106835 (fun s => s.RIP = 0x106835) (xorR32R32Effect 0x106835 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[2098, 2240]
    (.letOp (n := 2244) (.out 0x106837 (shlR32Effect 0x106837 3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2240]
    (.letOp (n := 2245) (.exec 0x106837 (fun s => s.RIP = 0x106837) (shlR32Effect 0x106837 3 0 2) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2240]
    (.letOp (n := 2246) (.exec 0x10683a (StorePre 0x10683a 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x10683a + BitVec.ofNat 64 8)) 2) (notMEffect 0x10683a 8 16 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2247) (.out 0x106842 (xorR32R32Effect 0x106842 2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[2244, 2242]
    (.letOp (n := 2248) (.exec 0x106842 (fun s => s.RIP = 0x106842) (xorR32R32Effect 0x106842 2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[2244, 2242]
    (.letOp (n := 2249) (.exec 0x106844 (StorePre 0x106844 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106844 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106844 8 16 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2250) (.exec 0x10684c (StorePre 0x10684c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10684c + BitVec.ofNat 64 8)) 2) (notMEffect 0x10684c 8 16 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2251) (.out 0x106854 (notR32Effect 0x106854 3 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1576]
    (.letOp (n := 2252) (.exec 0x106854 (fun s => s.RIP = 0x106854) (notR32Effect 0x106854 3 13) (Reg.operands [.gpr 13] [])) #v[1576]
    (.letOp (n := 2253) (.exec 0x106857 (StorePre 0x106857 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x106857 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106857 9 13 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[2251, 4]
    (.letOp (n := 2254) (.out 0x106860 (notR32Effect 0x106860 2 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1592]
    (.letOp (n := 2255) (.exec 0x106860 (fun s => s.RIP = 0x106860) (notR32Effect 0x106860 2 5) (Reg.operands [.gpr 5] [])) #v[1592]
    (.letOp (n := 2256) (.exec 0x106862 (StorePre 0x106862 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x106862 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106862 8 5 (.sib 4 none 0 (.d32 0xae))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[2254, 4]
    (.letOp (n := 2257) (.out 0x10686a (notR32Effect 0x10686a 2 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1659]
    (.letOp (n := 2258) (.exec 0x10686a (fun s => s.RIP = 0x10686a) (notR32Effect 0x10686a 2 3) (Reg.operands [.gpr 3] [])) #v[1659]
    (.letOp (n := 2259) (.exec 0x10686c (StorePre 0x10686c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x10686c + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10686c 8 3 (.sib 4 none 0 (.d32 0xb6))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[2257, 4]
    (.letOp (n := 2260) (.out 0x106874 (notR32Effect 0x106874 3 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[1675]
    (.letOp (n := 2261) (.exec 0x106874 (fun s => s.RIP = 0x106874) (notR32Effect 0x106874 3 11) (Reg.operands [.gpr 11] [])) #v[1675]
    (.letOp (n := 2262) (.exec 0x106877 (StorePre 0x106877 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x106877 + BitVec.ofNat 64 9)) 2) (movM16R16Effect 0x106877 9 11 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[2260, 4]
    (.letOp (n := 2263) (.out 0x106880 (notR32Effect 0x106880 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[1722]
    (.letOp (n := 2264) (.exec 0x106880 (fun s => s.RIP = 0x106880) (notR32Effect 0x106880 3 10) (Reg.operands [.gpr 10] [])) #v[1722]
    (b_l10593a_58))))))))))))))))))))))))))))))))

def bytes_l10593a_57 : List UInt8 :=
  [0x66, 0x44, 0x89, 0xA4, 0x24, 0x9C, 0x00, 0x00, 0x00, 0x89, 0xF0, 0xC1, 0xE8, 0x02, 0x31, 0xF0,
    0x25, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC6, 0xC1, 0xE0, 0x02, 0x66, 0xF7, 0x94, 0x24, 0x9E, 0x00,
    0x00, 0x00, 0x31, 0xF0, 0x66, 0xF7, 0x94, 0x24, 0xA6, 0x00, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24,
    0xA8, 0x00, 0x00, 0x00, 0x41, 0xF7, 0xD5, 0x66, 0x44, 0x89, 0xAC, 0x24, 0xAC, 0x00, 0x00, 0x00,
    0xF7, 0xD5, 0x66, 0x89, 0xAC, 0x24, 0xAE, 0x00, 0x00, 0x00, 0xF7, 0xD3, 0x66, 0x89, 0x9C, 0x24,
    0xB6, 0x00, 0x00, 0x00, 0x41, 0xF7, 0xD3, 0x66, 0x44, 0x89, 0x9C, 0x24, 0xB8, 0x00, 0x00, 0x00,
    0x41, 0xF7, 0xD2] ++ bytes_l10593a_58

theorem code_l10593a_57 : ∀ x ∈ codeRange 0x106820 bytes_l10593a_57, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6820 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_58

def b_l10593a_56 : Block Op Label signature Reg.count 2203 :=
  .letOp (n := 2203) (.exec 0x1067b7 (StorePre 0x1067b7 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x1067b7 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067b7 6 9 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[2201, 4]
    (.letOp (n := 2204) (.out 0x1067bd (notR32Effect 0x1067bd 3 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[1049]
    (.letOp (n := 2205) (.exec 0x1067bd (fun s => s.RIP = 0x1067bd) (notR32Effect 0x1067bd 3 14) (Reg.operands [.gpr 14] [])) #v[1049]
    (.letOp (n := 2206) (.exec 0x1067c0 (StorePre 0x1067c0 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x1067c0 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067c0 6 14 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[2204, 4]
    (.letOp (n := 2207) (.out 0x1067c6 (notR32Effect 0x1067c6 3 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[1096]
    (.letOp (n := 2208) (.exec 0x1067c6 (fun s => s.RIP = 0x1067c6) (notR32Effect 0x1067c6 3 15) (Reg.operands [.gpr 15] [])) #v[1096]
    (.letOp (n := 2209) (.exec 0x1067c9 (StorePre 0x1067c9 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x1067c9 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x1067c9 6 15 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[2207, 4]
    (.letOp (n := 2210) (.exec 0x1067cf (StorePre 0x1067cf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x1067cf + BitVec.ofNat 64 5)) 2) (notMEffect 0x1067cf 5 16 (.sib 4 none 0 (.d8 0x7e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2211) (.out 0x1067d4 (movR32R32Effect 0x1067d4 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 1] []) (.reg (.gpr 9))) #v[2187]
    (.letOp (n := 2212) (.exec 0x1067d4 (fun s => s.RIP = 0x1067d4) (movR32R32Effect 0x1067d4 3 9 1) (Reg.operands [.gpr 1] [])) #v[2187]
    (.letOp (n := 2213) (.exec 0x1067d7 (StorePre 0x1067d7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x1067d7 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067d7 8 16 (.sib 4 none 0 (.d32 0x86))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2214) (.out 0x1067df (shrR32Effect 0x1067df 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[2211]
    (.letOp (n := 2215) (.exec 0x1067df (fun s => s.RIP = 0x1067df) (shrR32Effect 0x1067df 3 9 1) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2211]
    (.letOp (n := 2216) (.exec 0x1067e2 (StorePre 0x1067e2 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1067e2 + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067e2 8 16 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2217) (.out 0x1067ea (xorR32R32Effect 0x1067ea 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[2214, 2187]
    (.letOp (n := 2218) (.exec 0x1067ea (fun s => s.RIP = 0x1067ea) (xorR32R32Effect 0x1067ea 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[2214, 2187]
    (.letOp (n := 2219) (.exec 0x1067ed (StorePre 0x1067ed 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8c)) s (0x1067ed + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067ed 8 16 (.sib 4 none 0 (.d32 0x8c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2220) (.out 0x1067f5 (andR32Imm32Effect 0x1067f5 7 9 0x5050) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[2217]
    (.letOp (n := 2221) (.exec 0x1067f5 (fun s => s.RIP = 0x1067f5) (andR32Imm32Effect 0x1067f5 7 9 0x5050) (Reg.operands [.gpr 9] [])) #v[2217]
    (.letOp (n := 2222) (.exec 0x1067fc (StorePre 0x1067fc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8e)) s (0x1067fc + BitVec.ofNat 64 8)) 2) (notMEffect 0x1067fc 8 16 (.sib 4 none 0 (.d32 0x8e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2223) (.out 0x106804 (xorR32R32Effect 0x106804 3 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[2187, 2220]
    (.letOp (n := 2224) (.exec 0x106804 (fun s => s.RIP = 0x106804) (xorR32R32Effect 0x106804 3 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[2187, 2220]
    (.letOp (n := 2225) (.exec 0x106807 (StorePre 0x106807 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x96)) s (0x106807 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106807 8 16 (.sib 4 none 0 (.d32 0x96))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2226) (.out 0x10680f (addR32R32Effect 0x10680f 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[2220, 2220]
    (.letOp (n := 2227) (.exec 0x10680f (fun s => s.RIP = 0x10680f) (addR32R32Effect 0x10680f 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[2220, 2220]
    (.letOp (n := 2228) (.exec 0x106812 (StorePre 0x106812 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x106812 + BitVec.ofNat 64 8)) 2) (notMEffect 0x106812 8 16 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2229) (.out 0x10681a (xorR32R32Effect 0x10681a 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[2226, 2223]
    (.letOp (n := 2230) (.exec 0x10681a (fun s => s.RIP = 0x10681a) (xorR32R32Effect 0x10681a 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[2226, 2223]
    (.letOp (n := 2231) (.out 0x10681d (notR32Effect 0x10681d 3 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1343]
    (.letOp (n := 2232) (.exec 0x10681d (fun s => s.RIP = 0x10681d) (notR32Effect 0x10681d 3 12) (Reg.operands [.gpr 12] [])) #v[1343]
    (b_l10593a_57))))))))))))))))))))))))))))))

def bytes_l10593a_56 : List UInt8 :=
  [0x66, 0x44, 0x89, 0x4C, 0x24, 0x76, 0x41, 0xF7, 0xD6, 0x66, 0x44, 0x89, 0x74, 0x24, 0x78, 0x41,
    0xF7, 0xD7, 0x66, 0x44, 0x89, 0x7C, 0x24, 0x7C, 0x66, 0xF7, 0x54, 0x24, 0x7E, 0x41, 0x89, 0xC9,
    0x66, 0xF7, 0x94, 0x24, 0x86, 0x00, 0x00, 0x00, 0x41, 0xD1, 0xE9, 0x66, 0xF7, 0x94, 0x24, 0x88,
    0x00, 0x00, 0x00, 0x41, 0x31, 0xC9, 0x66, 0xF7, 0x94, 0x24, 0x8C, 0x00, 0x00, 0x00, 0x41, 0x81,
    0xE1, 0x50, 0x50, 0x00, 0x00, 0x66, 0xF7, 0x94, 0x24, 0x8E, 0x00, 0x00, 0x00, 0x44, 0x31, 0xC9,
    0x66, 0xF7, 0x94, 0x24, 0x96, 0x00, 0x00, 0x00, 0x45, 0x01, 0xC9, 0x66, 0xF7, 0x94, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x41, 0x31, 0xC9, 0x41, 0xF7, 0xD4] ++ bytes_l10593a_57

theorem code_l10593a_56 : ∀ x ∈ codeRange 0x1067b7 bytes_l10593a_56, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x67b7 105 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_57

def b_l10593a_55 : Block Op Label signature Reg.count 2169 :=
  .letOp (n := 2169) (.out 0x106767 (movR32M32LowEffect 0x106767 0 (.sib 4 none 0 (.d32 0x104))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2170) (.exec 0x106767 (LoadPre 0x106767 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x106767 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106767 0 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2171) (.out 0x10676e (notR32Effect 0x10676e 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2169]
    (.letOp (n := 2172) (.exec 0x10676e (fun s => s.RIP = 0x10676e) (notR32Effect 0x10676e 2 0) (Reg.operands [.gpr 0] [])) #v[2169]
    (.letOp (n := 2173) (.exec 0x106770 (StorePre 0x106770 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x106770 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106770 5 0 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2171, 4]
    (.letOp (n := 2174) (.out 0x106775 (movR32R32Effect 0x106775 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2096]
    (.letOp (n := 2175) (.exec 0x106775 (fun s => s.RIP = 0x106775) (movR32R32Effect 0x106775 2 1 2) (Reg.operands [.gpr 2] [])) #v[2096]
    (.letOp (n := 2176) (.out 0x106777 (shrR32Effect 0x106777 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2174]
    (.letOp (n := 2177) (.exec 0x106777 (fun s => s.RIP = 0x106777) (shrR32Effect 0x106777 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2174]
    (.letOp (n := 2178) (.out 0x10677a (xorR32R32Effect 0x10677a 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2176, 2096]
    (.letOp (n := 2179) (.exec 0x10677a (fun s => s.RIP = 0x10677a) (xorR32R32Effect 0x10677a 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2176, 2096]
    (.letOp (n := 2180) (.out 0x10677c (andR32Imm32Effect 0x10677c 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2178]
    (.letOp (n := 2181) (.exec 0x10677c (fun s => s.RIP = 0x10677c) (andR32Imm32Effect 0x10677c 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[2178]
    (.letOp (n := 2182) (.out 0x106782 (xorR32R32Effect 0x106782 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[2096, 2180]
    (.letOp (n := 2183) (.exec 0x106782 (fun s => s.RIP = 0x106782) (xorR32R32Effect 0x106782 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[2096, 2180]
    (.letOp (n := 2184) (.out 0x106784 (shlR32Effect 0x106784 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2180]
    (.letOp (n := 2185) (.exec 0x106784 (fun s => s.RIP = 0x106784) (shlR32Effect 0x106784 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2180]
    (.letOp (n := 2186) (.exec 0x106787 (StorePre 0x106787 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x106787 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106787 5 16 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2187) (.out 0x10678c (xorR32R32Effect 0x10678c 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[2184, 2182]
    (.letOp (n := 2188) (.exec 0x10678c (fun s => s.RIP = 0x10678c) (xorR32R32Effect 0x10678c 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[2184, 2182]
    (.letOp (n := 2189) (.exec 0x10678e (StorePre 0x10678e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x10678e + BitVec.ofNat 64 5)) 2) (notMEffect 0x10678e 5 16 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2190) (.exec 0x106793 (StorePre 0x106793 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x106793 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106793 5 16 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2191) (.out 0x106798 (movR32M32LowEffect 0x106798 0 (.sib 4 none 0 (.d32 0x100))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2192) (.exec 0x106798 (LoadPre 0x106798 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x106798 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106798 0 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2193) (.out 0x10679f (notR32Effect 0x10679f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2191]
    (.letOp (n := 2194) (.exec 0x10679f (fun s => s.RIP = 0x10679f) (notR32Effect 0x10679f 2 0) (Reg.operands [.gpr 0] [])) #v[2191]
    (.letOp (n := 2195) (.exec 0x1067a1 (StorePre 0x1067a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x1067a1 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1067a1 5 0 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2193, 4]
    (.letOp (n := 2196) (.out 0x1067a6 (movR32M32LowEffect 0x1067a6 0 (.sib 4 none 0 (.d32 0xfc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2197) (.exec 0x1067a6 (LoadPre 0x1067a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x1067a6 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1067a6 0 (.sib 4 none 0 (.d32 0xfc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2198) (.out 0x1067ad (notR32Effect 0x1067ad 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2196]
    (.letOp (n := 2199) (.exec 0x1067ad (fun s => s.RIP = 0x1067ad) (notR32Effect 0x1067ad 2 0) (Reg.operands [.gpr 0] [])) #v[2196]
    (.letOp (n := 2200) (.exec 0x1067af (StorePre 0x1067af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x1067af + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1067af 5 0 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2198, 4]
    (.letOp (n := 2201) (.out 0x1067b4 (notR32Effect 0x1067b4 3 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[1033]
    (.letOp (n := 2202) (.exec 0x1067b4 (fun s => s.RIP = 0x1067b4) (notR32Effect 0x1067b4 3 9) (Reg.operands [.gpr 9] [])) #v[1033]
    (b_l10593a_56))))))))))))))))))))))))))))))))))

def bytes_l10593a_55 : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x04, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x5C, 0x89, 0xD1,
    0xC1, 0xE9, 0x02, 0x31, 0xD1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xCA, 0xC1, 0xE1, 0x02,
    0x66, 0xF7, 0x54, 0x24, 0x5E, 0x31, 0xD1, 0x66, 0xF7, 0x54, 0x24, 0x66, 0x66, 0xF7, 0x54, 0x24,
    0x68, 0x8B, 0x84, 0x24, 0x00, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x6C, 0x8B,
    0x84, 0x24, 0xFC, 0x00, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x6E, 0x41, 0xF7, 0xD1] ++ bytes_l10593a_56

theorem code_l10593a_55 : ∀ x ∈ codeRange 0x106767 bytes_l10593a_55, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6767 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_56

def b_l10593a_54 : Block Op Label signature Reg.count 2138 :=
  .letOp (n := 2138) (.out 0x106716 (movR32M32LowEffect 0x106716 0 (.sib 4 none 0 (.d32 0x10c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2139) (.exec 0x106716 (LoadPre 0x106716 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x106716 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106716 0 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2140) (.out 0x10671d (notR32Effect 0x10671d 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2138]
    (.letOp (n := 2141) (.exec 0x10671d (fun s => s.RIP = 0x10671d) (notR32Effect 0x10671d 2 0) (Reg.operands [.gpr 0] [])) #v[2138]
    (.letOp (n := 2142) (.exec 0x10671f (StorePre 0x10671f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10671f + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10671f 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2140, 4]
    (.letOp (n := 2143) (.out 0x106724 (movR32M32LowEffect 0x106724 0 (.sib 4 none 0 (.d32 0x108))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2144) (.exec 0x106724 (LoadPre 0x106724 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x106724 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106724 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2145) (.out 0x10672b (notR32Effect 0x10672b 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2143]
    (.letOp (n := 2146) (.exec 0x10672b (fun s => s.RIP = 0x10672b) (notR32Effect 0x10672b 2 0) (Reg.operands [.gpr 0] [])) #v[2143]
    (.letOp (n := 2147) (.exec 0x10672d (StorePre 0x10672d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x10672d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10672d 5 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2145, 4]
    (.letOp (n := 2148) (.exec 0x106732 (StorePre 0x106732 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x106732 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106732 5 16 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2149) (.exec 0x106737 (StorePre 0x106737 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x106737 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106737 5 16 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2150) (.out 0x10673c (movR32R32Effect 0x10673c 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[2119]
    (.letOp (n := 2151) (.exec 0x10673c (fun s => s.RIP = 0x10673c) (movR32R32Effect 0x10673c 2 7 1) (Reg.operands [.gpr 1] [])) #v[2119]
    (.letOp (n := 2152) (.out 0x10673e (shrR32Effect 0x10673e 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[2150]
    (.letOp (n := 2153) (.exec 0x10673e (fun s => s.RIP = 0x10673e) (shrR32Effect 0x10673e 2 7 1) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2150]
    (.letOp (n := 2154) (.exec 0x106740 (StorePre 0x106740 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x106740 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106740 5 16 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2155) (.out 0x106745 (xorR32R32Effect 0x106745 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2152, 2119]
    (.letOp (n := 2156) (.exec 0x106745 (fun s => s.RIP = 0x106745) (xorR32R32Effect 0x106745 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2152, 2119]
    (.letOp (n := 2157) (.exec 0x106747 (StorePre 0x106747 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4c)) s (0x106747 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106747 5 16 (.sib 4 none 0 (.d8 0x4c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2158) (.out 0x10674c (andR32Imm32Effect 0x10674c 6 7 0x5050) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[2155]
    (.letOp (n := 2159) (.exec 0x10674c (fun s => s.RIP = 0x10674c) (andR32Imm32Effect 0x10674c 6 7 0x5050) (Reg.operands [.gpr 7] [])) #v[2155]
    (.letOp (n := 2160) (.exec 0x106752 (StorePre 0x106752 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4e)) s (0x106752 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106752 5 16 (.sib 4 none 0 (.d8 0x4e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2161) (.out 0x106757 (xorR32R32Effect 0x106757 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2119, 2158]
    (.letOp (n := 2162) (.exec 0x106757 (fun s => s.RIP = 0x106757) (xorR32R32Effect 0x106757 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2119, 2158]
    (.letOp (n := 2163) (.exec 0x106759 (StorePre 0x106759 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x56)) s (0x106759 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106759 5 16 (.sib 4 none 0 (.d8 0x56))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2164) (.out 0x10675e (addR32R32Effect 0x10675e 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[2158, 2158]
    (.letOp (n := 2165) (.exec 0x10675e (fun s => s.RIP = 0x10675e) (addR32R32Effect 0x10675e 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[2158, 2158]
    (.letOp (n := 2166) (.exec 0x106760 (StorePre 0x106760 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x106760 + BitVec.ofNat 64 5)) 2) (notMEffect 0x106760 5 16 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2167) (.out 0x106765 (xorR32R32Effect 0x106765 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2164, 2161]
    (.letOp (n := 2168) (.exec 0x106765 (fun s => s.RIP = 0x106765) (xorR32R32Effect 0x106765 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2164, 2161]
    (b_l10593a_55)))))))))))))))))))))))))))))))

def bytes_l10593a_54 : List UInt8 :=
  [0x8B, 0x84, 0x24, 0x0C, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x38, 0x8B, 0x84,
    0x24, 0x08, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44, 0x24, 0x3C, 0x66, 0xF7, 0x54, 0x24,
    0x3E, 0x66, 0xF7, 0x54, 0x24, 0x46, 0x89, 0xCF, 0xD1, 0xEF, 0x66, 0xF7, 0x54, 0x24, 0x48, 0x31,
    0xCF, 0x66, 0xF7, 0x54, 0x24, 0x4C, 0x81, 0xE7, 0x50, 0x50, 0x00, 0x00, 0x66, 0xF7, 0x54, 0x24,
    0x4E, 0x31, 0xF9, 0x66, 0xF7, 0x54, 0x24, 0x56, 0x01, 0xFF, 0x66, 0xF7, 0x54, 0x24, 0x58, 0x31,
    0xCF] ++ bytes_l10593a_55

theorem code_l10593a_54 : ∀ x ∈ codeRange 0x106716 bytes_l10593a_54, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6716 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_55

def b_l10593a_53 : Block Op Label signature Reg.count 2105 :=
  .letOp (n := 2105) (.exec 0x1066c4 (StorePre 0x1066c4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x1066c4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1066c4 5 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2103, 4]
    (.letOp (n := 2106) (.out 0x1066c9 (movR32R32Effect 0x1066c9 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[2001]
    (.letOp (n := 2107) (.exec 0x1066c9 (fun s => s.RIP = 0x1066c9) (movR32R32Effect 0x1066c9 2 1 7) (Reg.operands [.gpr 7] [])) #v[2001]
    (.letOp (n := 2108) (.out 0x1066cb (shrR32Effect 0x1066cb 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2106]
    (.letOp (n := 2109) (.exec 0x1066cb (fun s => s.RIP = 0x1066cb) (shrR32Effect 0x1066cb 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2106]
    (.letOp (n := 2110) (.out 0x1066ce (xorR32R32Effect 0x1066ce 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2108, 2001]
    (.letOp (n := 2111) (.exec 0x1066ce (fun s => s.RIP = 0x1066ce) (xorR32R32Effect 0x1066ce 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2108, 2001]
    (.letOp (n := 2112) (.out 0x1066d0 (andR32Imm32Effect 0x1066d0 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2110]
    (.letOp (n := 2113) (.exec 0x1066d0 (fun s => s.RIP = 0x1066d0) (andR32Imm32Effect 0x1066d0 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[2110]
    (.letOp (n := 2114) (.out 0x1066d6 (xorR32R32Effect 0x1066d6 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[2001, 2112]
    (.letOp (n := 2115) (.exec 0x1066d6 (fun s => s.RIP = 0x1066d6) (xorR32R32Effect 0x1066d6 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[2001, 2112]
    (.letOp (n := 2116) (.out 0x1066d8 (shlR32Effect 0x1066d8 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2112]
    (.letOp (n := 2117) (.exec 0x1066d8 (fun s => s.RIP = 0x1066d8) (shlR32Effect 0x1066d8 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2112]
    (.letOp (n := 2118) (.exec 0x1066db (StorePre 0x1066db 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x1066db + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066db 5 16 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2119) (.out 0x1066e0 (xorR32R32Effect 0x1066e0 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[2116, 2114]
    (.letOp (n := 2120) (.exec 0x1066e0 (fun s => s.RIP = 0x1066e0) (xorR32R32Effect 0x1066e0 2 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[2116, 2114]
    (.letOp (n := 2121) (.exec 0x1066e2 (StorePre 0x1066e2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x1066e2 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066e2 5 16 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2122) (.exec 0x1066e7 (StorePre 0x1066e7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1066e7 + BitVec.ofNat 64 5)) 2) (notMEffect 0x1066e7 5 16 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2123) (.out 0x1066ec (movR32M32LowEffect 0x1066ec 0 (.sib 4 none 0 (.d32 0x118))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2124) (.exec 0x1066ec (LoadPre 0x1066ec (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x1066ec + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066ec 0 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2125) (.out 0x1066f3 (notR32Effect 0x1066f3 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2123]
    (.letOp (n := 2126) (.exec 0x1066f3 (fun s => s.RIP = 0x1066f3) (notR32Effect 0x1066f3 2 0) (Reg.operands [.gpr 0] [])) #v[2123]
    (.letOp (n := 2127) (.exec 0x1066f5 (StorePre 0x1066f5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x1066f5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1066f5 5 0 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2125, 4]
    (.letOp (n := 2128) (.out 0x1066fa (movR32M32LowEffect 0x1066fa 0 (.sib 4 none 0 (.d32 0x114))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2129) (.exec 0x1066fa (LoadPre 0x1066fa (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x1066fa + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066fa 0 (.sib 4 none 0 (.d32 0x114))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2130) (.out 0x106701 (notR32Effect 0x106701 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2128]
    (.letOp (n := 2131) (.exec 0x106701 (fun s => s.RIP = 0x106701) (notR32Effect 0x106701 2 0) (Reg.operands [.gpr 0] [])) #v[2128]
    (.letOp (n := 2132) (.exec 0x106703 (StorePre 0x106703 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x106703 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106703 5 0 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2130, 4]
    (.letOp (n := 2133) (.out 0x106708 (movR32M32LowEffect 0x106708 0 (.sib 4 none 0 (.d32 0x110))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2134) (.exec 0x106708 (LoadPre 0x106708 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x106708 + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x106708 0 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2135) (.out 0x10670f (notR32Effect 0x10670f 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2133]
    (.letOp (n := 2136) (.exec 0x10670f (fun s => s.RIP = 0x10670f) (notR32Effect 0x10670f 2 0) (Reg.operands [.gpr 0] [])) #v[2133]
    (.letOp (n := 2137) (.exec 0x106711 (StorePre 0x106711 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x106711 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106711 5 0 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2135, 4]
    (b_l10593a_54)))))))))))))))))))))))))))))))))

def bytes_l10593a_53 : List UInt8 :=
  [0x66, 0x89, 0x44, 0x24, 0x1C, 0x89, 0xF9, 0xC1, 0xE9, 0x02, 0x31, 0xF9, 0x81, 0xE1, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xCF, 0xC1, 0xE1, 0x02, 0x66, 0xF7, 0x54, 0x24, 0x1E, 0x31, 0xF9, 0x66, 0xF7,
    0x54, 0x24, 0x26, 0x66, 0xF7, 0x54, 0x24, 0x28, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, 0xF7,
    0xD0, 0x66, 0x89, 0x44, 0x24, 0x2C, 0x8B, 0x84, 0x24, 0x14, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66,
    0x89, 0x44, 0x24, 0x2E, 0x8B, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0xF7, 0xD0, 0x66, 0x89, 0x44,
    0x24, 0x36] ++ bytes_l10593a_54

theorem code_l10593a_53 : ∀ x ∈ codeRange 0x1066c4 bytes_l10593a_53, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x66c4 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_54

def b_l10593a_52 : Block Op Label signature Reg.count 2066 :=
  .letOp (n := 2066) (.out 0x106676 (movzxR32M16Effect 0x106676 8 0 (.sib 4 none 0 (.d32 0xea))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2067) (.exec 0x106676 (LoadPre 0x106676 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xea)) s (0x106676 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106676 8 0 (.sib 4 none 0 (.d32 0xea))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2068) (.out 0x10667e (movR32R32Effect 0x10667e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2066]
    (.letOp (n := 2069) (.exec 0x10667e (fun s => s.RIP = 0x10667e) (movR32R32Effect 0x10667e 2 1 0) (Reg.operands [.gpr 0] [])) #v[2066]
    (.letOp (n := 2070) (.out 0x106680 (shrR32Effect 0x106680 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2068]
    (.letOp (n := 2071) (.exec 0x106680 (fun s => s.RIP = 0x106680) (shrR32Effect 0x106680 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2068]
    (.letOp (n := 2072) (.out 0x106683 (xorR32R32Effect 0x106683 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2070, 2066]
    (.letOp (n := 2073) (.exec 0x106683 (fun s => s.RIP = 0x106683) (xorR32R32Effect 0x106683 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2070, 2066]
    (.letOp (n := 2074) (.out 0x106685 (andR32Imm32Effect 0x106685 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2072]
    (.letOp (n := 2075) (.exec 0x106685 (fun s => s.RIP = 0x106685) (andR32Imm32Effect 0x106685 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[2072]
    (.letOp (n := 2076) (.out 0x10668b (xorR32R32Effect 0x10668b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2066, 2074]
    (.letOp (n := 2077) (.exec 0x10668b (fun s => s.RIP = 0x10668b) (xorR32R32Effect 0x10668b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2066, 2074]
    (.letOp (n := 2078) (.out 0x10668d (shlR32Effect 0x10668d 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2074]
    (.letOp (n := 2079) (.exec 0x10668d (fun s => s.RIP = 0x10668d) (shlR32Effect 0x10668d 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2074]
    (.letOp (n := 2080) (.out 0x106690 (xorR32R32Effect 0x106690 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2078, 2076]
    (.letOp (n := 2081) (.exec 0x106690 (fun s => s.RIP = 0x106690) (xorR32R32Effect 0x106690 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2078, 2076]
    (.letOp (n := 2082) (.out 0x106692 (movR32R32Effect 0x106692 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2080]
    (.letOp (n := 2083) (.exec 0x106692 (fun s => s.RIP = 0x106692) (movR32R32Effect 0x106692 2 0 1) (Reg.operands [.gpr 1] [])) #v[2080]
    (.letOp (n := 2084) (.out 0x106694 (shrR32Effect 0x106694 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2082]
    (.letOp (n := 2085) (.exec 0x106694 (fun s => s.RIP = 0x106694) (shrR32Effect 0x106694 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2082]
    (.letOp (n := 2086) (.out 0x106696 (xorR32R32Effect 0x106696 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2084, 2080]
    (.letOp (n := 2087) (.exec 0x106696 (fun s => s.RIP = 0x106696) (xorR32R32Effect 0x106696 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2084, 2080]
    (.letOp (n := 2088) (.out 0x106698 (andEaxImm32Effect 0x106698 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2086]
    (.letOp (n := 2089) (.exec 0x106698 (fun s => s.RIP = 0x106698) (andEaxImm32Effect 0x106698 0x5050) (Reg.operands [.gpr 0] [])) #v[2086]
    (.letOp (n := 2090) (.out 0x10669d (xorR32R32Effect 0x10669d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2080, 2088]
    (.letOp (n := 2091) (.exec 0x10669d (fun s => s.RIP = 0x10669d) (xorR32R32Effect 0x10669d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2080, 2088]
    (.letOp (n := 2092) (.out 0x10669f (addR32R32Effect 0x10669f 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[2088, 2088]
    (.letOp (n := 2093) (.exec 0x10669f (fun s => s.RIP = 0x10669f) (addR32R32Effect 0x10669f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[2088, 2088]
    (.letOp (n := 2094) (.out 0x1066a1 (xorR32R32Effect 0x1066a1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2092, 2090]
    (.letOp (n := 2095) (.exec 0x1066a1 (fun s => s.RIP = 0x1066a1) (xorR32R32Effect 0x1066a1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2092, 2090]
    (.letOp (n := 2096) (.out 0x1066a3 (movzxR32M16Effect 0x1066a3 8 2 (.sib 4 none 0 (.d32 0xe6))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 2097) (.exec 0x1066a3 (LoadPre 0x1066a3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe6)) s (0x1066a3 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1066a3 8 2 (.sib 4 none 0 (.d32 0xe6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2098) (.out 0x1066ab (movzxR32M16Effect 0x1066ab 8 6 (.sib 4 none 0 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 2099) (.exec 0x1066ab (LoadPre 0x1066ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x1066ab + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1066ab 8 6 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2100) (.exec 0x1066b3 (StorePre 0x1066b3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xea)) s (0x1066b3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1066b3 8 0 (.sib 4 none 0 (.d32 0xea))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2094, 4]
    (.letOp (n := 2101) (.out 0x1066bb (movR32M32LowEffect 0x1066bb 0 (.sib 4 none 0 (.d32 0x11c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2102) (.exec 0x1066bb (LoadPre 0x1066bb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x1066bb + BitVec.ofNat 64 7)) 4) (movR32M32LowEffect 0x1066bb 0 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2103) (.out 0x1066c2 (notR32Effect 0x1066c2 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2101]
    (.letOp (n := 2104) (.exec 0x1066c2 (fun s => s.RIP = 0x1066c2) (notR32Effect 0x1066c2 2 0) (Reg.operands [.gpr 0] [])) #v[2101]
    (b_l10593a_53)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_52 : List UInt8 :=
  [0x0F, 0xB7, 0x84, 0x24, 0xEA, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81,
    0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8,
    0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x0F, 0xB7, 0x94,
    0x24, 0xE6, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0xB4, 0x24, 0xE8, 0x00, 0x00, 0x00, 0x66, 0x89, 0x84,
    0x24, 0xEA, 0x00, 0x00, 0x00, 0x8B, 0x84, 0x24, 0x1C, 0x01, 0x00, 0x00, 0xF7, 0xD0] ++ bytes_l10593a_53

theorem code_l10593a_52 : ∀ x ∈ codeRange 0x106676 bytes_l10593a_52, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6676 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_53

def b_l10593a_51 : Block Op Label signature Reg.count 2028 :=
  .letOp (n := 2028) (.out 0x106633 (xorR32R32Effect 0x106633 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2018, 2026]
    (.letOp (n := 2029) (.exec 0x106633 (fun s => s.RIP = 0x106633) (xorR32R32Effect 0x106633 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2018, 2026]
    (.letOp (n := 2030) (.out 0x106635 (addR32R32Effect 0x106635 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[2026, 2026]
    (.letOp (n := 2031) (.exec 0x106635 (fun s => s.RIP = 0x106635) (addR32R32Effect 0x106635 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[2026, 2026]
    (.letOp (n := 2032) (.out 0x106637 (xorR32R32Effect 0x106637 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2030, 2028]
    (.letOp (n := 2033) (.exec 0x106637 (fun s => s.RIP = 0x106637) (xorR32R32Effect 0x106637 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2030, 2028]
    (.letOp (n := 2034) (.exec 0x106639 (StorePre 0x106639 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe2)) s (0x106639 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106639 8 0 (.sib 4 none 0 (.d32 0xe2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2032, 4]
    (.letOp (n := 2035) (.out 0x106641 (movzxR32M16Effect 0x106641 8 0 (.sib 4 none 0 (.d32 0xe4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2036) (.exec 0x106641 (LoadPre 0x106641 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x106641 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106641 8 0 (.sib 4 none 0 (.d32 0xe4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2037) (.out 0x106649 (movR32R32Effect 0x106649 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2035]
    (.letOp (n := 2038) (.exec 0x106649 (fun s => s.RIP = 0x106649) (movR32R32Effect 0x106649 2 1 0) (Reg.operands [.gpr 0] [])) #v[2035]
    (.letOp (n := 2039) (.out 0x10664b (shrR32Effect 0x10664b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2037]
    (.letOp (n := 2040) (.exec 0x10664b (fun s => s.RIP = 0x10664b) (shrR32Effect 0x10664b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2037]
    (.letOp (n := 2041) (.out 0x10664e (xorR32R32Effect 0x10664e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2039, 2035]
    (.letOp (n := 2042) (.exec 0x10664e (fun s => s.RIP = 0x10664e) (xorR32R32Effect 0x10664e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2039, 2035]
    (.letOp (n := 2043) (.out 0x106650 (andR32Imm32Effect 0x106650 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2041]
    (.letOp (n := 2044) (.exec 0x106650 (fun s => s.RIP = 0x106650) (andR32Imm32Effect 0x106650 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[2041]
    (.letOp (n := 2045) (.out 0x106656 (xorR32R32Effect 0x106656 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2035, 2043]
    (.letOp (n := 2046) (.exec 0x106656 (fun s => s.RIP = 0x106656) (xorR32R32Effect 0x106656 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2035, 2043]
    (.letOp (n := 2047) (.out 0x106658 (shlR32Effect 0x106658 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2043]
    (.letOp (n := 2048) (.exec 0x106658 (fun s => s.RIP = 0x106658) (shlR32Effect 0x106658 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2043]
    (.letOp (n := 2049) (.out 0x10665b (xorR32R32Effect 0x10665b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2047, 2045]
    (.letOp (n := 2050) (.exec 0x10665b (fun s => s.RIP = 0x10665b) (xorR32R32Effect 0x10665b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2047, 2045]
    (.letOp (n := 2051) (.out 0x10665d (movR32R32Effect 0x10665d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2049]
    (.letOp (n := 2052) (.exec 0x10665d (fun s => s.RIP = 0x10665d) (movR32R32Effect 0x10665d 2 0 1) (Reg.operands [.gpr 1] [])) #v[2049]
    (.letOp (n := 2053) (.out 0x10665f (shrR32Effect 0x10665f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2051]
    (.letOp (n := 2054) (.exec 0x10665f (fun s => s.RIP = 0x10665f) (shrR32Effect 0x10665f 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2051]
    (.letOp (n := 2055) (.out 0x106661 (xorR32R32Effect 0x106661 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2053, 2049]
    (.letOp (n := 2056) (.exec 0x106661 (fun s => s.RIP = 0x106661) (xorR32R32Effect 0x106661 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2053, 2049]
    (.letOp (n := 2057) (.out 0x106663 (andEaxImm32Effect 0x106663 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2055]
    (.letOp (n := 2058) (.exec 0x106663 (fun s => s.RIP = 0x106663) (andEaxImm32Effect 0x106663 0x5050) (Reg.operands [.gpr 0] [])) #v[2055]
    (.letOp (n := 2059) (.out 0x106668 (xorR32R32Effect 0x106668 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2049, 2057]
    (.letOp (n := 2060) (.exec 0x106668 (fun s => s.RIP = 0x106668) (xorR32R32Effect 0x106668 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2049, 2057]
    (.letOp (n := 2061) (.out 0x10666a (addR32R32Effect 0x10666a 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[2057, 2057]
    (.letOp (n := 2062) (.exec 0x10666a (fun s => s.RIP = 0x10666a) (addR32R32Effect 0x10666a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[2057, 2057]
    (.letOp (n := 2063) (.out 0x10666c (xorR32R32Effect 0x10666c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2061, 2059]
    (.letOp (n := 2064) (.exec 0x10666c (fun s => s.RIP = 0x10666c) (xorR32R32Effect 0x10666c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2061, 2059]
    (.letOp (n := 2065) (.exec 0x10666e (StorePre 0x10666e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe4)) s (0x10666e + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10666e 8 0 (.sib 4 none 0 (.d32 0xe4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[2063, 4]
    (b_l10593a_52))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_51 : List UInt8 :=
  [0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xE2, 0x00, 0x00, 0x00, 0x0F, 0xB7,
    0x84, 0x24, 0xE4, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20,
    0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8,
    0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xE4,
    0x00, 0x00, 0x00] ++ bytes_l10593a_52

theorem code_l10593a_51 : ∀ x ∈ codeRange 0x106633 bytes_l10593a_51, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6633 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_52

def b_l10593a_50 : Block Op Label signature Reg.count 1989 :=
  .letOp (n := 1989) (.out 0x1065ed (shrR32Effect 0x1065ed 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1987]
    (.letOp (n := 1990) (.exec 0x1065ed (fun s => s.RIP = 0x1065ed) (shrR32Effect 0x1065ed 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1987]
    (.letOp (n := 1991) (.out 0x1065ef (xorR32R32Effect 0x1065ef 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1989, 1985]
    (.letOp (n := 1992) (.exec 0x1065ef (fun s => s.RIP = 0x1065ef) (xorR32R32Effect 0x1065ef 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1989, 1985]
    (.letOp (n := 1993) (.out 0x1065f1 (andEaxImm32Effect 0x1065f1 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1991]
    (.letOp (n := 1994) (.exec 0x1065f1 (fun s => s.RIP = 0x1065f1) (andEaxImm32Effect 0x1065f1 0x5050) (Reg.operands [.gpr 0] [])) #v[1991]
    (.letOp (n := 1995) (.out 0x1065f6 (xorR32R32Effect 0x1065f6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1985, 1993]
    (.letOp (n := 1996) (.exec 0x1065f6 (fun s => s.RIP = 0x1065f6) (xorR32R32Effect 0x1065f6 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1985, 1993]
    (.letOp (n := 1997) (.out 0x1065f8 (addR32R32Effect 0x1065f8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1993, 1993]
    (.letOp (n := 1998) (.exec 0x1065f8 (fun s => s.RIP = 0x1065f8) (addR32R32Effect 0x1065f8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1993, 1993]
    (.letOp (n := 1999) (.out 0x1065fa (xorR32R32Effect 0x1065fa 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1997, 1995]
    (.letOp (n := 2000) (.exec 0x1065fa (fun s => s.RIP = 0x1065fa) (xorR32R32Effect 0x1065fa 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1997, 1995]
    (.letOp (n := 2001) (.out 0x1065fc (movzxR32M16Effect 0x1065fc 8 7 (.sib 4 none 0 (.d32 0xde))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 2002) (.exec 0x1065fc (LoadPre 0x1065fc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xde)) s (0x1065fc + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1065fc 8 7 (.sib 4 none 0 (.d32 0xde))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2003) (.exec 0x106604 (StorePre 0x106604 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x106604 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106604 8 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1999, 4]
    (.letOp (n := 2004) (.out 0x10660c (movzxR32M16Effect 0x10660c 8 0 (.sib 4 none 0 (.d32 0xe2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 2005) (.exec 0x10660c (LoadPre 0x10660c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe2)) s (0x10660c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10660c 8 0 (.sib 4 none 0 (.d32 0xe2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 2006) (.out 0x106614 (movR32R32Effect 0x106614 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[2004]
    (.letOp (n := 2007) (.exec 0x106614 (fun s => s.RIP = 0x106614) (movR32R32Effect 0x106614 2 1 0) (Reg.operands [.gpr 0] [])) #v[2004]
    (.letOp (n := 2008) (.out 0x106616 (shrR32Effect 0x106616 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2006]
    (.letOp (n := 2009) (.exec 0x106616 (fun s => s.RIP = 0x106616) (shrR32Effect 0x106616 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2006]
    (.letOp (n := 2010) (.out 0x106619 (xorR32R32Effect 0x106619 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2008, 2004]
    (.letOp (n := 2011) (.exec 0x106619 (fun s => s.RIP = 0x106619) (xorR32R32Effect 0x106619 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2008, 2004]
    (.letOp (n := 2012) (.out 0x10661b (andR32Imm32Effect 0x10661b 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[2010]
    (.letOp (n := 2013) (.exec 0x10661b (fun s => s.RIP = 0x10661b) (andR32Imm32Effect 0x10661b 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[2010]
    (.letOp (n := 2014) (.out 0x106621 (xorR32R32Effect 0x106621 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2004, 2012]
    (.letOp (n := 2015) (.exec 0x106621 (fun s => s.RIP = 0x106621) (xorR32R32Effect 0x106621 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2004, 2012]
    (.letOp (n := 2016) (.out 0x106623 (shlR32Effect 0x106623 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[2012]
    (.letOp (n := 2017) (.exec 0x106623 (fun s => s.RIP = 0x106623) (shlR32Effect 0x106623 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2012]
    (.letOp (n := 2018) (.out 0x106626 (xorR32R32Effect 0x106626 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[2016, 2014]
    (.letOp (n := 2019) (.exec 0x106626 (fun s => s.RIP = 0x106626) (xorR32R32Effect 0x106626 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[2016, 2014]
    (.letOp (n := 2020) (.out 0x106628 (movR32R32Effect 0x106628 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[2018]
    (.letOp (n := 2021) (.exec 0x106628 (fun s => s.RIP = 0x106628) (movR32R32Effect 0x106628 2 0 1) (Reg.operands [.gpr 1] [])) #v[2018]
    (.letOp (n := 2022) (.out 0x10662a (shrR32Effect 0x10662a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[2020]
    (.letOp (n := 2023) (.exec 0x10662a (fun s => s.RIP = 0x10662a) (shrR32Effect 0x10662a 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[2020]
    (.letOp (n := 2024) (.out 0x10662c (xorR32R32Effect 0x10662c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[2022, 2018]
    (.letOp (n := 2025) (.exec 0x10662c (fun s => s.RIP = 0x10662c) (xorR32R32Effect 0x10662c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[2022, 2018]
    (.letOp (n := 2026) (.out 0x10662e (andEaxImm32Effect 0x10662e 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[2024]
    (.letOp (n := 2027) (.exec 0x10662e (fun s => s.RIP = 0x10662e) (andEaxImm32Effect 0x10662e 0x5050) (Reg.operands [.gpr 0] [])) #v[2024]
    (b_l10593a_51)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_50 : List UInt8 :=
  [0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x0F,
    0xB7, 0xBC, 0x24, 0xDE, 0x00, 0x00, 0x00, 0x66, 0x89, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x0F,
    0xB7, 0x84, 0x24, 0xE2, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1,
    0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31,
    0xC8, 0x25, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10593a_51

theorem code_l10593a_50 : ∀ x ∈ codeRange 0x1065ed bytes_l10593a_50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x65ed 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_51

def b_l10593a_49 : Block Op Label signature Reg.count 1949 :=
  .letOp (n := 1949) (.out 0x1065a9 (andR32Imm32Effect 0x1065a9 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1947]
    (.letOp (n := 1950) (.exec 0x1065a9 (fun s => s.RIP = 0x1065a9) (andR32Imm32Effect 0x1065a9 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1947]
    (.letOp (n := 1951) (.out 0x1065af (xorR32R32Effect 0x1065af 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1941, 1949]
    (.letOp (n := 1952) (.exec 0x1065af (fun s => s.RIP = 0x1065af) (xorR32R32Effect 0x1065af 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1941, 1949]
    (.letOp (n := 1953) (.out 0x1065b1 (shlR32Effect 0x1065b1 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1949]
    (.letOp (n := 1954) (.exec 0x1065b1 (fun s => s.RIP = 0x1065b1) (shlR32Effect 0x1065b1 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1949]
    (.letOp (n := 1955) (.out 0x1065b4 (xorR32R32Effect 0x1065b4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1953, 1951]
    (.letOp (n := 1956) (.exec 0x1065b4 (fun s => s.RIP = 0x1065b4) (xorR32R32Effect 0x1065b4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1953, 1951]
    (.letOp (n := 1957) (.out 0x1065b6 (movR32R32Effect 0x1065b6 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1955]
    (.letOp (n := 1958) (.exec 0x1065b6 (fun s => s.RIP = 0x1065b6) (movR32R32Effect 0x1065b6 3 8 1) (Reg.operands [.gpr 1] [])) #v[1955]
    (.letOp (n := 1959) (.out 0x1065b9 (shrR32Effect 0x1065b9 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[1957]
    (.letOp (n := 1960) (.exec 0x1065b9 (fun s => s.RIP = 0x1065b9) (shrR32Effect 0x1065b9 3 8 1) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1957]
    (.letOp (n := 1961) (.out 0x1065bc (xorR32R32Effect 0x1065bc 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1959, 1955]
    (.letOp (n := 1962) (.exec 0x1065bc (fun s => s.RIP = 0x1065bc) (xorR32R32Effect 0x1065bc 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1959, 1955]
    (.letOp (n := 1963) (.out 0x1065bf (andR32Imm32Effect 0x1065bf 7 8 0x5050) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[1961]
    (.letOp (n := 1964) (.exec 0x1065bf (fun s => s.RIP = 0x1065bf) (andR32Imm32Effect 0x1065bf 7 8 0x5050) (Reg.operands [.gpr 8] [])) #v[1961]
    (.letOp (n := 1965) (.out 0x1065c6 (xorR32R32Effect 0x1065c6 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[1955, 1963]
    (.letOp (n := 1966) (.exec 0x1065c6 (fun s => s.RIP = 0x1065c6) (xorR32R32Effect 0x1065c6 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[1955, 1963]
    (.letOp (n := 1967) (.out 0x1065c9 (addR32R32Effect 0x1065c9 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[1963, 1963]
    (.letOp (n := 1968) (.exec 0x1065c9 (fun s => s.RIP = 0x1065c9) (addR32R32Effect 0x1065c9 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[1963, 1963]
    (.letOp (n := 1969) (.out 0x1065cc (xorR32R32Effect 0x1065cc 3 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[1967, 1965]
    (.letOp (n := 1970) (.exec 0x1065cc (fun s => s.RIP = 0x1065cc) (xorR32R32Effect 0x1065cc 3 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[1967, 1965]
    (.letOp (n := 1971) (.out 0x1065cf (movzxR32M16Effect 0x1065cf 8 0 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1972) (.exec 0x1065cf (LoadPre 0x1065cf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x1065cf + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1065cf 8 0 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1973) (.out 0x1065d7 (movR32R32Effect 0x1065d7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1971]
    (.letOp (n := 1974) (.exec 0x1065d7 (fun s => s.RIP = 0x1065d7) (movR32R32Effect 0x1065d7 2 1 0) (Reg.operands [.gpr 0] [])) #v[1971]
    (.letOp (n := 1975) (.out 0x1065d9 (shrR32Effect 0x1065d9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1973]
    (.letOp (n := 1976) (.exec 0x1065d9 (fun s => s.RIP = 0x1065d9) (shrR32Effect 0x1065d9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1973]
    (.letOp (n := 1977) (.out 0x1065dc (xorR32R32Effect 0x1065dc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1975, 1971]
    (.letOp (n := 1978) (.exec 0x1065dc (fun s => s.RIP = 0x1065dc) (xorR32R32Effect 0x1065dc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1975, 1971]
    (.letOp (n := 1979) (.out 0x1065de (andR32Imm32Effect 0x1065de 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1977]
    (.letOp (n := 1980) (.exec 0x1065de (fun s => s.RIP = 0x1065de) (andR32Imm32Effect 0x1065de 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1977]
    (.letOp (n := 1981) (.out 0x1065e4 (xorR32R32Effect 0x1065e4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1971, 1979]
    (.letOp (n := 1982) (.exec 0x1065e4 (fun s => s.RIP = 0x1065e4) (xorR32R32Effect 0x1065e4 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1971, 1979]
    (.letOp (n := 1983) (.out 0x1065e6 (shlR32Effect 0x1065e6 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1979]
    (.letOp (n := 1984) (.exec 0x1065e6 (fun s => s.RIP = 0x1065e6) (shlR32Effect 0x1065e6 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1979]
    (.letOp (n := 1985) (.out 0x1065e9 (xorR32R32Effect 0x1065e9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1983, 1981]
    (.letOp (n := 1986) (.exec 0x1065e9 (fun s => s.RIP = 0x1065e9) (xorR32R32Effect 0x1065e9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1983, 1981]
    (.letOp (n := 1987) (.out 0x1065eb (movR32R32Effect 0x1065eb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1985]
    (.letOp (n := 1988) (.exec 0x1065eb (fun s => s.RIP = 0x1065eb) (movR32R32Effect 0x1065eb 2 0 1) (Reg.operands [.gpr 1] [])) #v[1985]
    (b_l10593a_50))))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_49 : List UInt8 :=
  [0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x41, 0x89, 0xC8,
    0x41, 0xD1, 0xE8, 0x41, 0x31, 0xC8, 0x41, 0x81, 0xE0, 0x50, 0x50, 0x00, 0x00, 0x44, 0x31, 0xC1,
    0x45, 0x01, 0xC0, 0x41, 0x31, 0xC8, 0x0F, 0xB7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x89, 0xC1,
    0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x89, 0xC8] ++ bytes_l10593a_50

theorem code_l10593a_49 : ∀ x ∈ codeRange 0x1065a9 bytes_l10593a_49, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x65a9 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_50

def b_l10593a_48 : Block Op Label signature Reg.count 1910 :=
  .letOp (n := 1910) (.out 0x106565 (movzxR32M16Effect 0x106565 8 0 (.sib 4 none 0 (.d32 0xca))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1911) (.exec 0x106565 (LoadPre 0x106565 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x106565 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106565 8 0 (.sib 4 none 0 (.d32 0xca))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1912) (.out 0x10656d (movR32R32Effect 0x10656d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1910]
    (.letOp (n := 1913) (.exec 0x10656d (fun s => s.RIP = 0x10656d) (movR32R32Effect 0x10656d 2 1 0) (Reg.operands [.gpr 0] [])) #v[1910]
    (.letOp (n := 1914) (.out 0x10656f (shrR32Effect 0x10656f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1912]
    (.letOp (n := 1915) (.exec 0x10656f (fun s => s.RIP = 0x10656f) (shrR32Effect 0x10656f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1912]
    (.letOp (n := 1916) (.out 0x106572 (xorR32R32Effect 0x106572 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1914, 1910]
    (.letOp (n := 1917) (.exec 0x106572 (fun s => s.RIP = 0x106572) (xorR32R32Effect 0x106572 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1914, 1910]
    (.letOp (n := 1918) (.out 0x106574 (andR32Imm32Effect 0x106574 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1916]
    (.letOp (n := 1919) (.exec 0x106574 (fun s => s.RIP = 0x106574) (andR32Imm32Effect 0x106574 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1916]
    (.letOp (n := 1920) (.out 0x10657a (xorR32R32Effect 0x10657a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1910, 1918]
    (.letOp (n := 1921) (.exec 0x10657a (fun s => s.RIP = 0x10657a) (xorR32R32Effect 0x10657a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1910, 1918]
    (.letOp (n := 1922) (.out 0x10657c (shlR32Effect 0x10657c 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1918]
    (.letOp (n := 1923) (.exec 0x10657c (fun s => s.RIP = 0x10657c) (shlR32Effect 0x10657c 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1918]
    (.letOp (n := 1924) (.out 0x10657f (xorR32R32Effect 0x10657f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1922, 1920]
    (.letOp (n := 1925) (.exec 0x10657f (fun s => s.RIP = 0x10657f) (xorR32R32Effect 0x10657f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1922, 1920]
    (.letOp (n := 1926) (.out 0x106581 (movR32R32Effect 0x106581 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1924]
    (.letOp (n := 1927) (.exec 0x106581 (fun s => s.RIP = 0x106581) (movR32R32Effect 0x106581 2 0 1) (Reg.operands [.gpr 1] [])) #v[1924]
    (.letOp (n := 1928) (.out 0x106583 (shrR32Effect 0x106583 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1926]
    (.letOp (n := 1929) (.exec 0x106583 (fun s => s.RIP = 0x106583) (shrR32Effect 0x106583 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1926]
    (.letOp (n := 1930) (.out 0x106585 (xorR32R32Effect 0x106585 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1928, 1924]
    (.letOp (n := 1931) (.exec 0x106585 (fun s => s.RIP = 0x106585) (xorR32R32Effect 0x106585 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1928, 1924]
    (.letOp (n := 1932) (.out 0x106587 (andEaxImm32Effect 0x106587 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1930]
    (.letOp (n := 1933) (.exec 0x106587 (fun s => s.RIP = 0x106587) (andEaxImm32Effect 0x106587 0x5050) (Reg.operands [.gpr 0] [])) #v[1930]
    (.letOp (n := 1934) (.out 0x10658c (xorR32R32Effect 0x10658c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1924, 1932]
    (.letOp (n := 1935) (.exec 0x10658c (fun s => s.RIP = 0x10658c) (xorR32R32Effect 0x10658c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1924, 1932]
    (.letOp (n := 1936) (.out 0x10658e (addR32R32Effect 0x10658e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1932, 1932]
    (.letOp (n := 1937) (.exec 0x10658e (fun s => s.RIP = 0x10658e) (addR32R32Effect 0x10658e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1932, 1932]
    (.letOp (n := 1938) (.out 0x106590 (xorR32R32Effect 0x106590 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1936, 1934]
    (.letOp (n := 1939) (.exec 0x106590 (fun s => s.RIP = 0x106590) (xorR32R32Effect 0x106590 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1936, 1934]
    (.letOp (n := 1940) (.exec 0x106592 (StorePre 0x106592 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xca)) s (0x106592 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106592 8 0 (.sib 4 none 0 (.d32 0xca))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1938, 4]
    (.letOp (n := 1941) (.out 0x10659a (movzxR32M16Effect 0x10659a 8 0 (.sib 4 none 0 (.d32 0xdc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1942) (.exec 0x10659a (LoadPre 0x10659a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xdc)) s (0x10659a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10659a 8 0 (.sib 4 none 0 (.d32 0xdc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1943) (.out 0x1065a2 (movR32R32Effect 0x1065a2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1941]
    (.letOp (n := 1944) (.exec 0x1065a2 (fun s => s.RIP = 0x1065a2) (movR32R32Effect 0x1065a2 2 1 0) (Reg.operands [.gpr 0] [])) #v[1941]
    (.letOp (n := 1945) (.out 0x1065a4 (shrR32Effect 0x1065a4 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1943]
    (.letOp (n := 1946) (.exec 0x1065a4 (fun s => s.RIP = 0x1065a4) (shrR32Effect 0x1065a4 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1943]
    (.letOp (n := 1947) (.out 0x1065a7 (xorR32R32Effect 0x1065a7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1945, 1941]
    (.letOp (n := 1948) (.exec 0x1065a7 (fun s => s.RIP = 0x1065a7) (xorR32R32Effect 0x1065a7 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1945, 1941]
    (b_l10593a_49)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_48 : List UInt8 :=
  [0x0F, 0xB7, 0x84, 0x24, 0xCA, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81,
    0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8,
    0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84,
    0x24, 0xCA, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xDC, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1] ++ bytes_l10593a_49

theorem code_l10593a_48 : ∀ x ∈ codeRange 0x106565 bytes_l10593a_48, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6565 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_49

def b_l10593a_47 : Block Op Label signature Reg.count 1872 :=
  .letOp (n := 1872) (.out 0x106522 (xorR32R32Effect 0x106522 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1862, 1870]
    (.letOp (n := 1873) (.exec 0x106522 (fun s => s.RIP = 0x106522) (xorR32R32Effect 0x106522 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1862, 1870]
    (.letOp (n := 1874) (.out 0x106524 (addR32R32Effect 0x106524 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1870, 1870]
    (.letOp (n := 1875) (.exec 0x106524 (fun s => s.RIP = 0x106524) (addR32R32Effect 0x106524 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1870, 1870]
    (.letOp (n := 1876) (.out 0x106526 (xorR32R32Effect 0x106526 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1874, 1872]
    (.letOp (n := 1877) (.exec 0x106526 (fun s => s.RIP = 0x106526) (xorR32R32Effect 0x106526 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1874, 1872]
    (.letOp (n := 1878) (.exec 0x106528 (StorePre 0x106528 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x106528 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106528 8 0 (.sib 4 none 0 (.d32 0xc6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1876, 4]
    (.letOp (n := 1879) (.out 0x106530 (movzxR32M16Effect 0x106530 8 0 (.sib 4 none 0 (.d32 0xc8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1880) (.exec 0x106530 (LoadPre 0x106530 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x106530 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106530 8 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1881) (.out 0x106538 (movR32R32Effect 0x106538 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1879]
    (.letOp (n := 1882) (.exec 0x106538 (fun s => s.RIP = 0x106538) (movR32R32Effect 0x106538 2 1 0) (Reg.operands [.gpr 0] [])) #v[1879]
    (.letOp (n := 1883) (.out 0x10653a (shrR32Effect 0x10653a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1881]
    (.letOp (n := 1884) (.exec 0x10653a (fun s => s.RIP = 0x10653a) (shrR32Effect 0x10653a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1881]
    (.letOp (n := 1885) (.out 0x10653d (xorR32R32Effect 0x10653d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1883, 1879]
    (.letOp (n := 1886) (.exec 0x10653d (fun s => s.RIP = 0x10653d) (xorR32R32Effect 0x10653d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1883, 1879]
    (.letOp (n := 1887) (.out 0x10653f (andR32Imm32Effect 0x10653f 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1885]
    (.letOp (n := 1888) (.exec 0x10653f (fun s => s.RIP = 0x10653f) (andR32Imm32Effect 0x10653f 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1885]
    (.letOp (n := 1889) (.out 0x106545 (xorR32R32Effect 0x106545 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1879, 1887]
    (.letOp (n := 1890) (.exec 0x106545 (fun s => s.RIP = 0x106545) (xorR32R32Effect 0x106545 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1879, 1887]
    (.letOp (n := 1891) (.out 0x106547 (shlR32Effect 0x106547 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1887]
    (.letOp (n := 1892) (.exec 0x106547 (fun s => s.RIP = 0x106547) (shlR32Effect 0x106547 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1887]
    (.letOp (n := 1893) (.out 0x10654a (xorR32R32Effect 0x10654a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1891, 1889]
    (.letOp (n := 1894) (.exec 0x10654a (fun s => s.RIP = 0x10654a) (xorR32R32Effect 0x10654a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1891, 1889]
    (.letOp (n := 1895) (.out 0x10654c (movR32R32Effect 0x10654c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1893]
    (.letOp (n := 1896) (.exec 0x10654c (fun s => s.RIP = 0x10654c) (movR32R32Effect 0x10654c 2 0 1) (Reg.operands [.gpr 1] [])) #v[1893]
    (.letOp (n := 1897) (.out 0x10654e (shrR32Effect 0x10654e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1895]
    (.letOp (n := 1898) (.exec 0x10654e (fun s => s.RIP = 0x10654e) (shrR32Effect 0x10654e 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1895]
    (.letOp (n := 1899) (.out 0x106550 (xorR32R32Effect 0x106550 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1897, 1893]
    (.letOp (n := 1900) (.exec 0x106550 (fun s => s.RIP = 0x106550) (xorR32R32Effect 0x106550 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1897, 1893]
    (.letOp (n := 1901) (.out 0x106552 (andEaxImm32Effect 0x106552 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1899]
    (.letOp (n := 1902) (.exec 0x106552 (fun s => s.RIP = 0x106552) (andEaxImm32Effect 0x106552 0x5050) (Reg.operands [.gpr 0] [])) #v[1899]
    (.letOp (n := 1903) (.out 0x106557 (xorR32R32Effect 0x106557 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1893, 1901]
    (.letOp (n := 1904) (.exec 0x106557 (fun s => s.RIP = 0x106557) (xorR32R32Effect 0x106557 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1893, 1901]
    (.letOp (n := 1905) (.out 0x106559 (addR32R32Effect 0x106559 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1901, 1901]
    (.letOp (n := 1906) (.exec 0x106559 (fun s => s.RIP = 0x106559) (addR32R32Effect 0x106559 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1901, 1901]
    (.letOp (n := 1907) (.out 0x10655b (xorR32R32Effect 0x10655b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1905, 1903]
    (.letOp (n := 1908) (.exec 0x10655b (fun s => s.RIP = 0x10655b) (xorR32R32Effect 0x10655b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1905, 1903]
    (.letOp (n := 1909) (.exec 0x10655d (StorePre 0x10655d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10655d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10655d 8 0 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1907, 4]
    (b_l10593a_48))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_47 : List UInt8 :=
  [0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xC6, 0x00, 0x00, 0x00, 0x0F, 0xB7,
    0x84, 0x24, 0xC8, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10,
    0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8,
    0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xC8,
    0x00, 0x00, 0x00] ++ bytes_l10593a_48

theorem code_l10593a_47 : ∀ x ∈ codeRange 0x106522 bytes_l10593a_47, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6522 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_48

def b_l10593a_46 : Block Op Label signature Reg.count 1833 :=
  .letOp (n := 1833) (.out 0x1064e2 (movR32R32Effect 0x1064e2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1831]
    (.letOp (n := 1834) (.exec 0x1064e2 (fun s => s.RIP = 0x1064e2) (movR32R32Effect 0x1064e2 2 0 1) (Reg.operands [.gpr 1] [])) #v[1831]
    (.letOp (n := 1835) (.out 0x1064e4 (shrR32Effect 0x1064e4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1833]
    (.letOp (n := 1836) (.exec 0x1064e4 (fun s => s.RIP = 0x1064e4) (shrR32Effect 0x1064e4 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1833]
    (.letOp (n := 1837) (.out 0x1064e6 (xorR32R32Effect 0x1064e6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1835, 1831]
    (.letOp (n := 1838) (.exec 0x1064e6 (fun s => s.RIP = 0x1064e6) (xorR32R32Effect 0x1064e6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1835, 1831]
    (.letOp (n := 1839) (.out 0x1064e8 (andEaxImm32Effect 0x1064e8 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1837]
    (.letOp (n := 1840) (.exec 0x1064e8 (fun s => s.RIP = 0x1064e8) (andEaxImm32Effect 0x1064e8 0x5050) (Reg.operands [.gpr 0] [])) #v[1837]
    (.letOp (n := 1841) (.out 0x1064ed (xorR32R32Effect 0x1064ed 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1831, 1839]
    (.letOp (n := 1842) (.exec 0x1064ed (fun s => s.RIP = 0x1064ed) (xorR32R32Effect 0x1064ed 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1831, 1839]
    (.letOp (n := 1843) (.out 0x1064ef (addR32R32Effect 0x1064ef 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1839, 1839]
    (.letOp (n := 1844) (.exec 0x1064ef (fun s => s.RIP = 0x1064ef) (addR32R32Effect 0x1064ef 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1839, 1839]
    (.letOp (n := 1845) (.out 0x1064f1 (xorR32R32Effect 0x1064f1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1843, 1841]
    (.letOp (n := 1846) (.exec 0x1064f1 (fun s => s.RIP = 0x1064f1) (xorR32R32Effect 0x1064f1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1843, 1841]
    (.letOp (n := 1847) (.exec 0x1064f3 (StorePre 0x1064f3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x1064f3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1064f3 8 0 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1845, 4]
    (.letOp (n := 1848) (.out 0x1064fb (movzxR32M16Effect 0x1064fb 8 0 (.sib 4 none 0 (.d32 0xc6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1849) (.exec 0x1064fb (LoadPre 0x1064fb (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc6)) s (0x1064fb + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1064fb 8 0 (.sib 4 none 0 (.d32 0xc6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1850) (.out 0x106503 (movR32R32Effect 0x106503 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1848]
    (.letOp (n := 1851) (.exec 0x106503 (fun s => s.RIP = 0x106503) (movR32R32Effect 0x106503 2 1 0) (Reg.operands [.gpr 0] [])) #v[1848]
    (.letOp (n := 1852) (.out 0x106505 (shrR32Effect 0x106505 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1850]
    (.letOp (n := 1853) (.exec 0x106505 (fun s => s.RIP = 0x106505) (shrR32Effect 0x106505 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1850]
    (.letOp (n := 1854) (.out 0x106508 (xorR32R32Effect 0x106508 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1852, 1848]
    (.letOp (n := 1855) (.exec 0x106508 (fun s => s.RIP = 0x106508) (xorR32R32Effect 0x106508 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1852, 1848]
    (.letOp (n := 1856) (.out 0x10650a (andR32Imm32Effect 0x10650a 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1854]
    (.letOp (n := 1857) (.exec 0x10650a (fun s => s.RIP = 0x10650a) (andR32Imm32Effect 0x10650a 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1854]
    (.letOp (n := 1858) (.out 0x106510 (xorR32R32Effect 0x106510 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1848, 1856]
    (.letOp (n := 1859) (.exec 0x106510 (fun s => s.RIP = 0x106510) (xorR32R32Effect 0x106510 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1848, 1856]
    (.letOp (n := 1860) (.out 0x106512 (shlR32Effect 0x106512 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1856]
    (.letOp (n := 1861) (.exec 0x106512 (fun s => s.RIP = 0x106512) (shlR32Effect 0x106512 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1856]
    (.letOp (n := 1862) (.out 0x106515 (xorR32R32Effect 0x106515 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1860, 1858]
    (.letOp (n := 1863) (.exec 0x106515 (fun s => s.RIP = 0x106515) (xorR32R32Effect 0x106515 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1860, 1858]
    (.letOp (n := 1864) (.out 0x106517 (movR32R32Effect 0x106517 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1862]
    (.letOp (n := 1865) (.exec 0x106517 (fun s => s.RIP = 0x106517) (movR32R32Effect 0x106517 2 0 1) (Reg.operands [.gpr 1] [])) #v[1862]
    (.letOp (n := 1866) (.out 0x106519 (shrR32Effect 0x106519 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1864]
    (.letOp (n := 1867) (.exec 0x106519 (fun s => s.RIP = 0x106519) (shrR32Effect 0x106519 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1864]
    (.letOp (n := 1868) (.out 0x10651b (xorR32R32Effect 0x10651b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1866, 1862]
    (.letOp (n := 1869) (.exec 0x10651b (fun s => s.RIP = 0x10651b) (xorR32R32Effect 0x10651b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1866, 1862]
    (.letOp (n := 1870) (.out 0x10651d (andEaxImm32Effect 0x10651d 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1868]
    (.letOp (n := 1871) (.exec 0x10651d (fun s => s.RIP = 0x10651d) (andEaxImm32Effect 0x10651d 0x5050) (Reg.operands [.gpr 0] [])) #v[1868]
    (b_l10593a_47)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_46 : List UInt8 :=
  [0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31,
    0xC8, 0x66, 0x89, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xC6, 0x00, 0x00,
    0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8,
    0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00] ++ bytes_l10593a_47

theorem code_l10593a_46 : ∀ x ∈ codeRange 0x1064e2 bytes_l10593a_46, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x64e2 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_47

def b_l10593a_45 : Block Op Label signature Reg.count 1794 :=
  .letOp (n := 1794) (.out 0x1064a0 (andR32Imm32Effect 0x1064a0 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1792]
    (.letOp (n := 1795) (.exec 0x1064a0 (fun s => s.RIP = 0x1064a0) (andR32Imm32Effect 0x1064a0 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1792]
    (.letOp (n := 1796) (.out 0x1064a6 (xorR32R32Effect 0x1064a6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1786, 1794]
    (.letOp (n := 1797) (.exec 0x1064a6 (fun s => s.RIP = 0x1064a6) (xorR32R32Effect 0x1064a6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1786, 1794]
    (.letOp (n := 1798) (.out 0x1064a8 (shlR32Effect 0x1064a8 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1794]
    (.letOp (n := 1799) (.exec 0x1064a8 (fun s => s.RIP = 0x1064a8) (shlR32Effect 0x1064a8 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1794]
    (.letOp (n := 1800) (.out 0x1064ab (xorR32R32Effect 0x1064ab 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1798, 1796]
    (.letOp (n := 1801) (.exec 0x1064ab (fun s => s.RIP = 0x1064ab) (xorR32R32Effect 0x1064ab 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1798, 1796]
    (.letOp (n := 1802) (.out 0x1064ad (movR32R32Effect 0x1064ad 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1800]
    (.letOp (n := 1803) (.exec 0x1064ad (fun s => s.RIP = 0x1064ad) (movR32R32Effect 0x1064ad 2 0 1) (Reg.operands [.gpr 1] [])) #v[1800]
    (.letOp (n := 1804) (.out 0x1064af (shrR32Effect 0x1064af 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1802]
    (.letOp (n := 1805) (.exec 0x1064af (fun s => s.RIP = 0x1064af) (shrR32Effect 0x1064af 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1802]
    (.letOp (n := 1806) (.out 0x1064b1 (xorR32R32Effect 0x1064b1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1804, 1800]
    (.letOp (n := 1807) (.exec 0x1064b1 (fun s => s.RIP = 0x1064b1) (xorR32R32Effect 0x1064b1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1804, 1800]
    (.letOp (n := 1808) (.out 0x1064b3 (andEaxImm32Effect 0x1064b3 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1806]
    (.letOp (n := 1809) (.exec 0x1064b3 (fun s => s.RIP = 0x1064b3) (andEaxImm32Effect 0x1064b3 0x5050) (Reg.operands [.gpr 0] [])) #v[1806]
    (.letOp (n := 1810) (.out 0x1064b8 (xorR32R32Effect 0x1064b8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1800, 1808]
    (.letOp (n := 1811) (.exec 0x1064b8 (fun s => s.RIP = 0x1064b8) (xorR32R32Effect 0x1064b8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1800, 1808]
    (.letOp (n := 1812) (.out 0x1064ba (addR32R32Effect 0x1064ba 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1808, 1808]
    (.letOp (n := 1813) (.exec 0x1064ba (fun s => s.RIP = 0x1064ba) (addR32R32Effect 0x1064ba 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1808, 1808]
    (.letOp (n := 1814) (.out 0x1064bc (xorR32R32Effect 0x1064bc 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1812, 1810]
    (.letOp (n := 1815) (.exec 0x1064bc (fun s => s.RIP = 0x1064bc) (xorR32R32Effect 0x1064bc 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1812, 1810]
    (.letOp (n := 1816) (.exec 0x1064be (StorePre 0x1064be 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x1064be + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1064be 8 0 (.sib 4 none 0 (.d32 0xc2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1814, 4]
    (.letOp (n := 1817) (.out 0x1064c6 (movzxR32M16Effect 0x1064c6 8 0 (.sib 4 none 0 (.d32 0xc4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1818) (.exec 0x1064c6 (LoadPre 0x1064c6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc4)) s (0x1064c6 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1064c6 8 0 (.sib 4 none 0 (.d32 0xc4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1819) (.out 0x1064ce (movR32R32Effect 0x1064ce 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1817]
    (.letOp (n := 1820) (.exec 0x1064ce (fun s => s.RIP = 0x1064ce) (movR32R32Effect 0x1064ce 2 1 0) (Reg.operands [.gpr 0] [])) #v[1817]
    (.letOp (n := 1821) (.out 0x1064d0 (shrR32Effect 0x1064d0 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1819]
    (.letOp (n := 1822) (.exec 0x1064d0 (fun s => s.RIP = 0x1064d0) (shrR32Effect 0x1064d0 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1819]
    (.letOp (n := 1823) (.out 0x1064d3 (xorR32R32Effect 0x1064d3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1821, 1817]
    (.letOp (n := 1824) (.exec 0x1064d3 (fun s => s.RIP = 0x1064d3) (xorR32R32Effect 0x1064d3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1821, 1817]
    (.letOp (n := 1825) (.out 0x1064d5 (andR32Imm32Effect 0x1064d5 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1823]
    (.letOp (n := 1826) (.exec 0x1064d5 (fun s => s.RIP = 0x1064d5) (andR32Imm32Effect 0x1064d5 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1823]
    (.letOp (n := 1827) (.out 0x1064db (xorR32R32Effect 0x1064db 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1817, 1825]
    (.letOp (n := 1828) (.exec 0x1064db (fun s => s.RIP = 0x1064db) (xorR32R32Effect 0x1064db 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1817, 1825]
    (.letOp (n := 1829) (.out 0x1064dd (shlR32Effect 0x1064dd 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1825]
    (.letOp (n := 1830) (.exec 0x1064dd (fun s => s.RIP = 0x1064dd) (shlR32Effect 0x1064dd 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1825]
    (.letOp (n := 1831) (.out 0x1064e0 (xorR32R32Effect 0x1064e0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1829, 1827]
    (.letOp (n := 1832) (.exec 0x1064e0 (fun s => s.RIP = 0x1064e0) (xorR32R32Effect 0x1064e0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1829, 1827]
    (b_l10593a_46)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_45 : List UInt8 :=
  [0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1,
    0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89,
    0x84, 0x24, 0xC2, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xC4, 0x00, 0x00, 0x00, 0x89, 0xC1,
    0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1] ++ bytes_l10593a_46

theorem code_l10593a_45 : ∀ x ∈ codeRange 0x1064a0 bytes_l10593a_45, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x64a0 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_46

def b_l10593a_44 : Block Op Label signature Reg.count 1755 :=
  .letOp (n := 1755) (.out 0x10645c (movzxR32M16Effect 0x10645c 8 0 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1756) (.exec 0x10645c (LoadPre 0x10645c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10645c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10645c 8 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1757) (.out 0x106464 (movR32R32Effect 0x106464 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1755]
    (.letOp (n := 1758) (.exec 0x106464 (fun s => s.RIP = 0x106464) (movR32R32Effect 0x106464 2 1 0) (Reg.operands [.gpr 0] [])) #v[1755]
    (.letOp (n := 1759) (.out 0x106466 (shrR32Effect 0x106466 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1757]
    (.letOp (n := 1760) (.exec 0x106466 (fun s => s.RIP = 0x106466) (shrR32Effect 0x106466 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1757]
    (.letOp (n := 1761) (.out 0x106469 (xorR32R32Effect 0x106469 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1759, 1755]
    (.letOp (n := 1762) (.exec 0x106469 (fun s => s.RIP = 0x106469) (xorR32R32Effect 0x106469 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1759, 1755]
    (.letOp (n := 1763) (.out 0x10646b (andR32Imm32Effect 0x10646b 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1761]
    (.letOp (n := 1764) (.exec 0x10646b (fun s => s.RIP = 0x10646b) (andR32Imm32Effect 0x10646b 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1761]
    (.letOp (n := 1765) (.out 0x106471 (xorR32R32Effect 0x106471 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1755, 1763]
    (.letOp (n := 1766) (.exec 0x106471 (fun s => s.RIP = 0x106471) (xorR32R32Effect 0x106471 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1755, 1763]
    (.letOp (n := 1767) (.out 0x106473 (shlR32Effect 0x106473 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1763]
    (.letOp (n := 1768) (.exec 0x106473 (fun s => s.RIP = 0x106473) (shlR32Effect 0x106473 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1763]
    (.letOp (n := 1769) (.out 0x106476 (xorR32R32Effect 0x106476 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1767, 1765]
    (.letOp (n := 1770) (.exec 0x106476 (fun s => s.RIP = 0x106476) (xorR32R32Effect 0x106476 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1767, 1765]
    (.letOp (n := 1771) (.out 0x106478 (movR32R32Effect 0x106478 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1769]
    (.letOp (n := 1772) (.exec 0x106478 (fun s => s.RIP = 0x106478) (movR32R32Effect 0x106478 2 0 1) (Reg.operands [.gpr 1] [])) #v[1769]
    (.letOp (n := 1773) (.out 0x10647a (shrR32Effect 0x10647a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1771]
    (.letOp (n := 1774) (.exec 0x10647a (fun s => s.RIP = 0x10647a) (shrR32Effect 0x10647a 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1771]
    (.letOp (n := 1775) (.out 0x10647c (xorR32R32Effect 0x10647c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1773, 1769]
    (.letOp (n := 1776) (.exec 0x10647c (fun s => s.RIP = 0x10647c) (xorR32R32Effect 0x10647c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1773, 1769]
    (.letOp (n := 1777) (.out 0x10647e (andEaxImm32Effect 0x10647e 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1775]
    (.letOp (n := 1778) (.exec 0x10647e (fun s => s.RIP = 0x10647e) (andEaxImm32Effect 0x10647e 0x5050) (Reg.operands [.gpr 0] [])) #v[1775]
    (.letOp (n := 1779) (.out 0x106483 (xorR32R32Effect 0x106483 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1769, 1777]
    (.letOp (n := 1780) (.exec 0x106483 (fun s => s.RIP = 0x106483) (xorR32R32Effect 0x106483 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1769, 1777]
    (.letOp (n := 1781) (.out 0x106485 (addR32R32Effect 0x106485 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1777, 1777]
    (.letOp (n := 1782) (.exec 0x106485 (fun s => s.RIP = 0x106485) (addR32R32Effect 0x106485 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1777, 1777]
    (.letOp (n := 1783) (.out 0x106487 (xorR32R32Effect 0x106487 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1781, 1779]
    (.letOp (n := 1784) (.exec 0x106487 (fun s => s.RIP = 0x106487) (xorR32R32Effect 0x106487 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1781, 1779]
    (.letOp (n := 1785) (.exec 0x106489 (StorePre 0x106489 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x106489 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106489 8 0 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1783, 4]
    (.letOp (n := 1786) (.out 0x106491 (movzxR32M16Effect 0x106491 8 0 (.sib 4 none 0 (.d32 0xc2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1787) (.exec 0x106491 (LoadPre 0x106491 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc2)) s (0x106491 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106491 8 0 (.sib 4 none 0 (.d32 0xc2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1788) (.out 0x106499 (movR32R32Effect 0x106499 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1786]
    (.letOp (n := 1789) (.exec 0x106499 (fun s => s.RIP = 0x106499) (movR32R32Effect 0x106499 2 1 0) (Reg.operands [.gpr 0] [])) #v[1786]
    (.letOp (n := 1790) (.out 0x10649b (shrR32Effect 0x10649b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1788]
    (.letOp (n := 1791) (.exec 0x10649b (fun s => s.RIP = 0x10649b) (shrR32Effect 0x10649b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1788]
    (.letOp (n := 1792) (.out 0x10649e (xorR32R32Effect 0x10649e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1790, 1786]
    (.letOp (n := 1793) (.exec 0x10649e (fun s => s.RIP = 0x10649e) (xorR32R32Effect 0x10649e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1790, 1786]
    (b_l10593a_45)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_44 : List UInt8 :=
  [0x0F, 0xB7, 0x84, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81,
    0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8,
    0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84,
    0x24, 0xC0, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xC2, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1] ++ bytes_l10593a_45

theorem code_l10593a_44 : ∀ x ∈ codeRange 0x10645c bytes_l10593a_44, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x645c 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_45

def b_l10593a_43 : Block Op Label signature Reg.count 1716 :=
  .letOp (n := 1716) (.out 0x106417 (andR32Imm32Effect 0x106417 7 10 0x5050) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[1714]
    (.letOp (n := 1717) (.exec 0x106417 (fun s => s.RIP = 0x106417) (andR32Imm32Effect 0x106417 7 10 0x5050) (Reg.operands [.gpr 10] [])) #v[1714]
    (.letOp (n := 1718) (.out 0x10641e (xorR32R32Effect 0x10641e 3 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[1708, 1716]
    (.letOp (n := 1719) (.exec 0x10641e (fun s => s.RIP = 0x10641e) (xorR32R32Effect 0x10641e 3 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[1708, 1716]
    (.letOp (n := 1720) (.out 0x106421 (addR32R32Effect 0x106421 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[1716, 1716]
    (.letOp (n := 1721) (.exec 0x106421 (fun s => s.RIP = 0x106421) (addR32R32Effect 0x106421 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[1716, 1716]
    (.letOp (n := 1722) (.out 0x106424 (xorR32R32Effect 0x106424 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[1720, 1718]
    (.letOp (n := 1723) (.exec 0x106424 (fun s => s.RIP = 0x106424) (xorR32R32Effect 0x106424 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[1720, 1718]
    (.letOp (n := 1724) (.out 0x106427 (movzxR32M16Effect 0x106427 8 0 (.sib 4 none 0 (.d32 0xbe))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1725) (.exec 0x106427 (LoadPre 0x106427 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x106427 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106427 8 0 (.sib 4 none 0 (.d32 0xbe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1726) (.out 0x10642f (movR32R32Effect 0x10642f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1724]
    (.letOp (n := 1727) (.exec 0x10642f (fun s => s.RIP = 0x10642f) (movR32R32Effect 0x10642f 2 1 0) (Reg.operands [.gpr 0] [])) #v[1724]
    (.letOp (n := 1728) (.out 0x106431 (shrR32Effect 0x106431 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1726]
    (.letOp (n := 1729) (.exec 0x106431 (fun s => s.RIP = 0x106431) (shrR32Effect 0x106431 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1726]
    (.letOp (n := 1730) (.out 0x106434 (xorR32R32Effect 0x106434 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1728, 1724]
    (.letOp (n := 1731) (.exec 0x106434 (fun s => s.RIP = 0x106434) (xorR32R32Effect 0x106434 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1728, 1724]
    (.letOp (n := 1732) (.out 0x106436 (andR32Imm32Effect 0x106436 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1730]
    (.letOp (n := 1733) (.exec 0x106436 (fun s => s.RIP = 0x106436) (andR32Imm32Effect 0x106436 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1730]
    (.letOp (n := 1734) (.out 0x10643c (xorR32R32Effect 0x10643c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1724, 1732]
    (.letOp (n := 1735) (.exec 0x10643c (fun s => s.RIP = 0x10643c) (xorR32R32Effect 0x10643c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1724, 1732]
    (.letOp (n := 1736) (.out 0x10643e (shlR32Effect 0x10643e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1732]
    (.letOp (n := 1737) (.exec 0x10643e (fun s => s.RIP = 0x10643e) (shlR32Effect 0x10643e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1732]
    (.letOp (n := 1738) (.out 0x106441 (xorR32R32Effect 0x106441 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1736, 1734]
    (.letOp (n := 1739) (.exec 0x106441 (fun s => s.RIP = 0x106441) (xorR32R32Effect 0x106441 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1736, 1734]
    (.letOp (n := 1740) (.out 0x106443 (movR32R32Effect 0x106443 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1738]
    (.letOp (n := 1741) (.exec 0x106443 (fun s => s.RIP = 0x106443) (movR32R32Effect 0x106443 2 0 1) (Reg.operands [.gpr 1] [])) #v[1738]
    (.letOp (n := 1742) (.out 0x106445 (shrR32Effect 0x106445 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1740]
    (.letOp (n := 1743) (.exec 0x106445 (fun s => s.RIP = 0x106445) (shrR32Effect 0x106445 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1740]
    (.letOp (n := 1744) (.out 0x106447 (xorR32R32Effect 0x106447 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1742, 1738]
    (.letOp (n := 1745) (.exec 0x106447 (fun s => s.RIP = 0x106447) (xorR32R32Effect 0x106447 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1742, 1738]
    (.letOp (n := 1746) (.out 0x106449 (andEaxImm32Effect 0x106449 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1744]
    (.letOp (n := 1747) (.exec 0x106449 (fun s => s.RIP = 0x106449) (andEaxImm32Effect 0x106449 0x5050) (Reg.operands [.gpr 0] [])) #v[1744]
    (.letOp (n := 1748) (.out 0x10644e (xorR32R32Effect 0x10644e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1738, 1746]
    (.letOp (n := 1749) (.exec 0x10644e (fun s => s.RIP = 0x10644e) (xorR32R32Effect 0x10644e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1738, 1746]
    (.letOp (n := 1750) (.out 0x106450 (addR32R32Effect 0x106450 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1746, 1746]
    (.letOp (n := 1751) (.exec 0x106450 (fun s => s.RIP = 0x106450) (addR32R32Effect 0x106450 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1746, 1746]
    (.letOp (n := 1752) (.out 0x106452 (xorR32R32Effect 0x106452 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1750, 1748]
    (.letOp (n := 1753) (.exec 0x106452 (fun s => s.RIP = 0x106452) (xorR32R32Effect 0x106452 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1750, 1748]
    (.letOp (n := 1754) (.exec 0x106454 (StorePre 0x106454 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbe)) s (0x106454 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106454 8 0 (.sib 4 none 0 (.d32 0xbe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1752, 4]
    (b_l10593a_44)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_43 : List UInt8 :=
  [0x41, 0x81, 0xE2, 0x50, 0x50, 0x00, 0x00, 0x44, 0x31, 0xD1, 0x45, 0x01, 0xD2, 0x41, 0x31, 0xCA,
    0x0F, 0xB7, 0x84, 0x24, 0xBE, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81,
    0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8,
    0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84,
    0x24, 0xBE, 0x00, 0x00, 0x00] ++ bytes_l10593a_44

theorem code_l10593a_43 : ∀ x ∈ codeRange 0x106417 bytes_l10593a_43, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6417 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_44

def b_l10593a_42 : Block Op Label signature Reg.count 1677 :=
  .letOp (n := 1677) (.out 0x1063ce (movzxR32M16Effect 0x1063ce 8 0 (.sib 4 none 0 (.d32 0xba))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1678) (.exec 0x1063ce (LoadPre 0x1063ce (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x1063ce + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063ce 8 0 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1679) (.out 0x1063d6 (movR32R32Effect 0x1063d6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1677]
    (.letOp (n := 1680) (.exec 0x1063d6 (fun s => s.RIP = 0x1063d6) (movR32R32Effect 0x1063d6 2 1 0) (Reg.operands [.gpr 0] [])) #v[1677]
    (.letOp (n := 1681) (.out 0x1063d8 (shrR32Effect 0x1063d8 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1679]
    (.letOp (n := 1682) (.exec 0x1063d8 (fun s => s.RIP = 0x1063d8) (shrR32Effect 0x1063d8 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1679]
    (.letOp (n := 1683) (.out 0x1063db (xorR32R32Effect 0x1063db 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1681, 1677]
    (.letOp (n := 1684) (.exec 0x1063db (fun s => s.RIP = 0x1063db) (xorR32R32Effect 0x1063db 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1681, 1677]
    (.letOp (n := 1685) (.out 0x1063dd (andR32Imm32Effect 0x1063dd 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1683]
    (.letOp (n := 1686) (.exec 0x1063dd (fun s => s.RIP = 0x1063dd) (andR32Imm32Effect 0x1063dd 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1683]
    (.letOp (n := 1687) (.out 0x1063e3 (xorR32R32Effect 0x1063e3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1677, 1685]
    (.letOp (n := 1688) (.exec 0x1063e3 (fun s => s.RIP = 0x1063e3) (xorR32R32Effect 0x1063e3 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1677, 1685]
    (.letOp (n := 1689) (.out 0x1063e5 (shlR32Effect 0x1063e5 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1685]
    (.letOp (n := 1690) (.exec 0x1063e5 (fun s => s.RIP = 0x1063e5) (shlR32Effect 0x1063e5 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1685]
    (.letOp (n := 1691) (.out 0x1063e8 (xorR32R32Effect 0x1063e8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1689, 1687]
    (.letOp (n := 1692) (.exec 0x1063e8 (fun s => s.RIP = 0x1063e8) (xorR32R32Effect 0x1063e8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1689, 1687]
    (.letOp (n := 1693) (.exec 0x1063ea (StorePre 0x1063ea 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xba)) s (0x1063ea + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1063ea 8 1 (.sib 4 none 0 (.d32 0xba))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1691, 4]
    (.letOp (n := 1694) (.out 0x1063f2 (movzxR32M16Effect 0x1063f2 8 0 (.sib 4 none 0 (.d32 0xbc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1695) (.exec 0x1063f2 (LoadPre 0x1063f2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xbc)) s (0x1063f2 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063f2 8 0 (.sib 4 none 0 (.d32 0xbc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1696) (.out 0x1063fa (movR32R32Effect 0x1063fa 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1694]
    (.letOp (n := 1697) (.exec 0x1063fa (fun s => s.RIP = 0x1063fa) (movR32R32Effect 0x1063fa 2 1 0) (Reg.operands [.gpr 0] [])) #v[1694]
    (.letOp (n := 1698) (.out 0x1063fc (shrR32Effect 0x1063fc 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1696]
    (.letOp (n := 1699) (.exec 0x1063fc (fun s => s.RIP = 0x1063fc) (shrR32Effect 0x1063fc 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1696]
    (.letOp (n := 1700) (.out 0x1063ff (xorR32R32Effect 0x1063ff 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1698, 1694]
    (.letOp (n := 1701) (.exec 0x1063ff (fun s => s.RIP = 0x1063ff) (xorR32R32Effect 0x1063ff 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1698, 1694]
    (.letOp (n := 1702) (.out 0x106401 (andR32Imm32Effect 0x106401 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1700]
    (.letOp (n := 1703) (.exec 0x106401 (fun s => s.RIP = 0x106401) (andR32Imm32Effect 0x106401 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1700]
    (.letOp (n := 1704) (.out 0x106407 (xorR32R32Effect 0x106407 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1694, 1702]
    (.letOp (n := 1705) (.exec 0x106407 (fun s => s.RIP = 0x106407) (xorR32R32Effect 0x106407 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1694, 1702]
    (.letOp (n := 1706) (.out 0x106409 (shlR32Effect 0x106409 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1702]
    (.letOp (n := 1707) (.exec 0x106409 (fun s => s.RIP = 0x106409) (shlR32Effect 0x106409 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1702]
    (.letOp (n := 1708) (.out 0x10640c (xorR32R32Effect 0x10640c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1706, 1704]
    (.letOp (n := 1709) (.exec 0x10640c (fun s => s.RIP = 0x10640c) (xorR32R32Effect 0x10640c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1706, 1704]
    (.letOp (n := 1710) (.out 0x10640e (movR32R32Effect 0x10640e 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[1708]
    (.letOp (n := 1711) (.exec 0x10640e (fun s => s.RIP = 0x10640e) (movR32R32Effect 0x10640e 3 10 1) (Reg.operands [.gpr 1] [])) #v[1708]
    (.letOp (n := 1712) (.out 0x106411 (shrR32Effect 0x106411 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[1710]
    (.letOp (n := 1713) (.exec 0x106411 (fun s => s.RIP = 0x106411) (shrR32Effect 0x106411 3 10 1) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1710]
    (.letOp (n := 1714) (.out 0x106414 (xorR32R32Effect 0x106414 3 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[1712, 1708]
    (.letOp (n := 1715) (.exec 0x106414 (fun s => s.RIP = 0x106414) (xorR32R32Effect 0x106414 3 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[1712, 1708]
    (b_l10593a_43)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_42 : List UInt8 :=
  [0x0F, 0xB7, 0x84, 0x24, 0xBA, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81,
    0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x8C, 0x24,
    0xBA, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xBC, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9,
    0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1,
    0x41, 0x89, 0xCA, 0x41, 0xD1, 0xEA, 0x41, 0x31, 0xCA] ++ bytes_l10593a_43

theorem code_l10593a_42 : ∀ x ∈ codeRange 0x1063ce bytes_l10593a_42, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x63ce 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_43

def b_l10593a_41 : Block Op Label signature Reg.count 1638 :=
  .letOp (n := 1638) (.out 0x106380 (xorR32R32Effect 0x106380 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1628, 1636]
    (.letOp (n := 1639) (.exec 0x106380 (fun s => s.RIP = 0x106380) (xorR32R32Effect 0x106380 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1628, 1636]
    (.letOp (n := 1640) (.out 0x106382 (shlR32Effect 0x106382 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1636]
    (.letOp (n := 1641) (.exec 0x106382 (fun s => s.RIP = 0x106382) (shlR32Effect 0x106382 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1636]
    (.letOp (n := 1642) (.out 0x106385 (xorR32R32Effect 0x106385 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1640, 1638]
    (.letOp (n := 1643) (.exec 0x106385 (fun s => s.RIP = 0x106385) (xorR32R32Effect 0x106385 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1640, 1638]
    (.letOp (n := 1644) (.exec 0x106387 (StorePre 0x106387 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x106387 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106387 8 1 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1642, 4]
    (.letOp (n := 1645) (.out 0x10638f (movzxR32M16Effect 0x10638f 8 0 (.sib 4 none 0 (.d32 0xb6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1646) (.exec 0x10638f (LoadPre 0x10638f (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb6)) s (0x10638f + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10638f 8 0 (.sib 4 none 0 (.d32 0xb6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1647) (.out 0x106397 (movR32R32Effect 0x106397 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[1645]
    (.letOp (n := 1648) (.exec 0x106397 (fun s => s.RIP = 0x106397) (movR32R32Effect 0x106397 2 3 0) (Reg.operands [.gpr 0] [])) #v[1645]
    (.letOp (n := 1649) (.out 0x106399 (shrR32Effect 0x106399 3 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1647]
    (.letOp (n := 1650) (.exec 0x106399 (fun s => s.RIP = 0x106399) (shrR32Effect 0x106399 3 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1647]
    (.letOp (n := 1651) (.out 0x10639c (xorR32R32Effect 0x10639c 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[1649, 1645]
    (.letOp (n := 1652) (.exec 0x10639c (fun s => s.RIP = 0x10639c) (xorR32R32Effect 0x10639c 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1649, 1645]
    (.letOp (n := 1653) (.out 0x10639e (andR32Imm32Effect 0x10639e 6 3 0x3030) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[1651]
    (.letOp (n := 1654) (.exec 0x10639e (fun s => s.RIP = 0x10639e) (andR32Imm32Effect 0x10639e 6 3 0x3030) (Reg.operands [.gpr 3] [])) #v[1651]
    (.letOp (n := 1655) (.out 0x1063a4 (xorR32R32Effect 0x1063a4 2 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[1645, 1653]
    (.letOp (n := 1656) (.exec 0x1063a4 (fun s => s.RIP = 0x1063a4) (xorR32R32Effect 0x1063a4 2 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[1645, 1653]
    (.letOp (n := 1657) (.out 0x1063a6 (shlR32Effect 0x1063a6 3 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[1653]
    (.letOp (n := 1658) (.exec 0x1063a6 (fun s => s.RIP = 0x1063a6) (shlR32Effect 0x1063a6 3 3 2) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1653]
    (.letOp (n := 1659) (.out 0x1063a9 (xorR32R32Effect 0x1063a9 2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[1657, 1655]
    (.letOp (n := 1660) (.exec 0x1063a9 (fun s => s.RIP = 0x1063a9) (xorR32R32Effect 0x1063a9 2 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[1657, 1655]
    (.letOp (n := 1661) (.out 0x1063ab (movzxR32M16Effect 0x1063ab 8 0 (.sib 4 none 0 (.d32 0xb8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1662) (.exec 0x1063ab (LoadPre 0x1063ab (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x1063ab + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1063ab 8 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1663) (.out 0x1063b3 (movR32R32Effect 0x1063b3 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[1661]
    (.letOp (n := 1664) (.exec 0x1063b3 (fun s => s.RIP = 0x1063b3) (movR32R32Effect 0x1063b3 3 11 0) (Reg.operands [.gpr 0] [])) #v[1661]
    (.letOp (n := 1665) (.out 0x1063b6 (shrR32Effect 0x1063b6 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1663]
    (.letOp (n := 1666) (.exec 0x1063b6 (fun s => s.RIP = 0x1063b6) (shrR32Effect 0x1063b6 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1663]
    (.letOp (n := 1667) (.out 0x1063ba (xorR32R32Effect 0x1063ba 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[1665, 1661]
    (.letOp (n := 1668) (.exec 0x1063ba (fun s => s.RIP = 0x1063ba) (xorR32R32Effect 0x1063ba 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1665, 1661]
    (.letOp (n := 1669) (.out 0x1063bd (andR32Imm32Effect 0x1063bd 7 11 0x3030) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[1667]
    (.letOp (n := 1670) (.exec 0x1063bd (fun s => s.RIP = 0x1063bd) (andR32Imm32Effect 0x1063bd 7 11 0x3030) (Reg.operands [.gpr 11] [])) #v[1667]
    (.letOp (n := 1671) (.out 0x1063c4 (xorR32R32Effect 0x1063c4 3 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[1661, 1669]
    (.letOp (n := 1672) (.exec 0x1063c4 (fun s => s.RIP = 0x1063c4) (xorR32R32Effect 0x1063c4 3 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[1661, 1669]
    (.letOp (n := 1673) (.out 0x1063c7 (shlR32Effect 0x1063c7 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[1669]
    (.letOp (n := 1674) (.exec 0x1063c7 (fun s => s.RIP = 0x1063c7) (shlR32Effect 0x1063c7 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1669]
    (.letOp (n := 1675) (.out 0x1063cb (xorR32R32Effect 0x1063cb 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[1673, 1671]
    (.letOp (n := 1676) (.exec 0x1063cb (fun s => s.RIP = 0x1063cb) (xorR32R32Effect 0x1063cb 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[1673, 1671]
    (b_l10593a_42)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_41 : List UInt8 :=
  [0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x8C, 0x24, 0xB4, 0x00, 0x00, 0x00, 0x0F,
    0xB7, 0x84, 0x24, 0xB6, 0x00, 0x00, 0x00, 0x89, 0xC3, 0xC1, 0xEB, 0x02, 0x31, 0xC3, 0x81, 0xE3,
    0x30, 0x30, 0x00, 0x00, 0x31, 0xD8, 0xC1, 0xE3, 0x02, 0x31, 0xC3, 0x0F, 0xB7, 0x84, 0x24, 0xB8,
    0x00, 0x00, 0x00, 0x41, 0x89, 0xC3, 0x41, 0xC1, 0xEB, 0x02, 0x41, 0x31, 0xC3, 0x41, 0x81, 0xE3,
    0x30, 0x30, 0x00, 0x00, 0x44, 0x31, 0xD8, 0x41, 0xC1, 0xE3, 0x02, 0x41, 0x31, 0xC3] ++ bytes_l10593a_42

theorem code_l10593a_41 : ∀ x ∈ codeRange 0x106380 bytes_l10593a_41, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6380 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_42

def b_l10593a_40 : Block Op Label signature Reg.count 1600 :=
  .letOp (n := 1600) (.out 0x106330 (xorR32R32Effect 0x106330 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1598, 1594]
    (.letOp (n := 1601) (.exec 0x106330 (fun s => s.RIP = 0x106330) (xorR32R32Effect 0x106330 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1598, 1594]
    (.letOp (n := 1602) (.out 0x106332 (andR32Imm32Effect 0x106332 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1600]
    (.letOp (n := 1603) (.exec 0x106332 (fun s => s.RIP = 0x106332) (andR32Imm32Effect 0x106332 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1600]
    (.letOp (n := 1604) (.out 0x106338 (xorR32R32Effect 0x106338 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1594, 1602]
    (.letOp (n := 1605) (.exec 0x106338 (fun s => s.RIP = 0x106338) (xorR32R32Effect 0x106338 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1594, 1602]
    (.letOp (n := 1606) (.out 0x10633a (shlR32Effect 0x10633a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1602]
    (.letOp (n := 1607) (.exec 0x10633a (fun s => s.RIP = 0x10633a) (shlR32Effect 0x10633a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1602]
    (.letOp (n := 1608) (.out 0x10633d (xorR32R32Effect 0x10633d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1606, 1604]
    (.letOp (n := 1609) (.exec 0x10633d (fun s => s.RIP = 0x10633d) (xorR32R32Effect 0x10633d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1606, 1604]
    (.letOp (n := 1610) (.exec 0x10633f (StorePre 0x10633f 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10633f + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10633f 8 1 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1608, 4]
    (.letOp (n := 1611) (.out 0x106347 (movzxR32M16Effect 0x106347 8 0 (.sib 4 none 0 (.d32 0xb2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1612) (.exec 0x106347 (LoadPre 0x106347 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x106347 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106347 8 0 (.sib 4 none 0 (.d32 0xb2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1613) (.out 0x10634f (movR32R32Effect 0x10634f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1611]
    (.letOp (n := 1614) (.exec 0x10634f (fun s => s.RIP = 0x10634f) (movR32R32Effect 0x10634f 2 1 0) (Reg.operands [.gpr 0] [])) #v[1611]
    (.letOp (n := 1615) (.out 0x106351 (shrR32Effect 0x106351 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1613]
    (.letOp (n := 1616) (.exec 0x106351 (fun s => s.RIP = 0x106351) (shrR32Effect 0x106351 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1613]
    (.letOp (n := 1617) (.out 0x106354 (xorR32R32Effect 0x106354 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1615, 1611]
    (.letOp (n := 1618) (.exec 0x106354 (fun s => s.RIP = 0x106354) (xorR32R32Effect 0x106354 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1615, 1611]
    (.letOp (n := 1619) (.out 0x106356 (andR32Imm32Effect 0x106356 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1617]
    (.letOp (n := 1620) (.exec 0x106356 (fun s => s.RIP = 0x106356) (andR32Imm32Effect 0x106356 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1617]
    (.letOp (n := 1621) (.out 0x10635c (xorR32R32Effect 0x10635c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1611, 1619]
    (.letOp (n := 1622) (.exec 0x10635c (fun s => s.RIP = 0x10635c) (xorR32R32Effect 0x10635c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1611, 1619]
    (.letOp (n := 1623) (.out 0x10635e (shlR32Effect 0x10635e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1619]
    (.letOp (n := 1624) (.exec 0x10635e (fun s => s.RIP = 0x10635e) (shlR32Effect 0x10635e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1619]
    (.letOp (n := 1625) (.out 0x106361 (xorR32R32Effect 0x106361 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1623, 1621]
    (.letOp (n := 1626) (.exec 0x106361 (fun s => s.RIP = 0x106361) (xorR32R32Effect 0x106361 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1623, 1621]
    (.letOp (n := 1627) (.exec 0x106363 (StorePre 0x106363 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb2)) s (0x106363 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106363 8 1 (.sib 4 none 0 (.d32 0xb2))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1625, 4]
    (.letOp (n := 1628) (.out 0x10636b (movzxR32M16Effect 0x10636b 8 0 (.sib 4 none 0 (.d32 0xb4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1629) (.exec 0x10636b (LoadPre 0x10636b (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb4)) s (0x10636b + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10636b 8 0 (.sib 4 none 0 (.d32 0xb4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1630) (.out 0x106373 (movR32R32Effect 0x106373 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1628]
    (.letOp (n := 1631) (.exec 0x106373 (fun s => s.RIP = 0x106373) (movR32R32Effect 0x106373 2 1 0) (Reg.operands [.gpr 0] [])) #v[1628]
    (.letOp (n := 1632) (.out 0x106375 (shrR32Effect 0x106375 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1630]
    (.letOp (n := 1633) (.exec 0x106375 (fun s => s.RIP = 0x106375) (shrR32Effect 0x106375 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1630]
    (.letOp (n := 1634) (.out 0x106378 (xorR32R32Effect 0x106378 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1632, 1628]
    (.letOp (n := 1635) (.exec 0x106378 (fun s => s.RIP = 0x106378) (xorR32R32Effect 0x106378 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1632, 1628]
    (.letOp (n := 1636) (.out 0x10637a (andR32Imm32Effect 0x10637a 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1634]
    (.letOp (n := 1637) (.exec 0x10637a (fun s => s.RIP = 0x10637a) (andR32Imm32Effect 0x10637a 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1634]
    (b_l10593a_41))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_40 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66,
    0x89, 0x8C, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xB2, 0x00, 0x00, 0x00, 0x89,
    0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1,
    0x02, 0x31, 0xC1, 0x66, 0x89, 0x8C, 0x24, 0xB2, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xB4,
    0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] ++ bytes_l10593a_41

theorem code_l10593a_40 : ∀ x ∈ codeRange 0x106330 bytes_l10593a_40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6330 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_41

def b_l10593a_39 : Block Op Label signature Reg.count 1561 :=
  .letOp (n := 1561) (.exec 0x1062dc (StorePre 0x1062dc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1062dc + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1062dc 8 0 (.sib 4 none 0 (.d32 0xaa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1559, 4]
    (.letOp (n := 1562) (.out 0x1062e4 (movzxR32M16Effect 0x1062e4 8 0 (.sib 4 none 0 (.d32 0xac))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1563) (.exec 0x1062e4 (LoadPre 0x1062e4 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xac)) s (0x1062e4 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1062e4 8 0 (.sib 4 none 0 (.d32 0xac))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1564) (.out 0x1062ec (movR32R32Effect 0x1062ec 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[1562]
    (.letOp (n := 1565) (.exec 0x1062ec (fun s => s.RIP = 0x1062ec) (movR32R32Effect 0x1062ec 3 13 0) (Reg.operands [.gpr 0] [])) #v[1562]
    (.letOp (n := 1566) (.out 0x1062ef (shrR32Effect 0x1062ef 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1564]
    (.letOp (n := 1567) (.exec 0x1062ef (fun s => s.RIP = 0x1062ef) (shrR32Effect 0x1062ef 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1564]
    (.letOp (n := 1568) (.out 0x1062f3 (xorR32R32Effect 0x1062f3 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1566, 1562]
    (.letOp (n := 1569) (.exec 0x1062f3 (fun s => s.RIP = 0x1062f3) (xorR32R32Effect 0x1062f3 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1566, 1562]
    (.letOp (n := 1570) (.out 0x1062f6 (andR32Imm32Effect 0x1062f6 7 13 0x3030) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[1568]
    (.letOp (n := 1571) (.exec 0x1062f6 (fun s => s.RIP = 0x1062f6) (andR32Imm32Effect 0x1062f6 7 13 0x3030) (Reg.operands [.gpr 13] [])) #v[1568]
    (.letOp (n := 1572) (.out 0x1062fd (xorR32R32Effect 0x1062fd 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[1562, 1570]
    (.letOp (n := 1573) (.exec 0x1062fd (fun s => s.RIP = 0x1062fd) (xorR32R32Effect 0x1062fd 3 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[1562, 1570]
    (.letOp (n := 1574) (.out 0x106300 (shlR32Effect 0x106300 4 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[1570]
    (.letOp (n := 1575) (.exec 0x106300 (fun s => s.RIP = 0x106300) (shlR32Effect 0x106300 4 13 2) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1570]
    (.letOp (n := 1576) (.out 0x106304 (xorR32R32Effect 0x106304 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[1574, 1572]
    (.letOp (n := 1577) (.exec 0x106304 (fun s => s.RIP = 0x106304) (xorR32R32Effect 0x106304 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[1574, 1572]
    (.letOp (n := 1578) (.out 0x106307 (movzxR32M16Effect 0x106307 8 0 (.sib 4 none 0 (.d32 0xae))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1579) (.exec 0x106307 (LoadPre 0x106307 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xae)) s (0x106307 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106307 8 0 (.sib 4 none 0 (.d32 0xae))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1580) (.out 0x10630f (movR32R32Effect 0x10630f 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[1578]
    (.letOp (n := 1581) (.exec 0x10630f (fun s => s.RIP = 0x10630f) (movR32R32Effect 0x10630f 2 5 0) (Reg.operands [.gpr 0] [])) #v[1578]
    (.letOp (n := 1582) (.out 0x106311 (shrR32Effect 0x106311 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1580]
    (.letOp (n := 1583) (.exec 0x106311 (fun s => s.RIP = 0x106311) (shrR32Effect 0x106311 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1580]
    (.letOp (n := 1584) (.out 0x106314 (xorR32R32Effect 0x106314 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[1582, 1578]
    (.letOp (n := 1585) (.exec 0x106314 (fun s => s.RIP = 0x106314) (xorR32R32Effect 0x106314 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1582, 1578]
    (.letOp (n := 1586) (.out 0x106316 (andR32Imm32Effect 0x106316 6 5 0x3030) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[1584]
    (.letOp (n := 1587) (.exec 0x106316 (fun s => s.RIP = 0x106316) (andR32Imm32Effect 0x106316 6 5 0x3030) (Reg.operands [.gpr 5] [])) #v[1584]
    (.letOp (n := 1588) (.out 0x10631c (xorR32R32Effect 0x10631c 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[1578, 1586]
    (.letOp (n := 1589) (.exec 0x10631c (fun s => s.RIP = 0x10631c) (xorR32R32Effect 0x10631c 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[1578, 1586]
    (.letOp (n := 1590) (.out 0x10631e (shlR32Effect 0x10631e 3 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[1586]
    (.letOp (n := 1591) (.exec 0x10631e (fun s => s.RIP = 0x10631e) (shlR32Effect 0x10631e 3 5 2) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1586]
    (.letOp (n := 1592) (.out 0x106321 (xorR32R32Effect 0x106321 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[1590, 1588]
    (.letOp (n := 1593) (.exec 0x106321 (fun s => s.RIP = 0x106321) (xorR32R32Effect 0x106321 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[1590, 1588]
    (.letOp (n := 1594) (.out 0x106323 (movzxR32M16Effect 0x106323 8 0 (.sib 4 none 0 (.d32 0xb0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1595) (.exec 0x106323 (LoadPre 0x106323 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x106323 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106323 8 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1596) (.out 0x10632b (movR32R32Effect 0x10632b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1594]
    (.letOp (n := 1597) (.exec 0x10632b (fun s => s.RIP = 0x10632b) (movR32R32Effect 0x10632b 2 1 0) (Reg.operands [.gpr 0] [])) #v[1594]
    (.letOp (n := 1598) (.out 0x10632d (shrR32Effect 0x10632d 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1596]
    (.letOp (n := 1599) (.exec 0x10632d (fun s => s.RIP = 0x10632d) (shrR32Effect 0x10632d 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1596]
    (b_l10593a_40)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_39 : List UInt8 :=
  [0x66, 0x89, 0x84, 0x24, 0xAA, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xAC, 0x00, 0x00, 0x00,
    0x41, 0x89, 0xC5, 0x41, 0xC1, 0xED, 0x02, 0x41, 0x31, 0xC5, 0x41, 0x81, 0xE5, 0x30, 0x30, 0x00,
    0x00, 0x44, 0x31, 0xE8, 0x41, 0xC1, 0xE5, 0x02, 0x41, 0x31, 0xC5, 0x0F, 0xB7, 0x84, 0x24, 0xAE,
    0x00, 0x00, 0x00, 0x89, 0xC5, 0xC1, 0xED, 0x02, 0x31, 0xC5, 0x81, 0xE5, 0x30, 0x30, 0x00, 0x00,
    0x31, 0xE8, 0xC1, 0xE5, 0x02, 0x31, 0xC5, 0x0F, 0xB7, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x89,
    0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_40

theorem code_l10593a_39 : ∀ x ∈ codeRange 0x1062dc bytes_l10593a_39, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x62dc 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_40

def b_l10593a_38 : Block Op Label signature Reg.count 1522 :=
  .letOp (n := 1522) (.out 0x10629c (andEaxImm32Effect 0x10629c 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1520]
    (.letOp (n := 1523) (.exec 0x10629c (fun s => s.RIP = 0x10629c) (andEaxImm32Effect 0x10629c 0x5050) (Reg.operands [.gpr 0] [])) #v[1520]
    (.letOp (n := 1524) (.out 0x1062a1 (xorR32R32Effect 0x1062a1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1514, 1522]
    (.letOp (n := 1525) (.exec 0x1062a1 (fun s => s.RIP = 0x1062a1) (xorR32R32Effect 0x1062a1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1514, 1522]
    (.letOp (n := 1526) (.out 0x1062a3 (addR32R32Effect 0x1062a3 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1522, 1522]
    (.letOp (n := 1527) (.exec 0x1062a3 (fun s => s.RIP = 0x1062a3) (addR32R32Effect 0x1062a3 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1522, 1522]
    (.letOp (n := 1528) (.out 0x1062a5 (xorR32R32Effect 0x1062a5 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1526, 1524]
    (.letOp (n := 1529) (.exec 0x1062a5 (fun s => s.RIP = 0x1062a5) (xorR32R32Effect 0x1062a5 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1526, 1524]
    (.letOp (n := 1530) (.exec 0x1062a7 (StorePre 0x1062a7 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x1062a7 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1062a7 8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1528, 4]
    (.letOp (n := 1531) (.out 0x1062af (movzxR32M16Effect 0x1062af 8 0 (.sib 4 none 0 (.d32 0xaa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1532) (.exec 0x1062af (LoadPre 0x1062af (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xaa)) s (0x1062af + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1062af 8 0 (.sib 4 none 0 (.d32 0xaa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1533) (.out 0x1062b7 (movR32R32Effect 0x1062b7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1531]
    (.letOp (n := 1534) (.exec 0x1062b7 (fun s => s.RIP = 0x1062b7) (movR32R32Effect 0x1062b7 2 1 0) (Reg.operands [.gpr 0] [])) #v[1531]
    (.letOp (n := 1535) (.out 0x1062b9 (shrR32Effect 0x1062b9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1533]
    (.letOp (n := 1536) (.exec 0x1062b9 (fun s => s.RIP = 0x1062b9) (shrR32Effect 0x1062b9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1533]
    (.letOp (n := 1537) (.out 0x1062bc (xorR32R32Effect 0x1062bc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1535, 1531]
    (.letOp (n := 1538) (.exec 0x1062bc (fun s => s.RIP = 0x1062bc) (xorR32R32Effect 0x1062bc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1535, 1531]
    (.letOp (n := 1539) (.out 0x1062be (andR32Imm32Effect 0x1062be 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1537]
    (.letOp (n := 1540) (.exec 0x1062be (fun s => s.RIP = 0x1062be) (andR32Imm32Effect 0x1062be 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1537]
    (.letOp (n := 1541) (.out 0x1062c4 (xorR32R32Effect 0x1062c4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1531, 1539]
    (.letOp (n := 1542) (.exec 0x1062c4 (fun s => s.RIP = 0x1062c4) (xorR32R32Effect 0x1062c4 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1531, 1539]
    (.letOp (n := 1543) (.out 0x1062c6 (shlR32Effect 0x1062c6 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1539]
    (.letOp (n := 1544) (.exec 0x1062c6 (fun s => s.RIP = 0x1062c6) (shlR32Effect 0x1062c6 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1539]
    (.letOp (n := 1545) (.out 0x1062c9 (xorR32R32Effect 0x1062c9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1543, 1541]
    (.letOp (n := 1546) (.exec 0x1062c9 (fun s => s.RIP = 0x1062c9) (xorR32R32Effect 0x1062c9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1543, 1541]
    (.letOp (n := 1547) (.out 0x1062cb (movR32R32Effect 0x1062cb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1545]
    (.letOp (n := 1548) (.exec 0x1062cb (fun s => s.RIP = 0x1062cb) (movR32R32Effect 0x1062cb 2 0 1) (Reg.operands [.gpr 1] [])) #v[1545]
    (.letOp (n := 1549) (.out 0x1062cd (shrR32Effect 0x1062cd 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1547]
    (.letOp (n := 1550) (.exec 0x1062cd (fun s => s.RIP = 0x1062cd) (shrR32Effect 0x1062cd 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1547]
    (.letOp (n := 1551) (.out 0x1062cf (xorR32R32Effect 0x1062cf 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1549, 1545]
    (.letOp (n := 1552) (.exec 0x1062cf (fun s => s.RIP = 0x1062cf) (xorR32R32Effect 0x1062cf 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1549, 1545]
    (.letOp (n := 1553) (.out 0x1062d1 (andEaxImm32Effect 0x1062d1 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1551]
    (.letOp (n := 1554) (.exec 0x1062d1 (fun s => s.RIP = 0x1062d1) (andEaxImm32Effect 0x1062d1 0x5050) (Reg.operands [.gpr 0] [])) #v[1551]
    (.letOp (n := 1555) (.out 0x1062d6 (xorR32R32Effect 0x1062d6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1545, 1553]
    (.letOp (n := 1556) (.exec 0x1062d6 (fun s => s.RIP = 0x1062d6) (xorR32R32Effect 0x1062d6 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1545, 1553]
    (.letOp (n := 1557) (.out 0x1062d8 (addR32R32Effect 0x1062d8 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1553, 1553]
    (.letOp (n := 1558) (.exec 0x1062d8 (fun s => s.RIP = 0x1062d8) (addR32R32Effect 0x1062d8 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1553, 1553]
    (.letOp (n := 1559) (.out 0x1062da (xorR32R32Effect 0x1062da 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1557, 1555]
    (.letOp (n := 1560) (.exec 0x1062da (fun s => s.RIP = 0x1062da) (xorR32R32Effect 0x1062da 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1557, 1555]
    (b_l10593a_39)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_38 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xAA, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02,
    0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_39

theorem code_l10593a_38 : ∀ x ∈ codeRange 0x10629c bytes_l10593a_38, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x629c 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_39

def b_l10593a_37 : Block Op Label signature Reg.count 1483 :=
  .letOp (n := 1483) (.out 0x10625f (xorR32R32Effect 0x10625f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1481, 1479]
    (.letOp (n := 1484) (.exec 0x10625f (fun s => s.RIP = 0x10625f) (xorR32R32Effect 0x10625f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1481, 1479]
    (.letOp (n := 1485) (.out 0x106261 (movR32R32Effect 0x106261 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1483]
    (.letOp (n := 1486) (.exec 0x106261 (fun s => s.RIP = 0x106261) (movR32R32Effect 0x106261 2 0 1) (Reg.operands [.gpr 1] [])) #v[1483]
    (.letOp (n := 1487) (.out 0x106263 (shrR32Effect 0x106263 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1485]
    (.letOp (n := 1488) (.exec 0x106263 (fun s => s.RIP = 0x106263) (shrR32Effect 0x106263 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1485]
    (.letOp (n := 1489) (.out 0x106265 (xorR32R32Effect 0x106265 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1487, 1483]
    (.letOp (n := 1490) (.exec 0x106265 (fun s => s.RIP = 0x106265) (xorR32R32Effect 0x106265 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1487, 1483]
    (.letOp (n := 1491) (.out 0x106267 (andEaxImm32Effect 0x106267 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1489]
    (.letOp (n := 1492) (.exec 0x106267 (fun s => s.RIP = 0x106267) (andEaxImm32Effect 0x106267 0x5050) (Reg.operands [.gpr 0] [])) #v[1489]
    (.letOp (n := 1493) (.out 0x10626c (xorR32R32Effect 0x10626c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1483, 1491]
    (.letOp (n := 1494) (.exec 0x10626c (fun s => s.RIP = 0x10626c) (xorR32R32Effect 0x10626c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1483, 1491]
    (.letOp (n := 1495) (.out 0x10626e (addR32R32Effect 0x10626e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1491, 1491]
    (.letOp (n := 1496) (.exec 0x10626e (fun s => s.RIP = 0x10626e) (addR32R32Effect 0x10626e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1491, 1491]
    (.letOp (n := 1497) (.out 0x106270 (xorR32R32Effect 0x106270 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1495, 1493]
    (.letOp (n := 1498) (.exec 0x106270 (fun s => s.RIP = 0x106270) (xorR32R32Effect 0x106270 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1495, 1493]
    (.letOp (n := 1499) (.exec 0x106272 (StorePre 0x106272 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106272 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106272 8 0 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1497, 4]
    (.letOp (n := 1500) (.out 0x10627a (movzxR32M16Effect 0x10627a 8 0 (.sib 4 none 0 (.d32 0xa8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1501) (.exec 0x10627a (LoadPre 0x10627a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10627a + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10627a 8 0 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1502) (.out 0x106282 (movR32R32Effect 0x106282 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1500]
    (.letOp (n := 1503) (.exec 0x106282 (fun s => s.RIP = 0x106282) (movR32R32Effect 0x106282 2 1 0) (Reg.operands [.gpr 0] [])) #v[1500]
    (.letOp (n := 1504) (.out 0x106284 (shrR32Effect 0x106284 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1502]
    (.letOp (n := 1505) (.exec 0x106284 (fun s => s.RIP = 0x106284) (shrR32Effect 0x106284 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1502]
    (.letOp (n := 1506) (.out 0x106287 (xorR32R32Effect 0x106287 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1504, 1500]
    (.letOp (n := 1507) (.exec 0x106287 (fun s => s.RIP = 0x106287) (xorR32R32Effect 0x106287 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1504, 1500]
    (.letOp (n := 1508) (.out 0x106289 (andR32Imm32Effect 0x106289 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1506]
    (.letOp (n := 1509) (.exec 0x106289 (fun s => s.RIP = 0x106289) (andR32Imm32Effect 0x106289 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1506]
    (.letOp (n := 1510) (.out 0x10628f (xorR32R32Effect 0x10628f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1500, 1508]
    (.letOp (n := 1511) (.exec 0x10628f (fun s => s.RIP = 0x10628f) (xorR32R32Effect 0x10628f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1500, 1508]
    (.letOp (n := 1512) (.out 0x106291 (shlR32Effect 0x106291 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1508]
    (.letOp (n := 1513) (.exec 0x106291 (fun s => s.RIP = 0x106291) (shlR32Effect 0x106291 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1508]
    (.letOp (n := 1514) (.out 0x106294 (xorR32R32Effect 0x106294 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1512, 1510]
    (.letOp (n := 1515) (.exec 0x106294 (fun s => s.RIP = 0x106294) (xorR32R32Effect 0x106294 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1512, 1510]
    (.letOp (n := 1516) (.out 0x106296 (movR32R32Effect 0x106296 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1514]
    (.letOp (n := 1517) (.exec 0x106296 (fun s => s.RIP = 0x106296) (movR32R32Effect 0x106296 2 0 1) (Reg.operands [.gpr 1] [])) #v[1514]
    (.letOp (n := 1518) (.out 0x106298 (shrR32Effect 0x106298 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1516]
    (.letOp (n := 1519) (.exec 0x106298 (fun s => s.RIP = 0x106298) (shrR32Effect 0x106298 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1516]
    (.letOp (n := 1520) (.out 0x10629a (xorR32R32Effect 0x10629a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1518, 1514]
    (.letOp (n := 1521) (.exec 0x10629a (fun s => s.RIP = 0x10629a) (xorR32R32Effect 0x10629a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1518, 1514]
    (b_l10593a_38)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_37 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xA8,
    0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00,
    0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_38

theorem code_l10593a_37 : ∀ x ∈ codeRange 0x10625f bytes_l10593a_37, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x625f 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_38

def b_l10593a_36 : Block Op Label signature Reg.count 1444 :=
  .letOp (n := 1444) (.out 0x10621d (xorR32R32Effect 0x10621d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1442, 1438]
    (.letOp (n := 1445) (.exec 0x10621d (fun s => s.RIP = 0x10621d) (xorR32R32Effect 0x10621d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1442, 1438]
    (.letOp (n := 1446) (.out 0x10621f (andR32Imm32Effect 0x10621f 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1444]
    (.letOp (n := 1447) (.exec 0x10621f (fun s => s.RIP = 0x10621f) (andR32Imm32Effect 0x10621f 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1444]
    (.letOp (n := 1448) (.out 0x106225 (xorR32R32Effect 0x106225 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1438, 1446]
    (.letOp (n := 1449) (.exec 0x106225 (fun s => s.RIP = 0x106225) (xorR32R32Effect 0x106225 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1438, 1446]
    (.letOp (n := 1450) (.out 0x106227 (shlR32Effect 0x106227 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1446]
    (.letOp (n := 1451) (.exec 0x106227 (fun s => s.RIP = 0x106227) (shlR32Effect 0x106227 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1446]
    (.letOp (n := 1452) (.out 0x10622a (xorR32R32Effect 0x10622a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1450, 1448]
    (.letOp (n := 1453) (.exec 0x10622a (fun s => s.RIP = 0x10622a) (xorR32R32Effect 0x10622a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1450, 1448]
    (.letOp (n := 1454) (.out 0x10622c (movR32R32Effect 0x10622c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1452]
    (.letOp (n := 1455) (.exec 0x10622c (fun s => s.RIP = 0x10622c) (movR32R32Effect 0x10622c 2 0 1) (Reg.operands [.gpr 1] [])) #v[1452]
    (.letOp (n := 1456) (.out 0x10622e (shrR32Effect 0x10622e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1454]
    (.letOp (n := 1457) (.exec 0x10622e (fun s => s.RIP = 0x10622e) (shrR32Effect 0x10622e 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1454]
    (.letOp (n := 1458) (.out 0x106230 (xorR32R32Effect 0x106230 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1456, 1452]
    (.letOp (n := 1459) (.exec 0x106230 (fun s => s.RIP = 0x106230) (xorR32R32Effect 0x106230 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1456, 1452]
    (.letOp (n := 1460) (.out 0x106232 (andEaxImm32Effect 0x106232 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1458]
    (.letOp (n := 1461) (.exec 0x106232 (fun s => s.RIP = 0x106232) (andEaxImm32Effect 0x106232 0x5050) (Reg.operands [.gpr 0] [])) #v[1458]
    (.letOp (n := 1462) (.out 0x106237 (xorR32R32Effect 0x106237 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1452, 1460]
    (.letOp (n := 1463) (.exec 0x106237 (fun s => s.RIP = 0x106237) (xorR32R32Effect 0x106237 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1452, 1460]
    (.letOp (n := 1464) (.out 0x106239 (addR32R32Effect 0x106239 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1460, 1460]
    (.letOp (n := 1465) (.exec 0x106239 (fun s => s.RIP = 0x106239) (addR32R32Effect 0x106239 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1460, 1460]
    (.letOp (n := 1466) (.out 0x10623b (xorR32R32Effect 0x10623b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1464, 1462]
    (.letOp (n := 1467) (.exec 0x10623b (fun s => s.RIP = 0x10623b) (xorR32R32Effect 0x10623b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1464, 1462]
    (.letOp (n := 1468) (.exec 0x10623d (StorePre 0x10623d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x10623d + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10623d 8 0 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1466, 4]
    (.letOp (n := 1469) (.out 0x106245 (movzxR32M16Effect 0x106245 8 0 (.sib 4 none 0 (.d32 0xa6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1470) (.exec 0x106245 (LoadPre 0x106245 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa6)) s (0x106245 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106245 8 0 (.sib 4 none 0 (.d32 0xa6))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1471) (.out 0x10624d (movR32R32Effect 0x10624d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1469]
    (.letOp (n := 1472) (.exec 0x10624d (fun s => s.RIP = 0x10624d) (movR32R32Effect 0x10624d 2 1 0) (Reg.operands [.gpr 0] [])) #v[1469]
    (.letOp (n := 1473) (.out 0x10624f (shrR32Effect 0x10624f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1471]
    (.letOp (n := 1474) (.exec 0x10624f (fun s => s.RIP = 0x10624f) (shrR32Effect 0x10624f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1471]
    (.letOp (n := 1475) (.out 0x106252 (xorR32R32Effect 0x106252 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1473, 1469]
    (.letOp (n := 1476) (.exec 0x106252 (fun s => s.RIP = 0x106252) (xorR32R32Effect 0x106252 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1473, 1469]
    (.letOp (n := 1477) (.out 0x106254 (andR32Imm32Effect 0x106254 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1475]
    (.letOp (n := 1478) (.exec 0x106254 (fun s => s.RIP = 0x106254) (andR32Imm32Effect 0x106254 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1475]
    (.letOp (n := 1479) (.out 0x10625a (xorR32R32Effect 0x10625a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1469, 1477]
    (.letOp (n := 1480) (.exec 0x10625a (fun s => s.RIP = 0x10625a) (xorR32R32Effect 0x10625a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1469, 1477]
    (.letOp (n := 1481) (.out 0x10625c (shlR32Effect 0x10625c 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1477]
    (.letOp (n := 1482) (.exec 0x10625c (fun s => s.RIP = 0x10625c) (shlR32Effect 0x10625c 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1477]
    (b_l10593a_37)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_36 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x84, 0x24, 0xA4, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xA6, 0x00, 0x00, 0x00,
    0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1,
    0xE1, 0x02] ++ bytes_l10593a_37

theorem code_l10593a_36 : ∀ x ∈ codeRange 0x10621d bytes_l10593a_36, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x621d 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_37

def b_l10593a_35 : Block Op Label signature Reg.count 1406 :=
  .letOp (n := 1406) (.exec 0x1061d3 (StorePre 0x1061d3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1061d3 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1061d3 8 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1404, 4]
    (.letOp (n := 1407) (.out 0x1061db (movzxR32M16Effect 0x1061db 8 0 (.sib 4 none 0 (.d32 0xa2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1408) (.exec 0x1061db (LoadPre 0x1061db (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x1061db + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1061db 8 0 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1409) (.out 0x1061e3 (movR32R32Effect 0x1061e3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1407]
    (.letOp (n := 1410) (.exec 0x1061e3 (fun s => s.RIP = 0x1061e3) (movR32R32Effect 0x1061e3 2 1 0) (Reg.operands [.gpr 0] [])) #v[1407]
    (.letOp (n := 1411) (.out 0x1061e5 (shrR32Effect 0x1061e5 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1409]
    (.letOp (n := 1412) (.exec 0x1061e5 (fun s => s.RIP = 0x1061e5) (shrR32Effect 0x1061e5 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1409]
    (.letOp (n := 1413) (.out 0x1061e8 (xorR32R32Effect 0x1061e8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1411, 1407]
    (.letOp (n := 1414) (.exec 0x1061e8 (fun s => s.RIP = 0x1061e8) (xorR32R32Effect 0x1061e8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1411, 1407]
    (.letOp (n := 1415) (.out 0x1061ea (andR32Imm32Effect 0x1061ea 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1413]
    (.letOp (n := 1416) (.exec 0x1061ea (fun s => s.RIP = 0x1061ea) (andR32Imm32Effect 0x1061ea 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1413]
    (.letOp (n := 1417) (.out 0x1061f0 (xorR32R32Effect 0x1061f0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1407, 1415]
    (.letOp (n := 1418) (.exec 0x1061f0 (fun s => s.RIP = 0x1061f0) (xorR32R32Effect 0x1061f0 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1407, 1415]
    (.letOp (n := 1419) (.out 0x1061f2 (shlR32Effect 0x1061f2 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1415]
    (.letOp (n := 1420) (.exec 0x1061f2 (fun s => s.RIP = 0x1061f2) (shlR32Effect 0x1061f2 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1415]
    (.letOp (n := 1421) (.out 0x1061f5 (xorR32R32Effect 0x1061f5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1419, 1417]
    (.letOp (n := 1422) (.exec 0x1061f5 (fun s => s.RIP = 0x1061f5) (xorR32R32Effect 0x1061f5 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1419, 1417]
    (.letOp (n := 1423) (.out 0x1061f7 (movR32R32Effect 0x1061f7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1421]
    (.letOp (n := 1424) (.exec 0x1061f7 (fun s => s.RIP = 0x1061f7) (movR32R32Effect 0x1061f7 2 0 1) (Reg.operands [.gpr 1] [])) #v[1421]
    (.letOp (n := 1425) (.out 0x1061f9 (shrR32Effect 0x1061f9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1423]
    (.letOp (n := 1426) (.exec 0x1061f9 (fun s => s.RIP = 0x1061f9) (shrR32Effect 0x1061f9 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1423]
    (.letOp (n := 1427) (.out 0x1061fb (xorR32R32Effect 0x1061fb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1425, 1421]
    (.letOp (n := 1428) (.exec 0x1061fb (fun s => s.RIP = 0x1061fb) (xorR32R32Effect 0x1061fb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1425, 1421]
    (.letOp (n := 1429) (.out 0x1061fd (andEaxImm32Effect 0x1061fd 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1427]
    (.letOp (n := 1430) (.exec 0x1061fd (fun s => s.RIP = 0x1061fd) (andEaxImm32Effect 0x1061fd 0x5050) (Reg.operands [.gpr 0] [])) #v[1427]
    (.letOp (n := 1431) (.out 0x106202 (xorR32R32Effect 0x106202 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1421, 1429]
    (.letOp (n := 1432) (.exec 0x106202 (fun s => s.RIP = 0x106202) (xorR32R32Effect 0x106202 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1421, 1429]
    (.letOp (n := 1433) (.out 0x106204 (addR32R32Effect 0x106204 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1429, 1429]
    (.letOp (n := 1434) (.exec 0x106204 (fun s => s.RIP = 0x106204) (addR32R32Effect 0x106204 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1429, 1429]
    (.letOp (n := 1435) (.out 0x106206 (xorR32R32Effect 0x106206 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1433, 1431]
    (.letOp (n := 1436) (.exec 0x106206 (fun s => s.RIP = 0x106206) (xorR32R32Effect 0x106206 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1433, 1431]
    (.letOp (n := 1437) (.exec 0x106208 (StorePre 0x106208 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa2)) s (0x106208 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106208 8 0 (.sib 4 none 0 (.d32 0xa2))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1435, 4]
    (.letOp (n := 1438) (.out 0x106210 (movzxR32M16Effect 0x106210 8 0 (.sib 4 none 0 (.d32 0xa4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1439) (.exec 0x106210 (LoadPre 0x106210 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa4)) s (0x106210 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106210 8 0 (.sib 4 none 0 (.d32 0xa4))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1440) (.out 0x106218 (movR32R32Effect 0x106218 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1438]
    (.letOp (n := 1441) (.exec 0x106218 (fun s => s.RIP = 0x106218) (movR32R32Effect 0x106218 2 1 0) (Reg.operands [.gpr 0] [])) #v[1438]
    (.letOp (n := 1442) (.out 0x10621a (shrR32Effect 0x10621a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1440]
    (.letOp (n := 1443) (.exec 0x10621a (fun s => s.RIP = 0x10621a) (shrR32Effect 0x10621a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1440]
    (b_l10593a_36))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_35 : List UInt8 :=
  [0x66, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00,
    0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1,
    0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31,
    0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0xA2, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84,
    0x24, 0xA4, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_36

theorem code_l10593a_35 : ∀ x ∈ codeRange 0x1061d3 bytes_l10593a_35, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x61d3 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_36

def b_l10593a_34 : Block Op Label signature Reg.count 1367 :=
  .letOp (n := 1367) (.out 0x106193 (andEaxImm32Effect 0x106193 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1365]
    (.letOp (n := 1368) (.exec 0x106193 (fun s => s.RIP = 0x106193) (andEaxImm32Effect 0x106193 0x5050) (Reg.operands [.gpr 0] [])) #v[1365]
    (.letOp (n := 1369) (.out 0x106198 (xorR32R32Effect 0x106198 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1359, 1367]
    (.letOp (n := 1370) (.exec 0x106198 (fun s => s.RIP = 0x106198) (xorR32R32Effect 0x106198 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1359, 1367]
    (.letOp (n := 1371) (.out 0x10619a (addR32R32Effect 0x10619a 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1367, 1367]
    (.letOp (n := 1372) (.exec 0x10619a (fun s => s.RIP = 0x10619a) (addR32R32Effect 0x10619a 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1367, 1367]
    (.letOp (n := 1373) (.out 0x10619c (xorR32R32Effect 0x10619c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1371, 1369]
    (.letOp (n := 1374) (.exec 0x10619c (fun s => s.RIP = 0x10619c) (xorR32R32Effect 0x10619c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1371, 1369]
    (.letOp (n := 1375) (.exec 0x10619e (StorePre 0x10619e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x10619e + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10619e 8 0 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1373, 4]
    (.letOp (n := 1376) (.out 0x1061a6 (movzxR32M16Effect 0x1061a6 8 0 (.sib 4 none 0 (.d32 0xa0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1377) (.exec 0x1061a6 (LoadPre 0x1061a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x1061a6 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1061a6 8 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1378) (.out 0x1061ae (movR32R32Effect 0x1061ae 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1376]
    (.letOp (n := 1379) (.exec 0x1061ae (fun s => s.RIP = 0x1061ae) (movR32R32Effect 0x1061ae 2 1 0) (Reg.operands [.gpr 0] [])) #v[1376]
    (.letOp (n := 1380) (.out 0x1061b0 (shrR32Effect 0x1061b0 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1378]
    (.letOp (n := 1381) (.exec 0x1061b0 (fun s => s.RIP = 0x1061b0) (shrR32Effect 0x1061b0 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1378]
    (.letOp (n := 1382) (.out 0x1061b3 (xorR32R32Effect 0x1061b3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1380, 1376]
    (.letOp (n := 1383) (.exec 0x1061b3 (fun s => s.RIP = 0x1061b3) (xorR32R32Effect 0x1061b3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1380, 1376]
    (.letOp (n := 1384) (.out 0x1061b5 (andR32Imm32Effect 0x1061b5 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1382]
    (.letOp (n := 1385) (.exec 0x1061b5 (fun s => s.RIP = 0x1061b5) (andR32Imm32Effect 0x1061b5 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1382]
    (.letOp (n := 1386) (.out 0x1061bb (xorR32R32Effect 0x1061bb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1376, 1384]
    (.letOp (n := 1387) (.exec 0x1061bb (fun s => s.RIP = 0x1061bb) (xorR32R32Effect 0x1061bb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1376, 1384]
    (.letOp (n := 1388) (.out 0x1061bd (shlR32Effect 0x1061bd 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1384]
    (.letOp (n := 1389) (.exec 0x1061bd (fun s => s.RIP = 0x1061bd) (shlR32Effect 0x1061bd 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1384]
    (.letOp (n := 1390) (.out 0x1061c0 (xorR32R32Effect 0x1061c0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1388, 1386]
    (.letOp (n := 1391) (.exec 0x1061c0 (fun s => s.RIP = 0x1061c0) (xorR32R32Effect 0x1061c0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1388, 1386]
    (.letOp (n := 1392) (.out 0x1061c2 (movR32R32Effect 0x1061c2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1390]
    (.letOp (n := 1393) (.exec 0x1061c2 (fun s => s.RIP = 0x1061c2) (movR32R32Effect 0x1061c2 2 0 1) (Reg.operands [.gpr 1] [])) #v[1390]
    (.letOp (n := 1394) (.out 0x1061c4 (shrR32Effect 0x1061c4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1392]
    (.letOp (n := 1395) (.exec 0x1061c4 (fun s => s.RIP = 0x1061c4) (shrR32Effect 0x1061c4 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1392]
    (.letOp (n := 1396) (.out 0x1061c6 (xorR32R32Effect 0x1061c6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1394, 1390]
    (.letOp (n := 1397) (.exec 0x1061c6 (fun s => s.RIP = 0x1061c6) (xorR32R32Effect 0x1061c6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1394, 1390]
    (.letOp (n := 1398) (.out 0x1061c8 (andEaxImm32Effect 0x1061c8 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1396]
    (.letOp (n := 1399) (.exec 0x1061c8 (fun s => s.RIP = 0x1061c8) (andEaxImm32Effect 0x1061c8 0x5050) (Reg.operands [.gpr 0] [])) #v[1396]
    (.letOp (n := 1400) (.out 0x1061cd (xorR32R32Effect 0x1061cd 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1390, 1398]
    (.letOp (n := 1401) (.exec 0x1061cd (fun s => s.RIP = 0x1061cd) (xorR32R32Effect 0x1061cd 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1390, 1398]
    (.letOp (n := 1402) (.out 0x1061cf (addR32R32Effect 0x1061cf 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1398, 1398]
    (.letOp (n := 1403) (.exec 0x1061cf (fun s => s.RIP = 0x1061cf) (addR32R32Effect 0x1061cf 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1398, 1398]
    (.letOp (n := 1404) (.out 0x1061d1 (xorR32R32Effect 0x1061d1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1402, 1400]
    (.letOp (n := 1405) (.exec 0x1061d1 (fun s => s.RIP = 0x1061d1) (xorR32R32Effect 0x1061d1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1402, 1400]
    (b_l10593a_35)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_34 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x9E,
    0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0xA0, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02,
    0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_35

theorem code_l10593a_34 : ∀ x ∈ codeRange 0x106193 bytes_l10593a_34, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6193 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_35

def b_l10593a_33 : Block Op Label signature Reg.count 1327 :=
  .letOp (n := 1327) (.out 0x106153 (shlR32Effect 0x106153 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1323]
    (.letOp (n := 1328) (.exec 0x106153 (fun s => s.RIP = 0x106153) (shlR32Effect 0x106153 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1323]
    (.letOp (n := 1329) (.out 0x106156 (xorR32R32Effect 0x106156 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1327, 1325]
    (.letOp (n := 1330) (.exec 0x106156 (fun s => s.RIP = 0x106156) (xorR32R32Effect 0x106156 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1327, 1325]
    (.letOp (n := 1331) (.out 0x106158 (movR32R32Effect 0x106158 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 1] []) (.reg (.gpr 12))) #v[1329]
    (.letOp (n := 1332) (.exec 0x106158 (fun s => s.RIP = 0x106158) (movR32R32Effect 0x106158 3 12 1) (Reg.operands [.gpr 1] [])) #v[1329]
    (.letOp (n := 1333) (.out 0x10615b (shrR32Effect 0x10615b 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1331]
    (.letOp (n := 1334) (.exec 0x10615b (fun s => s.RIP = 0x10615b) (shrR32Effect 0x10615b 3 12 1) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1331]
    (.letOp (n := 1335) (.out 0x10615e (xorR32R32Effect 0x10615e 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[1333, 1329]
    (.letOp (n := 1336) (.exec 0x10615e (fun s => s.RIP = 0x10615e) (xorR32R32Effect 0x10615e 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[1333, 1329]
    (.letOp (n := 1337) (.out 0x106161 (andR32Imm32Effect 0x106161 7 12 0x5050) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[1335]
    (.letOp (n := 1338) (.exec 0x106161 (fun s => s.RIP = 0x106161) (andR32Imm32Effect 0x106161 7 12 0x5050) (Reg.operands [.gpr 12] [])) #v[1335]
    (.letOp (n := 1339) (.out 0x106168 (xorR32R32Effect 0x106168 3 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 12] []) (.reg (.gpr 1))) #v[1329, 1337]
    (.letOp (n := 1340) (.exec 0x106168 (fun s => s.RIP = 0x106168) (xorR32R32Effect 0x106168 3 1 12) (Reg.operands [.gpr 1, .gpr 12] [])) #v[1329, 1337]
    (.letOp (n := 1341) (.out 0x10616b (addR32R32Effect 0x10616b 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[1337, 1337]
    (.letOp (n := 1342) (.exec 0x10616b (fun s => s.RIP = 0x10616b) (addR32R32Effect 0x10616b 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[1337, 1337]
    (.letOp (n := 1343) (.out 0x10616e (xorR32R32Effect 0x10616e 3 12 1) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1] []) (.reg (.gpr 12))) #v[1341, 1339]
    (.letOp (n := 1344) (.exec 0x10616e (fun s => s.RIP = 0x10616e) (xorR32R32Effect 0x10616e 3 12 1) (Reg.operands [.gpr 12, .gpr 1] [])) #v[1341, 1339]
    (.letOp (n := 1345) (.out 0x106171 (movzxR32M16Effect 0x106171 8 0 (.sib 4 none 0 (.d32 0x9e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1346) (.exec 0x106171 (LoadPre 0x106171 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9e)) s (0x106171 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106171 8 0 (.sib 4 none 0 (.d32 0x9e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1347) (.out 0x106179 (movR32R32Effect 0x106179 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1345]
    (.letOp (n := 1348) (.exec 0x106179 (fun s => s.RIP = 0x106179) (movR32R32Effect 0x106179 2 1 0) (Reg.operands [.gpr 0] [])) #v[1345]
    (.letOp (n := 1349) (.out 0x10617b (shrR32Effect 0x10617b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1347]
    (.letOp (n := 1350) (.exec 0x10617b (fun s => s.RIP = 0x10617b) (shrR32Effect 0x10617b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1347]
    (.letOp (n := 1351) (.out 0x10617e (xorR32R32Effect 0x10617e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1349, 1345]
    (.letOp (n := 1352) (.exec 0x10617e (fun s => s.RIP = 0x10617e) (xorR32R32Effect 0x10617e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1349, 1345]
    (.letOp (n := 1353) (.out 0x106180 (andR32Imm32Effect 0x106180 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1351]
    (.letOp (n := 1354) (.exec 0x106180 (fun s => s.RIP = 0x106180) (andR32Imm32Effect 0x106180 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1351]
    (.letOp (n := 1355) (.out 0x106186 (xorR32R32Effect 0x106186 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1345, 1353]
    (.letOp (n := 1356) (.exec 0x106186 (fun s => s.RIP = 0x106186) (xorR32R32Effect 0x106186 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1345, 1353]
    (.letOp (n := 1357) (.out 0x106188 (shlR32Effect 0x106188 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1353]
    (.letOp (n := 1358) (.exec 0x106188 (fun s => s.RIP = 0x106188) (shlR32Effect 0x106188 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1353]
    (.letOp (n := 1359) (.out 0x10618b (xorR32R32Effect 0x10618b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1357, 1355]
    (.letOp (n := 1360) (.exec 0x10618b (fun s => s.RIP = 0x10618b) (xorR32R32Effect 0x10618b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1357, 1355]
    (.letOp (n := 1361) (.out 0x10618d (movR32R32Effect 0x10618d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1359]
    (.letOp (n := 1362) (.exec 0x10618d (fun s => s.RIP = 0x10618d) (movR32R32Effect 0x10618d 2 0 1) (Reg.operands [.gpr 1] [])) #v[1359]
    (.letOp (n := 1363) (.out 0x10618f (shrR32Effect 0x10618f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1361]
    (.letOp (n := 1364) (.exec 0x10618f (fun s => s.RIP = 0x10618f) (shrR32Effect 0x10618f 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1361]
    (.letOp (n := 1365) (.out 0x106191 (xorR32R32Effect 0x106191 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1363, 1359]
    (.letOp (n := 1366) (.exec 0x106191 (fun s => s.RIP = 0x106191) (xorR32R32Effect 0x106191 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1363, 1359]
    (b_l10593a_34))))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_33 : List UInt8 :=
  [0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x41, 0x89, 0xCC, 0x41, 0xD1, 0xEC, 0x41, 0x31, 0xCC, 0x41, 0x81,
    0xE4, 0x50, 0x50, 0x00, 0x00, 0x44, 0x31, 0xE1, 0x45, 0x01, 0xE4, 0x41, 0x31, 0xCC, 0x0F, 0xB7,
    0x84, 0x24, 0x9E, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20,
    0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_34

theorem code_l10593a_33 : ∀ x ∈ codeRange 0x106153 bytes_l10593a_33, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6153 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_34

def b_l10593a_32 : Block Op Label signature Reg.count 1288 :=
  .letOp (n := 1288) (.out 0x106111 (shrR32Effect 0x106111 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1286]
    (.letOp (n := 1289) (.exec 0x106111 (fun s => s.RIP = 0x106111) (shrR32Effect 0x106111 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1286]
    (.letOp (n := 1290) (.out 0x106114 (xorR32R32Effect 0x106114 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1288, 1284]
    (.letOp (n := 1291) (.exec 0x106114 (fun s => s.RIP = 0x106114) (xorR32R32Effect 0x106114 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1288, 1284]
    (.letOp (n := 1292) (.out 0x106116 (andR32Imm32Effect 0x106116 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1290]
    (.letOp (n := 1293) (.exec 0x106116 (fun s => s.RIP = 0x106116) (andR32Imm32Effect 0x106116 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1290]
    (.letOp (n := 1294) (.out 0x10611c (xorR32R32Effect 0x10611c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1284, 1292]
    (.letOp (n := 1295) (.exec 0x10611c (fun s => s.RIP = 0x10611c) (xorR32R32Effect 0x10611c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1284, 1292]
    (.letOp (n := 1296) (.out 0x10611e (shlR32Effect 0x10611e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1292]
    (.letOp (n := 1297) (.exec 0x10611e (fun s => s.RIP = 0x10611e) (shlR32Effect 0x10611e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1292]
    (.letOp (n := 1298) (.out 0x106121 (xorR32R32Effect 0x106121 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1296, 1294]
    (.letOp (n := 1299) (.exec 0x106121 (fun s => s.RIP = 0x106121) (xorR32R32Effect 0x106121 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1296, 1294]
    (.letOp (n := 1300) (.out 0x106123 (movR32R32Effect 0x106123 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1298]
    (.letOp (n := 1301) (.exec 0x106123 (fun s => s.RIP = 0x106123) (movR32R32Effect 0x106123 2 0 1) (Reg.operands [.gpr 1] [])) #v[1298]
    (.letOp (n := 1302) (.out 0x106125 (shrR32Effect 0x106125 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1300]
    (.letOp (n := 1303) (.exec 0x106125 (fun s => s.RIP = 0x106125) (shrR32Effect 0x106125 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1300]
    (.letOp (n := 1304) (.out 0x106127 (xorR32R32Effect 0x106127 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1302, 1298]
    (.letOp (n := 1305) (.exec 0x106127 (fun s => s.RIP = 0x106127) (xorR32R32Effect 0x106127 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1302, 1298]
    (.letOp (n := 1306) (.out 0x106129 (andEaxImm32Effect 0x106129 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1304]
    (.letOp (n := 1307) (.exec 0x106129 (fun s => s.RIP = 0x106129) (andEaxImm32Effect 0x106129 0x5050) (Reg.operands [.gpr 0] [])) #v[1304]
    (.letOp (n := 1308) (.out 0x10612e (xorR32R32Effect 0x10612e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1298, 1306]
    (.letOp (n := 1309) (.exec 0x10612e (fun s => s.RIP = 0x10612e) (xorR32R32Effect 0x10612e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1298, 1306]
    (.letOp (n := 1310) (.out 0x106130 (addR32R32Effect 0x106130 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1306, 1306]
    (.letOp (n := 1311) (.exec 0x106130 (fun s => s.RIP = 0x106130) (addR32R32Effect 0x106130 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1306, 1306]
    (.letOp (n := 1312) (.out 0x106132 (xorR32R32Effect 0x106132 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1310, 1308]
    (.letOp (n := 1313) (.exec 0x106132 (fun s => s.RIP = 0x106132) (xorR32R32Effect 0x106132 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1310, 1308]
    (.letOp (n := 1314) (.exec 0x106134 (StorePre 0x106134 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x106134 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106134 8 0 (.sib 4 none 0 (.d32 0x8a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1312, 4]
    (.letOp (n := 1315) (.out 0x10613c (movzxR32M16Effect 0x10613c 8 0 (.sib 4 none 0 (.d32 0x9c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1316) (.exec 0x10613c (LoadPre 0x10613c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x9c)) s (0x10613c + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10613c 8 0 (.sib 4 none 0 (.d32 0x9c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1317) (.out 0x106144 (movR32R32Effect 0x106144 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1315]
    (.letOp (n := 1318) (.exec 0x106144 (fun s => s.RIP = 0x106144) (movR32R32Effect 0x106144 2 1 0) (Reg.operands [.gpr 0] [])) #v[1315]
    (.letOp (n := 1319) (.out 0x106146 (shrR32Effect 0x106146 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1317]
    (.letOp (n := 1320) (.exec 0x106146 (fun s => s.RIP = 0x106146) (shrR32Effect 0x106146 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1317]
    (.letOp (n := 1321) (.out 0x106149 (xorR32R32Effect 0x106149 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1319, 1315]
    (.letOp (n := 1322) (.exec 0x106149 (fun s => s.RIP = 0x106149) (xorR32R32Effect 0x106149 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1319, 1315]
    (.letOp (n := 1323) (.out 0x10614b (andR32Imm32Effect 0x10614b 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1321]
    (.letOp (n := 1324) (.exec 0x10614b (fun s => s.RIP = 0x10614b) (andR32Imm32Effect 0x10614b 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[1321]
    (.letOp (n := 1325) (.out 0x106151 (xorR32R32Effect 0x106151 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1315, 1323]
    (.letOp (n := 1326) (.exec 0x106151 (fun s => s.RIP = 0x106151) (xorR32R32Effect 0x106151 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1315, 1323]
    (b_l10593a_33)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_32 : List UInt8 :=
  [0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x8A, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0x9C,
    0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00,
    0x31, 0xC8] ++ bytes_l10593a_33

theorem code_l10593a_32 : ∀ x ∈ codeRange 0x106111 bytes_l10593a_32, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6111 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_33

def b_l10593a_31 : Block Op Label signature Reg.count 1250 :=
  .letOp (n := 1250) (.out 0x1060c8 (xorR32R32Effect 0x1060c8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1248, 1246]
    (.letOp (n := 1251) (.exec 0x1060c8 (fun s => s.RIP = 0x1060c8) (xorR32R32Effect 0x1060c8 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1248, 1246]
    (.letOp (n := 1252) (.exec 0x1060ca (StorePre 0x1060ca 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x1060ca + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1060ca 8 0 (.sib 4 none 0 (.d32 0x86))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1250, 4]
    (.letOp (n := 1253) (.out 0x1060d2 (movzxR32M16Effect 0x1060d2 8 0 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1254) (.exec 0x1060d2 (LoadPre 0x1060d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1060d2 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x1060d2 8 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1255) (.out 0x1060da (movR32R32Effect 0x1060da 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1253]
    (.letOp (n := 1256) (.exec 0x1060da (fun s => s.RIP = 0x1060da) (movR32R32Effect 0x1060da 2 1 0) (Reg.operands [.gpr 0] [])) #v[1253]
    (.letOp (n := 1257) (.out 0x1060dc (shrR32Effect 0x1060dc 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1255]
    (.letOp (n := 1258) (.exec 0x1060dc (fun s => s.RIP = 0x1060dc) (shrR32Effect 0x1060dc 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1255]
    (.letOp (n := 1259) (.out 0x1060df (xorR32R32Effect 0x1060df 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1257, 1253]
    (.letOp (n := 1260) (.exec 0x1060df (fun s => s.RIP = 0x1060df) (xorR32R32Effect 0x1060df 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1257, 1253]
    (.letOp (n := 1261) (.out 0x1060e1 (andR32Imm32Effect 0x1060e1 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1259]
    (.letOp (n := 1262) (.exec 0x1060e1 (fun s => s.RIP = 0x1060e1) (andR32Imm32Effect 0x1060e1 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1259]
    (.letOp (n := 1263) (.out 0x1060e7 (xorR32R32Effect 0x1060e7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1253, 1261]
    (.letOp (n := 1264) (.exec 0x1060e7 (fun s => s.RIP = 0x1060e7) (xorR32R32Effect 0x1060e7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1253, 1261]
    (.letOp (n := 1265) (.out 0x1060e9 (shlR32Effect 0x1060e9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1261]
    (.letOp (n := 1266) (.exec 0x1060e9 (fun s => s.RIP = 0x1060e9) (shlR32Effect 0x1060e9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1261]
    (.letOp (n := 1267) (.out 0x1060ec (xorR32R32Effect 0x1060ec 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1265, 1263]
    (.letOp (n := 1268) (.exec 0x1060ec (fun s => s.RIP = 0x1060ec) (xorR32R32Effect 0x1060ec 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1265, 1263]
    (.letOp (n := 1269) (.out 0x1060ee (movR32R32Effect 0x1060ee 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1267]
    (.letOp (n := 1270) (.exec 0x1060ee (fun s => s.RIP = 0x1060ee) (movR32R32Effect 0x1060ee 2 0 1) (Reg.operands [.gpr 1] [])) #v[1267]
    (.letOp (n := 1271) (.out 0x1060f0 (shrR32Effect 0x1060f0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1269]
    (.letOp (n := 1272) (.exec 0x1060f0 (fun s => s.RIP = 0x1060f0) (shrR32Effect 0x1060f0 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1269]
    (.letOp (n := 1273) (.out 0x1060f2 (xorR32R32Effect 0x1060f2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1271, 1267]
    (.letOp (n := 1274) (.exec 0x1060f2 (fun s => s.RIP = 0x1060f2) (xorR32R32Effect 0x1060f2 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1271, 1267]
    (.letOp (n := 1275) (.out 0x1060f4 (andEaxImm32Effect 0x1060f4 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1273]
    (.letOp (n := 1276) (.exec 0x1060f4 (fun s => s.RIP = 0x1060f4) (andEaxImm32Effect 0x1060f4 0x5050) (Reg.operands [.gpr 0] [])) #v[1273]
    (.letOp (n := 1277) (.out 0x1060f9 (xorR32R32Effect 0x1060f9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1267, 1275]
    (.letOp (n := 1278) (.exec 0x1060f9 (fun s => s.RIP = 0x1060f9) (xorR32R32Effect 0x1060f9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1267, 1275]
    (.letOp (n := 1279) (.out 0x1060fb (addR32R32Effect 0x1060fb 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1275, 1275]
    (.letOp (n := 1280) (.exec 0x1060fb (fun s => s.RIP = 0x1060fb) (addR32R32Effect 0x1060fb 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1275, 1275]
    (.letOp (n := 1281) (.out 0x1060fd (xorR32R32Effect 0x1060fd 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1279, 1277]
    (.letOp (n := 1282) (.exec 0x1060fd (fun s => s.RIP = 0x1060fd) (xorR32R32Effect 0x1060fd 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1279, 1277]
    (.letOp (n := 1283) (.exec 0x1060ff (StorePre 0x1060ff 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x1060ff + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x1060ff 8 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1281, 4]
    (.letOp (n := 1284) (.out 0x106107 (movzxR32M16Effect 0x106107 8 0 (.sib 4 none 0 (.d32 0x8a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1285) (.exec 0x106107 (LoadPre 0x106107 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x8a)) s (0x106107 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106107 8 0 (.sib 4 none 0 (.d32 0x8a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1286) (.out 0x10610f (movR32R32Effect 0x10610f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1284]
    (.letOp (n := 1287) (.exec 0x10610f (fun s => s.RIP = 0x10610f) (movR32R32Effect 0x10610f 2 1 0) (Reg.operands [.gpr 0] [])) #v[1284]
    (b_l10593a_32))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_31 : List UInt8 :=
  [0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x86, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0x88, 0x00,
    0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31,
    0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00,
    0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x0F,
    0xB7, 0x84, 0x24, 0x8A, 0x00, 0x00, 0x00, 0x89, 0xC1] ++ bytes_l10593a_32

theorem code_l10593a_31 : ∀ x ∈ codeRange 0x1060c8 bytes_l10593a_31, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x60c8 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_32

def b_l10593a_30 : Block Op Label signature Reg.count 1211 :=
  .letOp (n := 1211) (.out 0x106088 (xorR32R32Effect 0x106088 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1209, 1205]
    (.letOp (n := 1212) (.exec 0x106088 (fun s => s.RIP = 0x106088) (xorR32R32Effect 0x106088 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1209, 1205]
    (.letOp (n := 1213) (.out 0x10608a (andEaxImm32Effect 0x10608a 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1211]
    (.letOp (n := 1214) (.exec 0x10608a (fun s => s.RIP = 0x10608a) (andEaxImm32Effect 0x10608a 0x5050) (Reg.operands [.gpr 0] [])) #v[1211]
    (.letOp (n := 1215) (.out 0x10608f (xorR32R32Effect 0x10608f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1205, 1213]
    (.letOp (n := 1216) (.exec 0x10608f (fun s => s.RIP = 0x10608f) (xorR32R32Effect 0x10608f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1205, 1213]
    (.letOp (n := 1217) (.out 0x106091 (addR32R32Effect 0x106091 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1213, 1213]
    (.letOp (n := 1218) (.exec 0x106091 (fun s => s.RIP = 0x106091) (addR32R32Effect 0x106091 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1213, 1213]
    (.letOp (n := 1219) (.out 0x106093 (xorR32R32Effect 0x106093 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1217, 1215]
    (.letOp (n := 1220) (.exec 0x106093 (fun s => s.RIP = 0x106093) (xorR32R32Effect 0x106093 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1217, 1215]
    (.letOp (n := 1221) (.exec 0x106095 (StorePre 0x106095 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x106095 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106095 8 0 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1219, 4]
    (.letOp (n := 1222) (.out 0x10609d (movzxR32M16Effect 0x10609d 8 0 (.sib 4 none 0 (.d32 0x86))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1223) (.exec 0x10609d (LoadPre 0x10609d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x86)) s (0x10609d + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x10609d 8 0 (.sib 4 none 0 (.d32 0x86))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1224) (.out 0x1060a5 (movR32R32Effect 0x1060a5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1222]
    (.letOp (n := 1225) (.exec 0x1060a5 (fun s => s.RIP = 0x1060a5) (movR32R32Effect 0x1060a5 2 1 0) (Reg.operands [.gpr 0] [])) #v[1222]
    (.letOp (n := 1226) (.out 0x1060a7 (shrR32Effect 0x1060a7 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1224]
    (.letOp (n := 1227) (.exec 0x1060a7 (fun s => s.RIP = 0x1060a7) (shrR32Effect 0x1060a7 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1224]
    (.letOp (n := 1228) (.out 0x1060aa (xorR32R32Effect 0x1060aa 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1226, 1222]
    (.letOp (n := 1229) (.exec 0x1060aa (fun s => s.RIP = 0x1060aa) (xorR32R32Effect 0x1060aa 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1226, 1222]
    (.letOp (n := 1230) (.out 0x1060ac (andR32Imm32Effect 0x1060ac 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1228]
    (.letOp (n := 1231) (.exec 0x1060ac (fun s => s.RIP = 0x1060ac) (andR32Imm32Effect 0x1060ac 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1228]
    (.letOp (n := 1232) (.out 0x1060b2 (xorR32R32Effect 0x1060b2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1222, 1230]
    (.letOp (n := 1233) (.exec 0x1060b2 (fun s => s.RIP = 0x1060b2) (xorR32R32Effect 0x1060b2 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1222, 1230]
    (.letOp (n := 1234) (.out 0x1060b4 (shlR32Effect 0x1060b4 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1230]
    (.letOp (n := 1235) (.exec 0x1060b4 (fun s => s.RIP = 0x1060b4) (shlR32Effect 0x1060b4 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1230]
    (.letOp (n := 1236) (.out 0x1060b7 (xorR32R32Effect 0x1060b7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1234, 1232]
    (.letOp (n := 1237) (.exec 0x1060b7 (fun s => s.RIP = 0x1060b7) (xorR32R32Effect 0x1060b7 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1234, 1232]
    (.letOp (n := 1238) (.out 0x1060b9 (movR32R32Effect 0x1060b9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1236]
    (.letOp (n := 1239) (.exec 0x1060b9 (fun s => s.RIP = 0x1060b9) (movR32R32Effect 0x1060b9 2 0 1) (Reg.operands [.gpr 1] [])) #v[1236]
    (.letOp (n := 1240) (.out 0x1060bb (shrR32Effect 0x1060bb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1238]
    (.letOp (n := 1241) (.exec 0x1060bb (fun s => s.RIP = 0x1060bb) (shrR32Effect 0x1060bb 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1238]
    (.letOp (n := 1242) (.out 0x1060bd (xorR32R32Effect 0x1060bd 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1240, 1236]
    (.letOp (n := 1243) (.exec 0x1060bd (fun s => s.RIP = 0x1060bd) (xorR32R32Effect 0x1060bd 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1240, 1236]
    (.letOp (n := 1244) (.out 0x1060bf (andEaxImm32Effect 0x1060bf 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1242]
    (.letOp (n := 1245) (.exec 0x1060bf (fun s => s.RIP = 0x1060bf) (andEaxImm32Effect 0x1060bf 0x5050) (Reg.operands [.gpr 0] [])) #v[1242]
    (.letOp (n := 1246) (.out 0x1060c4 (xorR32R32Effect 0x1060c4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1236, 1244]
    (.letOp (n := 1247) (.exec 0x1060c4 (fun s => s.RIP = 0x1060c4) (xorR32R32Effect 0x1060c4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1236, 1244]
    (.letOp (n := 1248) (.out 0x1060c6 (addR32R32Effect 0x1060c6 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1244, 1244]
    (.letOp (n := 1249) (.exec 0x1060c6 (fun s => s.RIP = 0x1060c6) (addR32R32Effect 0x1060c6 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1244, 1244]
    (b_l10593a_31)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_30 : List UInt8 :=
  [0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84,
    0x24, 0x84, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0x86, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0] ++ bytes_l10593a_31

theorem code_l10593a_30 : ∀ x ∈ codeRange 0x106088 bytes_l10593a_30, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6088 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_31

def b_l10593a_29 : Block Op Label signature Reg.count 1172 :=
  .letOp (n := 1172) (.out 0x10604a (shlR32Effect 0x10604a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1168]
    (.letOp (n := 1173) (.exec 0x10604a (fun s => s.RIP = 0x10604a) (shlR32Effect 0x10604a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1168]
    (.letOp (n := 1174) (.out 0x10604d (xorR32R32Effect 0x10604d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1172, 1170]
    (.letOp (n := 1175) (.exec 0x10604d (fun s => s.RIP = 0x10604d) (xorR32R32Effect 0x10604d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1172, 1170]
    (.letOp (n := 1176) (.out 0x10604f (movR32R32Effect 0x10604f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1174]
    (.letOp (n := 1177) (.exec 0x10604f (fun s => s.RIP = 0x10604f) (movR32R32Effect 0x10604f 2 0 1) (Reg.operands [.gpr 1] [])) #v[1174]
    (.letOp (n := 1178) (.out 0x106051 (shrR32Effect 0x106051 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1176]
    (.letOp (n := 1179) (.exec 0x106051 (fun s => s.RIP = 0x106051) (shrR32Effect 0x106051 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1176]
    (.letOp (n := 1180) (.out 0x106053 (xorR32R32Effect 0x106053 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1178, 1174]
    (.letOp (n := 1181) (.exec 0x106053 (fun s => s.RIP = 0x106053) (xorR32R32Effect 0x106053 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1178, 1174]
    (.letOp (n := 1182) (.out 0x106055 (andEaxImm32Effect 0x106055 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1180]
    (.letOp (n := 1183) (.exec 0x106055 (fun s => s.RIP = 0x106055) (andEaxImm32Effect 0x106055 0x5050) (Reg.operands [.gpr 0] [])) #v[1180]
    (.letOp (n := 1184) (.out 0x10605a (xorR32R32Effect 0x10605a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1174, 1182]
    (.letOp (n := 1185) (.exec 0x10605a (fun s => s.RIP = 0x10605a) (xorR32R32Effect 0x10605a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1174, 1182]
    (.letOp (n := 1186) (.out 0x10605c (addR32R32Effect 0x10605c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1182, 1182]
    (.letOp (n := 1187) (.exec 0x10605c (fun s => s.RIP = 0x10605c) (addR32R32Effect 0x10605c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1182, 1182]
    (.letOp (n := 1188) (.out 0x10605e (xorR32R32Effect 0x10605e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1186, 1184]
    (.letOp (n := 1189) (.exec 0x10605e (fun s => s.RIP = 0x10605e) (xorR32R32Effect 0x10605e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1186, 1184]
    (.letOp (n := 1190) (.exec 0x106060 (StorePre 0x106060 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x106060 + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x106060 8 0 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1188, 4]
    (.letOp (n := 1191) (.out 0x106068 (movzxR32M16Effect 0x106068 8 0 (.sib 4 none 0 (.d32 0x84))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1192) (.exec 0x106068 (LoadPre 0x106068 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x84)) s (0x106068 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106068 8 0 (.sib 4 none 0 (.d32 0x84))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1193) (.out 0x106070 (movR32R32Effect 0x106070 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1191]
    (.letOp (n := 1194) (.exec 0x106070 (fun s => s.RIP = 0x106070) (movR32R32Effect 0x106070 2 1 0) (Reg.operands [.gpr 0] [])) #v[1191]
    (.letOp (n := 1195) (.out 0x106072 (shrR32Effect 0x106072 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1193]
    (.letOp (n := 1196) (.exec 0x106072 (fun s => s.RIP = 0x106072) (shrR32Effect 0x106072 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1193]
    (.letOp (n := 1197) (.out 0x106075 (xorR32R32Effect 0x106075 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1195, 1191]
    (.letOp (n := 1198) (.exec 0x106075 (fun s => s.RIP = 0x106075) (xorR32R32Effect 0x106075 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1195, 1191]
    (.letOp (n := 1199) (.out 0x106077 (andR32Imm32Effect 0x106077 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1197]
    (.letOp (n := 1200) (.exec 0x106077 (fun s => s.RIP = 0x106077) (andR32Imm32Effect 0x106077 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1197]
    (.letOp (n := 1201) (.out 0x10607d (xorR32R32Effect 0x10607d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1191, 1199]
    (.letOp (n := 1202) (.exec 0x10607d (fun s => s.RIP = 0x10607d) (xorR32R32Effect 0x10607d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1191, 1199]
    (.letOp (n := 1203) (.out 0x10607f (shlR32Effect 0x10607f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1199]
    (.letOp (n := 1204) (.exec 0x10607f (fun s => s.RIP = 0x10607f) (shlR32Effect 0x10607f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1199]
    (.letOp (n := 1205) (.out 0x106082 (xorR32R32Effect 0x106082 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1203, 1201]
    (.letOp (n := 1206) (.exec 0x106082 (fun s => s.RIP = 0x106082) (xorR32R32Effect 0x106082 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1203, 1201]
    (.letOp (n := 1207) (.out 0x106084 (movR32R32Effect 0x106084 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1205]
    (.letOp (n := 1208) (.exec 0x106084 (fun s => s.RIP = 0x106084) (movR32R32Effect 0x106084 2 0 1) (Reg.operands [.gpr 1] [])) #v[1205]
    (.letOp (n := 1209) (.out 0x106086 (shrR32Effect 0x106086 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1207]
    (.letOp (n := 1210) (.exec 0x106086 (fun s => s.RIP = 0x106086) (shrR32Effect 0x106086 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1207]
    (b_l10593a_30)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_29 : List UInt8 :=
  [0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00,
    0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x82, 0x00, 0x00, 0x00, 0x0F, 0xB7,
    0x84, 0x24, 0x84, 0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10,
    0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8] ++ bytes_l10593a_30

theorem code_l10593a_29 : ∀ x ∈ codeRange 0x10604a bytes_l10593a_29, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x604a 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_30

def b_l10593a_28 : Block Op Label signature Reg.count 1133 :=
  .letOp (n := 1133) (.out 0x106008 (shrR32Effect 0x106008 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1131]
    (.letOp (n := 1134) (.exec 0x106008 (fun s => s.RIP = 0x106008) (shrR32Effect 0x106008 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1131]
    (.letOp (n := 1135) (.out 0x10600b (xorR32R32Effect 0x10600b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1133, 1129]
    (.letOp (n := 1136) (.exec 0x10600b (fun s => s.RIP = 0x10600b) (xorR32R32Effect 0x10600b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1133, 1129]
    (.letOp (n := 1137) (.out 0x10600d (andR32Imm32Effect 0x10600d 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1135]
    (.letOp (n := 1138) (.exec 0x10600d (fun s => s.RIP = 0x10600d) (andR32Imm32Effect 0x10600d 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1135]
    (.letOp (n := 1139) (.out 0x106013 (xorR32R32Effect 0x106013 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1129, 1137]
    (.letOp (n := 1140) (.exec 0x106013 (fun s => s.RIP = 0x106013) (xorR32R32Effect 0x106013 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1129, 1137]
    (.letOp (n := 1141) (.out 0x106015 (shlR32Effect 0x106015 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1137]
    (.letOp (n := 1142) (.exec 0x106015 (fun s => s.RIP = 0x106015) (shlR32Effect 0x106015 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1137]
    (.letOp (n := 1143) (.out 0x106018 (xorR32R32Effect 0x106018 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1141, 1139]
    (.letOp (n := 1144) (.exec 0x106018 (fun s => s.RIP = 0x106018) (xorR32R32Effect 0x106018 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1141, 1139]
    (.letOp (n := 1145) (.out 0x10601a (movR32R32Effect 0x10601a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1143]
    (.letOp (n := 1146) (.exec 0x10601a (fun s => s.RIP = 0x10601a) (movR32R32Effect 0x10601a 2 0 1) (Reg.operands [.gpr 1] [])) #v[1143]
    (.letOp (n := 1147) (.out 0x10601c (shrR32Effect 0x10601c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1145]
    (.letOp (n := 1148) (.exec 0x10601c (fun s => s.RIP = 0x10601c) (shrR32Effect 0x10601c 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1145]
    (.letOp (n := 1149) (.out 0x10601e (xorR32R32Effect 0x10601e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1147, 1143]
    (.letOp (n := 1150) (.exec 0x10601e (fun s => s.RIP = 0x10601e) (xorR32R32Effect 0x10601e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1147, 1143]
    (.letOp (n := 1151) (.out 0x106020 (andEaxImm32Effect 0x106020 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1149]
    (.letOp (n := 1152) (.exec 0x106020 (fun s => s.RIP = 0x106020) (andEaxImm32Effect 0x106020 0x5050) (Reg.operands [.gpr 0] [])) #v[1149]
    (.letOp (n := 1153) (.out 0x106025 (xorR32R32Effect 0x106025 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1143, 1151]
    (.letOp (n := 1154) (.exec 0x106025 (fun s => s.RIP = 0x106025) (xorR32R32Effect 0x106025 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1143, 1151]
    (.letOp (n := 1155) (.out 0x106027 (addR32R32Effect 0x106027 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1151, 1151]
    (.letOp (n := 1156) (.exec 0x106027 (fun s => s.RIP = 0x106027) (addR32R32Effect 0x106027 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1151, 1151]
    (.letOp (n := 1157) (.out 0x106029 (xorR32R32Effect 0x106029 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1155, 1153]
    (.letOp (n := 1158) (.exec 0x106029 (fun s => s.RIP = 0x106029) (xorR32R32Effect 0x106029 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1155, 1153]
    (.letOp (n := 1159) (.exec 0x10602b (StorePre 0x10602b 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10602b + BitVec.ofNat 64 8)) 2) (movM16R16Effect 0x10602b 8 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1157, 4]
    (.letOp (n := 1160) (.out 0x106033 (movzxR32M16Effect 0x106033 8 0 (.sib 4 none 0 (.d32 0x82))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1161) (.exec 0x106033 (LoadPre 0x106033 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x82)) s (0x106033 + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x106033 8 0 (.sib 4 none 0 (.d32 0x82))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1162) (.out 0x10603b (movR32R32Effect 0x10603b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1160]
    (.letOp (n := 1163) (.exec 0x10603b (fun s => s.RIP = 0x10603b) (movR32R32Effect 0x10603b 2 1 0) (Reg.operands [.gpr 0] [])) #v[1160]
    (.letOp (n := 1164) (.out 0x10603d (shrR32Effect 0x10603d 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1162]
    (.letOp (n := 1165) (.exec 0x10603d (fun s => s.RIP = 0x10603d) (shrR32Effect 0x10603d 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1162]
    (.letOp (n := 1166) (.out 0x106040 (xorR32R32Effect 0x106040 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1164, 1160]
    (.letOp (n := 1167) (.exec 0x106040 (fun s => s.RIP = 0x106040) (xorR32R32Effect 0x106040 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1164, 1160]
    (.letOp (n := 1168) (.out 0x106042 (andR32Imm32Effect 0x106042 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1166]
    (.letOp (n := 1169) (.exec 0x106042 (fun s => s.RIP = 0x106042) (andR32Imm32Effect 0x106042 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1166]
    (.letOp (n := 1170) (.out 0x106048 (xorR32R32Effect 0x106048 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1160, 1168]
    (.letOp (n := 1171) (.exec 0x106048 (fun s => s.RIP = 0x106048) (xorR32R32Effect 0x106048 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1160, 1168]
    (b_l10593a_29)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_28 : List UInt8 :=
  [0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x84, 0x24, 0x82,
    0x00, 0x00, 0x00, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00,
    0x31, 0xC8] ++ bytes_l10593a_29

theorem code_l10593a_28 : ∀ x ∈ codeRange 0x106008 bytes_l10593a_28, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6008 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_29

def b_l10593a_27 : Block Op Label signature Reg.count 1094 :=
  .letOp (n := 1094) (.out 0x105fc9 (addR32R32Effect 0x105fc9 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[1090, 1090]
    (.letOp (n := 1095) (.exec 0x105fc9 (fun s => s.RIP = 0x105fc9) (addR32R32Effect 0x105fc9 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[1090, 1090]
    (.letOp (n := 1096) (.out 0x105fcc (xorR32R32Effect 0x105fcc 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[1094, 1092]
    (.letOp (n := 1097) (.exec 0x105fcc (fun s => s.RIP = 0x105fcc) (xorR32R32Effect 0x105fcc 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[1094, 1092]
    (.letOp (n := 1098) (.out 0x105fcf (movzxR32M16Effect 0x105fcf 5 0 (.sib 4 none 0 (.d8 0x7e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1099) (.exec 0x105fcf (LoadPre 0x105fcf (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x105fcf + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105fcf 5 0 (.sib 4 none 0 (.d8 0x7e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1100) (.out 0x105fd4 (movR32R32Effect 0x105fd4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1098]
    (.letOp (n := 1101) (.exec 0x105fd4 (fun s => s.RIP = 0x105fd4) (movR32R32Effect 0x105fd4 2 1 0) (Reg.operands [.gpr 0] [])) #v[1098]
    (.letOp (n := 1102) (.out 0x105fd6 (shrR32Effect 0x105fd6 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1100]
    (.letOp (n := 1103) (.exec 0x105fd6 (fun s => s.RIP = 0x105fd6) (shrR32Effect 0x105fd6 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1100]
    (.letOp (n := 1104) (.out 0x105fd9 (xorR32R32Effect 0x105fd9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1102, 1098]
    (.letOp (n := 1105) (.exec 0x105fd9 (fun s => s.RIP = 0x105fd9) (xorR32R32Effect 0x105fd9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1102, 1098]
    (.letOp (n := 1106) (.out 0x105fdb (andR32Imm32Effect 0x105fdb 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1104]
    (.letOp (n := 1107) (.exec 0x105fdb (fun s => s.RIP = 0x105fdb) (andR32Imm32Effect 0x105fdb 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1104]
    (.letOp (n := 1108) (.out 0x105fe1 (xorR32R32Effect 0x105fe1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1098, 1106]
    (.letOp (n := 1109) (.exec 0x105fe1 (fun s => s.RIP = 0x105fe1) (xorR32R32Effect 0x105fe1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1098, 1106]
    (.letOp (n := 1110) (.out 0x105fe3 (shlR32Effect 0x105fe3 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1106]
    (.letOp (n := 1111) (.exec 0x105fe3 (fun s => s.RIP = 0x105fe3) (shlR32Effect 0x105fe3 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1106]
    (.letOp (n := 1112) (.out 0x105fe6 (xorR32R32Effect 0x105fe6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1110, 1108]
    (.letOp (n := 1113) (.exec 0x105fe6 (fun s => s.RIP = 0x105fe6) (xorR32R32Effect 0x105fe6 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1110, 1108]
    (.letOp (n := 1114) (.out 0x105fe8 (movR32R32Effect 0x105fe8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1112]
    (.letOp (n := 1115) (.exec 0x105fe8 (fun s => s.RIP = 0x105fe8) (movR32R32Effect 0x105fe8 2 0 1) (Reg.operands [.gpr 1] [])) #v[1112]
    (.letOp (n := 1116) (.out 0x105fea (shrR32Effect 0x105fea 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[1114]
    (.letOp (n := 1117) (.exec 0x105fea (fun s => s.RIP = 0x105fea) (shrR32Effect 0x105fea 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1114]
    (.letOp (n := 1118) (.out 0x105fec (xorR32R32Effect 0x105fec 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1116, 1112]
    (.letOp (n := 1119) (.exec 0x105fec (fun s => s.RIP = 0x105fec) (xorR32R32Effect 0x105fec 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1116, 1112]
    (.letOp (n := 1120) (.out 0x105fee (andEaxImm32Effect 0x105fee 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[1118]
    (.letOp (n := 1121) (.exec 0x105fee (fun s => s.RIP = 0x105fee) (andEaxImm32Effect 0x105fee 0x5050) (Reg.operands [.gpr 0] [])) #v[1118]
    (.letOp (n := 1122) (.out 0x105ff3 (xorR32R32Effect 0x105ff3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1112, 1120]
    (.letOp (n := 1123) (.exec 0x105ff3 (fun s => s.RIP = 0x105ff3) (xorR32R32Effect 0x105ff3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1112, 1120]
    (.letOp (n := 1124) (.out 0x105ff5 (addR32R32Effect 0x105ff5 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[1120, 1120]
    (.letOp (n := 1125) (.exec 0x105ff5 (fun s => s.RIP = 0x105ff5) (addR32R32Effect 0x105ff5 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[1120, 1120]
    (.letOp (n := 1126) (.out 0x105ff7 (xorR32R32Effect 0x105ff7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1124, 1122]
    (.letOp (n := 1127) (.exec 0x105ff7 (fun s => s.RIP = 0x105ff7) (xorR32R32Effect 0x105ff7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1124, 1122]
    (.letOp (n := 1128) (.exec 0x105ff9 (StorePre 0x105ff9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7e)) s (0x105ff9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ff9 5 0 (.sib 4 none 0 (.d8 0x7e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1126, 4]
    (.letOp (n := 1129) (.out 0x105ffe (movzxR32M16Effect 0x105ffe 8 0 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1130) (.exec 0x105ffe (LoadPre 0x105ffe (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x105ffe + BitVec.ofNat 64 8)) 2) (movzxR32M16Effect 0x105ffe 8 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1131) (.out 0x106006 (movR32R32Effect 0x106006 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1129]
    (.letOp (n := 1132) (.exec 0x106006 (fun s => s.RIP = 0x106006) (movR32R32Effect 0x106006 2 1 0) (Reg.operands [.gpr 0] [])) #v[1129]
    (b_l10593a_28)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_27 : List UInt8 :=
  [0x45, 0x01, 0xFF, 0x41, 0x31, 0xCF, 0x0F, 0xB7, 0x44, 0x24, 0x7E, 0x89, 0xC1, 0xC1, 0xE9, 0x02,
    0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x7E, 0x0F, 0xB7, 0x84, 0x24, 0x80, 0x00, 0x00, 0x00, 0x89, 0xC1] ++ bytes_l10593a_28

theorem code_l10593a_27 : ∀ x ∈ codeRange 0x105fc9 bytes_l10593a_27, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5fc9 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_28

def b_l10593a_26 : Block Op Label signature Reg.count 1055 :=
  .letOp (n := 1055) (.out 0x105f86 (shrR32Effect 0x105f86 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1053]
    (.letOp (n := 1056) (.exec 0x105f86 (fun s => s.RIP = 0x105f86) (shrR32Effect 0x105f86 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1053]
    (.letOp (n := 1057) (.out 0x105f89 (xorR32R32Effect 0x105f89 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1055, 1051]
    (.letOp (n := 1058) (.exec 0x105f89 (fun s => s.RIP = 0x105f89) (xorR32R32Effect 0x105f89 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1055, 1051]
    (.letOp (n := 1059) (.out 0x105f8b (andR32Imm32Effect 0x105f8b 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1057]
    (.letOp (n := 1060) (.exec 0x105f8b (fun s => s.RIP = 0x105f8b) (andR32Imm32Effect 0x105f8b 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1057]
    (.letOp (n := 1061) (.out 0x105f91 (xorR32R32Effect 0x105f91 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1051, 1059]
    (.letOp (n := 1062) (.exec 0x105f91 (fun s => s.RIP = 0x105f91) (xorR32R32Effect 0x105f91 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1051, 1059]
    (.letOp (n := 1063) (.out 0x105f93 (shlR32Effect 0x105f93 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1059]
    (.letOp (n := 1064) (.exec 0x105f93 (fun s => s.RIP = 0x105f93) (shlR32Effect 0x105f93 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1059]
    (.letOp (n := 1065) (.out 0x105f96 (xorR32R32Effect 0x105f96 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1063, 1061]
    (.letOp (n := 1066) (.exec 0x105f96 (fun s => s.RIP = 0x105f96) (xorR32R32Effect 0x105f96 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1063, 1061]
    (.letOp (n := 1067) (.exec 0x105f98 (StorePre 0x105f98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105f98 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f98 5 1 (.sib 4 none 0 (.d8 0x7a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1065, 4]
    (.letOp (n := 1068) (.out 0x105f9d (movzxR32M16Effect 0x105f9d 5 0 (.sib 4 none 0 (.d8 0x7c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1069) (.exec 0x105f9d (LoadPre 0x105f9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7c)) s (0x105f9d + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f9d 5 0 (.sib 4 none 0 (.d8 0x7c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1070) (.out 0x105fa2 (movR32R32Effect 0x105fa2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1068]
    (.letOp (n := 1071) (.exec 0x105fa2 (fun s => s.RIP = 0x105fa2) (movR32R32Effect 0x105fa2 2 1 0) (Reg.operands [.gpr 0] [])) #v[1068]
    (.letOp (n := 1072) (.out 0x105fa4 (shrR32Effect 0x105fa4 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1070]
    (.letOp (n := 1073) (.exec 0x105fa4 (fun s => s.RIP = 0x105fa4) (shrR32Effect 0x105fa4 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1070]
    (.letOp (n := 1074) (.out 0x105fa7 (xorR32R32Effect 0x105fa7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1072, 1068]
    (.letOp (n := 1075) (.exec 0x105fa7 (fun s => s.RIP = 0x105fa7) (xorR32R32Effect 0x105fa7 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1072, 1068]
    (.letOp (n := 1076) (.out 0x105fa9 (andR32Imm32Effect 0x105fa9 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1074]
    (.letOp (n := 1077) (.exec 0x105fa9 (fun s => s.RIP = 0x105fa9) (andR32Imm32Effect 0x105fa9 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[1074]
    (.letOp (n := 1078) (.out 0x105faf (xorR32R32Effect 0x105faf 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1068, 1076]
    (.letOp (n := 1079) (.exec 0x105faf (fun s => s.RIP = 0x105faf) (xorR32R32Effect 0x105faf 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1068, 1076]
    (.letOp (n := 1080) (.out 0x105fb1 (shlR32Effect 0x105fb1 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1076]
    (.letOp (n := 1081) (.exec 0x105fb1 (fun s => s.RIP = 0x105fb1) (shlR32Effect 0x105fb1 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1076]
    (.letOp (n := 1082) (.out 0x105fb4 (xorR32R32Effect 0x105fb4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1080, 1078]
    (.letOp (n := 1083) (.exec 0x105fb4 (fun s => s.RIP = 0x105fb4) (xorR32R32Effect 0x105fb4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1080, 1078]
    (.letOp (n := 1084) (.out 0x105fb6 (movR32R32Effect 0x105fb6 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 1] []) (.reg (.gpr 15))) #v[1082]
    (.letOp (n := 1085) (.exec 0x105fb6 (fun s => s.RIP = 0x105fb6) (movR32R32Effect 0x105fb6 3 15 1) (Reg.operands [.gpr 1] [])) #v[1082]
    (.letOp (n := 1086) (.out 0x105fb9 (shrR32Effect 0x105fb9 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[1084]
    (.letOp (n := 1087) (.exec 0x105fb9 (fun s => s.RIP = 0x105fb9) (shrR32Effect 0x105fb9 3 15 1) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1084]
    (.letOp (n := 1088) (.out 0x105fbc (xorR32R32Effect 0x105fbc 3 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[1086, 1082]
    (.letOp (n := 1089) (.exec 0x105fbc (fun s => s.RIP = 0x105fbc) (xorR32R32Effect 0x105fbc 3 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[1086, 1082]
    (.letOp (n := 1090) (.out 0x105fbf (andR32Imm32Effect 0x105fbf 7 15 0x5050) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[1088]
    (.letOp (n := 1091) (.exec 0x105fbf (fun s => s.RIP = 0x105fbf) (andR32Imm32Effect 0x105fbf 7 15 0x5050) (Reg.operands [.gpr 15] [])) #v[1088]
    (.letOp (n := 1092) (.out 0x105fc6 (xorR32R32Effect 0x105fc6 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[1082, 1090]
    (.letOp (n := 1093) (.exec 0x105fc6 (fun s => s.RIP = 0x105fc6) (xorR32R32Effect 0x105fc6 3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[1082, 1090]
    (b_l10593a_27)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_26 : List UInt8 :=
  [0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x7A, 0x0F, 0xB7, 0x44, 0x24, 0x7C, 0x89, 0xC1, 0xC1, 0xE9,
    0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1,
    0x41, 0x89, 0xCF, 0x41, 0xD1, 0xEF, 0x41, 0x31, 0xCF, 0x41, 0x81, 0xE7, 0x50, 0x50, 0x00, 0x00,
    0x44, 0x31, 0xF9] ++ bytes_l10593a_27

theorem code_l10593a_26 : ∀ x ∈ codeRange 0x105f86 bytes_l10593a_26, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5f86 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_27

def b_l10593a_25 : Block Op Label signature Reg.count 1016 :=
  .letOp (n := 1016) (.out 0x105f38 (xorR32R32Effect 0x105f38 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1014, 1012]
    (.letOp (n := 1017) (.exec 0x105f38 (fun s => s.RIP = 0x105f38) (xorR32R32Effect 0x105f38 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1014, 1012]
    (.letOp (n := 1018) (.exec 0x105f3a (StorePre 0x105f3a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105f3a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f3a 5 1 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1016, 4]
    (.letOp (n := 1019) (.out 0x105f3f (movzxR32M16Effect 0x105f3f 5 0 (.sib 4 none 0 (.d8 0x76))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1020) (.exec 0x105f3f (LoadPre 0x105f3f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x76)) s (0x105f3f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f3f 5 0 (.sib 4 none 0 (.d8 0x76))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1021) (.out 0x105f44 (movR32R32Effect 0x105f44 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[1019]
    (.letOp (n := 1022) (.exec 0x105f44 (fun s => s.RIP = 0x105f44) (movR32R32Effect 0x105f44 3 9 0) (Reg.operands [.gpr 0] [])) #v[1019]
    (.letOp (n := 1023) (.out 0x105f47 (shrR32Effect 0x105f47 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1021]
    (.letOp (n := 1024) (.exec 0x105f47 (fun s => s.RIP = 0x105f47) (shrR32Effect 0x105f47 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1021]
    (.letOp (n := 1025) (.out 0x105f4b (xorR32R32Effect 0x105f4b 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1023, 1019]
    (.letOp (n := 1026) (.exec 0x105f4b (fun s => s.RIP = 0x105f4b) (xorR32R32Effect 0x105f4b 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1023, 1019]
    (.letOp (n := 1027) (.out 0x105f4e (andR32Imm32Effect 0x105f4e 7 9 0x3030) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[1025]
    (.letOp (n := 1028) (.exec 0x105f4e (fun s => s.RIP = 0x105f4e) (andR32Imm32Effect 0x105f4e 7 9 0x3030) (Reg.operands [.gpr 9] [])) #v[1025]
    (.letOp (n := 1029) (.out 0x105f55 (xorR32R32Effect 0x105f55 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[1019, 1027]
    (.letOp (n := 1030) (.exec 0x105f55 (fun s => s.RIP = 0x105f55) (xorR32R32Effect 0x105f55 3 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[1019, 1027]
    (.letOp (n := 1031) (.out 0x105f58 (shlR32Effect 0x105f58 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1027]
    (.letOp (n := 1032) (.exec 0x105f58 (fun s => s.RIP = 0x105f58) (shlR32Effect 0x105f58 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1027]
    (.letOp (n := 1033) (.out 0x105f5c (xorR32R32Effect 0x105f5c 3 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[1031, 1029]
    (.letOp (n := 1034) (.exec 0x105f5c (fun s => s.RIP = 0x105f5c) (xorR32R32Effect 0x105f5c 3 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[1031, 1029]
    (.letOp (n := 1035) (.out 0x105f5f (movzxR32M16Effect 0x105f5f 5 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1036) (.exec 0x105f5f (LoadPre 0x105f5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x105f5f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f5f 5 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1037) (.out 0x105f64 (movR32R32Effect 0x105f64 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[1035]
    (.letOp (n := 1038) (.exec 0x105f64 (fun s => s.RIP = 0x105f64) (movR32R32Effect 0x105f64 3 14 0) (Reg.operands [.gpr 0] [])) #v[1035]
    (.letOp (n := 1039) (.out 0x105f67 (shrR32Effect 0x105f67 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1037]
    (.letOp (n := 1040) (.exec 0x105f67 (fun s => s.RIP = 0x105f67) (shrR32Effect 0x105f67 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1037]
    (.letOp (n := 1041) (.out 0x105f6b (xorR32R32Effect 0x105f6b 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1039, 1035]
    (.letOp (n := 1042) (.exec 0x105f6b (fun s => s.RIP = 0x105f6b) (xorR32R32Effect 0x105f6b 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1039, 1035]
    (.letOp (n := 1043) (.out 0x105f6e (andR32Imm32Effect 0x105f6e 7 14 0x3030) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[1041]
    (.letOp (n := 1044) (.exec 0x105f6e (fun s => s.RIP = 0x105f6e) (andR32Imm32Effect 0x105f6e 7 14 0x3030) (Reg.operands [.gpr 14] [])) #v[1041]
    (.letOp (n := 1045) (.out 0x105f75 (xorR32R32Effect 0x105f75 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[1035, 1043]
    (.letOp (n := 1046) (.exec 0x105f75 (fun s => s.RIP = 0x105f75) (xorR32R32Effect 0x105f75 3 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[1035, 1043]
    (.letOp (n := 1047) (.out 0x105f78 (shlR32Effect 0x105f78 4 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[1043]
    (.letOp (n := 1048) (.exec 0x105f78 (fun s => s.RIP = 0x105f78) (shlR32Effect 0x105f78 4 14 2) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1043]
    (.letOp (n := 1049) (.out 0x105f7c (xorR32R32Effect 0x105f7c 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[1047, 1045]
    (.letOp (n := 1050) (.exec 0x105f7c (fun s => s.RIP = 0x105f7c) (xorR32R32Effect 0x105f7c 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[1047, 1045]
    (.letOp (n := 1051) (.out 0x105f7f (movzxR32M16Effect 0x105f7f 5 0 (.sib 4 none 0 (.d8 0x7a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1052) (.exec 0x105f7f (LoadPre 0x105f7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7a)) s (0x105f7f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f7f 5 0 (.sib 4 none 0 (.d8 0x7a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1053) (.out 0x105f84 (movR32R32Effect 0x105f84 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1051]
    (.letOp (n := 1054) (.exec 0x105f84 (fun s => s.RIP = 0x105f84) (movR32R32Effect 0x105f84 2 1 0) (Reg.operands [.gpr 0] [])) #v[1051]
    (b_l10593a_26)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_25 : List UInt8 :=
  [0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x74, 0x0F, 0xB7, 0x44, 0x24, 0x76, 0x41, 0x89, 0xC1, 0x41,
    0xC1, 0xE9, 0x02, 0x41, 0x31, 0xC1, 0x41, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x44, 0x31, 0xC8,
    0x41, 0xC1, 0xE1, 0x02, 0x41, 0x31, 0xC1, 0x0F, 0xB7, 0x44, 0x24, 0x78, 0x41, 0x89, 0xC6, 0x41,
    0xC1, 0xEE, 0x02, 0x41, 0x31, 0xC6, 0x41, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00, 0x44, 0x31, 0xF0,
    0x41, 0xC1, 0xE6, 0x02, 0x41, 0x31, 0xC6, 0x0F, 0xB7, 0x44, 0x24, 0x7A, 0x89, 0xC1] ++ bytes_l10593a_26

theorem code_l10593a_25 : ∀ x ∈ codeRange 0x105f38 bytes_l10593a_25, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5f38 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_26

def b_l10593a_24 : Block Op Label signature Reg.count 978 :=
  .letOp (n := 978) (.out 0x105ef7 (xorR32R32Effect 0x105ef7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[968, 976]
    (.letOp (n := 979) (.exec 0x105ef7 (fun s => s.RIP = 0x105ef7) (xorR32R32Effect 0x105ef7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[968, 976]
    (.letOp (n := 980) (.out 0x105ef9 (shlR32Effect 0x105ef9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[976]
    (.letOp (n := 981) (.exec 0x105ef9 (fun s => s.RIP = 0x105ef9) (shlR32Effect 0x105ef9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[976]
    (.letOp (n := 982) (.out 0x105efc (xorR32R32Effect 0x105efc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[980, 978]
    (.letOp (n := 983) (.exec 0x105efc (fun s => s.RIP = 0x105efc) (xorR32R32Effect 0x105efc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[980, 978]
    (.letOp (n := 984) (.exec 0x105efe (StorePre 0x105efe 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x105efe + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105efe 5 1 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[982, 4]
    (.letOp (n := 985) (.out 0x105f03 (movzxR32M16Effect 0x105f03 5 0 (.sib 4 none 0 (.d8 0x72))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 986) (.exec 0x105f03 (LoadPre 0x105f03 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x105f03 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f03 5 0 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 987) (.out 0x105f08 (movR32R32Effect 0x105f08 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[985]
    (.letOp (n := 988) (.exec 0x105f08 (fun s => s.RIP = 0x105f08) (movR32R32Effect 0x105f08 2 1 0) (Reg.operands [.gpr 0] [])) #v[985]
    (.letOp (n := 989) (.out 0x105f0a (shrR32Effect 0x105f0a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[987]
    (.letOp (n := 990) (.exec 0x105f0a (fun s => s.RIP = 0x105f0a) (shrR32Effect 0x105f0a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[987]
    (.letOp (n := 991) (.out 0x105f0d (xorR32R32Effect 0x105f0d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[989, 985]
    (.letOp (n := 992) (.exec 0x105f0d (fun s => s.RIP = 0x105f0d) (xorR32R32Effect 0x105f0d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[989, 985]
    (.letOp (n := 993) (.out 0x105f0f (andR32Imm32Effect 0x105f0f 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[991]
    (.letOp (n := 994) (.exec 0x105f0f (fun s => s.RIP = 0x105f0f) (andR32Imm32Effect 0x105f0f 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[991]
    (.letOp (n := 995) (.out 0x105f15 (xorR32R32Effect 0x105f15 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[985, 993]
    (.letOp (n := 996) (.exec 0x105f15 (fun s => s.RIP = 0x105f15) (xorR32R32Effect 0x105f15 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[985, 993]
    (.letOp (n := 997) (.out 0x105f17 (shlR32Effect 0x105f17 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[993]
    (.letOp (n := 998) (.exec 0x105f17 (fun s => s.RIP = 0x105f17) (shlR32Effect 0x105f17 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[993]
    (.letOp (n := 999) (.out 0x105f1a (xorR32R32Effect 0x105f1a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[997, 995]
    (.letOp (n := 1000) (.exec 0x105f1a (fun s => s.RIP = 0x105f1a) (xorR32R32Effect 0x105f1a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[997, 995]
    (.letOp (n := 1001) (.exec 0x105f1c (StorePre 0x105f1c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x72)) s (0x105f1c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105f1c 5 1 (.sib 4 none 0 (.d8 0x72))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[999, 4]
    (.letOp (n := 1002) (.out 0x105f21 (movzxR32M16Effect 0x105f21 5 0 (.sib 4 none 0 (.d8 0x74))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 1003) (.exec 0x105f21 (LoadPre 0x105f21 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x74)) s (0x105f21 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105f21 5 0 (.sib 4 none 0 (.d8 0x74))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 1004) (.out 0x105f26 (movR32R32Effect 0x105f26 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[1002]
    (.letOp (n := 1005) (.exec 0x105f26 (fun s => s.RIP = 0x105f26) (movR32R32Effect 0x105f26 2 1 0) (Reg.operands [.gpr 0] [])) #v[1002]
    (.letOp (n := 1006) (.out 0x105f28 (shrR32Effect 0x105f28 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1004]
    (.letOp (n := 1007) (.exec 0x105f28 (fun s => s.RIP = 0x105f28) (shrR32Effect 0x105f28 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1004]
    (.letOp (n := 1008) (.out 0x105f2b (xorR32R32Effect 0x105f2b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[1006, 1002]
    (.letOp (n := 1009) (.exec 0x105f2b (fun s => s.RIP = 0x105f2b) (xorR32R32Effect 0x105f2b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[1006, 1002]
    (.letOp (n := 1010) (.out 0x105f2d (andR32Imm32Effect 0x105f2d 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1008]
    (.letOp (n := 1011) (.exec 0x105f2d (fun s => s.RIP = 0x105f2d) (andR32Imm32Effect 0x105f2d 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[1008]
    (.letOp (n := 1012) (.out 0x105f33 (xorR32R32Effect 0x105f33 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[1002, 1010]
    (.letOp (n := 1013) (.exec 0x105f33 (fun s => s.RIP = 0x105f33) (xorR32R32Effect 0x105f33 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[1002, 1010]
    (.letOp (n := 1014) (.out 0x105f35 (shlR32Effect 0x105f35 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1010]
    (.letOp (n := 1015) (.exec 0x105f35 (fun s => s.RIP = 0x105f35) (shlR32Effect 0x105f35 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1010]
    (b_l10593a_25))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_24 : List UInt8 :=
  [0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x70, 0x0F, 0xB7, 0x44, 0x24,
    0x72, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8,
    0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x72, 0x0F, 0xB7, 0x44, 0x24, 0x74, 0x89,
    0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1,
    0x02] ++ bytes_l10593a_25

theorem code_l10593a_24 : ∀ x ∈ codeRange 0x105ef7 bytes_l10593a_24, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5ef7 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_25

def b_l10593a_23 : Block Op Label signature Reg.count 940 :=
  .letOp (n := 940) (.out 0x105eaf (xorR32R32Effect 0x105eaf 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[938, 934]
    (.letOp (n := 941) (.exec 0x105eaf (fun s => s.RIP = 0x105eaf) (xorR32R32Effect 0x105eaf 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[938, 934]
    (.letOp (n := 942) (.out 0x105eb1 (andR32Imm32Effect 0x105eb1 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[940]
    (.letOp (n := 943) (.exec 0x105eb1 (fun s => s.RIP = 0x105eb1) (andR32Imm32Effect 0x105eb1 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[940]
    (.letOp (n := 944) (.out 0x105eb7 (xorR32R32Effect 0x105eb7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[934, 942]
    (.letOp (n := 945) (.exec 0x105eb7 (fun s => s.RIP = 0x105eb7) (xorR32R32Effect 0x105eb7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[934, 942]
    (.letOp (n := 946) (.out 0x105eb9 (shlR32Effect 0x105eb9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[942]
    (.letOp (n := 947) (.exec 0x105eb9 (fun s => s.RIP = 0x105eb9) (shlR32Effect 0x105eb9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[942]
    (.letOp (n := 948) (.out 0x105ebc (xorR32R32Effect 0x105ebc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[946, 944]
    (.letOp (n := 949) (.exec 0x105ebc (fun s => s.RIP = 0x105ebc) (xorR32R32Effect 0x105ebc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[946, 944]
    (.letOp (n := 950) (.exec 0x105ebe (StorePre 0x105ebe 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x100)) s (0x105ebe + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ebe 1 (.sib 4 none 0 (.d32 0x100))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[948, 4]
    (.letOp (n := 951) (.out 0x105ec5 (movzxR32M16Effect 0x105ec5 5 0 (.sib 4 none 0 (.d8 0x6e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 952) (.exec 0x105ec5 (LoadPre 0x105ec5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6e)) s (0x105ec5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ec5 5 0 (.sib 4 none 0 (.d8 0x6e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 953) (.out 0x105eca (movR32R32Effect 0x105eca 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[951]
    (.letOp (n := 954) (.exec 0x105eca (fun s => s.RIP = 0x105eca) (movR32R32Effect 0x105eca 2 1 0) (Reg.operands [.gpr 0] [])) #v[951]
    (.letOp (n := 955) (.out 0x105ecc (shrR32Effect 0x105ecc 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[953]
    (.letOp (n := 956) (.exec 0x105ecc (fun s => s.RIP = 0x105ecc) (shrR32Effect 0x105ecc 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[953]
    (.letOp (n := 957) (.out 0x105ecf (xorR32R32Effect 0x105ecf 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[955, 951]
    (.letOp (n := 958) (.exec 0x105ecf (fun s => s.RIP = 0x105ecf) (xorR32R32Effect 0x105ecf 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[955, 951]
    (.letOp (n := 959) (.out 0x105ed1 (andR32Imm32Effect 0x105ed1 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[957]
    (.letOp (n := 960) (.exec 0x105ed1 (fun s => s.RIP = 0x105ed1) (andR32Imm32Effect 0x105ed1 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[957]
    (.letOp (n := 961) (.out 0x105ed7 (xorR32R32Effect 0x105ed7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[951, 959]
    (.letOp (n := 962) (.exec 0x105ed7 (fun s => s.RIP = 0x105ed7) (xorR32R32Effect 0x105ed7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[951, 959]
    (.letOp (n := 963) (.out 0x105ed9 (shlR32Effect 0x105ed9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[959]
    (.letOp (n := 964) (.exec 0x105ed9 (fun s => s.RIP = 0x105ed9) (shlR32Effect 0x105ed9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[959]
    (.letOp (n := 965) (.out 0x105edc (xorR32R32Effect 0x105edc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[963, 961]
    (.letOp (n := 966) (.exec 0x105edc (fun s => s.RIP = 0x105edc) (xorR32R32Effect 0x105edc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[963, 961]
    (.letOp (n := 967) (.exec 0x105ede (StorePre 0x105ede 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xfc)) s (0x105ede + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ede 1 (.sib 4 none 0 (.d32 0xfc))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[965, 4]
    (.letOp (n := 968) (.out 0x105ee5 (movzxR32M16Effect 0x105ee5 5 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 969) (.exec 0x105ee5 (LoadPre 0x105ee5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x105ee5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ee5 5 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 970) (.out 0x105eea (movR32R32Effect 0x105eea 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[968]
    (.letOp (n := 971) (.exec 0x105eea (fun s => s.RIP = 0x105eea) (movR32R32Effect 0x105eea 2 1 0) (Reg.operands [.gpr 0] [])) #v[968]
    (.letOp (n := 972) (.out 0x105eec (shrR32Effect 0x105eec 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[970]
    (.letOp (n := 973) (.exec 0x105eec (fun s => s.RIP = 0x105eec) (shrR32Effect 0x105eec 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[970]
    (.letOp (n := 974) (.out 0x105eef (xorR32R32Effect 0x105eef 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[972, 968]
    (.letOp (n := 975) (.exec 0x105eef (fun s => s.RIP = 0x105eef) (xorR32R32Effect 0x105eef 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[972, 968]
    (.letOp (n := 976) (.out 0x105ef1 (andR32Imm32Effect 0x105ef1 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[974]
    (.letOp (n := 977) (.exec 0x105ef1 (fun s => s.RIP = 0x105ef1) (andR32Imm32Effect 0x105ef1 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[974]
    (b_l10593a_24))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_23 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0x8C, 0x24, 0x00, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x6E, 0x89, 0xC1, 0xC1, 0xE9, 0x02,
    0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0x8C, 0x24, 0xFC, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x70, 0x89, 0xC1, 0xC1, 0xE9, 0x02,
    0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] ++ bytes_l10593a_24

theorem code_l10593a_23 : ∀ x ∈ codeRange 0x105eaf bytes_l10593a_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5eaf 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_24

def b_l10593a_22 : Block Op Label signature Reg.count 902 :=
  .letOp (n := 902) (.exec 0x105e71 (StorePre 0x105e71 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x105e71 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e71 5 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[900, 4]
    (.letOp (n := 903) (.out 0x105e76 (movzxR32M16Effect 0x105e76 5 0 (.sib 4 none 0 (.d8 0x6a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 904) (.exec 0x105e76 (LoadPre 0x105e76 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105e76 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e76 5 0 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 905) (.out 0x105e7b (movR32R32Effect 0x105e7b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[903]
    (.letOp (n := 906) (.exec 0x105e7b (fun s => s.RIP = 0x105e7b) (movR32R32Effect 0x105e7b 2 1 0) (Reg.operands [.gpr 0] [])) #v[903]
    (.letOp (n := 907) (.out 0x105e7d (shrR32Effect 0x105e7d 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[905]
    (.letOp (n := 908) (.exec 0x105e7d (fun s => s.RIP = 0x105e7d) (shrR32Effect 0x105e7d 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[905]
    (.letOp (n := 909) (.out 0x105e80 (xorR32R32Effect 0x105e80 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[907, 903]
    (.letOp (n := 910) (.exec 0x105e80 (fun s => s.RIP = 0x105e80) (xorR32R32Effect 0x105e80 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[907, 903]
    (.letOp (n := 911) (.out 0x105e82 (andR32Imm32Effect 0x105e82 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[909]
    (.letOp (n := 912) (.exec 0x105e82 (fun s => s.RIP = 0x105e82) (andR32Imm32Effect 0x105e82 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[909]
    (.letOp (n := 913) (.out 0x105e88 (xorR32R32Effect 0x105e88 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[903, 911]
    (.letOp (n := 914) (.exec 0x105e88 (fun s => s.RIP = 0x105e88) (xorR32R32Effect 0x105e88 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[903, 911]
    (.letOp (n := 915) (.out 0x105e8a (shlR32Effect 0x105e8a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[911]
    (.letOp (n := 916) (.exec 0x105e8a (fun s => s.RIP = 0x105e8a) (shlR32Effect 0x105e8a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[911]
    (.letOp (n := 917) (.out 0x105e8d (xorR32R32Effect 0x105e8d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[915, 913]
    (.letOp (n := 918) (.exec 0x105e8d (fun s => s.RIP = 0x105e8d) (xorR32R32Effect 0x105e8d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[915, 913]
    (.letOp (n := 919) (.out 0x105e8f (movR32R32Effect 0x105e8f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[917]
    (.letOp (n := 920) (.exec 0x105e8f (fun s => s.RIP = 0x105e8f) (movR32R32Effect 0x105e8f 2 0 1) (Reg.operands [.gpr 1] [])) #v[917]
    (.letOp (n := 921) (.out 0x105e91 (shrR32Effect 0x105e91 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[919]
    (.letOp (n := 922) (.exec 0x105e91 (fun s => s.RIP = 0x105e91) (shrR32Effect 0x105e91 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[919]
    (.letOp (n := 923) (.out 0x105e93 (xorR32R32Effect 0x105e93 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[921, 917]
    (.letOp (n := 924) (.exec 0x105e93 (fun s => s.RIP = 0x105e93) (xorR32R32Effect 0x105e93 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[921, 917]
    (.letOp (n := 925) (.out 0x105e95 (andEaxImm32Effect 0x105e95 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[923]
    (.letOp (n := 926) (.exec 0x105e95 (fun s => s.RIP = 0x105e95) (andEaxImm32Effect 0x105e95 0x5050) (Reg.operands [.gpr 0] [])) #v[923]
    (.letOp (n := 927) (.out 0x105e9a (xorR32R32Effect 0x105e9a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[917, 925]
    (.letOp (n := 928) (.exec 0x105e9a (fun s => s.RIP = 0x105e9a) (xorR32R32Effect 0x105e9a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[917, 925]
    (.letOp (n := 929) (.out 0x105e9c (addR32R32Effect 0x105e9c 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[925, 925]
    (.letOp (n := 930) (.exec 0x105e9c (fun s => s.RIP = 0x105e9c) (addR32R32Effect 0x105e9c 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[925, 925]
    (.letOp (n := 931) (.out 0x105e9e (xorR32R32Effect 0x105e9e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[929, 927]
    (.letOp (n := 932) (.exec 0x105e9e (fun s => s.RIP = 0x105e9e) (xorR32R32Effect 0x105e9e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[929, 927]
    (.letOp (n := 933) (.exec 0x105ea0 (StorePre 0x105ea0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6a)) s (0x105ea0 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ea0 5 0 (.sib 4 none 0 (.d8 0x6a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[931, 4]
    (.letOp (n := 934) (.out 0x105ea5 (movzxR32M16Effect 0x105ea5 5 0 (.sib 4 none 0 (.d8 0x6c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 935) (.exec 0x105ea5 (LoadPre 0x105ea5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6c)) s (0x105ea5 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ea5 5 0 (.sib 4 none 0 (.d8 0x6c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 936) (.out 0x105eaa (movR32R32Effect 0x105eaa 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[934]
    (.letOp (n := 937) (.exec 0x105eaa (fun s => s.RIP = 0x105eaa) (movR32R32Effect 0x105eaa 2 1 0) (Reg.operands [.gpr 0] [])) #v[934]
    (.letOp (n := 938) (.out 0x105eac (shrR32Effect 0x105eac 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[936]
    (.letOp (n := 939) (.exec 0x105eac (fun s => s.RIP = 0x105eac) (shrR32Effect 0x105eac 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[936]
    (b_l10593a_23))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_22 : List UInt8 :=
  [0x66, 0x89, 0x44, 0x24, 0x68, 0x0F, 0xB7, 0x44, 0x24, 0x6A, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8,
    0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66,
    0x89, 0x44, 0x24, 0x6A, 0x0F, 0xB7, 0x44, 0x24, 0x6C, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_23

theorem code_l10593a_22 : ∀ x ∈ codeRange 0x105e71 bytes_l10593a_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5e71 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_23

def b_l10593a_21 : Block Op Label signature Reg.count 863 :=
  .letOp (n := 863) (.out 0x105e37 (andEaxImm32Effect 0x105e37 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[861]
    (.letOp (n := 864) (.exec 0x105e37 (fun s => s.RIP = 0x105e37) (andEaxImm32Effect 0x105e37 0x5050) (Reg.operands [.gpr 0] [])) #v[861]
    (.letOp (n := 865) (.out 0x105e3c (xorR32R32Effect 0x105e3c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[855, 863]
    (.letOp (n := 866) (.exec 0x105e3c (fun s => s.RIP = 0x105e3c) (xorR32R32Effect 0x105e3c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[855, 863]
    (.letOp (n := 867) (.out 0x105e3e (addR32R32Effect 0x105e3e 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[863, 863]
    (.letOp (n := 868) (.exec 0x105e3e (fun s => s.RIP = 0x105e3e) (addR32R32Effect 0x105e3e 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[863, 863]
    (.letOp (n := 869) (.out 0x105e40 (xorR32R32Effect 0x105e40 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[867, 865]
    (.letOp (n := 870) (.exec 0x105e40 (fun s => s.RIP = 0x105e40) (xorR32R32Effect 0x105e40 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[867, 865]
    (.letOp (n := 871) (.exec 0x105e42 (StorePre 0x105e42 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x105e42 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e42 5 0 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[869, 4]
    (.letOp (n := 872) (.out 0x105e47 (movzxR32M16Effect 0x105e47 5 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 873) (.exec 0x105e47 (LoadPre 0x105e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x105e47 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e47 5 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 874) (.out 0x105e4c (movR32R32Effect 0x105e4c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[872]
    (.letOp (n := 875) (.exec 0x105e4c (fun s => s.RIP = 0x105e4c) (movR32R32Effect 0x105e4c 2 1 0) (Reg.operands [.gpr 0] [])) #v[872]
    (.letOp (n := 876) (.out 0x105e4e (shrR32Effect 0x105e4e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[874]
    (.letOp (n := 877) (.exec 0x105e4e (fun s => s.RIP = 0x105e4e) (shrR32Effect 0x105e4e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[874]
    (.letOp (n := 878) (.out 0x105e51 (xorR32R32Effect 0x105e51 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[876, 872]
    (.letOp (n := 879) (.exec 0x105e51 (fun s => s.RIP = 0x105e51) (xorR32R32Effect 0x105e51 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[876, 872]
    (.letOp (n := 880) (.out 0x105e53 (andR32Imm32Effect 0x105e53 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[878]
    (.letOp (n := 881) (.exec 0x105e53 (fun s => s.RIP = 0x105e53) (andR32Imm32Effect 0x105e53 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[878]
    (.letOp (n := 882) (.out 0x105e59 (xorR32R32Effect 0x105e59 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[872, 880]
    (.letOp (n := 883) (.exec 0x105e59 (fun s => s.RIP = 0x105e59) (xorR32R32Effect 0x105e59 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[872, 880]
    (.letOp (n := 884) (.out 0x105e5b (shlR32Effect 0x105e5b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[880]
    (.letOp (n := 885) (.exec 0x105e5b (fun s => s.RIP = 0x105e5b) (shlR32Effect 0x105e5b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[880]
    (.letOp (n := 886) (.out 0x105e5e (xorR32R32Effect 0x105e5e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[884, 882]
    (.letOp (n := 887) (.exec 0x105e5e (fun s => s.RIP = 0x105e5e) (xorR32R32Effect 0x105e5e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[884, 882]
    (.letOp (n := 888) (.out 0x105e60 (movR32R32Effect 0x105e60 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[886]
    (.letOp (n := 889) (.exec 0x105e60 (fun s => s.RIP = 0x105e60) (movR32R32Effect 0x105e60 2 0 1) (Reg.operands [.gpr 1] [])) #v[886]
    (.letOp (n := 890) (.out 0x105e62 (shrR32Effect 0x105e62 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[888]
    (.letOp (n := 891) (.exec 0x105e62 (fun s => s.RIP = 0x105e62) (shrR32Effect 0x105e62 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[888]
    (.letOp (n := 892) (.out 0x105e64 (xorR32R32Effect 0x105e64 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[890, 886]
    (.letOp (n := 893) (.exec 0x105e64 (fun s => s.RIP = 0x105e64) (xorR32R32Effect 0x105e64 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[890, 886]
    (.letOp (n := 894) (.out 0x105e66 (andEaxImm32Effect 0x105e66 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[892]
    (.letOp (n := 895) (.exec 0x105e66 (fun s => s.RIP = 0x105e66) (andEaxImm32Effect 0x105e66 0x5050) (Reg.operands [.gpr 0] [])) #v[892]
    (.letOp (n := 896) (.out 0x105e6b (xorR32R32Effect 0x105e6b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[886, 894]
    (.letOp (n := 897) (.exec 0x105e6b (fun s => s.RIP = 0x105e6b) (xorR32R32Effect 0x105e6b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[886, 894]
    (.letOp (n := 898) (.out 0x105e6d (addR32R32Effect 0x105e6d 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[894, 894]
    (.letOp (n := 899) (.exec 0x105e6d (fun s => s.RIP = 0x105e6d) (addR32R32Effect 0x105e6d 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[894, 894]
    (.letOp (n := 900) (.out 0x105e6f (xorR32R32Effect 0x105e6f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[898, 896]
    (.letOp (n := 901) (.exec 0x105e6f (fun s => s.RIP = 0x105e6f) (xorR32R32Effect 0x105e6f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[898, 896]
    (b_l10593a_22)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_21 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x66,
    0x0F, 0xB7, 0x44, 0x24, 0x68, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25,
    0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_22

theorem code_l10593a_21 : ∀ x ∈ codeRange 0x105e37 bytes_l10593a_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5e37 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_22

def b_l10593a_20 : Block Op Label signature Reg.count 824 :=
  .letOp (n := 824) (.out 0x105e00 (xorR32R32Effect 0x105e00 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[822, 820]
    (.letOp (n := 825) (.exec 0x105e00 (fun s => s.RIP = 0x105e00) (xorR32R32Effect 0x105e00 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[822, 820]
    (.letOp (n := 826) (.out 0x105e02 (movR32R32Effect 0x105e02 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[824]
    (.letOp (n := 827) (.exec 0x105e02 (fun s => s.RIP = 0x105e02) (movR32R32Effect 0x105e02 2 0 1) (Reg.operands [.gpr 1] [])) #v[824]
    (.letOp (n := 828) (.out 0x105e04 (shrR32Effect 0x105e04 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[826]
    (.letOp (n := 829) (.exec 0x105e04 (fun s => s.RIP = 0x105e04) (shrR32Effect 0x105e04 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[826]
    (.letOp (n := 830) (.out 0x105e06 (xorR32R32Effect 0x105e06 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[828, 824]
    (.letOp (n := 831) (.exec 0x105e06 (fun s => s.RIP = 0x105e06) (xorR32R32Effect 0x105e06 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[828, 824]
    (.letOp (n := 832) (.out 0x105e08 (andEaxImm32Effect 0x105e08 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[830]
    (.letOp (n := 833) (.exec 0x105e08 (fun s => s.RIP = 0x105e08) (andEaxImm32Effect 0x105e08 0x5050) (Reg.operands [.gpr 0] [])) #v[830]
    (.letOp (n := 834) (.out 0x105e0d (xorR32R32Effect 0x105e0d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[824, 832]
    (.letOp (n := 835) (.exec 0x105e0d (fun s => s.RIP = 0x105e0d) (xorR32R32Effect 0x105e0d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[824, 832]
    (.letOp (n := 836) (.out 0x105e0f (addR32R32Effect 0x105e0f 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[832, 832]
    (.letOp (n := 837) (.exec 0x105e0f (fun s => s.RIP = 0x105e0f) (addR32R32Effect 0x105e0f 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[832, 832]
    (.letOp (n := 838) (.out 0x105e11 (xorR32R32Effect 0x105e11 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[836, 834]
    (.letOp (n := 839) (.exec 0x105e11 (fun s => s.RIP = 0x105e11) (xorR32R32Effect 0x105e11 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[836, 834]
    (.letOp (n := 840) (.exec 0x105e13 (StorePre 0x105e13 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105e13 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105e13 5 0 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[838, 4]
    (.letOp (n := 841) (.out 0x105e18 (movzxR32M16Effect 0x105e18 5 0 (.sib 4 none 0 (.d8 0x66))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 842) (.exec 0x105e18 (LoadPre 0x105e18 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x66)) s (0x105e18 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105e18 5 0 (.sib 4 none 0 (.d8 0x66))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 843) (.out 0x105e1d (movR32R32Effect 0x105e1d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[841]
    (.letOp (n := 844) (.exec 0x105e1d (fun s => s.RIP = 0x105e1d) (movR32R32Effect 0x105e1d 2 1 0) (Reg.operands [.gpr 0] [])) #v[841]
    (.letOp (n := 845) (.out 0x105e1f (shrR32Effect 0x105e1f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[843]
    (.letOp (n := 846) (.exec 0x105e1f (fun s => s.RIP = 0x105e1f) (shrR32Effect 0x105e1f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[843]
    (.letOp (n := 847) (.out 0x105e22 (xorR32R32Effect 0x105e22 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[845, 841]
    (.letOp (n := 848) (.exec 0x105e22 (fun s => s.RIP = 0x105e22) (xorR32R32Effect 0x105e22 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[845, 841]
    (.letOp (n := 849) (.out 0x105e24 (andR32Imm32Effect 0x105e24 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[847]
    (.letOp (n := 850) (.exec 0x105e24 (fun s => s.RIP = 0x105e24) (andR32Imm32Effect 0x105e24 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[847]
    (.letOp (n := 851) (.out 0x105e2a (xorR32R32Effect 0x105e2a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[841, 849]
    (.letOp (n := 852) (.exec 0x105e2a (fun s => s.RIP = 0x105e2a) (xorR32R32Effect 0x105e2a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[841, 849]
    (.letOp (n := 853) (.out 0x105e2c (shlR32Effect 0x105e2c 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[849]
    (.letOp (n := 854) (.exec 0x105e2c (fun s => s.RIP = 0x105e2c) (shlR32Effect 0x105e2c 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[849]
    (.letOp (n := 855) (.out 0x105e2f (xorR32R32Effect 0x105e2f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[853, 851]
    (.letOp (n := 856) (.exec 0x105e2f (fun s => s.RIP = 0x105e2f) (xorR32R32Effect 0x105e2f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[853, 851]
    (.letOp (n := 857) (.out 0x105e31 (movR32R32Effect 0x105e31 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[855]
    (.letOp (n := 858) (.exec 0x105e31 (fun s => s.RIP = 0x105e31) (movR32R32Effect 0x105e31 2 0 1) (Reg.operands [.gpr 1] [])) #v[855]
    (.letOp (n := 859) (.out 0x105e33 (shrR32Effect 0x105e33 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[857]
    (.letOp (n := 860) (.exec 0x105e33 (fun s => s.RIP = 0x105e33) (shrR32Effect 0x105e33 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[857]
    (.letOp (n := 861) (.out 0x105e35 (xorR32R32Effect 0x105e35 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[859, 855]
    (.letOp (n := 862) (.exec 0x105e35 (fun s => s.RIP = 0x105e35) (xorR32R32Effect 0x105e35 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[859, 855]
    (b_l10593a_21)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_20 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x64, 0x0F, 0xB7, 0x44, 0x24, 0x66, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_21

theorem code_l10593a_20 : ∀ x ∈ codeRange 0x105e00 bytes_l10593a_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5e00 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_21

def b_l10593a_19 : Block Op Label signature Reg.count 785 :=
  .letOp (n := 785) (.out 0x105dc4 (xorR32R32Effect 0x105dc4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[783, 779]
    (.letOp (n := 786) (.exec 0x105dc4 (fun s => s.RIP = 0x105dc4) (xorR32R32Effect 0x105dc4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[783, 779]
    (.letOp (n := 787) (.out 0x105dc6 (andR32Imm32Effect 0x105dc6 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[785]
    (.letOp (n := 788) (.exec 0x105dc6 (fun s => s.RIP = 0x105dc6) (andR32Imm32Effect 0x105dc6 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[785]
    (.letOp (n := 789) (.out 0x105dcc (xorR32R32Effect 0x105dcc 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[779, 787]
    (.letOp (n := 790) (.exec 0x105dcc (fun s => s.RIP = 0x105dcc) (xorR32R32Effect 0x105dcc 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[779, 787]
    (.letOp (n := 791) (.out 0x105dce (shlR32Effect 0x105dce 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[787]
    (.letOp (n := 792) (.exec 0x105dce (fun s => s.RIP = 0x105dce) (shlR32Effect 0x105dce 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[787]
    (.letOp (n := 793) (.out 0x105dd1 (xorR32R32Effect 0x105dd1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[791, 789]
    (.letOp (n := 794) (.exec 0x105dd1 (fun s => s.RIP = 0x105dd1) (xorR32R32Effect 0x105dd1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[791, 789]
    (.letOp (n := 795) (.out 0x105dd3 (movR32R32Effect 0x105dd3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[793]
    (.letOp (n := 796) (.exec 0x105dd3 (fun s => s.RIP = 0x105dd3) (movR32R32Effect 0x105dd3 2 0 1) (Reg.operands [.gpr 1] [])) #v[793]
    (.letOp (n := 797) (.out 0x105dd5 (shrR32Effect 0x105dd5 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[795]
    (.letOp (n := 798) (.exec 0x105dd5 (fun s => s.RIP = 0x105dd5) (shrR32Effect 0x105dd5 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[795]
    (.letOp (n := 799) (.out 0x105dd7 (xorR32R32Effect 0x105dd7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[797, 793]
    (.letOp (n := 800) (.exec 0x105dd7 (fun s => s.RIP = 0x105dd7) (xorR32R32Effect 0x105dd7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[797, 793]
    (.letOp (n := 801) (.out 0x105dd9 (andEaxImm32Effect 0x105dd9 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[799]
    (.letOp (n := 802) (.exec 0x105dd9 (fun s => s.RIP = 0x105dd9) (andEaxImm32Effect 0x105dd9 0x5050) (Reg.operands [.gpr 0] [])) #v[799]
    (.letOp (n := 803) (.out 0x105dde (xorR32R32Effect 0x105dde 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[793, 801]
    (.letOp (n := 804) (.exec 0x105dde (fun s => s.RIP = 0x105dde) (xorR32R32Effect 0x105dde 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[793, 801]
    (.letOp (n := 805) (.out 0x105de0 (addR32R32Effect 0x105de0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[801, 801]
    (.letOp (n := 806) (.exec 0x105de0 (fun s => s.RIP = 0x105de0) (addR32R32Effect 0x105de0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[801, 801]
    (.letOp (n := 807) (.out 0x105de2 (xorR32R32Effect 0x105de2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[805, 803]
    (.letOp (n := 808) (.exec 0x105de2 (fun s => s.RIP = 0x105de2) (xorR32R32Effect 0x105de2 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[805, 803]
    (.letOp (n := 809) (.exec 0x105de4 (StorePre 0x105de4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x105de4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105de4 5 0 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[807, 4]
    (.letOp (n := 810) (.out 0x105de9 (movzxR32M16Effect 0x105de9 5 0 (.sib 4 none 0 (.d8 0x64))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 811) (.exec 0x105de9 (LoadPre 0x105de9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x64)) s (0x105de9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105de9 5 0 (.sib 4 none 0 (.d8 0x64))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 812) (.out 0x105dee (movR32R32Effect 0x105dee 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[810]
    (.letOp (n := 813) (.exec 0x105dee (fun s => s.RIP = 0x105dee) (movR32R32Effect 0x105dee 2 1 0) (Reg.operands [.gpr 0] [])) #v[810]
    (.letOp (n := 814) (.out 0x105df0 (shrR32Effect 0x105df0 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[812]
    (.letOp (n := 815) (.exec 0x105df0 (fun s => s.RIP = 0x105df0) (shrR32Effect 0x105df0 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[812]
    (.letOp (n := 816) (.out 0x105df3 (xorR32R32Effect 0x105df3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[814, 810]
    (.letOp (n := 817) (.exec 0x105df3 (fun s => s.RIP = 0x105df3) (xorR32R32Effect 0x105df3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[814, 810]
    (.letOp (n := 818) (.out 0x105df5 (andR32Imm32Effect 0x105df5 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[816]
    (.letOp (n := 819) (.exec 0x105df5 (fun s => s.RIP = 0x105df5) (andR32Imm32Effect 0x105df5 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[816]
    (.letOp (n := 820) (.out 0x105dfb (xorR32R32Effect 0x105dfb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[810, 818]
    (.letOp (n := 821) (.exec 0x105dfb (fun s => s.RIP = 0x105dfb) (xorR32R32Effect 0x105dfb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[810, 818]
    (.letOp (n := 822) (.out 0x105dfd (shlR32Effect 0x105dfd 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[818]
    (.letOp (n := 823) (.exec 0x105dfd (fun s => s.RIP = 0x105dfd) (shlR32Effect 0x105dfd 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[818]
    (b_l10593a_20)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_19 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x62, 0x0F, 0xB7, 0x44, 0x24, 0x64, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02] ++ bytes_l10593a_20

theorem code_l10593a_19 : ∀ x ∈ codeRange 0x105dc4 bytes_l10593a_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5dc4 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_20

def b_l10593a_18 : Block Op Label signature Reg.count 747 :=
  .letOp (n := 747) (.exec 0x105d86 (StorePre 0x105d86 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x105d86 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105d86 5 0 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[745, 4]
    (.letOp (n := 748) (.out 0x105d8b (movzxR32M16Effect 0x105d8b 5 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 749) (.exec 0x105d8b (LoadPre 0x105d8b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105d8b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d8b 5 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 750) (.out 0x105d90 (movR32R32Effect 0x105d90 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[748]
    (.letOp (n := 751) (.exec 0x105d90 (fun s => s.RIP = 0x105d90) (movR32R32Effect 0x105d90 2 1 0) (Reg.operands [.gpr 0] [])) #v[748]
    (.letOp (n := 752) (.out 0x105d92 (shrR32Effect 0x105d92 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[750]
    (.letOp (n := 753) (.exec 0x105d92 (fun s => s.RIP = 0x105d92) (shrR32Effect 0x105d92 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[750]
    (.letOp (n := 754) (.out 0x105d95 (xorR32R32Effect 0x105d95 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[752, 748]
    (.letOp (n := 755) (.exec 0x105d95 (fun s => s.RIP = 0x105d95) (xorR32R32Effect 0x105d95 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[752, 748]
    (.letOp (n := 756) (.out 0x105d97 (andR32Imm32Effect 0x105d97 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[754]
    (.letOp (n := 757) (.exec 0x105d97 (fun s => s.RIP = 0x105d97) (andR32Imm32Effect 0x105d97 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[754]
    (.letOp (n := 758) (.out 0x105d9d (xorR32R32Effect 0x105d9d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[748, 756]
    (.letOp (n := 759) (.exec 0x105d9d (fun s => s.RIP = 0x105d9d) (xorR32R32Effect 0x105d9d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[748, 756]
    (.letOp (n := 760) (.out 0x105d9f (shlR32Effect 0x105d9f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[756]
    (.letOp (n := 761) (.exec 0x105d9f (fun s => s.RIP = 0x105d9f) (shlR32Effect 0x105d9f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[756]
    (.letOp (n := 762) (.out 0x105da2 (xorR32R32Effect 0x105da2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[760, 758]
    (.letOp (n := 763) (.exec 0x105da2 (fun s => s.RIP = 0x105da2) (xorR32R32Effect 0x105da2 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[760, 758]
    (.letOp (n := 764) (.out 0x105da4 (movR32R32Effect 0x105da4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[762]
    (.letOp (n := 765) (.exec 0x105da4 (fun s => s.RIP = 0x105da4) (movR32R32Effect 0x105da4 2 0 1) (Reg.operands [.gpr 1] [])) #v[762]
    (.letOp (n := 766) (.out 0x105da6 (shrR32Effect 0x105da6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[764]
    (.letOp (n := 767) (.exec 0x105da6 (fun s => s.RIP = 0x105da6) (shrR32Effect 0x105da6 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[764]
    (.letOp (n := 768) (.out 0x105da8 (xorR32R32Effect 0x105da8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[766, 762]
    (.letOp (n := 769) (.exec 0x105da8 (fun s => s.RIP = 0x105da8) (xorR32R32Effect 0x105da8 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[766, 762]
    (.letOp (n := 770) (.out 0x105daa (andEaxImm32Effect 0x105daa 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[768]
    (.letOp (n := 771) (.exec 0x105daa (fun s => s.RIP = 0x105daa) (andEaxImm32Effect 0x105daa 0x5050) (Reg.operands [.gpr 0] [])) #v[768]
    (.letOp (n := 772) (.out 0x105daf (xorR32R32Effect 0x105daf 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[762, 770]
    (.letOp (n := 773) (.exec 0x105daf (fun s => s.RIP = 0x105daf) (xorR32R32Effect 0x105daf 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[762, 770]
    (.letOp (n := 774) (.out 0x105db1 (addR32R32Effect 0x105db1 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[770, 770]
    (.letOp (n := 775) (.exec 0x105db1 (fun s => s.RIP = 0x105db1) (addR32R32Effect 0x105db1 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[770, 770]
    (.letOp (n := 776) (.out 0x105db3 (xorR32R32Effect 0x105db3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[774, 772]
    (.letOp (n := 777) (.exec 0x105db3 (fun s => s.RIP = 0x105db3) (xorR32R32Effect 0x105db3 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[774, 772]
    (.letOp (n := 778) (.exec 0x105db5 (StorePre 0x105db5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x105db5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105db5 5 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[776, 4]
    (.letOp (n := 779) (.out 0x105dba (movzxR32M16Effect 0x105dba 5 0 (.sib 4 none 0 (.d8 0x62))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 780) (.exec 0x105dba (LoadPre 0x105dba (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x62)) s (0x105dba + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105dba 5 0 (.sib 4 none 0 (.d8 0x62))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 781) (.out 0x105dbf (movR32R32Effect 0x105dbf 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[779]
    (.letOp (n := 782) (.exec 0x105dbf (fun s => s.RIP = 0x105dbf) (movR32R32Effect 0x105dbf 2 1 0) (Reg.operands [.gpr 0] [])) #v[779]
    (.letOp (n := 783) (.out 0x105dc1 (shrR32Effect 0x105dc1 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[781]
    (.letOp (n := 784) (.exec 0x105dc1 (fun s => s.RIP = 0x105dc1) (shrR32Effect 0x105dc1 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[781]
    (b_l10593a_19))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_18 : List UInt8 :=
  [0x66, 0x89, 0x44, 0x24, 0x5E, 0x0F, 0xB7, 0x44, 0x24, 0x60, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8,
    0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66,
    0x89, 0x44, 0x24, 0x60, 0x0F, 0xB7, 0x44, 0x24, 0x62, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_19

theorem code_l10593a_18 : ∀ x ∈ codeRange 0x105d86 bytes_l10593a_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5d86 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_19

def b_l10593a_17 : Block Op Label signature Reg.count 708 :=
  .letOp (n := 708) (.out 0x105d4a (andEaxImm32Effect 0x105d4a 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[706]
    (.letOp (n := 709) (.exec 0x105d4a (fun s => s.RIP = 0x105d4a) (andEaxImm32Effect 0x105d4a 0x5050) (Reg.operands [.gpr 0] [])) #v[706]
    (.letOp (n := 710) (.out 0x105d4f (xorR32R32Effect 0x105d4f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[700, 708]
    (.letOp (n := 711) (.exec 0x105d4f (fun s => s.RIP = 0x105d4f) (xorR32R32Effect 0x105d4f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[700, 708]
    (.letOp (n := 712) (.out 0x105d51 (addR32R32Effect 0x105d51 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[708, 708]
    (.letOp (n := 713) (.exec 0x105d51 (fun s => s.RIP = 0x105d51) (addR32R32Effect 0x105d51 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[708, 708]
    (.letOp (n := 714) (.out 0x105d53 (xorR32R32Effect 0x105d53 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[712, 710]
    (.letOp (n := 715) (.exec 0x105d53 (fun s => s.RIP = 0x105d53) (xorR32R32Effect 0x105d53 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[712, 710]
    (.letOp (n := 716) (.exec 0x105d55 (StorePre 0x105d55 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x104)) s (0x105d55 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105d55 0 (.sib 4 none 0 (.d32 0x104))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[714, 4]
    (.letOp (n := 717) (.out 0x105d5c (movzxR32M16Effect 0x105d5c 5 0 (.sib 4 none 0 (.d8 0x5e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 718) (.exec 0x105d5c (LoadPre 0x105d5c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5e)) s (0x105d5c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d5c 5 0 (.sib 4 none 0 (.d8 0x5e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 719) (.out 0x105d61 (movR32R32Effect 0x105d61 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[717]
    (.letOp (n := 720) (.exec 0x105d61 (fun s => s.RIP = 0x105d61) (movR32R32Effect 0x105d61 2 1 0) (Reg.operands [.gpr 0] [])) #v[717]
    (.letOp (n := 721) (.out 0x105d63 (shrR32Effect 0x105d63 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[719]
    (.letOp (n := 722) (.exec 0x105d63 (fun s => s.RIP = 0x105d63) (shrR32Effect 0x105d63 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[719]
    (.letOp (n := 723) (.out 0x105d66 (xorR32R32Effect 0x105d66 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[721, 717]
    (.letOp (n := 724) (.exec 0x105d66 (fun s => s.RIP = 0x105d66) (xorR32R32Effect 0x105d66 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[721, 717]
    (.letOp (n := 725) (.out 0x105d68 (andR32Imm32Effect 0x105d68 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[723]
    (.letOp (n := 726) (.exec 0x105d68 (fun s => s.RIP = 0x105d68) (andR32Imm32Effect 0x105d68 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[723]
    (.letOp (n := 727) (.out 0x105d6e (xorR32R32Effect 0x105d6e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[717, 725]
    (.letOp (n := 728) (.exec 0x105d6e (fun s => s.RIP = 0x105d6e) (xorR32R32Effect 0x105d6e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[717, 725]
    (.letOp (n := 729) (.out 0x105d70 (shlR32Effect 0x105d70 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[725]
    (.letOp (n := 730) (.exec 0x105d70 (fun s => s.RIP = 0x105d70) (shlR32Effect 0x105d70 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[725]
    (.letOp (n := 731) (.out 0x105d73 (xorR32R32Effect 0x105d73 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[729, 727]
    (.letOp (n := 732) (.exec 0x105d73 (fun s => s.RIP = 0x105d73) (xorR32R32Effect 0x105d73 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[729, 727]
    (.letOp (n := 733) (.out 0x105d75 (movR32R32Effect 0x105d75 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[731]
    (.letOp (n := 734) (.exec 0x105d75 (fun s => s.RIP = 0x105d75) (movR32R32Effect 0x105d75 2 0 1) (Reg.operands [.gpr 1] [])) #v[731]
    (.letOp (n := 735) (.out 0x105d77 (shrR32Effect 0x105d77 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[733]
    (.letOp (n := 736) (.exec 0x105d77 (fun s => s.RIP = 0x105d77) (shrR32Effect 0x105d77 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[733]
    (.letOp (n := 737) (.out 0x105d79 (xorR32R32Effect 0x105d79 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[735, 731]
    (.letOp (n := 738) (.exec 0x105d79 (fun s => s.RIP = 0x105d79) (xorR32R32Effect 0x105d79 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[735, 731]
    (.letOp (n := 739) (.out 0x105d7b (andEaxImm32Effect 0x105d7b 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[737]
    (.letOp (n := 740) (.exec 0x105d7b (fun s => s.RIP = 0x105d7b) (andEaxImm32Effect 0x105d7b 0x5050) (Reg.operands [.gpr 0] [])) #v[737]
    (.letOp (n := 741) (.out 0x105d80 (xorR32R32Effect 0x105d80 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[731, 739]
    (.letOp (n := 742) (.exec 0x105d80 (fun s => s.RIP = 0x105d80) (xorR32R32Effect 0x105d80 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[731, 739]
    (.letOp (n := 743) (.out 0x105d82 (addR32R32Effect 0x105d82 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[739, 739]
    (.letOp (n := 744) (.exec 0x105d82 (fun s => s.RIP = 0x105d82) (addR32R32Effect 0x105d82 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[739, 739]
    (.letOp (n := 745) (.out 0x105d84 (xorR32R32Effect 0x105d84 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[743, 741]
    (.letOp (n := 746) (.exec 0x105d84 (fun s => s.RIP = 0x105d84) (xorR32R32Effect 0x105d84 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[743, 741]
    (b_l10593a_18)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_17 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x89, 0x84, 0x24, 0x04, 0x01,
    0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x5E, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1,
    0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31,
    0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_18

theorem code_l10593a_17 : ∀ x ∈ codeRange 0x105d4a bytes_l10593a_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5d4a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_18

def b_l10593a_16 : Block Op Label signature Reg.count 669 :=
  .letOp (n := 669) (.out 0x105d13 (xorR32R32Effect 0x105d13 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[667, 665]
    (.letOp (n := 670) (.exec 0x105d13 (fun s => s.RIP = 0x105d13) (xorR32R32Effect 0x105d13 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[667, 665]
    (.letOp (n := 671) (.out 0x105d15 (movR32R32Effect 0x105d15 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[669]
    (.letOp (n := 672) (.exec 0x105d15 (fun s => s.RIP = 0x105d15) (movR32R32Effect 0x105d15 2 0 1) (Reg.operands [.gpr 1] [])) #v[669]
    (.letOp (n := 673) (.out 0x105d17 (shrR32Effect 0x105d17 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[671]
    (.letOp (n := 674) (.exec 0x105d17 (fun s => s.RIP = 0x105d17) (shrR32Effect 0x105d17 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[671]
    (.letOp (n := 675) (.out 0x105d19 (xorR32R32Effect 0x105d19 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[673, 669]
    (.letOp (n := 676) (.exec 0x105d19 (fun s => s.RIP = 0x105d19) (xorR32R32Effect 0x105d19 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[673, 669]
    (.letOp (n := 677) (.out 0x105d1b (andEaxImm32Effect 0x105d1b 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[675]
    (.letOp (n := 678) (.exec 0x105d1b (fun s => s.RIP = 0x105d1b) (andEaxImm32Effect 0x105d1b 0x5050) (Reg.operands [.gpr 0] [])) #v[675]
    (.letOp (n := 679) (.out 0x105d20 (xorR32R32Effect 0x105d20 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[669, 677]
    (.letOp (n := 680) (.exec 0x105d20 (fun s => s.RIP = 0x105d20) (xorR32R32Effect 0x105d20 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[669, 677]
    (.letOp (n := 681) (.out 0x105d22 (addR32R32Effect 0x105d22 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[677, 677]
    (.letOp (n := 682) (.exec 0x105d22 (fun s => s.RIP = 0x105d22) (addR32R32Effect 0x105d22 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[677, 677]
    (.letOp (n := 683) (.out 0x105d24 (xorR32R32Effect 0x105d24 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[681, 679]
    (.letOp (n := 684) (.exec 0x105d24 (fun s => s.RIP = 0x105d24) (xorR32R32Effect 0x105d24 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[681, 679]
    (.letOp (n := 685) (.exec 0x105d26 (StorePre 0x105d26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x105d26 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105d26 5 0 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[683, 4]
    (.letOp (n := 686) (.out 0x105d2b (movzxR32M16Effect 0x105d2b 5 0 (.sib 4 none 0 (.d8 0x5c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 687) (.exec 0x105d2b (LoadPre 0x105d2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5c)) s (0x105d2b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105d2b 5 0 (.sib 4 none 0 (.d8 0x5c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 688) (.out 0x105d30 (movR32R32Effect 0x105d30 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[686]
    (.letOp (n := 689) (.exec 0x105d30 (fun s => s.RIP = 0x105d30) (movR32R32Effect 0x105d30 2 1 0) (Reg.operands [.gpr 0] [])) #v[686]
    (.letOp (n := 690) (.out 0x105d32 (shrR32Effect 0x105d32 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[688]
    (.letOp (n := 691) (.exec 0x105d32 (fun s => s.RIP = 0x105d32) (shrR32Effect 0x105d32 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[688]
    (.letOp (n := 692) (.out 0x105d35 (xorR32R32Effect 0x105d35 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[690, 686]
    (.letOp (n := 693) (.exec 0x105d35 (fun s => s.RIP = 0x105d35) (xorR32R32Effect 0x105d35 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[690, 686]
    (.letOp (n := 694) (.out 0x105d37 (andR32Imm32Effect 0x105d37 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[692]
    (.letOp (n := 695) (.exec 0x105d37 (fun s => s.RIP = 0x105d37) (andR32Imm32Effect 0x105d37 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[692]
    (.letOp (n := 696) (.out 0x105d3d (xorR32R32Effect 0x105d3d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[686, 694]
    (.letOp (n := 697) (.exec 0x105d3d (fun s => s.RIP = 0x105d3d) (xorR32R32Effect 0x105d3d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[686, 694]
    (.letOp (n := 698) (.out 0x105d3f (shlR32Effect 0x105d3f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[694]
    (.letOp (n := 699) (.exec 0x105d3f (fun s => s.RIP = 0x105d3f) (shlR32Effect 0x105d3f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[694]
    (.letOp (n := 700) (.out 0x105d42 (xorR32R32Effect 0x105d42 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[698, 696]
    (.letOp (n := 701) (.exec 0x105d42 (fun s => s.RIP = 0x105d42) (xorR32R32Effect 0x105d42 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[698, 696]
    (.letOp (n := 702) (.out 0x105d44 (movR32R32Effect 0x105d44 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[700]
    (.letOp (n := 703) (.exec 0x105d44 (fun s => s.RIP = 0x105d44) (movR32R32Effect 0x105d44 2 0 1) (Reg.operands [.gpr 1] [])) #v[700]
    (.letOp (n := 704) (.out 0x105d46 (shrR32Effect 0x105d46 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[702]
    (.letOp (n := 705) (.exec 0x105d46 (fun s => s.RIP = 0x105d46) (shrR32Effect 0x105d46 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[702]
    (.letOp (n := 706) (.out 0x105d48 (xorR32R32Effect 0x105d48 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[704, 700]
    (.letOp (n := 707) (.exec 0x105d48 (fun s => s.RIP = 0x105d48) (xorR32R32Effect 0x105d48 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[704, 700]
    (b_l10593a_17)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_16 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x4A, 0x0F, 0xB7, 0x44, 0x24, 0x5C, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_17

theorem code_l10593a_16 : ∀ x ∈ codeRange 0x105d13 bytes_l10593a_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5d13 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_17

def b_l10593a_15 : Block Op Label signature Reg.count 630 :=
  .letOp (n := 630) (.out 0x105cd7 (xorR32R32Effect 0x105cd7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[628, 624]
    (.letOp (n := 631) (.exec 0x105cd7 (fun s => s.RIP = 0x105cd7) (xorR32R32Effect 0x105cd7 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[628, 624]
    (.letOp (n := 632) (.out 0x105cd9 (andR32Imm32Effect 0x105cd9 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[630]
    (.letOp (n := 633) (.exec 0x105cd9 (fun s => s.RIP = 0x105cd9) (andR32Imm32Effect 0x105cd9 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[630]
    (.letOp (n := 634) (.out 0x105cdf (xorR32R32Effect 0x105cdf 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[624, 632]
    (.letOp (n := 635) (.exec 0x105cdf (fun s => s.RIP = 0x105cdf) (xorR32R32Effect 0x105cdf 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[624, 632]
    (.letOp (n := 636) (.out 0x105ce1 (shlR32Effect 0x105ce1 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[632]
    (.letOp (n := 637) (.exec 0x105ce1 (fun s => s.RIP = 0x105ce1) (shlR32Effect 0x105ce1 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[632]
    (.letOp (n := 638) (.out 0x105ce4 (xorR32R32Effect 0x105ce4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[636, 634]
    (.letOp (n := 639) (.exec 0x105ce4 (fun s => s.RIP = 0x105ce4) (xorR32R32Effect 0x105ce4 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[636, 634]
    (.letOp (n := 640) (.out 0x105ce6 (movR32R32Effect 0x105ce6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[638]
    (.letOp (n := 641) (.exec 0x105ce6 (fun s => s.RIP = 0x105ce6) (movR32R32Effect 0x105ce6 2 0 1) (Reg.operands [.gpr 1] [])) #v[638]
    (.letOp (n := 642) (.out 0x105ce8 (shrR32Effect 0x105ce8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[640]
    (.letOp (n := 643) (.exec 0x105ce8 (fun s => s.RIP = 0x105ce8) (shrR32Effect 0x105ce8 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[640]
    (.letOp (n := 644) (.out 0x105cea (xorR32R32Effect 0x105cea 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[642, 638]
    (.letOp (n := 645) (.exec 0x105cea (fun s => s.RIP = 0x105cea) (xorR32R32Effect 0x105cea 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[642, 638]
    (.letOp (n := 646) (.out 0x105cec (andEaxImm32Effect 0x105cec 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[644]
    (.letOp (n := 647) (.exec 0x105cec (fun s => s.RIP = 0x105cec) (andEaxImm32Effect 0x105cec 0x5050) (Reg.operands [.gpr 0] [])) #v[644]
    (.letOp (n := 648) (.out 0x105cf1 (xorR32R32Effect 0x105cf1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[638, 646]
    (.letOp (n := 649) (.exec 0x105cf1 (fun s => s.RIP = 0x105cf1) (xorR32R32Effect 0x105cf1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[638, 646]
    (.letOp (n := 650) (.out 0x105cf3 (addR32R32Effect 0x105cf3 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[646, 646]
    (.letOp (n := 651) (.exec 0x105cf3 (fun s => s.RIP = 0x105cf3) (addR32R32Effect 0x105cf3 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[646, 646]
    (.letOp (n := 652) (.out 0x105cf5 (xorR32R32Effect 0x105cf5 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[650, 648]
    (.letOp (n := 653) (.exec 0x105cf5 (fun s => s.RIP = 0x105cf5) (xorR32R32Effect 0x105cf5 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[650, 648]
    (.letOp (n := 654) (.exec 0x105cf7 (StorePre 0x105cf7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105cf7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105cf7 5 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[652, 4]
    (.letOp (n := 655) (.out 0x105cfc (movzxR32M16Effect 0x105cfc 5 0 (.sib 4 none 0 (.d8 0x4a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 656) (.exec 0x105cfc (LoadPre 0x105cfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4a)) s (0x105cfc + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105cfc 5 0 (.sib 4 none 0 (.d8 0x4a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 657) (.out 0x105d01 (movR32R32Effect 0x105d01 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[655]
    (.letOp (n := 658) (.exec 0x105d01 (fun s => s.RIP = 0x105d01) (movR32R32Effect 0x105d01 2 1 0) (Reg.operands [.gpr 0] [])) #v[655]
    (.letOp (n := 659) (.out 0x105d03 (shrR32Effect 0x105d03 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[657]
    (.letOp (n := 660) (.exec 0x105d03 (fun s => s.RIP = 0x105d03) (shrR32Effect 0x105d03 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[657]
    (.letOp (n := 661) (.out 0x105d06 (xorR32R32Effect 0x105d06 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[659, 655]
    (.letOp (n := 662) (.exec 0x105d06 (fun s => s.RIP = 0x105d06) (xorR32R32Effect 0x105d06 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[659, 655]
    (.letOp (n := 663) (.out 0x105d08 (andR32Imm32Effect 0x105d08 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[661]
    (.letOp (n := 664) (.exec 0x105d08 (fun s => s.RIP = 0x105d08) (andR32Imm32Effect 0x105d08 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[661]
    (.letOp (n := 665) (.out 0x105d0e (xorR32R32Effect 0x105d0e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[655, 663]
    (.letOp (n := 666) (.exec 0x105d0e (fun s => s.RIP = 0x105d0e) (xorR32R32Effect 0x105d0e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[655, 663]
    (.letOp (n := 667) (.out 0x105d10 (shlR32Effect 0x105d10 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[663]
    (.letOp (n := 668) (.exec 0x105d10 (fun s => s.RIP = 0x105d10) (shlR32Effect 0x105d10 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[663]
    (b_l10593a_16)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_15 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x48, 0x0F, 0xB7, 0x44, 0x24, 0x4A, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02] ++ bytes_l10593a_16

theorem code_l10593a_15 : ∀ x ∈ codeRange 0x105cd7 bytes_l10593a_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5cd7 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_16

def b_l10593a_14 : Block Op Label signature Reg.count 592 :=
  .letOp (n := 592) (.exec 0x105c99 (StorePre 0x105c99 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x105c99 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c99 5 0 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[590, 4]
    (.letOp (n := 593) (.out 0x105c9e (movzxR32M16Effect 0x105c9e 5 0 (.sib 4 none 0 (.d8 0x46))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 594) (.exec 0x105c9e (LoadPre 0x105c9e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x105c9e + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c9e 5 0 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 595) (.out 0x105ca3 (movR32R32Effect 0x105ca3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[593]
    (.letOp (n := 596) (.exec 0x105ca3 (fun s => s.RIP = 0x105ca3) (movR32R32Effect 0x105ca3 2 1 0) (Reg.operands [.gpr 0] [])) #v[593]
    (.letOp (n := 597) (.out 0x105ca5 (shrR32Effect 0x105ca5 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[595]
    (.letOp (n := 598) (.exec 0x105ca5 (fun s => s.RIP = 0x105ca5) (shrR32Effect 0x105ca5 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[595]
    (.letOp (n := 599) (.out 0x105ca8 (xorR32R32Effect 0x105ca8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[597, 593]
    (.letOp (n := 600) (.exec 0x105ca8 (fun s => s.RIP = 0x105ca8) (xorR32R32Effect 0x105ca8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[597, 593]
    (.letOp (n := 601) (.out 0x105caa (andR32Imm32Effect 0x105caa 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[599]
    (.letOp (n := 602) (.exec 0x105caa (fun s => s.RIP = 0x105caa) (andR32Imm32Effect 0x105caa 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[599]
    (.letOp (n := 603) (.out 0x105cb0 (xorR32R32Effect 0x105cb0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[593, 601]
    (.letOp (n := 604) (.exec 0x105cb0 (fun s => s.RIP = 0x105cb0) (xorR32R32Effect 0x105cb0 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[593, 601]
    (.letOp (n := 605) (.out 0x105cb2 (shlR32Effect 0x105cb2 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[601]
    (.letOp (n := 606) (.exec 0x105cb2 (fun s => s.RIP = 0x105cb2) (shlR32Effect 0x105cb2 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[601]
    (.letOp (n := 607) (.out 0x105cb5 (xorR32R32Effect 0x105cb5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[605, 603]
    (.letOp (n := 608) (.exec 0x105cb5 (fun s => s.RIP = 0x105cb5) (xorR32R32Effect 0x105cb5 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[605, 603]
    (.letOp (n := 609) (.out 0x105cb7 (movR32R32Effect 0x105cb7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[607]
    (.letOp (n := 610) (.exec 0x105cb7 (fun s => s.RIP = 0x105cb7) (movR32R32Effect 0x105cb7 2 0 1) (Reg.operands [.gpr 1] [])) #v[607]
    (.letOp (n := 611) (.out 0x105cb9 (shrR32Effect 0x105cb9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[609]
    (.letOp (n := 612) (.exec 0x105cb9 (fun s => s.RIP = 0x105cb9) (shrR32Effect 0x105cb9 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[609]
    (.letOp (n := 613) (.out 0x105cbb (xorR32R32Effect 0x105cbb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[611, 607]
    (.letOp (n := 614) (.exec 0x105cbb (fun s => s.RIP = 0x105cbb) (xorR32R32Effect 0x105cbb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[611, 607]
    (.letOp (n := 615) (.out 0x105cbd (andEaxImm32Effect 0x105cbd 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[613]
    (.letOp (n := 616) (.exec 0x105cbd (fun s => s.RIP = 0x105cbd) (andEaxImm32Effect 0x105cbd 0x5050) (Reg.operands [.gpr 0] [])) #v[613]
    (.letOp (n := 617) (.out 0x105cc2 (xorR32R32Effect 0x105cc2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[607, 615]
    (.letOp (n := 618) (.exec 0x105cc2 (fun s => s.RIP = 0x105cc2) (xorR32R32Effect 0x105cc2 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[607, 615]
    (.letOp (n := 619) (.out 0x105cc4 (addR32R32Effect 0x105cc4 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[615, 615]
    (.letOp (n := 620) (.exec 0x105cc4 (fun s => s.RIP = 0x105cc4) (addR32R32Effect 0x105cc4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[615, 615]
    (.letOp (n := 621) (.out 0x105cc6 (xorR32R32Effect 0x105cc6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[619, 617]
    (.letOp (n := 622) (.exec 0x105cc6 (fun s => s.RIP = 0x105cc6) (xorR32R32Effect 0x105cc6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[619, 617]
    (.letOp (n := 623) (.exec 0x105cc8 (StorePre 0x105cc8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x46)) s (0x105cc8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105cc8 5 0 (.sib 4 none 0 (.d8 0x46))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[621, 4]
    (.letOp (n := 624) (.out 0x105ccd (movzxR32M16Effect 0x105ccd 5 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 625) (.exec 0x105ccd (LoadPre 0x105ccd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x105ccd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ccd 5 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 626) (.out 0x105cd2 (movR32R32Effect 0x105cd2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[624]
    (.letOp (n := 627) (.exec 0x105cd2 (fun s => s.RIP = 0x105cd2) (movR32R32Effect 0x105cd2 2 1 0) (Reg.operands [.gpr 0] [])) #v[624]
    (.letOp (n := 628) (.out 0x105cd4 (shrR32Effect 0x105cd4 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[626]
    (.letOp (n := 629) (.exec 0x105cd4 (fun s => s.RIP = 0x105cd4) (shrR32Effect 0x105cd4 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[626]
    (b_l10593a_15))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_14 : List UInt8 :=
  [0x66, 0x89, 0x44, 0x24, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x46, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8,
    0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66,
    0x89, 0x44, 0x24, 0x46, 0x0F, 0xB7, 0x44, 0x24, 0x48, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_15

theorem code_l10593a_14 : ∀ x ∈ codeRange 0x105c99 bytes_l10593a_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5c99 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_15

def b_l10593a_13 : Block Op Label signature Reg.count 553 :=
  .letOp (n := 553) (.out 0x105c5f (andEaxImm32Effect 0x105c5f 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[551]
    (.letOp (n := 554) (.exec 0x105c5f (fun s => s.RIP = 0x105c5f) (andEaxImm32Effect 0x105c5f 0x5050) (Reg.operands [.gpr 0] [])) #v[551]
    (.letOp (n := 555) (.out 0x105c64 (xorR32R32Effect 0x105c64 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[545, 553]
    (.letOp (n := 556) (.exec 0x105c64 (fun s => s.RIP = 0x105c64) (xorR32R32Effect 0x105c64 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[545, 553]
    (.letOp (n := 557) (.out 0x105c66 (addR32R32Effect 0x105c66 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[553, 553]
    (.letOp (n := 558) (.exec 0x105c66 (fun s => s.RIP = 0x105c66) (addR32R32Effect 0x105c66 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[553, 553]
    (.letOp (n := 559) (.out 0x105c68 (xorR32R32Effect 0x105c68 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[557, 555]
    (.letOp (n := 560) (.exec 0x105c68 (fun s => s.RIP = 0x105c68) (xorR32R32Effect 0x105c68 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[557, 555]
    (.letOp (n := 561) (.exec 0x105c6a (StorePre 0x105c6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x105c6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c6a 5 0 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[559, 4]
    (.letOp (n := 562) (.out 0x105c6f (movzxR32M16Effect 0x105c6f 5 0 (.sib 4 none 0 (.d8 0x44))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 563) (.exec 0x105c6f (LoadPre 0x105c6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x44)) s (0x105c6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c6f 5 0 (.sib 4 none 0 (.d8 0x44))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 564) (.out 0x105c74 (movR32R32Effect 0x105c74 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[562]
    (.letOp (n := 565) (.exec 0x105c74 (fun s => s.RIP = 0x105c74) (movR32R32Effect 0x105c74 2 1 0) (Reg.operands [.gpr 0] [])) #v[562]
    (.letOp (n := 566) (.out 0x105c76 (shrR32Effect 0x105c76 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[564]
    (.letOp (n := 567) (.exec 0x105c76 (fun s => s.RIP = 0x105c76) (shrR32Effect 0x105c76 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[564]
    (.letOp (n := 568) (.out 0x105c79 (xorR32R32Effect 0x105c79 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[566, 562]
    (.letOp (n := 569) (.exec 0x105c79 (fun s => s.RIP = 0x105c79) (xorR32R32Effect 0x105c79 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[566, 562]
    (.letOp (n := 570) (.out 0x105c7b (andR32Imm32Effect 0x105c7b 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[568]
    (.letOp (n := 571) (.exec 0x105c7b (fun s => s.RIP = 0x105c7b) (andR32Imm32Effect 0x105c7b 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[568]
    (.letOp (n := 572) (.out 0x105c81 (xorR32R32Effect 0x105c81 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[562, 570]
    (.letOp (n := 573) (.exec 0x105c81 (fun s => s.RIP = 0x105c81) (xorR32R32Effect 0x105c81 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[562, 570]
    (.letOp (n := 574) (.out 0x105c83 (shlR32Effect 0x105c83 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[570]
    (.letOp (n := 575) (.exec 0x105c83 (fun s => s.RIP = 0x105c83) (shlR32Effect 0x105c83 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[570]
    (.letOp (n := 576) (.out 0x105c86 (xorR32R32Effect 0x105c86 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[574, 572]
    (.letOp (n := 577) (.exec 0x105c86 (fun s => s.RIP = 0x105c86) (xorR32R32Effect 0x105c86 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[574, 572]
    (.letOp (n := 578) (.out 0x105c88 (movR32R32Effect 0x105c88 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[576]
    (.letOp (n := 579) (.exec 0x105c88 (fun s => s.RIP = 0x105c88) (movR32R32Effect 0x105c88 2 0 1) (Reg.operands [.gpr 1] [])) #v[576]
    (.letOp (n := 580) (.out 0x105c8a (shrR32Effect 0x105c8a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[578]
    (.letOp (n := 581) (.exec 0x105c8a (fun s => s.RIP = 0x105c8a) (shrR32Effect 0x105c8a 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[578]
    (.letOp (n := 582) (.out 0x105c8c (xorR32R32Effect 0x105c8c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[580, 576]
    (.letOp (n := 583) (.exec 0x105c8c (fun s => s.RIP = 0x105c8c) (xorR32R32Effect 0x105c8c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[580, 576]
    (.letOp (n := 584) (.out 0x105c8e (andEaxImm32Effect 0x105c8e 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[582]
    (.letOp (n := 585) (.exec 0x105c8e (fun s => s.RIP = 0x105c8e) (andEaxImm32Effect 0x105c8e 0x5050) (Reg.operands [.gpr 0] [])) #v[582]
    (.letOp (n := 586) (.out 0x105c93 (xorR32R32Effect 0x105c93 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[576, 584]
    (.letOp (n := 587) (.exec 0x105c93 (fun s => s.RIP = 0x105c93) (xorR32R32Effect 0x105c93 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[576, 584]
    (.letOp (n := 588) (.out 0x105c95 (addR32R32Effect 0x105c95 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[584, 584]
    (.letOp (n := 589) (.exec 0x105c95 (fun s => s.RIP = 0x105c95) (addR32R32Effect 0x105c95 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[584, 584]
    (.letOp (n := 590) (.out 0x105c97 (xorR32R32Effect 0x105c97 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[588, 586]
    (.letOp (n := 591) (.exec 0x105c97 (fun s => s.RIP = 0x105c97) (xorR32R32Effect 0x105c97 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[588, 586]
    (b_l10593a_14)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_13 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x42,
    0x0F, 0xB7, 0x44, 0x24, 0x44, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23,
    0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25,
    0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_14

theorem code_l10593a_13 : ∀ x ∈ codeRange 0x105c5f bytes_l10593a_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5c5f 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_14

def b_l10593a_12 : Block Op Label signature Reg.count 514 :=
  .letOp (n := 514) (.out 0x105c28 (xorR32R32Effect 0x105c28 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[512, 510]
    (.letOp (n := 515) (.exec 0x105c28 (fun s => s.RIP = 0x105c28) (xorR32R32Effect 0x105c28 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[512, 510]
    (.letOp (n := 516) (.out 0x105c2a (movR32R32Effect 0x105c2a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[514]
    (.letOp (n := 517) (.exec 0x105c2a (fun s => s.RIP = 0x105c2a) (movR32R32Effect 0x105c2a 2 0 1) (Reg.operands [.gpr 1] [])) #v[514]
    (.letOp (n := 518) (.out 0x105c2c (shrR32Effect 0x105c2c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[516]
    (.letOp (n := 519) (.exec 0x105c2c (fun s => s.RIP = 0x105c2c) (shrR32Effect 0x105c2c 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[516]
    (.letOp (n := 520) (.out 0x105c2e (xorR32R32Effect 0x105c2e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[518, 514]
    (.letOp (n := 521) (.exec 0x105c2e (fun s => s.RIP = 0x105c2e) (xorR32R32Effect 0x105c2e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[518, 514]
    (.letOp (n := 522) (.out 0x105c30 (andEaxImm32Effect 0x105c30 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[520]
    (.letOp (n := 523) (.exec 0x105c30 (fun s => s.RIP = 0x105c30) (andEaxImm32Effect 0x105c30 0x5050) (Reg.operands [.gpr 0] [])) #v[520]
    (.letOp (n := 524) (.out 0x105c35 (xorR32R32Effect 0x105c35 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[514, 522]
    (.letOp (n := 525) (.exec 0x105c35 (fun s => s.RIP = 0x105c35) (xorR32R32Effect 0x105c35 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[514, 522]
    (.letOp (n := 526) (.out 0x105c37 (addR32R32Effect 0x105c37 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[522, 522]
    (.letOp (n := 527) (.exec 0x105c37 (fun s => s.RIP = 0x105c37) (addR32R32Effect 0x105c37 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[522, 522]
    (.letOp (n := 528) (.out 0x105c39 (xorR32R32Effect 0x105c39 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[526, 524]
    (.letOp (n := 529) (.exec 0x105c39 (fun s => s.RIP = 0x105c39) (xorR32R32Effect 0x105c39 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[526, 524]
    (.letOp (n := 530) (.exec 0x105c3b (StorePre 0x105c3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105c3b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c3b 5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[528, 4]
    (.letOp (n := 531) (.out 0x105c40 (movzxR32M16Effect 0x105c40 5 0 (.sib 4 none 0 (.d8 0x42))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 532) (.exec 0x105c40 (LoadPre 0x105c40 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x42)) s (0x105c40 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c40 5 0 (.sib 4 none 0 (.d8 0x42))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 533) (.out 0x105c45 (movR32R32Effect 0x105c45 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[531]
    (.letOp (n := 534) (.exec 0x105c45 (fun s => s.RIP = 0x105c45) (movR32R32Effect 0x105c45 2 1 0) (Reg.operands [.gpr 0] [])) #v[531]
    (.letOp (n := 535) (.out 0x105c47 (shrR32Effect 0x105c47 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[533]
    (.letOp (n := 536) (.exec 0x105c47 (fun s => s.RIP = 0x105c47) (shrR32Effect 0x105c47 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[533]
    (.letOp (n := 537) (.out 0x105c4a (xorR32R32Effect 0x105c4a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[535, 531]
    (.letOp (n := 538) (.exec 0x105c4a (fun s => s.RIP = 0x105c4a) (xorR32R32Effect 0x105c4a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[535, 531]
    (.letOp (n := 539) (.out 0x105c4c (andR32Imm32Effect 0x105c4c 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[537]
    (.letOp (n := 540) (.exec 0x105c4c (fun s => s.RIP = 0x105c4c) (andR32Imm32Effect 0x105c4c 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[537]
    (.letOp (n := 541) (.out 0x105c52 (xorR32R32Effect 0x105c52 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[531, 539]
    (.letOp (n := 542) (.exec 0x105c52 (fun s => s.RIP = 0x105c52) (xorR32R32Effect 0x105c52 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[531, 539]
    (.letOp (n := 543) (.out 0x105c54 (shlR32Effect 0x105c54 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[539]
    (.letOp (n := 544) (.exec 0x105c54 (fun s => s.RIP = 0x105c54) (shlR32Effect 0x105c54 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[539]
    (.letOp (n := 545) (.out 0x105c57 (xorR32R32Effect 0x105c57 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[543, 541]
    (.letOp (n := 546) (.exec 0x105c57 (fun s => s.RIP = 0x105c57) (xorR32R32Effect 0x105c57 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[543, 541]
    (.letOp (n := 547) (.out 0x105c59 (movR32R32Effect 0x105c59 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[545]
    (.letOp (n := 548) (.exec 0x105c59 (fun s => s.RIP = 0x105c59) (movR32R32Effect 0x105c59 2 0 1) (Reg.operands [.gpr 1] [])) #v[545]
    (.letOp (n := 549) (.out 0x105c5b (shrR32Effect 0x105c5b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[547]
    (.letOp (n := 550) (.exec 0x105c5b (fun s => s.RIP = 0x105c5b) (shrR32Effect 0x105c5b 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[547]
    (.letOp (n := 551) (.out 0x105c5d (xorR32R32Effect 0x105c5d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[549, 545]
    (.letOp (n := 552) (.exec 0x105c5d (fun s => s.RIP = 0x105c5d) (xorR32R32Effect 0x105c5d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[549, 545]
    (b_l10593a_13)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_12 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x40, 0x0F, 0xB7, 0x44, 0x24, 0x42, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_13

theorem code_l10593a_12 : ∀ x ∈ codeRange 0x105c28 bytes_l10593a_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5c28 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_13

def b_l10593a_11 : Block Op Label signature Reg.count 475 :=
  .letOp (n := 475) (.out 0x105bec (xorR32R32Effect 0x105bec 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[473, 469]
    (.letOp (n := 476) (.exec 0x105bec (fun s => s.RIP = 0x105bec) (xorR32R32Effect 0x105bec 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[473, 469]
    (.letOp (n := 477) (.out 0x105bee (andR32Imm32Effect 0x105bee 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[475]
    (.letOp (n := 478) (.exec 0x105bee (fun s => s.RIP = 0x105bee) (andR32Imm32Effect 0x105bee 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[475]
    (.letOp (n := 479) (.out 0x105bf4 (xorR32R32Effect 0x105bf4 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[469, 477]
    (.letOp (n := 480) (.exec 0x105bf4 (fun s => s.RIP = 0x105bf4) (xorR32R32Effect 0x105bf4 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[469, 477]
    (.letOp (n := 481) (.out 0x105bf6 (shlR32Effect 0x105bf6 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[477]
    (.letOp (n := 482) (.exec 0x105bf6 (fun s => s.RIP = 0x105bf6) (shlR32Effect 0x105bf6 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[477]
    (.letOp (n := 483) (.out 0x105bf9 (xorR32R32Effect 0x105bf9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[481, 479]
    (.letOp (n := 484) (.exec 0x105bf9 (fun s => s.RIP = 0x105bf9) (xorR32R32Effect 0x105bf9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[481, 479]
    (.letOp (n := 485) (.out 0x105bfb (movR32R32Effect 0x105bfb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[483]
    (.letOp (n := 486) (.exec 0x105bfb (fun s => s.RIP = 0x105bfb) (movR32R32Effect 0x105bfb 2 0 1) (Reg.operands [.gpr 1] [])) #v[483]
    (.letOp (n := 487) (.out 0x105bfd (shrR32Effect 0x105bfd 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[485]
    (.letOp (n := 488) (.exec 0x105bfd (fun s => s.RIP = 0x105bfd) (shrR32Effect 0x105bfd 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[485]
    (.letOp (n := 489) (.out 0x105bff (xorR32R32Effect 0x105bff 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[487, 483]
    (.letOp (n := 490) (.exec 0x105bff (fun s => s.RIP = 0x105bff) (xorR32R32Effect 0x105bff 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[487, 483]
    (.letOp (n := 491) (.out 0x105c01 (andEaxImm32Effect 0x105c01 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[489]
    (.letOp (n := 492) (.exec 0x105c01 (fun s => s.RIP = 0x105c01) (andEaxImm32Effect 0x105c01 0x5050) (Reg.operands [.gpr 0] [])) #v[489]
    (.letOp (n := 493) (.out 0x105c06 (xorR32R32Effect 0x105c06 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[483, 491]
    (.letOp (n := 494) (.exec 0x105c06 (fun s => s.RIP = 0x105c06) (xorR32R32Effect 0x105c06 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[483, 491]
    (.letOp (n := 495) (.out 0x105c08 (addR32R32Effect 0x105c08 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[491, 491]
    (.letOp (n := 496) (.exec 0x105c08 (fun s => s.RIP = 0x105c08) (addR32R32Effect 0x105c08 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[491, 491]
    (.letOp (n := 497) (.out 0x105c0a (xorR32R32Effect 0x105c0a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[495, 493]
    (.letOp (n := 498) (.exec 0x105c0a (fun s => s.RIP = 0x105c0a) (xorR32R32Effect 0x105c0a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[495, 493]
    (.letOp (n := 499) (.exec 0x105c0c (StorePre 0x105c0c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x105c0c + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105c0c 5 0 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[497, 4]
    (.letOp (n := 500) (.out 0x105c11 (movzxR32M16Effect 0x105c11 5 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 501) (.exec 0x105c11 (LoadPre 0x105c11 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x105c11 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105c11 5 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 502) (.out 0x105c16 (movR32R32Effect 0x105c16 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[500]
    (.letOp (n := 503) (.exec 0x105c16 (fun s => s.RIP = 0x105c16) (movR32R32Effect 0x105c16 2 1 0) (Reg.operands [.gpr 0] [])) #v[500]
    (.letOp (n := 504) (.out 0x105c18 (shrR32Effect 0x105c18 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[502]
    (.letOp (n := 505) (.exec 0x105c18 (fun s => s.RIP = 0x105c18) (shrR32Effect 0x105c18 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[502]
    (.letOp (n := 506) (.out 0x105c1b (xorR32R32Effect 0x105c1b 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[504, 500]
    (.letOp (n := 507) (.exec 0x105c1b (fun s => s.RIP = 0x105c1b) (xorR32R32Effect 0x105c1b 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[504, 500]
    (.letOp (n := 508) (.out 0x105c1d (andR32Imm32Effect 0x105c1d 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[506]
    (.letOp (n := 509) (.exec 0x105c1d (fun s => s.RIP = 0x105c1d) (andR32Imm32Effect 0x105c1d 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[506]
    (.letOp (n := 510) (.out 0x105c23 (xorR32R32Effect 0x105c23 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[500, 508]
    (.letOp (n := 511) (.exec 0x105c23 (fun s => s.RIP = 0x105c23) (xorR32R32Effect 0x105c23 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[500, 508]
    (.letOp (n := 512) (.out 0x105c25 (shlR32Effect 0x105c25 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[508]
    (.letOp (n := 513) (.exec 0x105c25 (fun s => s.RIP = 0x105c25) (shlR32Effect 0x105c25 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[508]
    (b_l10593a_12)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_11 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x3E, 0x0F, 0xB7, 0x44, 0x24, 0x40, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02] ++ bytes_l10593a_12

theorem code_l10593a_11 : ∀ x ∈ codeRange 0x105bec bytes_l10593a_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5bec 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_12

def b_l10593a_10 : Block Op Label signature Reg.count 437 :=
  .letOp (n := 437) (.exec 0x105bac (StorePre 0x105bac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x105bac + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105bac 5 1 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[435, 4]
    (.letOp (n := 438) (.out 0x105bb1 (movzxR32M16Effect 0x105bb1 5 0 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 439) (.exec 0x105bb1 (LoadPre 0x105bb1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x105bb1 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105bb1 5 0 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 440) (.out 0x105bb6 (movR32R32Effect 0x105bb6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[438]
    (.letOp (n := 441) (.exec 0x105bb6 (fun s => s.RIP = 0x105bb6) (movR32R32Effect 0x105bb6 2 1 0) (Reg.operands [.gpr 0] [])) #v[438]
    (.letOp (n := 442) (.out 0x105bb8 (shrR32Effect 0x105bb8 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[440]
    (.letOp (n := 443) (.exec 0x105bb8 (fun s => s.RIP = 0x105bb8) (shrR32Effect 0x105bb8 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[440]
    (.letOp (n := 444) (.out 0x105bbb (xorR32R32Effect 0x105bbb 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[442, 438]
    (.letOp (n := 445) (.exec 0x105bbb (fun s => s.RIP = 0x105bbb) (xorR32R32Effect 0x105bbb 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[442, 438]
    (.letOp (n := 446) (.out 0x105bbd (andR32Imm32Effect 0x105bbd 6 1 0x2310) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[444]
    (.letOp (n := 447) (.exec 0x105bbd (fun s => s.RIP = 0x105bbd) (andR32Imm32Effect 0x105bbd 6 1 0x2310) (Reg.operands [.gpr 1] [])) #v[444]
    (.letOp (n := 448) (.out 0x105bc3 (xorR32R32Effect 0x105bc3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[438, 446]
    (.letOp (n := 449) (.exec 0x105bc3 (fun s => s.RIP = 0x105bc3) (xorR32R32Effect 0x105bc3 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[438, 446]
    (.letOp (n := 450) (.out 0x105bc5 (shlR32Effect 0x105bc5 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[446]
    (.letOp (n := 451) (.exec 0x105bc5 (fun s => s.RIP = 0x105bc5) (shlR32Effect 0x105bc5 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[446]
    (.letOp (n := 452) (.out 0x105bc8 (xorR32R32Effect 0x105bc8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[450, 448]
    (.letOp (n := 453) (.exec 0x105bc8 (fun s => s.RIP = 0x105bc8) (xorR32R32Effect 0x105bc8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[450, 448]
    (.letOp (n := 454) (.out 0x105bca (movR32R32Effect 0x105bca 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[452]
    (.letOp (n := 455) (.exec 0x105bca (fun s => s.RIP = 0x105bca) (movR32R32Effect 0x105bca 2 0 1) (Reg.operands [.gpr 1] [])) #v[452]
    (.letOp (n := 456) (.out 0x105bcc (shrR32Effect 0x105bcc 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[454]
    (.letOp (n := 457) (.exec 0x105bcc (fun s => s.RIP = 0x105bcc) (shrR32Effect 0x105bcc 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[454]
    (.letOp (n := 458) (.out 0x105bce (xorR32R32Effect 0x105bce 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[456, 452]
    (.letOp (n := 459) (.exec 0x105bce (fun s => s.RIP = 0x105bce) (xorR32R32Effect 0x105bce 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[456, 452]
    (.letOp (n := 460) (.out 0x105bd0 (andEaxImm32Effect 0x105bd0 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[458]
    (.letOp (n := 461) (.exec 0x105bd0 (fun s => s.RIP = 0x105bd0) (andEaxImm32Effect 0x105bd0 0x5050) (Reg.operands [.gpr 0] [])) #v[458]
    (.letOp (n := 462) (.out 0x105bd5 (xorR32R32Effect 0x105bd5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[452, 460]
    (.letOp (n := 463) (.exec 0x105bd5 (fun s => s.RIP = 0x105bd5) (xorR32R32Effect 0x105bd5 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[452, 460]
    (.letOp (n := 464) (.out 0x105bd7 (addR32R32Effect 0x105bd7 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[460, 460]
    (.letOp (n := 465) (.exec 0x105bd7 (fun s => s.RIP = 0x105bd7) (addR32R32Effect 0x105bd7 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[460, 460]
    (.letOp (n := 466) (.out 0x105bd9 (xorR32R32Effect 0x105bd9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[464, 462]
    (.letOp (n := 467) (.exec 0x105bd9 (fun s => s.RIP = 0x105bd9) (xorR32R32Effect 0x105bd9 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[464, 462]
    (.letOp (n := 468) (.exec 0x105bdb (StorePre 0x105bdb 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x108)) s (0x105bdb + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105bdb 0 (.sib 4 none 0 (.d32 0x108))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[466, 4]
    (.letOp (n := 469) (.out 0x105be2 (movzxR32M16Effect 0x105be2 5 0 (.sib 4 none 0 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 470) (.exec 0x105be2 (LoadPre 0x105be2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3e)) s (0x105be2 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105be2 5 0 (.sib 4 none 0 (.d8 0x3e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 471) (.out 0x105be7 (movR32R32Effect 0x105be7 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[469]
    (.letOp (n := 472) (.exec 0x105be7 (fun s => s.RIP = 0x105be7) (movR32R32Effect 0x105be7 2 1 0) (Reg.operands [.gpr 0] [])) #v[469]
    (.letOp (n := 473) (.out 0x105be9 (shrR32Effect 0x105be9 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[471]
    (.letOp (n := 474) (.exec 0x105be9 (fun s => s.RIP = 0x105be9) (shrR32Effect 0x105be9 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[471]
    (b_l10593a_11))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_10 : List UInt8 :=
  [0x66, 0x89, 0x4C, 0x24, 0x3A, 0x0F, 0xB7, 0x44, 0x24, 0x3C, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x10, 0x23, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8,
    0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x89,
    0x84, 0x24, 0x08, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x3E, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_11

theorem code_l10593a_10 : ∀ x ∈ codeRange 0x105bac bytes_l10593a_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5bac 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_11

def b_l10593a_9 : Block Op Label signature Reg.count 399 :=
  .letOp (n := 399) (.out 0x105b67 (shlR32Effect 0x105b67 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[395]
    (.letOp (n := 400) (.exec 0x105b67 (fun s => s.RIP = 0x105b67) (shlR32Effect 0x105b67 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[395]
    (.letOp (n := 401) (.out 0x105b6a (xorR32R32Effect 0x105b6a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[399, 397]
    (.letOp (n := 402) (.exec 0x105b6a (fun s => s.RIP = 0x105b6a) (xorR32R32Effect 0x105b6a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[399, 397]
    (.letOp (n := 403) (.exec 0x105b6c (StorePre 0x105b6c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x110)) s (0x105b6c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105b6c 1 (.sib 4 none 0 (.d32 0x110))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[401, 4]
    (.letOp (n := 404) (.out 0x105b73 (movzxR32M16Effect 0x105b73 5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 405) (.exec 0x105b73 (LoadPre 0x105b73 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x105b73 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b73 5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 406) (.out 0x105b78 (movR32R32Effect 0x105b78 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[404]
    (.letOp (n := 407) (.exec 0x105b78 (fun s => s.RIP = 0x105b78) (movR32R32Effect 0x105b78 2 1 0) (Reg.operands [.gpr 0] [])) #v[404]
    (.letOp (n := 408) (.out 0x105b7a (shrR32Effect 0x105b7a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[406]
    (.letOp (n := 409) (.exec 0x105b7a (fun s => s.RIP = 0x105b7a) (shrR32Effect 0x105b7a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[406]
    (.letOp (n := 410) (.out 0x105b7d (xorR32R32Effect 0x105b7d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[408, 404]
    (.letOp (n := 411) (.exec 0x105b7d (fun s => s.RIP = 0x105b7d) (xorR32R32Effect 0x105b7d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[408, 404]
    (.letOp (n := 412) (.out 0x105b7f (andR32Imm32Effect 0x105b7f 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[410]
    (.letOp (n := 413) (.exec 0x105b7f (fun s => s.RIP = 0x105b7f) (andR32Imm32Effect 0x105b7f 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[410]
    (.letOp (n := 414) (.out 0x105b85 (xorR32R32Effect 0x105b85 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[404, 412]
    (.letOp (n := 415) (.exec 0x105b85 (fun s => s.RIP = 0x105b85) (xorR32R32Effect 0x105b85 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[404, 412]
    (.letOp (n := 416) (.out 0x105b87 (shlR32Effect 0x105b87 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[412]
    (.letOp (n := 417) (.exec 0x105b87 (fun s => s.RIP = 0x105b87) (shlR32Effect 0x105b87 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[412]
    (.letOp (n := 418) (.out 0x105b8a (xorR32R32Effect 0x105b8a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[416, 414]
    (.letOp (n := 419) (.exec 0x105b8a (fun s => s.RIP = 0x105b8a) (xorR32R32Effect 0x105b8a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[416, 414]
    (.letOp (n := 420) (.exec 0x105b8c (StorePre 0x105b8c 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x10c)) s (0x105b8c + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105b8c 1 (.sib 4 none 0 (.d32 0x10c))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[418, 4]
    (.letOp (n := 421) (.out 0x105b93 (movzxR32M16Effect 0x105b93 5 0 (.sib 4 none 0 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 422) (.exec 0x105b93 (LoadPre 0x105b93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3a)) s (0x105b93 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b93 5 0 (.sib 4 none 0 (.d8 0x3a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 423) (.out 0x105b98 (movR32R32Effect 0x105b98 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[421]
    (.letOp (n := 424) (.exec 0x105b98 (fun s => s.RIP = 0x105b98) (movR32R32Effect 0x105b98 2 1 0) (Reg.operands [.gpr 0] [])) #v[421]
    (.letOp (n := 425) (.out 0x105b9a (shrR32Effect 0x105b9a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[423]
    (.letOp (n := 426) (.exec 0x105b9a (fun s => s.RIP = 0x105b9a) (shrR32Effect 0x105b9a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[423]
    (.letOp (n := 427) (.out 0x105b9d (xorR32R32Effect 0x105b9d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[425, 421]
    (.letOp (n := 428) (.exec 0x105b9d (fun s => s.RIP = 0x105b9d) (xorR32R32Effect 0x105b9d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[425, 421]
    (.letOp (n := 429) (.out 0x105b9f (andR32Imm32Effect 0x105b9f 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[427]
    (.letOp (n := 430) (.exec 0x105b9f (fun s => s.RIP = 0x105b9f) (andR32Imm32Effect 0x105b9f 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[427]
    (.letOp (n := 431) (.out 0x105ba5 (xorR32R32Effect 0x105ba5 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[421, 429]
    (.letOp (n := 432) (.exec 0x105ba5 (fun s => s.RIP = 0x105ba5) (xorR32R32Effect 0x105ba5 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[421, 429]
    (.letOp (n := 433) (.out 0x105ba7 (shlR32Effect 0x105ba7 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[429]
    (.letOp (n := 434) (.exec 0x105ba7 (fun s => s.RIP = 0x105ba7) (shlR32Effect 0x105ba7 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[429]
    (.letOp (n := 435) (.out 0x105baa (xorR32R32Effect 0x105baa 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[433, 431]
    (.letOp (n := 436) (.exec 0x105baa (fun s => s.RIP = 0x105baa) (xorR32R32Effect 0x105baa 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[433, 431]
    (b_l10593a_10))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_9 : List UInt8 :=
  [0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0x8C, 0x24, 0x10, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24,
    0x38, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8,
    0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0x8C, 0x24, 0x0C, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24,
    0x3A, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8,
    0xC1, 0xE1, 0x02, 0x31, 0xC1] ++ bytes_l10593a_10

theorem code_l10593a_9 : ∀ x ∈ codeRange 0x105b67 bytes_l10593a_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5b67 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_10

def b_l10593a_8 : Block Op Label signature Reg.count 361 :=
  .letOp (n := 361) (.out 0x105b23 (andR32Imm32Effect 0x105b23 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[359]
    (.letOp (n := 362) (.exec 0x105b23 (fun s => s.RIP = 0x105b23) (andR32Imm32Effect 0x105b23 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[359]
    (.letOp (n := 363) (.out 0x105b29 (xorR32R32Effect 0x105b29 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[353, 361]
    (.letOp (n := 364) (.exec 0x105b29 (fun s => s.RIP = 0x105b29) (xorR32R32Effect 0x105b29 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[353, 361]
    (.letOp (n := 365) (.out 0x105b2b (shlR32Effect 0x105b2b 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[361]
    (.letOp (n := 366) (.exec 0x105b2b (fun s => s.RIP = 0x105b2b) (shlR32Effect 0x105b2b 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[361]
    (.letOp (n := 367) (.out 0x105b2e (xorR32R32Effect 0x105b2e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[365, 363]
    (.letOp (n := 368) (.exec 0x105b2e (fun s => s.RIP = 0x105b2e) (xorR32R32Effect 0x105b2e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[365, 363]
    (.letOp (n := 369) (.exec 0x105b30 (StorePre 0x105b30 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x105b30 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b30 5 1 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[367, 4]
    (.letOp (n := 370) (.out 0x105b35 (movzxR32M16Effect 0x105b35 5 0 (.sib 4 none 0 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 371) (.exec 0x105b35 (LoadPre 0x105b35 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x105b35 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b35 5 0 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 372) (.out 0x105b3a (movR32R32Effect 0x105b3a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[370]
    (.letOp (n := 373) (.exec 0x105b3a (fun s => s.RIP = 0x105b3a) (movR32R32Effect 0x105b3a 2 1 0) (Reg.operands [.gpr 0] [])) #v[370]
    (.letOp (n := 374) (.out 0x105b3c (shrR32Effect 0x105b3c 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[372]
    (.letOp (n := 375) (.exec 0x105b3c (fun s => s.RIP = 0x105b3c) (shrR32Effect 0x105b3c 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[372]
    (.letOp (n := 376) (.out 0x105b3f (xorR32R32Effect 0x105b3f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[374, 370]
    (.letOp (n := 377) (.exec 0x105b3f (fun s => s.RIP = 0x105b3f) (xorR32R32Effect 0x105b3f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[374, 370]
    (.letOp (n := 378) (.out 0x105b41 (andR32Imm32Effect 0x105b41 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[376]
    (.letOp (n := 379) (.exec 0x105b41 (fun s => s.RIP = 0x105b41) (andR32Imm32Effect 0x105b41 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[376]
    (.letOp (n := 380) (.out 0x105b47 (xorR32R32Effect 0x105b47 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[370, 378]
    (.letOp (n := 381) (.exec 0x105b47 (fun s => s.RIP = 0x105b47) (xorR32R32Effect 0x105b47 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[370, 378]
    (.letOp (n := 382) (.out 0x105b49 (shlR32Effect 0x105b49 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[378]
    (.letOp (n := 383) (.exec 0x105b49 (fun s => s.RIP = 0x105b49) (shlR32Effect 0x105b49 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[378]
    (.letOp (n := 384) (.out 0x105b4c (xorR32R32Effect 0x105b4c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[382, 380]
    (.letOp (n := 385) (.exec 0x105b4c (fun s => s.RIP = 0x105b4c) (xorR32R32Effect 0x105b4c 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[382, 380]
    (.letOp (n := 386) (.exec 0x105b4e (StorePre 0x105b4e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x34)) s (0x105b4e + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b4e 5 1 (.sib 4 none 0 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[384, 4]
    (.letOp (n := 387) (.out 0x105b53 (movzxR32M16Effect 0x105b53 5 0 (.sib 4 none 0 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 388) (.exec 0x105b53 (LoadPre 0x105b53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x36)) s (0x105b53 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b53 5 0 (.sib 4 none 0 (.d8 0x36))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 389) (.out 0x105b58 (movR32R32Effect 0x105b58 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[387]
    (.letOp (n := 390) (.exec 0x105b58 (fun s => s.RIP = 0x105b58) (movR32R32Effect 0x105b58 2 1 0) (Reg.operands [.gpr 0] [])) #v[387]
    (.letOp (n := 391) (.out 0x105b5a (shrR32Effect 0x105b5a 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[389]
    (.letOp (n := 392) (.exec 0x105b5a (fun s => s.RIP = 0x105b5a) (shrR32Effect 0x105b5a 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[389]
    (.letOp (n := 393) (.out 0x105b5d (xorR32R32Effect 0x105b5d 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[391, 387]
    (.letOp (n := 394) (.exec 0x105b5d (fun s => s.RIP = 0x105b5d) (xorR32R32Effect 0x105b5d 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[391, 387]
    (.letOp (n := 395) (.out 0x105b5f (andR32Imm32Effect 0x105b5f 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[393]
    (.letOp (n := 396) (.exec 0x105b5f (fun s => s.RIP = 0x105b5f) (andR32Imm32Effect 0x105b5f 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[393]
    (.letOp (n := 397) (.out 0x105b65 (xorR32R32Effect 0x105b65 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[387, 395]
    (.letOp (n := 398) (.exec 0x105b65 (fun s => s.RIP = 0x105b65) (xorR32R32Effect 0x105b65 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[387, 395]
    (b_l10593a_9))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_8 : List UInt8 :=
  [0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C,
    0x24, 0x32, 0x0F, 0xB7, 0x44, 0x24, 0x34, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1,
    0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x34,
    0x0F, 0xB7, 0x44, 0x24, 0x36, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30,
    0x00, 0x00, 0x31, 0xC8] ++ bytes_l10593a_9

theorem code_l10593a_8 : ∀ x ∈ codeRange 0x105b23 bytes_l10593a_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5b23 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_9

def b_l10593a_7 : Block Op Label signature Reg.count 323 :=
  .letOp (n := 323) (.out 0x105ae0 (shrR32Effect 0x105ae0 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[321]
    (.letOp (n := 324) (.exec 0x105ae0 (fun s => s.RIP = 0x105ae0) (shrR32Effect 0x105ae0 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[321]
    (.letOp (n := 325) (.out 0x105ae3 (xorR32R32Effect 0x105ae3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[323, 319]
    (.letOp (n := 326) (.exec 0x105ae3 (fun s => s.RIP = 0x105ae3) (xorR32R32Effect 0x105ae3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[323, 319]
    (.letOp (n := 327) (.out 0x105ae5 (andR32Imm32Effect 0x105ae5 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[325]
    (.letOp (n := 328) (.exec 0x105ae5 (fun s => s.RIP = 0x105ae5) (andR32Imm32Effect 0x105ae5 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[325]
    (.letOp (n := 329) (.out 0x105aeb (xorR32R32Effect 0x105aeb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[319, 327]
    (.letOp (n := 330) (.exec 0x105aeb (fun s => s.RIP = 0x105aeb) (xorR32R32Effect 0x105aeb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[319, 327]
    (.letOp (n := 331) (.out 0x105aed (shlR32Effect 0x105aed 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[327]
    (.letOp (n := 332) (.exec 0x105aed (fun s => s.RIP = 0x105aed) (shlR32Effect 0x105aed 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[327]
    (.letOp (n := 333) (.out 0x105af0 (xorR32R32Effect 0x105af0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[331, 329]
    (.letOp (n := 334) (.exec 0x105af0 (fun s => s.RIP = 0x105af0) (xorR32R32Effect 0x105af0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[331, 329]
    (.letOp (n := 335) (.exec 0x105af2 (StorePre 0x105af2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x114)) s (0x105af2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105af2 1 (.sib 4 none 0 (.d32 0x114))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[333, 4]
    (.letOp (n := 336) (.out 0x105af9 (movzxR32M16Effect 0x105af9 5 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 337) (.exec 0x105af9 (LoadPre 0x105af9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105af9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105af9 5 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 338) (.out 0x105afe (movR32R32Effect 0x105afe 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[336]
    (.letOp (n := 339) (.exec 0x105afe (fun s => s.RIP = 0x105afe) (movR32R32Effect 0x105afe 2 1 0) (Reg.operands [.gpr 0] [])) #v[336]
    (.letOp (n := 340) (.out 0x105b00 (shrR32Effect 0x105b00 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[338]
    (.letOp (n := 341) (.exec 0x105b00 (fun s => s.RIP = 0x105b00) (shrR32Effect 0x105b00 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[338]
    (.letOp (n := 342) (.out 0x105b03 (xorR32R32Effect 0x105b03 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[340, 336]
    (.letOp (n := 343) (.exec 0x105b03 (fun s => s.RIP = 0x105b03) (xorR32R32Effect 0x105b03 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[340, 336]
    (.letOp (n := 344) (.out 0x105b05 (andR32Imm32Effect 0x105b05 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[342]
    (.letOp (n := 345) (.exec 0x105b05 (fun s => s.RIP = 0x105b05) (andR32Imm32Effect 0x105b05 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[342]
    (.letOp (n := 346) (.out 0x105b0b (xorR32R32Effect 0x105b0b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[336, 344]
    (.letOp (n := 347) (.exec 0x105b0b (fun s => s.RIP = 0x105b0b) (xorR32R32Effect 0x105b0b 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[336, 344]
    (.letOp (n := 348) (.out 0x105b0d (shlR32Effect 0x105b0d 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[344]
    (.letOp (n := 349) (.exec 0x105b0d (fun s => s.RIP = 0x105b0d) (shlR32Effect 0x105b0d 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[344]
    (.letOp (n := 350) (.out 0x105b10 (xorR32R32Effect 0x105b10 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[348, 346]
    (.letOp (n := 351) (.exec 0x105b10 (fun s => s.RIP = 0x105b10) (xorR32R32Effect 0x105b10 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[348, 346]
    (.letOp (n := 352) (.exec 0x105b12 (StorePre 0x105b12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x105b12 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105b12 5 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[350, 4]
    (.letOp (n := 353) (.out 0x105b17 (movzxR32M16Effect 0x105b17 5 0 (.sib 4 none 0 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 354) (.exec 0x105b17 (LoadPre 0x105b17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x32)) s (0x105b17 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105b17 5 0 (.sib 4 none 0 (.d8 0x32))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 355) (.out 0x105b1c (movR32R32Effect 0x105b1c 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[353]
    (.letOp (n := 356) (.exec 0x105b1c (fun s => s.RIP = 0x105b1c) (movR32R32Effect 0x105b1c 2 1 0) (Reg.operands [.gpr 0] [])) #v[353]
    (.letOp (n := 357) (.out 0x105b1e (shrR32Effect 0x105b1e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[355]
    (.letOp (n := 358) (.exec 0x105b1e (fun s => s.RIP = 0x105b1e) (shrR32Effect 0x105b1e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[355]
    (.letOp (n := 359) (.out 0x105b21 (xorR32R32Effect 0x105b21 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[357, 353]
    (.letOp (n := 360) (.exec 0x105b21 (fun s => s.RIP = 0x105b21) (xorR32R32Effect 0x105b21 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[357, 353]
    (b_l10593a_8))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_7 : List UInt8 :=
  [0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x89, 0x8C, 0x24, 0x14, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x30, 0x89, 0xC1,
    0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02,
    0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x30, 0x0F, 0xB7, 0x44, 0x24, 0x32, 0x89, 0xC1, 0xC1, 0xE9,
    0x02, 0x31, 0xC1] ++ bytes_l10593a_8

theorem code_l10593a_7 : ∀ x ∈ codeRange 0x105ae0 bytes_l10593a_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5ae0 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_8

def b_l10593a_6 : Block Op Label signature Reg.count 285 :=
  .letOp (n := 285) (.out 0x105aa1 (xorR32R32Effect 0x105aa1 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[283, 281]
    (.letOp (n := 286) (.exec 0x105aa1 (fun s => s.RIP = 0x105aa1) (xorR32R32Effect 0x105aa1 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[283, 281]
    (.letOp (n := 287) (.out 0x105aa3 (movR32R32Effect 0x105aa3 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[285]
    (.letOp (n := 288) (.exec 0x105aa3 (fun s => s.RIP = 0x105aa3) (movR32R32Effect 0x105aa3 2 0 1) (Reg.operands [.gpr 1] [])) #v[285]
    (.letOp (n := 289) (.out 0x105aa5 (shrR32Effect 0x105aa5 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[287]
    (.letOp (n := 290) (.exec 0x105aa5 (fun s => s.RIP = 0x105aa5) (shrR32Effect 0x105aa5 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[287]
    (.letOp (n := 291) (.out 0x105aa7 (xorR32R32Effect 0x105aa7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[289, 285]
    (.letOp (n := 292) (.exec 0x105aa7 (fun s => s.RIP = 0x105aa7) (xorR32R32Effect 0x105aa7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[289, 285]
    (.letOp (n := 293) (.out 0x105aa9 (andEaxImm32Effect 0x105aa9 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[291]
    (.letOp (n := 294) (.exec 0x105aa9 (fun s => s.RIP = 0x105aa9) (andEaxImm32Effect 0x105aa9 0x5050) (Reg.operands [.gpr 0] [])) #v[291]
    (.letOp (n := 295) (.out 0x105aae (xorR32R32Effect 0x105aae 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[285, 293]
    (.letOp (n := 296) (.exec 0x105aae (fun s => s.RIP = 0x105aae) (xorR32R32Effect 0x105aae 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[285, 293]
    (.letOp (n := 297) (.out 0x105ab0 (addR32R32Effect 0x105ab0 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[293, 293]
    (.letOp (n := 298) (.exec 0x105ab0 (fun s => s.RIP = 0x105ab0) (addR32R32Effect 0x105ab0 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[293, 293]
    (.letOp (n := 299) (.out 0x105ab2 (xorR32R32Effect 0x105ab2 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[297, 295]
    (.letOp (n := 300) (.exec 0x105ab2 (fun s => s.RIP = 0x105ab2) (xorR32R32Effect 0x105ab2 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[297, 295]
    (.letOp (n := 301) (.exec 0x105ab4 (StorePre 0x105ab4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x105ab4 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105ab4 5 0 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[299, 4]
    (.letOp (n := 302) (.out 0x105ab9 (movzxR32M16Effect 0x105ab9 5 0 (.sib 4 none 0 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 303) (.exec 0x105ab9 (LoadPre 0x105ab9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2c)) s (0x105ab9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ab9 5 0 (.sib 4 none 0 (.d8 0x2c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 304) (.out 0x105abe (movR32R32Effect 0x105abe 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[302]
    (.letOp (n := 305) (.exec 0x105abe (fun s => s.RIP = 0x105abe) (movR32R32Effect 0x105abe 2 1 0) (Reg.operands [.gpr 0] [])) #v[302]
    (.letOp (n := 306) (.out 0x105ac0 (shrR32Effect 0x105ac0 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[304]
    (.letOp (n := 307) (.exec 0x105ac0 (fun s => s.RIP = 0x105ac0) (shrR32Effect 0x105ac0 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[304]
    (.letOp (n := 308) (.out 0x105ac3 (xorR32R32Effect 0x105ac3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[306, 302]
    (.letOp (n := 309) (.exec 0x105ac3 (fun s => s.RIP = 0x105ac3) (xorR32R32Effect 0x105ac3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[306, 302]
    (.letOp (n := 310) (.out 0x105ac5 (andR32Imm32Effect 0x105ac5 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[308]
    (.letOp (n := 311) (.exec 0x105ac5 (fun s => s.RIP = 0x105ac5) (andR32Imm32Effect 0x105ac5 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[308]
    (.letOp (n := 312) (.out 0x105acb (xorR32R32Effect 0x105acb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[302, 310]
    (.letOp (n := 313) (.exec 0x105acb (fun s => s.RIP = 0x105acb) (xorR32R32Effect 0x105acb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[302, 310]
    (.letOp (n := 314) (.out 0x105acd (shlR32Effect 0x105acd 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[310]
    (.letOp (n := 315) (.exec 0x105acd (fun s => s.RIP = 0x105acd) (shlR32Effect 0x105acd 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[310]
    (.letOp (n := 316) (.out 0x105ad0 (xorR32R32Effect 0x105ad0 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[314, 312]
    (.letOp (n := 317) (.exec 0x105ad0 (fun s => s.RIP = 0x105ad0) (xorR32R32Effect 0x105ad0 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[314, 312]
    (.letOp (n := 318) (.exec 0x105ad2 (StorePre 0x105ad2 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x118)) s (0x105ad2 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105ad2 1 (.sib 4 none 0 (.d32 0x118))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[316, 4]
    (.letOp (n := 319) (.out 0x105ad9 (movzxR32M16Effect 0x105ad9 5 0 (.sib 4 none 0 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 320) (.exec 0x105ad9 (LoadPre 0x105ad9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2e)) s (0x105ad9 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105ad9 5 0 (.sib 4 none 0 (.d8 0x2e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 321) (.out 0x105ade (movR32R32Effect 0x105ade 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[319]
    (.letOp (n := 322) (.exec 0x105ade (fun s => s.RIP = 0x105ade) (movR32R32Effect 0x105ade 2 1 0) (Reg.operands [.gpr 0] [])) #v[319]
    (b_l10593a_7))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_6 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x2A, 0x0F, 0xB7, 0x44, 0x24, 0x2C, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0x8C, 0x24, 0x18, 0x01, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x2E, 0x89, 0xC1] ++ bytes_l10593a_7

theorem code_l10593a_6 : ∀ x ∈ codeRange 0x105aa1 bytes_l10593a_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5aa1 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_7

def b_l10593a_5 : Block Op Label signature Reg.count 246 :=
  .letOp (n := 246) (.out 0x105a65 (xorR32R32Effect 0x105a65 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[244, 240]
    (.letOp (n := 247) (.exec 0x105a65 (fun s => s.RIP = 0x105a65) (xorR32R32Effect 0x105a65 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[244, 240]
    (.letOp (n := 248) (.out 0x105a67 (andR32Imm32Effect 0x105a67 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[246]
    (.letOp (n := 249) (.exec 0x105a67 (fun s => s.RIP = 0x105a67) (andR32Imm32Effect 0x105a67 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[246]
    (.letOp (n := 250) (.out 0x105a6d (xorR32R32Effect 0x105a6d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[240, 248]
    (.letOp (n := 251) (.exec 0x105a6d (fun s => s.RIP = 0x105a6d) (xorR32R32Effect 0x105a6d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[240, 248]
    (.letOp (n := 252) (.out 0x105a6f (shlR32Effect 0x105a6f 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[248]
    (.letOp (n := 253) (.exec 0x105a6f (fun s => s.RIP = 0x105a6f) (shlR32Effect 0x105a6f 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248]
    (.letOp (n := 254) (.out 0x105a72 (xorR32R32Effect 0x105a72 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[252, 250]
    (.letOp (n := 255) (.exec 0x105a72 (fun s => s.RIP = 0x105a72) (xorR32R32Effect 0x105a72 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[252, 250]
    (.letOp (n := 256) (.out 0x105a74 (movR32R32Effect 0x105a74 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[254]
    (.letOp (n := 257) (.exec 0x105a74 (fun s => s.RIP = 0x105a74) (movR32R32Effect 0x105a74 2 0 1) (Reg.operands [.gpr 1] [])) #v[254]
    (.letOp (n := 258) (.out 0x105a76 (shrR32Effect 0x105a76 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[256]
    (.letOp (n := 259) (.exec 0x105a76 (fun s => s.RIP = 0x105a76) (shrR32Effect 0x105a76 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[256]
    (.letOp (n := 260) (.out 0x105a78 (xorR32R32Effect 0x105a78 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[258, 254]
    (.letOp (n := 261) (.exec 0x105a78 (fun s => s.RIP = 0x105a78) (xorR32R32Effect 0x105a78 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[258, 254]
    (.letOp (n := 262) (.out 0x105a7a (andEaxImm32Effect 0x105a7a 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[260]
    (.letOp (n := 263) (.exec 0x105a7a (fun s => s.RIP = 0x105a7a) (andEaxImm32Effect 0x105a7a 0x5050) (Reg.operands [.gpr 0] [])) #v[260]
    (.letOp (n := 264) (.out 0x105a7f (xorR32R32Effect 0x105a7f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[254, 262]
    (.letOp (n := 265) (.exec 0x105a7f (fun s => s.RIP = 0x105a7f) (xorR32R32Effect 0x105a7f 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[254, 262]
    (.letOp (n := 266) (.out 0x105a81 (addR32R32Effect 0x105a81 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[262, 262]
    (.letOp (n := 267) (.exec 0x105a81 (fun s => s.RIP = 0x105a81) (addR32R32Effect 0x105a81 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[262, 262]
    (.letOp (n := 268) (.out 0x105a83 (xorR32R32Effect 0x105a83 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[266, 264]
    (.letOp (n := 269) (.exec 0x105a83 (fun s => s.RIP = 0x105a83) (xorR32R32Effect 0x105a83 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[266, 264]
    (.letOp (n := 270) (.exec 0x105a85 (StorePre 0x105a85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105a85 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a85 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 4]
    (.letOp (n := 271) (.out 0x105a8a (movzxR32M16Effect 0x105a8a 5 0 (.sib 4 none 0 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 272) (.exec 0x105a8a (LoadPre 0x105a8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2a)) s (0x105a8a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a8a 5 0 (.sib 4 none 0 (.d8 0x2a))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 273) (.out 0x105a8f (movR32R32Effect 0x105a8f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[271]
    (.letOp (n := 274) (.exec 0x105a8f (fun s => s.RIP = 0x105a8f) (movR32R32Effect 0x105a8f 2 1 0) (Reg.operands [.gpr 0] [])) #v[271]
    (.letOp (n := 275) (.out 0x105a91 (shrR32Effect 0x105a91 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[273]
    (.letOp (n := 276) (.exec 0x105a91 (fun s => s.RIP = 0x105a91) (shrR32Effect 0x105a91 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[273]
    (.letOp (n := 277) (.out 0x105a94 (xorR32R32Effect 0x105a94 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[275, 271]
    (.letOp (n := 278) (.exec 0x105a94 (fun s => s.RIP = 0x105a94) (xorR32R32Effect 0x105a94 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[275, 271]
    (.letOp (n := 279) (.out 0x105a96 (andR32Imm32Effect 0x105a96 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[277]
    (.letOp (n := 280) (.exec 0x105a96 (fun s => s.RIP = 0x105a96) (andR32Imm32Effect 0x105a96 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[277]
    (.letOp (n := 281) (.out 0x105a9c (xorR32R32Effect 0x105a9c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[271, 279]
    (.letOp (n := 282) (.exec 0x105a9c (fun s => s.RIP = 0x105a9c) (xorR32R32Effect 0x105a9c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[271, 279]
    (.letOp (n := 283) (.out 0x105a9e (shlR32Effect 0x105a9e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[279]
    (.letOp (n := 284) (.exec 0x105a9e (fun s => s.RIP = 0x105a9e) (shlR32Effect 0x105a9e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[279]
    (b_l10593a_6)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_5 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x28, 0x0F, 0xB7, 0x44, 0x24, 0x2A, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02] ++ bytes_l10593a_6

theorem code_l10593a_5 : ∀ x ∈ codeRange 0x105a65 bytes_l10593a_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5a65 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_6

def b_l10593a_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.exec 0x105a27 (StorePre 0x105a27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x105a27 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a27 5 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[206, 4]
    (.letOp (n := 209) (.out 0x105a2c (movzxR32M16Effect 0x105a2c 5 0 (.sib 4 none 0 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 210) (.exec 0x105a2c (LoadPre 0x105a2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x105a2c + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a2c 5 0 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 211) (.out 0x105a31 (movR32R32Effect 0x105a31 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[209]
    (.letOp (n := 212) (.exec 0x105a31 (fun s => s.RIP = 0x105a31) (movR32R32Effect 0x105a31 2 1 0) (Reg.operands [.gpr 0] [])) #v[209]
    (.letOp (n := 213) (.out 0x105a33 (shrR32Effect 0x105a33 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[211]
    (.letOp (n := 214) (.exec 0x105a33 (fun s => s.RIP = 0x105a33) (shrR32Effect 0x105a33 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[211]
    (.letOp (n := 215) (.out 0x105a36 (xorR32R32Effect 0x105a36 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[213, 209]
    (.letOp (n := 216) (.exec 0x105a36 (fun s => s.RIP = 0x105a36) (xorR32R32Effect 0x105a36 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[213, 209]
    (.letOp (n := 217) (.out 0x105a38 (andR32Imm32Effect 0x105a38 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[215]
    (.letOp (n := 218) (.exec 0x105a38 (fun s => s.RIP = 0x105a38) (andR32Imm32Effect 0x105a38 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[215]
    (.letOp (n := 219) (.out 0x105a3e (xorR32R32Effect 0x105a3e 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[209, 217]
    (.letOp (n := 220) (.exec 0x105a3e (fun s => s.RIP = 0x105a3e) (xorR32R32Effect 0x105a3e 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[209, 217]
    (.letOp (n := 221) (.out 0x105a40 (shlR32Effect 0x105a40 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[217]
    (.letOp (n := 222) (.exec 0x105a40 (fun s => s.RIP = 0x105a40) (shlR32Effect 0x105a40 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[217]
    (.letOp (n := 223) (.out 0x105a43 (xorR32R32Effect 0x105a43 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[221, 219]
    (.letOp (n := 224) (.exec 0x105a43 (fun s => s.RIP = 0x105a43) (xorR32R32Effect 0x105a43 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[221, 219]
    (.letOp (n := 225) (.out 0x105a45 (movR32R32Effect 0x105a45 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[223]
    (.letOp (n := 226) (.exec 0x105a45 (fun s => s.RIP = 0x105a45) (movR32R32Effect 0x105a45 2 0 1) (Reg.operands [.gpr 1] [])) #v[223]
    (.letOp (n := 227) (.out 0x105a47 (shrR32Effect 0x105a47 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[225]
    (.letOp (n := 228) (.exec 0x105a47 (fun s => s.RIP = 0x105a47) (shrR32Effect 0x105a47 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[225]
    (.letOp (n := 229) (.out 0x105a49 (xorR32R32Effect 0x105a49 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[227, 223]
    (.letOp (n := 230) (.exec 0x105a49 (fun s => s.RIP = 0x105a49) (xorR32R32Effect 0x105a49 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[227, 223]
    (.letOp (n := 231) (.out 0x105a4b (andEaxImm32Effect 0x105a4b 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[229]
    (.letOp (n := 232) (.exec 0x105a4b (fun s => s.RIP = 0x105a4b) (andEaxImm32Effect 0x105a4b 0x5050) (Reg.operands [.gpr 0] [])) #v[229]
    (.letOp (n := 233) (.out 0x105a50 (xorR32R32Effect 0x105a50 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[223, 231]
    (.letOp (n := 234) (.exec 0x105a50 (fun s => s.RIP = 0x105a50) (xorR32R32Effect 0x105a50 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[223, 231]
    (.letOp (n := 235) (.out 0x105a52 (addR32R32Effect 0x105a52 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[231, 231]
    (.letOp (n := 236) (.exec 0x105a52 (fun s => s.RIP = 0x105a52) (addR32R32Effect 0x105a52 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[231, 231]
    (.letOp (n := 237) (.out 0x105a54 (xorR32R32Effect 0x105a54 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[235, 233]
    (.letOp (n := 238) (.exec 0x105a54 (fun s => s.RIP = 0x105a54) (xorR32R32Effect 0x105a54 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[235, 233]
    (.letOp (n := 239) (.exec 0x105a56 (StorePre 0x105a56 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x26)) s (0x105a56 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x105a56 5 0 (.sib 4 none 0 (.d8 0x26))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[237, 4]
    (.letOp (n := 240) (.out 0x105a5b (movzxR32M16Effect 0x105a5b 5 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 241) (.exec 0x105a5b (LoadPre 0x105a5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x105a5b + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105a5b 5 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 242) (.out 0x105a60 (movR32R32Effect 0x105a60 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[240]
    (.letOp (n := 243) (.exec 0x105a60 (fun s => s.RIP = 0x105a60) (movR32R32Effect 0x105a60 2 1 0) (Reg.operands [.gpr 0] [])) #v[240]
    (.letOp (n := 244) (.out 0x105a62 (shrR32Effect 0x105a62 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[242]
    (.letOp (n := 245) (.exec 0x105a62 (fun s => s.RIP = 0x105a62) (shrR32Effect 0x105a62 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[242]
    (b_l10593a_5))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_4 : List UInt8 :=
  [0x66, 0x89, 0x44, 0x24, 0x24, 0x0F, 0xB7, 0x44, 0x24, 0x26, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8,
    0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66,
    0x89, 0x44, 0x24, 0x26, 0x0F, 0xB7, 0x44, 0x24, 0x28, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_5

theorem code_l10593a_4 : ∀ x ∈ codeRange 0x105a27 bytes_l10593a_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x5a27 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_5

def b_l10593a_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x1059ed (andEaxImm32Effect 0x1059ed 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 170) (.exec 0x1059ed (fun s => s.RIP = 0x1059ed) (andEaxImm32Effect 0x1059ed 0x5050) (Reg.operands [.gpr 0] [])) #v[167]
    (.letOp (n := 171) (.out 0x1059f2 (xorR32R32Effect 0x1059f2 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[161, 169]
    (.letOp (n := 172) (.exec 0x1059f2 (fun s => s.RIP = 0x1059f2) (xorR32R32Effect 0x1059f2 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[161, 169]
    (.letOp (n := 173) (.out 0x1059f4 (addR32R32Effect 0x1059f4 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[169, 169]
    (.letOp (n := 174) (.exec 0x1059f4 (fun s => s.RIP = 0x1059f4) (addR32R32Effect 0x1059f4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[169, 169]
    (.letOp (n := 175) (.out 0x1059f6 (xorR32R32Effect 0x1059f6 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[173, 171]
    (.letOp (n := 176) (.exec 0x1059f6 (fun s => s.RIP = 0x1059f6) (xorR32R32Effect 0x1059f6 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[173, 171]
    (.letOp (n := 177) (.exec 0x1059f8 (StorePre 0x1059f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1059f8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1059f8 5 0 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[175, 4]
    (.letOp (n := 178) (.out 0x1059fd (movzxR32M16Effect 0x1059fd 5 0 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 179) (.exec 0x1059fd (LoadPre 0x1059fd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x1059fd + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1059fd 5 0 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 180) (.out 0x105a02 (movR32R32Effect 0x105a02 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[178]
    (.letOp (n := 181) (.exec 0x105a02 (fun s => s.RIP = 0x105a02) (movR32R32Effect 0x105a02 2 1 0) (Reg.operands [.gpr 0] [])) #v[178]
    (.letOp (n := 182) (.out 0x105a04 (shrR32Effect 0x105a04 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[180]
    (.letOp (n := 183) (.exec 0x105a04 (fun s => s.RIP = 0x105a04) (shrR32Effect 0x105a04 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[180]
    (.letOp (n := 184) (.out 0x105a07 (xorR32R32Effect 0x105a07 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[182, 178]
    (.letOp (n := 185) (.exec 0x105a07 (fun s => s.RIP = 0x105a07) (xorR32R32Effect 0x105a07 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[182, 178]
    (.letOp (n := 186) (.out 0x105a09 (andR32Imm32Effect 0x105a09 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[184]
    (.letOp (n := 187) (.exec 0x105a09 (fun s => s.RIP = 0x105a09) (andR32Imm32Effect 0x105a09 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[184]
    (.letOp (n := 188) (.out 0x105a0f (xorR32R32Effect 0x105a0f 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[178, 186]
    (.letOp (n := 189) (.exec 0x105a0f (fun s => s.RIP = 0x105a0f) (xorR32R32Effect 0x105a0f 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[178, 186]
    (.letOp (n := 190) (.out 0x105a11 (shlR32Effect 0x105a11 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[186]
    (.letOp (n := 191) (.exec 0x105a11 (fun s => s.RIP = 0x105a11) (shlR32Effect 0x105a11 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[186]
    (.letOp (n := 192) (.out 0x105a14 (xorR32R32Effect 0x105a14 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[190, 188]
    (.letOp (n := 193) (.exec 0x105a14 (fun s => s.RIP = 0x105a14) (xorR32R32Effect 0x105a14 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[190, 188]
    (.letOp (n := 194) (.out 0x105a16 (movR32R32Effect 0x105a16 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[192]
    (.letOp (n := 195) (.exec 0x105a16 (fun s => s.RIP = 0x105a16) (movR32R32Effect 0x105a16 2 0 1) (Reg.operands [.gpr 1] [])) #v[192]
    (.letOp (n := 196) (.out 0x105a18 (shrR32Effect 0x105a18 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[194]
    (.letOp (n := 197) (.exec 0x105a18 (fun s => s.RIP = 0x105a18) (shrR32Effect 0x105a18 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.out 0x105a1a (xorR32R32Effect 0x105a1a 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[196, 192]
    (.letOp (n := 199) (.exec 0x105a1a (fun s => s.RIP = 0x105a1a) (xorR32R32Effect 0x105a1a 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[196, 192]
    (.letOp (n := 200) (.out 0x105a1c (andEaxImm32Effect 0x105a1c 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[198]
    (.letOp (n := 201) (.exec 0x105a1c (fun s => s.RIP = 0x105a1c) (andEaxImm32Effect 0x105a1c 0x5050) (Reg.operands [.gpr 0] [])) #v[198]
    (.letOp (n := 202) (.out 0x105a21 (xorR32R32Effect 0x105a21 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[192, 200]
    (.letOp (n := 203) (.exec 0x105a21 (fun s => s.RIP = 0x105a21) (xorR32R32Effect 0x105a21 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[192, 200]
    (.letOp (n := 204) (.out 0x105a23 (addR32R32Effect 0x105a23 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[200, 200]
    (.letOp (n := 205) (.exec 0x105a23 (fun s => s.RIP = 0x105a23) (addR32R32Effect 0x105a23 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[200, 200]
    (.letOp (n := 206) (.out 0x105a25 (xorR32R32Effect 0x105a25 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[204, 202]
    (.letOp (n := 207) (.exec 0x105a25 (fun s => s.RIP = 0x105a25) (xorR32R32Effect 0x105a25 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[204, 202]
    (b_l10593a_4)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_3 : List UInt8 :=
  [0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x22,
    0x0F, 0xB7, 0x44, 0x24, 0x24, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25,
    0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8] ++ bytes_l10593a_4

theorem code_l10593a_3 : ∀ x ∈ codeRange 0x1059ed bytes_l10593a_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x59ed 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_4

def b_l10593a_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x1059b6 (xorR32R32Effect 0x1059b6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[128, 126]
    (.letOp (n := 131) (.exec 0x1059b6 (fun s => s.RIP = 0x1059b6) (xorR32R32Effect 0x1059b6 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[128, 126]
    (.letOp (n := 132) (.out 0x1059b8 (movR32R32Effect 0x1059b8 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[130]
    (.letOp (n := 133) (.exec 0x1059b8 (fun s => s.RIP = 0x1059b8) (movR32R32Effect 0x1059b8 2 0 1) (Reg.operands [.gpr 1] [])) #v[130]
    (.letOp (n := 134) (.out 0x1059ba (shrR32Effect 0x1059ba 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[132]
    (.letOp (n := 135) (.exec 0x1059ba (fun s => s.RIP = 0x1059ba) (shrR32Effect 0x1059ba 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[132]
    (.letOp (n := 136) (.out 0x1059bc (xorR32R32Effect 0x1059bc 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[134, 130]
    (.letOp (n := 137) (.exec 0x1059bc (fun s => s.RIP = 0x1059bc) (xorR32R32Effect 0x1059bc 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[134, 130]
    (.letOp (n := 138) (.out 0x1059be (andEaxImm32Effect 0x1059be 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[136]
    (.letOp (n := 139) (.exec 0x1059be (fun s => s.RIP = 0x1059be) (andEaxImm32Effect 0x1059be 0x5050) (Reg.operands [.gpr 0] [])) #v[136]
    (.letOp (n := 140) (.out 0x1059c3 (xorR32R32Effect 0x1059c3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[130, 138]
    (.letOp (n := 141) (.exec 0x1059c3 (fun s => s.RIP = 0x1059c3) (xorR32R32Effect 0x1059c3 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[130, 138]
    (.letOp (n := 142) (.out 0x1059c5 (addR32R32Effect 0x1059c5 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[138, 138]
    (.letOp (n := 143) (.exec 0x1059c5 (fun s => s.RIP = 0x1059c5) (addR32R32Effect 0x1059c5 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[138, 138]
    (.letOp (n := 144) (.out 0x1059c7 (xorR32R32Effect 0x1059c7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[142, 140]
    (.letOp (n := 145) (.exec 0x1059c7 (fun s => s.RIP = 0x1059c7) (xorR32R32Effect 0x1059c7 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[142, 140]
    (.letOp (n := 146) (.exec 0x1059c9 (StorePre 0x1059c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1059c9 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1059c9 5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[144, 4]
    (.letOp (n := 147) (.out 0x1059ce (movzxR32M16Effect 0x1059ce 5 0 (.sib 4 none 0 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 148) (.exec 0x1059ce (LoadPre 0x1059ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x22)) s (0x1059ce + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1059ce 5 0 (.sib 4 none 0 (.d8 0x22))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 149) (.out 0x1059d3 (movR32R32Effect 0x1059d3 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[147]
    (.letOp (n := 150) (.exec 0x1059d3 (fun s => s.RIP = 0x1059d3) (movR32R32Effect 0x1059d3 2 1 0) (Reg.operands [.gpr 0] [])) #v[147]
    (.letOp (n := 151) (.out 0x1059d5 (shrR32Effect 0x1059d5 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[149]
    (.letOp (n := 152) (.exec 0x1059d5 (fun s => s.RIP = 0x1059d5) (shrR32Effect 0x1059d5 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 153) (.out 0x1059d8 (xorR32R32Effect 0x1059d8 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[151, 147]
    (.letOp (n := 154) (.exec 0x1059d8 (fun s => s.RIP = 0x1059d8) (xorR32R32Effect 0x1059d8 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[151, 147]
    (.letOp (n := 155) (.out 0x1059da (andR32Imm32Effect 0x1059da 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[153]
    (.letOp (n := 156) (.exec 0x1059da (fun s => s.RIP = 0x1059da) (andR32Imm32Effect 0x1059da 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[153]
    (.letOp (n := 157) (.out 0x1059e0 (xorR32R32Effect 0x1059e0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[147, 155]
    (.letOp (n := 158) (.exec 0x1059e0 (fun s => s.RIP = 0x1059e0) (xorR32R32Effect 0x1059e0 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[147, 155]
    (.letOp (n := 159) (.out 0x1059e2 (shlR32Effect 0x1059e2 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[155]
    (.letOp (n := 160) (.exec 0x1059e2 (fun s => s.RIP = 0x1059e2) (shlR32Effect 0x1059e2 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[155]
    (.letOp (n := 161) (.out 0x1059e5 (xorR32R32Effect 0x1059e5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[159, 157]
    (.letOp (n := 162) (.exec 0x1059e5 (fun s => s.RIP = 0x1059e5) (xorR32R32Effect 0x1059e5 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[159, 157]
    (.letOp (n := 163) (.out 0x1059e7 (movR32R32Effect 0x1059e7 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[161]
    (.letOp (n := 164) (.exec 0x1059e7 (fun s => s.RIP = 0x1059e7) (movR32R32Effect 0x1059e7 2 0 1) (Reg.operands [.gpr 1] [])) #v[161]
    (.letOp (n := 165) (.out 0x1059e9 (shrR32Effect 0x1059e9 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[163]
    (.letOp (n := 166) (.exec 0x1059e9 (fun s => s.RIP = 0x1059e9) (shrR32Effect 0x1059e9 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[163]
    (.letOp (n := 167) (.out 0x1059eb (xorR32R32Effect 0x1059eb 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[165, 161]
    (.letOp (n := 168) (.exec 0x1059eb (fun s => s.RIP = 0x1059eb) (xorR32R32Effect 0x1059eb 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[165, 161]
    (b_l10593a_3)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_2 : List UInt8 :=
  [0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01,
    0xC0, 0x31, 0xC8, 0x66, 0x89, 0x44, 0x24, 0x20, 0x0F, 0xB7, 0x44, 0x24, 0x22, 0x89, 0xC1, 0xC1,
    0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31,
    0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8] ++ bytes_l10593a_3

theorem code_l10593a_2 : ∀ x ∈ codeRange 0x1059b6 bytes_l10593a_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x59b6 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_3

def b_l10593a_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x10597a (xorR32R32Effect 0x10597a 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[89, 85]
    (.letOp (n := 92) (.exec 0x10597a (fun s => s.RIP = 0x10597a) (xorR32R32Effect 0x10597a 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[89, 85]
    (.letOp (n := 93) (.out 0x10597c (andR32Imm32Effect 0x10597c 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 94) (.exec 0x10597c (fun s => s.RIP = 0x10597c) (andR32Imm32Effect 0x10597c 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[91]
    (.letOp (n := 95) (.out 0x105982 (xorR32R32Effect 0x105982 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[85, 93]
    (.letOp (n := 96) (.exec 0x105982 (fun s => s.RIP = 0x105982) (xorR32R32Effect 0x105982 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[85, 93]
    (.letOp (n := 97) (.out 0x105984 (shlR32Effect 0x105984 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[93]
    (.letOp (n := 98) (.exec 0x105984 (fun s => s.RIP = 0x105984) (shlR32Effect 0x105984 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 99) (.out 0x105987 (xorR32R32Effect 0x105987 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[97, 95]
    (.letOp (n := 100) (.exec 0x105987 (fun s => s.RIP = 0x105987) (xorR32R32Effect 0x105987 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[97, 95]
    (.letOp (n := 101) (.out 0x105989 (movR32R32Effect 0x105989 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[99]
    (.letOp (n := 102) (.exec 0x105989 (fun s => s.RIP = 0x105989) (movR32R32Effect 0x105989 2 0 1) (Reg.operands [.gpr 1] [])) #v[99]
    (.letOp (n := 103) (.out 0x10598b (shrR32Effect 0x10598b 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[101]
    (.letOp (n := 104) (.exec 0x10598b (fun s => s.RIP = 0x10598b) (shrR32Effect 0x10598b 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[101]
    (.letOp (n := 105) (.out 0x10598d (xorR32R32Effect 0x10598d 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[103, 99]
    (.letOp (n := 106) (.exec 0x10598d (fun s => s.RIP = 0x10598d) (xorR32R32Effect 0x10598d 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[103, 99]
    (.letOp (n := 107) (.out 0x10598f (andEaxImm32Effect 0x10598f 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 108) (.exec 0x10598f (fun s => s.RIP = 0x10598f) (andEaxImm32Effect 0x10598f 0x5050) (Reg.operands [.gpr 0] [])) #v[105]
    (.letOp (n := 109) (.out 0x105994 (xorR32R32Effect 0x105994 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[99, 107]
    (.letOp (n := 110) (.exec 0x105994 (fun s => s.RIP = 0x105994) (xorR32R32Effect 0x105994 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[99, 107]
    (.letOp (n := 111) (.out 0x105996 (addR32R32Effect 0x105996 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[107, 107]
    (.letOp (n := 112) (.exec 0x105996 (fun s => s.RIP = 0x105996) (addR32R32Effect 0x105996 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[107, 107]
    (.letOp (n := 113) (.out 0x105998 (xorR32R32Effect 0x105998 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x105998 (fun s => s.RIP = 0x105998) (xorR32R32Effect 0x105998 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[111, 109]
    (.letOp (n := 115) (.exec 0x10599a (StorePre 0x10599a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x10599a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10599a 5 0 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[113, 4]
    (.letOp (n := 116) (.out 0x10599f (movzxR32M16Effect 0x10599f 5 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 117) (.exec 0x10599f (LoadPre 0x10599f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10599f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10599f 5 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 118) (.out 0x1059a4 (movR32R32Effect 0x1059a4 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[116]
    (.letOp (n := 119) (.exec 0x1059a4 (fun s => s.RIP = 0x1059a4) (movR32R32Effect 0x1059a4 2 1 0) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 120) (.out 0x1059a6 (shrR32Effect 0x1059a6 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[118]
    (.letOp (n := 121) (.exec 0x1059a6 (fun s => s.RIP = 0x1059a6) (shrR32Effect 0x1059a6 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[118]
    (.letOp (n := 122) (.out 0x1059a9 (xorR32R32Effect 0x1059a9 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[120, 116]
    (.letOp (n := 123) (.exec 0x1059a9 (fun s => s.RIP = 0x1059a9) (xorR32R32Effect 0x1059a9 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[120, 116]
    (.letOp (n := 124) (.out 0x1059ab (andR32Imm32Effect 0x1059ab 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[122]
    (.letOp (n := 125) (.exec 0x1059ab (fun s => s.RIP = 0x1059ab) (andR32Imm32Effect 0x1059ab 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[122]
    (.letOp (n := 126) (.out 0x1059b1 (xorR32R32Effect 0x1059b1 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[116, 124]
    (.letOp (n := 127) (.exec 0x1059b1 (fun s => s.RIP = 0x1059b1) (xorR32R32Effect 0x1059b1 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[116, 124]
    (.letOp (n := 128) (.out 0x1059b3 (shlR32Effect 0x1059b3 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[124]
    (.letOp (n := 129) (.exec 0x1059b3 (fun s => s.RIP = 0x1059b3) (shlR32Effect 0x1059b3 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[124]
    (b_l10593a_2)))))))))))))))))))))))))))))))))))))))

def bytes_l10593a_1 : List UInt8 :=
  [0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89,
    0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25, 0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8,
    0x66, 0x89, 0x44, 0x24, 0x1E, 0x0F, 0xB7, 0x44, 0x24, 0x20, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31,
    0xC1, 0x81, 0xE1, 0x20, 0x13, 0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02] ++ bytes_l10593a_2

theorem code_l10593a_1 : ∀ x ∈ codeRange 0x10597a bytes_l10593a_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x597a 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_2

def b_l10593a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10593a (movzxR32M16Effect 0x10593a 5 0 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10593a (LoadPre 0x10593a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10593a + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x10593a 5 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10593f (movR32R32Effect 0x10593f 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 56) (.exec 0x10593f (fun s => s.RIP = 0x10593f) (movR32R32Effect 0x10593f 2 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x105941 (shrR32Effect 0x105941 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x105941 (fun s => s.RIP = 0x105941) (shrR32Effect 0x105941 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x105944 (xorR32R32Effect 0x105944 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x105944 (fun s => s.RIP = 0x105944) (xorR32R32Effect 0x105944 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x105946 (andR32Imm32Effect 0x105946 6 1 0x1320) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x105946 (fun s => s.RIP = 0x105946) (andR32Imm32Effect 0x105946 6 1 0x1320) (Reg.operands [.gpr 1] [])) #v[59]
    (.letOp (n := 63) (.out 0x10594c (xorR32R32Effect 0x10594c 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[53, 61]
    (.letOp (n := 64) (.exec 0x10594c (fun s => s.RIP = 0x10594c) (xorR32R32Effect 0x10594c 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[53, 61]
    (.letOp (n := 65) (.out 0x10594e (shlR32Effect 0x10594e 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 66) (.exec 0x10594e (fun s => s.RIP = 0x10594e) (shlR32Effect 0x10594e 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 67) (.out 0x105951 (xorR32R32Effect 0x105951 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x105951 (fun s => s.RIP = 0x105951) (xorR32R32Effect 0x105951 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x105953 (movR32R32Effect 0x105953 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x105953 (fun s => s.RIP = 0x105953) (movR32R32Effect 0x105953 2 0 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 71) (.out 0x105955 (shrR32Effect 0x105955 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 72) (.exec 0x105955 (fun s => s.RIP = 0x105955) (shrR32Effect 0x105955 2 0 1) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x105957 (xorR32R32Effect 0x105957 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x105957 (fun s => s.RIP = 0x105957) (xorR32R32Effect 0x105957 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x105959 (andEaxImm32Effect 0x105959 0x5050) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[73]
    (.letOp (n := 76) (.exec 0x105959 (fun s => s.RIP = 0x105959) (andEaxImm32Effect 0x105959 0x5050) (Reg.operands [.gpr 0] [])) #v[73]
    (.letOp (n := 77) (.out 0x10595e (xorR32R32Effect 0x10595e 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[67, 75]
    (.letOp (n := 78) (.exec 0x10595e (fun s => s.RIP = 0x10595e) (xorR32R32Effect 0x10595e 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 75]
    (.letOp (n := 79) (.out 0x105960 (addR32R32Effect 0x105960 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[75, 75]
    (.letOp (n := 80) (.exec 0x105960 (fun s => s.RIP = 0x105960) (addR32R32Effect 0x105960 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[75, 75]
    (.letOp (n := 81) (.out 0x105962 (xorR32R32Effect 0x105962 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x105962 (fun s => s.RIP = 0x105962) (xorR32R32Effect 0x105962 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[79, 77]
    (.letOp (n := 83) (.exec 0x105964 (StorePre 0x105964 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x11c)) s (0x105964 + BitVec.ofNat 64 7)) 4) (movM32R32LowEffect 0x105964 0 (.sib 4 none 0 (.d32 0x11c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.exec 0x10596b (StorePre 0x10596b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x10596b + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x10596b 5 0 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 85) (.out 0x105970 (movzxR32M16Effect 0x105970 5 0 (.sib 4 none 0 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 86) (.exec 0x105970 (LoadPre 0x105970 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x105970 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x105970 5 0 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x105975 (movR32R32Effect 0x105975 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[85]
    (.letOp (n := 88) (.exec 0x105975 (fun s => s.RIP = 0x105975) (movR32R32Effect 0x105975 2 1 0) (Reg.operands [.gpr 0] [])) #v[85]
    (.letOp (n := 89) (.out 0x105977 (shrR32Effect 0x105977 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[87]
    (.letOp (n := 90) (.exec 0x105977 (fun s => s.RIP = 0x105977) (shrR32Effect 0x105977 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (b_l10593a_1))))))))))))))))))))))))))))))))))))))

def bytes_l10593a : List UInt8 :=
  [0x0F, 0xB7, 0x44, 0x24, 0x1C, 0x89, 0xC1, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x20, 0x13,
    0x00, 0x00, 0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x89, 0xC8, 0xD1, 0xE8, 0x31, 0xC8, 0x25,
    0x50, 0x50, 0x00, 0x00, 0x31, 0xC1, 0x01, 0xC0, 0x31, 0xC8, 0x89, 0x84, 0x24, 0x1C, 0x01, 0x00,
    0x00, 0x66, 0x89, 0x44, 0x24, 0x1C, 0x0F, 0xB7, 0x44, 0x24, 0x1E, 0x89, 0xC1, 0xC1, 0xE9, 0x02] ++ bytes_l10593a_1

theorem code_l10593a : ∀ x ∈ codeRange 0x10593a bytes_l10593a, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x593a 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10593a_1

@[cfg_block] def b_l10693d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10693d (movR64R64Effect 0x10693d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10693d (fun s => s.RIP = 0x10693d) (movR64R64Effect 0x10693d 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x106940 (addR64Imm32Effect 0x106940 4 0x138) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106940 (fun s => s.RIP = 0x106940) (addR64Imm32Effect 0x106940 4 0x138) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106947 (popR64Effect 0x106947 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x106947 (popR64Effect 0x106947 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x106947 (PopPre 0x106947) (popR64Effect 0x106947 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x106948 (popR64Effect 0x106948 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x106948 (popR64Effect 0x106948 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x106948 (PopPre 0x106948) (popR64Effect 0x106948 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10694a (popR64Effect 0x10694a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10694a (popR64Effect 0x10694a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10694a (PopPre 0x10694a) (popR64Effect 0x10694a 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10694c (popR64Effect 0x10694c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10694c (popR64Effect 0x10694c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10694c (PopPre 0x10694c) (popR64Effect 0x10694c 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10694e (popR64Effect 0x10694e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10694e (popR64Effect 0x10694e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10694e (PopPre 0x10694e) (popR64Effect 0x10694e 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x106950 (popR64Effect 0x106950 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x106950 (popR64Effect 0x106950 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x106950 (PopPre 0x106950) (popR64Effect 0x106950 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x106951 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x106951 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x106951 (RetPre 0x106951) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10693d : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x38, 0x01, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10693d : ∀ x ∈ codeRange 0x10693d bytes_l10693d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x693d 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106960 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106960 (pushR64Effect 0x106960 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x106960 (PushPre 0x106960 1) (pushR64Effect 0x106960 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x106961 (pushR64Effect 0x106961 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x106961 (PushPre 0x106961 2) (pushR64Effect 0x106961 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x106963 (pushR64Effect 0x106963 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x106963 (PushPre 0x106963 2) (pushR64Effect 0x106963 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x106965 (pushR64Effect 0x106965 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x106965 (PushPre 0x106965 2) (pushR64Effect 0x106965 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x106967 (pushR64Effect 0x106967 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x106967 (PushPre 0x106967 2) (pushR64Effect 0x106967 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x106969 (pushR64Effect 0x106969 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x106969 (PushPre 0x106969 1) (pushR64Effect 0x106969 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10696a (subR64Imm8Effect 0x10696a 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10696a (fun s => s.RIP = 0x10696a) (subR64Imm8Effect 0x10696a 4 0x48) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10696e (movR64R64Effect 0x10696e 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x10696e (fun s => s.RIP = 0x10696e) (movR64R64Effect 0x10696e 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.exec 0x106971 (StorePre 0x106971 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x106971 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106971 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 70) (.exec 0x106976 (StorePre 0x106976 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106976 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x106976 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 71) (.exec 0x10697f (StorePre 0x10697f 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10697f + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10697f (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 72) (.out 0x106988 (leaR64Effect 0x106988 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 73) (.exec 0x106988 (fun s => s.RIP = 0x106988) (leaR64Effect 0x106988 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 74) (.out 0x10698d (movR32Imm32Effect 0x10698d 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 75) (.exec 0x10698d (fun s => s.RIP = 0x10698d) (movR32Imm32Effect 0x10698d 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x106992 (callEffect (fun _ => 0x109ff0) 0x106997) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 77) (.exec 0x106992 (PushPre 0x106992 5) (callEffect (fun _ => 0x109ff0) 0x106997) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 78) (.const ⟨64, 0x106997⟩) #v[]
    (.terminate (.call ⟨.l109ff0, RegMap.args [(2, 2), (3, 67), (4, 76), (5, 5), (6, 74), (7, 72), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 79⟩ { target := .l106997, kept := #v[], arity := rfl, guard := some (Fin.last 78) })))))))))))))))))))))))))))

def bytes_l106960 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x48, 0x48, 0x89,
    0xF3, 0x48, 0x89, 0x7C, 0x24, 0x40, 0x48, 0xC7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xBE, 0x08, 0x00,
    0x00, 0x00, 0xE8, 0x59, 0x36, 0x00, 0x00]

theorem code_l106960 : ∀ x ∈ codeRange 0x106960 bytes_l106960, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6960 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106997 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106997 (movzxR32M16Effect 0x106997 3 0 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x106997 (LoadPre 0x106997 (fun s => AddrMode.addr (.base 3 .none) s (0x106997 + BitVec.ofNat 64 3)) 2) (movzxR32M16Effect 0x106997 3 0 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.exec 0x10699a (StorePre 0x10699a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10699a + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10699a 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x10699f (movzxR32M16Effect 0x10699f 4 0 (.base 3 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 57) (.exec 0x10699f (LoadPre 0x10699f (fun s => AddrMode.addr (.base 3 (.d8 0x2)) s (0x10699f + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x10699f 4 0 (.base 3 (.d8 0x2))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 58) (.exec 0x1069a3 (StorePre 0x1069a3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x1069a3 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069a3 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1069a8 (movzxR32M16Effect 0x1069a8 4 0 (.base 3 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 60) (.exec 0x1069a8 (LoadPre 0x1069a8 (fun s => AddrMode.addr (.base 3 (.d8 0x4)) s (0x1069a8 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069a8 4 0 (.base 3 (.d8 0x4))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 61) (.exec 0x1069ac (StorePre 0x1069ac 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x1069ac + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069ac 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1069b1 (movzxR32M16Effect 0x1069b1 4 0 (.base 3 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 63) (.exec 0x1069b1 (LoadPre 0x1069b1 (fun s => AddrMode.addr (.base 3 (.d8 0x6)) s (0x1069b1 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069b1 4 0 (.base 3 (.d8 0x6))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.exec 0x1069b5 (StorePre 0x1069b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x1069b5 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069b5 5 16 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1069ba (movzxR32M16Effect 0x1069ba 4 0 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 66) (.exec 0x1069ba (LoadPre 0x1069ba (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x1069ba + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069ba 4 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 67) (.exec 0x1069be (StorePre 0x1069be 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1069be + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069be 5 16 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1069c3 (movzxR32M16Effect 0x1069c3 4 0 (.base 3 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 69) (.exec 0x1069c3 (LoadPre 0x1069c3 (fun s => AddrMode.addr (.base 3 (.d8 0xa)) s (0x1069c3 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069c3 4 0 (.base 3 (.d8 0xa))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 70) (.exec 0x1069c7 (StorePre 0x1069c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x1069c7 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069c7 5 16 0 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.exec 0x1069cc (StorePre 0x1069cc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1069cc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1069cc 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[3, 4]
    (.letOp (n := 72) (.out 0x1069d1 (movzxR32M16Effect 0x1069d1 4 0 (.base 3 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 73) (.exec 0x1069d1 (LoadPre 0x1069d1 (fun s => AddrMode.addr (.base 3 (.d8 0xc)) s (0x1069d1 + BitVec.ofNat 64 4)) 2) (movzxR32M16Effect 0x1069d1 4 0 (.base 3 (.d8 0xc))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 74) (.exec 0x1069d5 (StorePre 0x1069d5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x1069d5 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x1069d5 5 16 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 75) (.out 0x1069da (movR32Imm32Effect 0x1069da 6 12 0x7) (EffectPart.reads (.reg (.gpr 12)) [] []) (.reg (.gpr 12))) #v[]
    (.letOp (n := 76) (.exec 0x1069da (fun s => s.RIP = 0x1069da) (movR32Imm32Effect 0x1069da 6 12 0x7) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x1069e0 (movzxR32M16Effect 0x1069e0 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 78) (.exec 0x1069e0 (LoadPre 0x1069e0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1069e0 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x1069e0 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 79) (.exec 0x1069e5 (fun s => s.RIP = 0x1069e5) (fun _ => nopEffect 0x1069e5 11) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l1069f0, RegMap.args [(0, 77), (3, 3), (4, 4), (5, 5), (12, 75), (13, 13), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l106997 : List UInt8 :=
  [0x0F, 0xB7, 0x03, 0x66, 0x31, 0x44, 0x24, 0x08, 0x0F, 0xB7, 0x43, 0x02, 0x66, 0x31, 0x44, 0x24,
    0x0A, 0x0F, 0xB7, 0x43, 0x04, 0x66, 0x31, 0x44, 0x24, 0x0C, 0x0F, 0xB7, 0x43, 0x06, 0x66, 0x31,
    0x44, 0x24, 0x0E, 0x0F, 0xB7, 0x43, 0x08, 0x66, 0x31, 0x44, 0x24, 0x10, 0x0F, 0xB7, 0x43, 0x0A,
    0x66, 0x31, 0x44, 0x24, 0x12, 0x48, 0x89, 0x5C, 0x24, 0x30, 0x0F, 0xB7, 0x43, 0x0C, 0x66, 0x31,
    0x44, 0x24, 0x14, 0x41, 0xBC, 0x07, 0x00, 0x00, 0x00, 0x0F, 0xB7, 0x44, 0x24, 0x16, 0x66, 0x66,
    0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l106997 : ∀ x ∈ codeRange 0x106997 bytes_l106997, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6997 89 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1069f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1069f0 (movR64M64Effect 0x1069f0 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 54) (.exec 0x1069f0 (LoadPre 0x1069f0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1069f0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1069f0 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x1069f5 (xorR16M16Effect 0x1069f5 5 0 (.sib 3 (some 12) 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[0, 53, 12]
    (.letOp (n := 56) (.exec 0x1069f5 (LoadPre 0x1069f5 (fun s => AddrMode.addr (.sib 3 (some 12) 1 .none) s (0x1069f5 + BitVec.ofNat 64 5)) 2) (xorR16M16Effect 0x1069f5 5 0 (.sib 3 (some 12) 1 .none)) (Reg.operands [.gpr 0, .gpr 3, .gpr 12] [])) #v[0, 53, 12]
    (.letOp (n := 57) (.exec 0x1069fa (StorePre 0x1069fa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x1069fa + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x1069fa 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x1069ff (movR32Imm32Effect 0x1069ff 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 59) (.exec 0x1069ff (fun s => s.RIP = 0x1069ff) (movR32Imm32Effect 0x1069ff 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x106a04 (leaR64Effect 0x106a04 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 61) (.exec 0x106a04 (fun s => s.RIP = 0x106a04) (leaR64Effect 0x106a04 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x106a09 (movR64R64Effect 0x106a09 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[60]
    (.letOp (n := 63) (.exec 0x106a09 (fun s => s.RIP = 0x106a09) (movR64R64Effect 0x106a09 7 14) (Reg.operands [.gpr 14] [])) #v[60]
    (.letOp (n := 64) (.out 0x106a0c (callEffect (fun _ => 0x100b10) 0x106a11) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 65) (.exec 0x106a0c (PushPre 0x106a0c 5) (callEffect (fun _ => 0x100b10) 0x106a11) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.const ⟨64, 0x106a11⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 55), (3, 53), (4, 64), (5, 5), (6, 58), (7, 62), (12, 12), (13, 13), (14, 60), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 67⟩ { target := .l106a11, kept := #v[], arity := rfl, guard := some (Fin.last 66) })))))))))))))))

def bytes_l1069f0 : List UInt8 :=
  [0x48, 0x8B, 0x5C, 0x24, 0x30, 0x66, 0x42, 0x33, 0x04, 0x63, 0x66, 0x89, 0x44, 0x24, 0x16, 0xBE,
    0x08, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xF7, 0xE8, 0xFF, 0xA0, 0xFF,
    0xFF]

theorem code_l1069f0 : ∀ x ∈ codeRange 0x1069f0 bytes_l1069f0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x69f0 33 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a11 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a11 (movR64R64Effect 0x106a11 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x106a11 (fun s => s.RIP = 0x106a11) (movR64R64Effect 0x106a11 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x106a14 (callEffect (fun _ => 0x100000) 0x106a19) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106a14 (PushPre 0x106a14 5) (callEffect (fun _ => 0x100000) 0x106a19) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x106a19⟩) #v[]
    (.terminate (.call ⟨.l100000, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l106a19, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l106a11 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0xE8, 0xE7, 0x95, 0xFF, 0xFF]

theorem code_l106a11 : ∀ x ∈ codeRange 0x106a11 bytes_l106a11, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a11 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a19_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.exec 0x106a8a (StorePre 0x106a8a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106a8a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a8a 5 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[85, 4]
    (.letOp (n := 88) (.out 0x106a8f (movzxR32M16Effect 0x106a8f 5 0 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 89) (.exec 0x106a8f (LoadPre 0x106a8f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106a8f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a8f 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 90) (.out 0x106a94 (xorR16M16Effect 0x106a94 6 0 (.sib 3 (some 12) 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[88, 3, 12]
    (.letOp (n := 91) (.exec 0x106a94 (LoadPre 0x106a94 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x10)) s (0x106a94 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a94 6 0 (.sib 3 (some 12) 1 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 3, .gpr 12] [])) #v[88, 3, 12]
    (.letOp (n := 92) (.exec 0x106a9a (StorePre 0x106a9a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106a9a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a9a 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[90, 4]
    (.letOp (n := 93) (.out 0x106a9f (cmpR64Imm8Effect 0x106a9f 12 0x67) (EffectPart.reads (.flag .ZF) [.gpr 12] []) (.flag .ZF)) #v[12]
    (.letOp (n := 94) (.exec 0x106a9f (fun s => s.RIP = 0x106a9f) (cmpR64Imm8Effect 0x106a9f 12 0x67) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 95) (.pure (condOp 4)) #v[93]
    (.terminate (.condBr (Fin.last 95) ⟨.l106ebc, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩ ⟨.l106aa9, RegMap.args [(0, 90), (1, 85), (2, 80), (3, 3), (4, 4), (5, 5), (6, 75), (7, 70), (8, 65), (9, 60), (10, 57), (12, 12), (13, 13), (14, 14), (15, 15), (19, 93), (22, 22), (39, 39), (50, 50), (51, 51)] 96⟩))))))))))

def bytes_l106a19_1 : List UInt8 :=
  [0x66, 0x89, 0x4C, 0x24, 0x14, 0x0F, 0xB7, 0x44, 0x24, 0x16, 0x66, 0x42, 0x33, 0x44, 0x63, 0x10,
    0x66, 0x89, 0x44, 0x24, 0x16, 0x49, 0x83, 0xFC, 0x67, 0x0F, 0x84, 0x13, 0x04, 0x00, 0x00]

theorem code_l106a19_1 : ∀ x ∈ codeRange 0x106a8a bytes_l106a19_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6a8a 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106a19 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106a19 (movzxR32M16Effect 0x106a19 6 10 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 54) (.exec 0x106a19 (LoadPre 0x106a19 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a19 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a19 6 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106a1f (movzxR32M16Effect 0x106a1f 6 9 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 56) (.exec 0x106a1f (LoadPre 0x106a1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106a1f + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a1f 6 9 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106a25 (xorR16M16Effect 0x106a25 6 10 (.sib 3 (some 12) 1 (.d8 0x2))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .gpr 12] []) (.reg (.gpr 10))) #v[53, 3, 12]
    (.letOp (n := 58) (.exec 0x106a25 (LoadPre 0x106a25 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2)) s (0x106a25 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a25 6 10 (.sib 3 (some 12) 1 (.d8 0x2))) (Reg.operands [.gpr 10, .gpr 3, .gpr 12] [])) #v[53, 3, 12]
    (.letOp (n := 59) (.exec 0x106a2b (StorePre 0x106a2b 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106a2b + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a2b 6 10 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[57, 4]
    (.letOp (n := 60) (.out 0x106a31 (xorR16M16Effect 0x106a31 6 9 (.sib 3 (some 12) 1 (.d8 0x4))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .gpr 12] []) (.reg (.gpr 9))) #v[55, 3, 12]
    (.letOp (n := 61) (.exec 0x106a31 (LoadPre 0x106a31 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x4)) s (0x106a31 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a31 6 9 (.sib 3 (some 12) 1 (.d8 0x4))) (Reg.operands [.gpr 9, .gpr 3, .gpr 12] [])) #v[55, 3, 12]
    (.letOp (n := 62) (.exec 0x106a37 (StorePre 0x106a37 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106a37 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a37 6 9 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 63) (.out 0x106a3d (movzxR32M16Effect 0x106a3d 6 8 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 64) (.exec 0x106a3d (LoadPre 0x106a3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a3d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106a3d 6 8 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x106a43 (xorR16M16Effect 0x106a43 6 8 (.sib 3 (some 12) 1 (.d8 0x6))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[63, 3, 12]
    (.letOp (n := 66) (.exec 0x106a43 (LoadPre 0x106a43 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x6)) s (0x106a43 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a43 6 8 (.sib 3 (some 12) 1 (.d8 0x6))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[63, 3, 12]
    (.letOp (n := 67) (.exec 0x106a49 (StorePre 0x106a49 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106a49 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106a49 6 8 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x106a4f (movzxR32M16Effect 0x106a4f 5 7 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 69) (.exec 0x106a4f (LoadPre 0x106a4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106a4f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a4f 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x106a54 (xorR16M16Effect 0x106a54 6 7 (.sib 3 (some 12) 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .gpr 12] []) (.reg (.gpr 7))) #v[68, 3, 12]
    (.letOp (n := 71) (.exec 0x106a54 (LoadPre 0x106a54 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x8)) s (0x106a54 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a54 6 7 (.sib 3 (some 12) 1 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 3, .gpr 12] [])) #v[68, 3, 12]
    (.letOp (n := 72) (.exec 0x106a5a (StorePre 0x106a5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106a5a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a5a 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x106a5f (movzxR32M16Effect 0x106a5f 5 6 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 74) (.exec 0x106a5f (LoadPre 0x106a5f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a5f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a5f 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 75) (.out 0x106a64 (xorR16M16Effect 0x106a64 6 6 (.sib 3 (some 12) 1 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3, .gpr 12] []) (.reg (.gpr 6))) #v[73, 3, 12]
    (.letOp (n := 76) (.exec 0x106a64 (LoadPre 0x106a64 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xa)) s (0x106a64 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a64 6 6 (.sib 3 (some 12) 1 (.d8 0xa))) (Reg.operands [.gpr 6, .gpr 3, .gpr 12] [])) #v[73, 3, 12]
    (.letOp (n := 77) (.exec 0x106a6a (StorePre 0x106a6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106a6a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a6a 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 78) (.out 0x106a6f (movzxR32M16Effect 0x106a6f 5 2 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 79) (.exec 0x106a6f (LoadPre 0x106a6f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106a6f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a6f 5 2 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 80) (.out 0x106a74 (xorR16M16Effect 0x106a74 6 2 (.sib 3 (some 12) 1 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[78, 3, 12]
    (.letOp (n := 81) (.exec 0x106a74 (LoadPre 0x106a74 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xc)) s (0x106a74 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a74 6 2 (.sib 3 (some 12) 1 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[78, 3, 12]
    (.letOp (n := 82) (.exec 0x106a7a (StorePre 0x106a7a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106a7a + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106a7a 5 2 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x106a7f (movzxR32M16Effect 0x106a7f 5 1 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 84) (.exec 0x106a7f (LoadPre 0x106a7f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106a7f + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106a7f 5 1 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x106a84 (xorR16M16Effect 0x106a84 6 1 (.sib 3 (some 12) 1 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[83, 3, 12]
    (.letOp (n := 86) (.exec 0x106a84 (LoadPre 0x106a84 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0xe)) s (0x106a84 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106a84 6 1 (.sib 3 (some 12) 1 (.d8 0xe))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[83, 3, 12]
    (b_l106a19_1))))))))))))))))))))))))))))))))))

def bytes_l106a19 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x54, 0x24, 0x08, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x0A, 0x66, 0x46, 0x33, 0x54,
    0x63, 0x02, 0x66, 0x44, 0x89, 0x54, 0x24, 0x08, 0x66, 0x46, 0x33, 0x4C, 0x63, 0x04, 0x66, 0x44,
    0x89, 0x4C, 0x24, 0x0A, 0x44, 0x0F, 0xB7, 0x44, 0x24, 0x0C, 0x66, 0x46, 0x33, 0x44, 0x63, 0x06,
    0x66, 0x44, 0x89, 0x44, 0x24, 0x0C, 0x0F, 0xB7, 0x7C, 0x24, 0x0E, 0x66, 0x42, 0x33, 0x7C, 0x63,
    0x08, 0x66, 0x89, 0x7C, 0x24, 0x0E, 0x0F, 0xB7, 0x74, 0x24, 0x10, 0x66, 0x42, 0x33, 0x74, 0x63,
    0x0A, 0x66, 0x89, 0x74, 0x24, 0x10, 0x0F, 0xB7, 0x54, 0x24, 0x12, 0x66, 0x42, 0x33, 0x54, 0x63,
    0x0C, 0x66, 0x89, 0x54, 0x24, 0x12, 0x0F, 0xB7, 0x4C, 0x24, 0x14, 0x66, 0x42, 0x33, 0x4C, 0x63,
    0x0E] ++ bytes_l106a19_1

theorem code_l106a19 : ∀ x ∈ codeRange 0x106a19 bytes_l106a19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6a19 113 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106a19_1

@[cfg_block] def b_l106aa9 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106aa9 (movR32Imm32Effect 0x106aa9 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 54) (.exec 0x106aa9 (fun s => s.RIP = 0x106aa9) (movR32Imm32Effect 0x106aa9 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x106aae (leaR64Effect 0x106aae 7 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106aae (fun s => s.RIP = 0x106aae) (leaR64Effect 0x106aae 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106ab3 (callEffect (fun _ => 0x100b10) 0x106ab8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x106ab3 (PushPre 0x106ab3 5) (callEffect (fun _ => 0x100b10) 0x106ab8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x106ab8⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 53), (7, 55), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l106ab8, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l106aa9 : List UInt8 :=
  [0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x7C, 0x24, 0x08, 0xE8, 0x58, 0xA0, 0xFF, 0xFF]

theorem code_l106aa9 : ∀ x ∈ codeRange 0x106aa9 bytes_l106aa9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6aa9 15 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ab8_6 : Block Op Label signature Reg.count 283 :=
  .letOp (n := 283) (.out 0x106c9d (movR32M32LowEffect 0x106c9d 2 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 284) (.exec 0x106c9d (LoadPre 0x106c9d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106c9d + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c9d 2 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 285) (.out 0x106ca1 (xorR32R32Effect 0x106ca1 3 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 11] []) (.reg (.gpr 2))) #v[283, 165]
    (.letOp (n := 286) (.exec 0x106ca1 (fun s => s.RIP = 0x106ca1) (xorR32R32Effect 0x106ca1 3 2 11) (Reg.operands [.gpr 2, .gpr 11] [])) #v[283, 165]
    (.letOp (n := 287) (.out 0x106ca4 (xorR32R32Effect 0x106ca4 3 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[270, 165]
    (.letOp (n := 288) (.exec 0x106ca4 (fun s => s.RIP = 0x106ca4) (xorR32R32Effect 0x106ca4 3 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[270, 165]
    (.letOp (n := 289) (.out 0x106ca7 (movR32R32Effect 0x106ca7 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 290) (.exec 0x106ca7 (fun s => s.RIP = 0x106ca7) (movR32R32Effect 0x106ca7 2 1 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 291) (.out 0x106ca9 (rolR16Effect 0x106ca9 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[289]
    (.letOp (n := 292) (.exec 0x106ca9 (fun s => s.RIP = 0x106ca9) (rolR16Effect 0x106ca9 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[289]
    (.letOp (n := 293) (.out 0x106cad (xorR16M16Effect 0x106cad 6 1 (.sib 3 (some 12) 1 (.d8 0x1e))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[291, 191, 12]
    (.letOp (n := 294) (.exec 0x106cad (LoadPre 0x106cad (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1e)) s (0x106cad + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106cad 6 1 (.sib 3 (some 12) 1 (.d8 0x1e))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[291, 191, 12]
    (.letOp (n := 295) (.out 0x106cb3 (xorR32R32Effect 0x106cb3 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[287, 293]
    (.letOp (n := 296) (.exec 0x106cb3 (fun s => s.RIP = 0x106cb3) (xorR32R32Effect 0x106cb3 2 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[287, 293]
    (.letOp (n := 297) (.exec 0x106cb5 (StorePre 0x106cb5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106cb5 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106cb5 5 6 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[295, 4]
    (.letOp (n := 298) (.out 0x106cba (movR32R32Effect 0x106cba 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[285]
    (.letOp (n := 299) (.exec 0x106cba (fun s => s.RIP = 0x106cba) (movR32R32Effect 0x106cba 2 1 2) (Reg.operands [.gpr 2] [])) #v[285]
    (.letOp (n := 300) (.out 0x106cbc (xorR32R32Effect 0x106cbc 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[298, 181]
    (.letOp (n := 301) (.exec 0x106cbc (fun s => s.RIP = 0x106cbc) (xorR32R32Effect 0x106cbc 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[298, 181]
    (.letOp (n := 302) (.out 0x106cbe (rolR16Effect 0x106cbe 5 14 8) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[185]
    (.letOp (n := 303) (.exec 0x106cbe (fun s => s.RIP = 0x106cbe) (rolR16Effect 0x106cbe 5 14 8) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[185]
    (.letOp (n := 304) (.out 0x106cc3 (xorR16M16Effect 0x106cc3 6 14 (.sib 3 (some 12) 1 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3, .gpr 12] []) (.reg (.gpr 14))) #v[302, 191, 12]
    (.letOp (n := 305) (.exec 0x106cc3 (LoadPre 0x106cc3 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x20)) s (0x106cc3 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106cc3 6 14 (.sib 3 (some 12) 1 (.d8 0x20))) (Reg.operands [.gpr 14, .gpr 3, .gpr 12] [])) #v[302, 191, 12]
    (.letOp (n := 306) (.out 0x106cc9 (xorR32R32Effect 0x106cc9 3 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[300, 304]
    (.letOp (n := 307) (.exec 0x106cc9 (fun s => s.RIP = 0x106cc9) (xorR32R32Effect 0x106cc9 3 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[300, 304]
    (.letOp (n := 308) (.exec 0x106ccc (StorePre 0x106ccc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106ccc + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106ccc 5 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[306, 4]
    (.letOp (n := 309) (.out 0x106cd1 (movR32Imm32Effect 0x106cd1 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 310) (.exec 0x106cd1 (fun s => s.RIP = 0x106cd1) (movR32Imm32Effect 0x106cd1 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 311) (.out 0x106cd6 (leaR64Effect 0x106cd6 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 312) (.exec 0x106cd6 (fun s => s.RIP = 0x106cd6) (leaR64Effect 0x106cd6 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 313) (.out 0x106cdb (movR64R64Effect 0x106cdb 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[311]
    (.letOp (n := 314) (.exec 0x106cdb (fun s => s.RIP = 0x106cdb) (movR64R64Effect 0x106cdb 7 14) (Reg.operands [.gpr 14] [])) #v[311]
    (.letOp (n := 315) (.out 0x106cde (callEffect (fun _ => 0x100b10) 0x106ce3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 316) (.exec 0x106cde (PushPre 0x106cde 5) (callEffect (fun _ => 0x100b10) 0x106ce3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 317) (.const ⟨64, 0x106ce3⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 181), (1, 306), (2, 285), (3, 191), (4, 315), (5, 197), (6, 309), (7, 313), (8, 263), (9, 212), (10, 193), (11, 165), (12, 12), (13, 134), (14, 311), (15, 259), (22, 22), (39, 39), (50, 50), (51, 51)] 318⟩ { target := .l106ce3, kept := #v[], arity := rfl, guard := some (Fin.last 317) }))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_6 : List UInt8 :=
  [0x8B, 0x54, 0x24, 0x24, 0x44, 0x31, 0xDA, 0x44, 0x31, 0xDE, 0x89, 0xD1, 0x66, 0xC1, 0xC1, 0x08,
    0x66, 0x42, 0x33, 0x4C, 0x63, 0x1E, 0x31, 0xCE, 0x66, 0x89, 0x74, 0x24, 0x14, 0x89, 0xD1, 0x31,
    0xC1, 0x66, 0x41, 0xC1, 0xC6, 0x08, 0x66, 0x46, 0x33, 0x74, 0x63, 0x20, 0x44, 0x31, 0xF1, 0x66,
    0x89, 0x4C, 0x24, 0x16, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x74, 0x24, 0x08, 0x4C, 0x89,
    0xF7, 0xE8, 0x2D, 0x9E, 0xFF, 0xFF]

theorem code_l106ab8_6 : ∀ x ∈ codeRange 0x106c9d bytes_l106ab8_6, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6c9d 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ab8_5 : Block Op Label signature Reg.count 246 :=
  .letOp (n := 246) (.exec 0x106c55 (StorePre 0x106c55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106c55 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c55 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[240, 4]
    (.letOp (n := 247) (.out 0x106c5a (movR32R32Effect 0x106c5a 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[244]
    (.letOp (n := 248) (.exec 0x106c5a (fun s => s.RIP = 0x106c5a) (movR32R32Effect 0x106c5a 2 2 1) (Reg.operands [.gpr 1] [])) #v[244]
    (.letOp (n := 249) (.out 0x106c5c (movR32R32Effect 0x106c5c 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 250) (.exec 0x106c5c (fun s => s.RIP = 0x106c5c) (movR32R32Effect 0x106c5c 2 7 1) (Reg.operands [.gpr 1] [])) #v[244]
    (.letOp (n := 251) (.out 0x106c5e (rolR16Effect 0x106c5e 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[247]
    (.letOp (n := 252) (.exec 0x106c5e (fun s => s.RIP = 0x106c5e) (rolR16Effect 0x106c5e 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[247]
    (.letOp (n := 253) (.out 0x106c62 (xorR32R32Effect 0x106c62 3 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[227, 134]
    (.letOp (n := 254) (.exec 0x106c62 (fun s => s.RIP = 0x106c62) (xorR32R32Effect 0x106c62 3 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[227, 134]
    (.letOp (n := 255) (.out 0x106c65 (xorR16M16Effect 0x106c65 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[251, 191, 12]
    (.letOp (n := 256) (.exec 0x106c65 (LoadPre 0x106c65 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1a)) s (0x106c65 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c65 6 2 (.sib 3 (some 12) 1 (.d8 0x1a))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[251, 191, 12]
    (.letOp (n := 257) (.out 0x106c6b (xorR32R32Effect 0x106c6b 3 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[253, 185]
    (.letOp (n := 258) (.exec 0x106c6b (fun s => s.RIP = 0x106c6b) (xorR32R32Effect 0x106c6b 3 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[253, 185]
    (.letOp (n := 259) (.out 0x106c6e (xorR32R32Effect 0x106c6e 3 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[257, 255]
    (.letOp (n := 260) (.exec 0x106c6e (fun s => s.RIP = 0x106c6e) (xorR32R32Effect 0x106c6e 3 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[257, 255]
    (.letOp (n := 261) (.out 0x106c71 (movR32M32LowEffect 0x106c71 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 262) (.exec 0x106c71 (LoadPre 0x106c71 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106c71 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c71 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 263) (.out 0x106c75 (movR32M32Effect 0x106c75 8 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 264) (.exec 0x106c75 (LoadPre 0x106c75 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106c75 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106c75 8 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 265) (.out 0x106c7a (xorR32R32Effect 0x106c7a 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[261, 263]
    (.letOp (n := 266) (.exec 0x106c7a (fun s => s.RIP = 0x106c7a) (xorR32R32Effect 0x106c7a 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[261, 263]
    (.letOp (n := 267) (.exec 0x106c7d (StorePre 0x106c7d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106c7d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106c7d 6 15 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[259, 4]
    (.letOp (n := 268) (.out 0x106c83 (movR32R32Effect 0x106c83 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[265]
    (.letOp (n := 269) (.exec 0x106c83 (fun s => s.RIP = 0x106c83) (movR32R32Effect 0x106c83 2 2 1) (Reg.operands [.gpr 1] [])) #v[265]
    (.letOp (n := 270) (.out 0x106c85 (movR32R32Effect 0x106c85 2 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[265]
    (.letOp (n := 271) (.exec 0x106c85 (fun s => s.RIP = 0x106c85) (movR32R32Effect 0x106c85 2 6 1) (Reg.operands [.gpr 1] [])) #v[265]
    (.letOp (n := 272) (.out 0x106c87 (rolR16Effect 0x106c87 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[268]
    (.letOp (n := 273) (.exec 0x106c87 (fun s => s.RIP = 0x106c87) (rolR16Effect 0x106c87 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[268]
    (.letOp (n := 274) (.out 0x106c8b (xorR16M16Effect 0x106c8b 6 2 (.sib 3 (some 12) 1 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[272, 191, 12]
    (.letOp (n := 275) (.exec 0x106c8b (LoadPre 0x106c8b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x1c)) s (0x106c8b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c8b 6 2 (.sib 3 (some 12) 1 (.d8 0x1c))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[272, 191, 12]
    (.letOp (n := 276) (.out 0x106c91 (movR32R32Effect 0x106c91 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[249]
    (.letOp (n := 277) (.exec 0x106c91 (fun s => s.RIP = 0x106c91) (movR32R32Effect 0x106c91 2 1 7) (Reg.operands [.gpr 7] [])) #v[249]
    (.letOp (n := 278) (.out 0x106c93 (xorR32R32Effect 0x106c93 3 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[276, 263]
    (.letOp (n := 279) (.exec 0x106c93 (fun s => s.RIP = 0x106c93) (xorR32R32Effect 0x106c93 3 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[276, 263]
    (.letOp (n := 280) (.out 0x106c96 (xorR32R32Effect 0x106c96 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[278, 274]
    (.letOp (n := 281) (.exec 0x106c96 (fun s => s.RIP = 0x106c96) (xorR32R32Effect 0x106c96 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[278, 274]
    (.letOp (n := 282) (.exec 0x106c98 (StorePre 0x106c98 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106c98 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c98 5 1 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[280, 4]
    (b_l106ab8_6)))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_5 : List UInt8 :=
  [0x66, 0x89, 0x7C, 0x24, 0x0E, 0x89, 0xCA, 0x89, 0xCF, 0x66, 0xC1, 0xC2, 0x08, 0x45, 0x31, 0xEF,
    0x66, 0x42, 0x33, 0x54, 0x63, 0x1A, 0x45, 0x31, 0xF7, 0x41, 0x31, 0xD7, 0x8B, 0x4C, 0x24, 0x20,
    0x44, 0x8B, 0x44, 0x24, 0x1C, 0x44, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x7C, 0x24, 0x10, 0x89, 0xCA,
    0x89, 0xCE, 0x66, 0xC1, 0xC2, 0x08, 0x66, 0x42, 0x33, 0x54, 0x63, 0x1C, 0x89, 0xF9, 0x44, 0x31,
    0xC1, 0x31, 0xD1, 0x66, 0x89, 0x4C, 0x24, 0x12] ++ bytes_l106ab8_6

theorem code_l106ab8_5 : ∀ x ∈ codeRange 0x106c55 bytes_l106ab8_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6c55 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_6

@[cfg_block] def b_l106ab8_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x106c0b (xorR16M16Effect 0x106c0b 6 8 (.sib 3 (some 12) 1 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[206, 191, 12]
    (.letOp (n := 209) (.exec 0x106c0b (LoadPre 0x106c0b (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x14)) s (0x106c0b + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c0b 6 8 (.sib 3 (some 12) 1 (.d8 0x14))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[206, 191, 12]
    (.letOp (n := 210) (.out 0x106c11 (xorR32R32Effect 0x106c11 3 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[202, 185]
    (.letOp (n := 211) (.exec 0x106c11 (fun s => s.RIP = 0x106c11) (xorR32R32Effect 0x106c11 3 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[202, 185]
    (.letOp (n := 212) (.out 0x106c14 (xorR32R32Effect 0x106c14 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[210, 208]
    (.letOp (n := 213) (.exec 0x106c14 (fun s => s.RIP = 0x106c14) (xorR32R32Effect 0x106c14 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[210, 208]
    (.letOp (n := 214) (.exec 0x106c17 (StorePre 0x106c17 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106c17 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106c17 6 9 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[212, 4]
    (.letOp (n := 215) (.out 0x106c1d (xorR32R32Effect 0x106c1d 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[55, 107]
    (.letOp (n := 216) (.exec 0x106c1d (fun s => s.RIP = 0x106c1d) (xorR32R32Effect 0x106c1d 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[55, 107]
    (.letOp (n := 217) (.out 0x106c1f (xorR32R32Effect 0x106c1f 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[200, 107]
    (.letOp (n := 218) (.exec 0x106c1f (fun s => s.RIP = 0x106c1f) (xorR32R32Effect 0x106c1f 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[200, 107]
    (.letOp (n := 219) (.out 0x106c21 (movR32R32Effect 0x106c21 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[215]
    (.letOp (n := 220) (.exec 0x106c21 (fun s => s.RIP = 0x106c21) (movR32R32Effect 0x106c21 3 8 7) (Reg.operands [.gpr 7] [])) #v[215]
    (.letOp (n := 221) (.out 0x106c24 (rolR16Effect 0x106c24 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[219]
    (.letOp (n := 222) (.exec 0x106c24 (fun s => s.RIP = 0x106c24) (rolR16Effect 0x106c24 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[219]
    (.letOp (n := 223) (.out 0x106c29 (xorR16M16Effect 0x106c29 6 8 (.sib 3 (some 12) 1 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[221, 191, 12]
    (.letOp (n := 224) (.exec 0x106c29 (LoadPre 0x106c29 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x16)) s (0x106c29 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c29 6 8 (.sib 3 (some 12) 1 (.d8 0x16))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[221, 191, 12]
    (.letOp (n := 225) (.out 0x106c2f (xorR32R32Effect 0x106c2f 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[217, 223]
    (.letOp (n := 226) (.exec 0x106c2f (fun s => s.RIP = 0x106c2f) (xorR32R32Effect 0x106c2f 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[217, 223]
    (.letOp (n := 227) (.out 0x106c32 (xorR32R32Effect 0x106c32 3 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[59, 121]
    (.letOp (n := 228) (.exec 0x106c32 (fun s => s.RIP = 0x106c32) (xorR32R32Effect 0x106c32 3 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[59, 121]
    (.letOp (n := 229) (.exec 0x106c35 (StorePre 0x106c35 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106c35 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106c35 5 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[225, 4]
    (.letOp (n := 230) (.out 0x106c3a (movR32R32Effect 0x106c3a 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[227]
    (.letOp (n := 231) (.exec 0x106c3a (fun s => s.RIP = 0x106c3a) (movR32R32Effect 0x106c3a 3 2 15) (Reg.operands [.gpr 15] [])) #v[227]
    (.letOp (n := 232) (.out 0x106c3d (rolR16Effect 0x106c3d 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[230]
    (.letOp (n := 233) (.exec 0x106c3d (fun s => s.RIP = 0x106c3d) (rolR16Effect 0x106c3d 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[230]
    (.letOp (n := 234) (.out 0x106c41 (xorR16M16Effect 0x106c41 6 2 (.sib 3 (some 12) 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3, .gpr 12] []) (.reg (.gpr 2))) #v[232, 191, 12]
    (.letOp (n := 235) (.exec 0x106c41 (LoadPre 0x106c41 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x18)) s (0x106c41 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106c41 6 2 (.sib 3 (some 12) 1 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 3, .gpr 12] [])) #v[232, 191, 12]
    (.letOp (n := 236) (.out 0x106c47 (xorR32R32Effect 0x106c47 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[215, 121]
    (.letOp (n := 237) (.exec 0x106c47 (fun s => s.RIP = 0x106c47) (xorR32R32Effect 0x106c47 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[215, 121]
    (.letOp (n := 238) (.out 0x106c49 (xorR32R32Effect 0x106c49 3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[236, 185]
    (.letOp (n := 239) (.exec 0x106c49 (fun s => s.RIP = 0x106c49) (xorR32R32Effect 0x106c49 3 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[236, 185]
    (.letOp (n := 240) (.out 0x106c4c (xorR32R32Effect 0x106c4c 2 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[238, 234]
    (.letOp (n := 241) (.exec 0x106c4c (fun s => s.RIP = 0x106c4c) (xorR32R32Effect 0x106c4c 2 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[238, 234]
    (.letOp (n := 242) (.out 0x106c4e (movR32M32LowEffect 0x106c4e 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 243) (.exec 0x106c4e (LoadPre 0x106c4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106c4e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106c4e 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 244) (.out 0x106c52 (xorR32R32Effect 0x106c52 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[242, 134]
    (.letOp (n := 245) (.exec 0x106c52 (fun s => s.RIP = 0x106c52) (xorR32R32Effect 0x106c52 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[242, 134]
    (b_l106ab8_5))))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_4 : List UInt8 :=
  [0x66, 0x46, 0x33, 0x44, 0x63, 0x14, 0x45, 0x31, 0xF1, 0x45, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x4C,
    0x24, 0x0A, 0x31, 0xCF, 0x31, 0xCA, 0x41, 0x89, 0xF8, 0x66, 0x41, 0xC1, 0xC0, 0x08, 0x66, 0x46,
    0x33, 0x44, 0x63, 0x16, 0x44, 0x31, 0xC2, 0x41, 0x31, 0xF7, 0x66, 0x89, 0x54, 0x24, 0x0C, 0x44,
    0x89, 0xFA, 0x66, 0xC1, 0xC2, 0x08, 0x66, 0x42, 0x33, 0x54, 0x63, 0x18, 0x31, 0xF7, 0x44, 0x31,
    0xF7, 0x31, 0xD7, 0x8B, 0x4C, 0x24, 0x28, 0x44, 0x31, 0xE9] ++ bytes_l106ab8_5

theorem code_l106ab8_4 : ∀ x ∈ codeRange 0x106c0b bytes_l106ab8_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6c0b 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_5

@[cfg_block] def b_l106ab8_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x106bbb (movR32R32Effect 0x106bbb 3 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 14] []) (.reg (.gpr 10))) #v[167]
    (.letOp (n := 170) (.exec 0x106bbb (fun s => s.RIP = 0x106bbb) (movR32R32Effect 0x106bbb 3 10 14) (Reg.operands [.gpr 14] [])) #v[167]
    (.letOp (n := 171) (.out 0x106bbe (rolR16Effect 0x106bbe 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[169]
    (.letOp (n := 172) (.exec 0x106bbe (fun s => s.RIP = 0x106bbe) (rolR16Effect 0x106bbe 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[169]
    (.letOp (n := 173) (.out 0x106bc3 (andR32Imm32Effect 0x106bc3 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[171]
    (.letOp (n := 174) (.exec 0x106bc3 (fun s => s.RIP = 0x106bc3) (andR32Imm32Effect 0x106bc3 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[171]
    (.letOp (n := 175) (.out 0x106bca (movR32R32Effect 0x106bca 3 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[167]
    (.letOp (n := 176) (.exec 0x106bca (fun s => s.RIP = 0x106bca) (movR32R32Effect 0x106bca 3 0 14) (Reg.operands [.gpr 14] [])) #v[167]
    (.letOp (n := 177) (.out 0x106bcd (rolR16Effect 0x106bcd 4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[175]
    (.letOp (n := 178) (.exec 0x106bcd (fun s => s.RIP = 0x106bcd) (rolR16Effect 0x106bcd 4 0 14) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.out 0x106bd1 (andEaxImm32Effect 0x106bd1 0xffffcccc) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[177]
    (.letOp (n := 180) (.exec 0x106bd1 (fun s => s.RIP = 0x106bd1) (andEaxImm32Effect 0x106bd1 0xffffcccc) (Reg.operands [.gpr 0] [])) #v[177]
    (.letOp (n := 181) (.out 0x106bd6 (orR32R32Effect 0x106bd6 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[179, 173]
    (.letOp (n := 182) (.exec 0x106bd6 (fun s => s.RIP = 0x106bd6) (orR32R32Effect 0x106bd6 3 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[179, 173]
    (.letOp (n := 183) (.out 0x106bd9 (xorR32R32Effect 0x106bd9 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[53, 79]
    (.letOp (n := 184) (.exec 0x106bd9 (fun s => s.RIP = 0x106bd9) (xorR32R32Effect 0x106bd9 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[53, 79]
    (.letOp (n := 185) (.out 0x106bdc (xorR32R32Effect 0x106bdc 3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[167, 181]
    (.letOp (n := 186) (.exec 0x106bdc (fun s => s.RIP = 0x106bdc) (xorR32R32Effect 0x106bdc 3 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[167, 181]
    (.letOp (n := 187) (.out 0x106bdf (movR32R32Effect 0x106bdf 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[183]
    (.letOp (n := 188) (.exec 0x106bdf (fun s => s.RIP = 0x106bdf) (movR32R32Effect 0x106bdf 3 10 9) (Reg.operands [.gpr 9] [])) #v[183]
    (.letOp (n := 189) (.out 0x106be2 (rolR16Effect 0x106be2 5 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[187]
    (.letOp (n := 190) (.exec 0x106be2 (fun s => s.RIP = 0x106be2) (rolR16Effect 0x106be2 5 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x106be7 (movR64M64Effect 0x106be7 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 192) (.exec 0x106be7 (LoadPre 0x106be7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106be7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106be7 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 193) (.out 0x106bec (xorR16M16Effect 0x106bec 6 10 (.sib 3 (some 12) 1 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .gpr 12] []) (.reg (.gpr 10))) #v[189, 191, 12]
    (.letOp (n := 194) (.exec 0x106bec (LoadPre 0x106bec (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x12)) s (0x106bec + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106bec 6 10 (.sib 3 (some 12) 1 (.d8 0x12))) (Reg.operands [.gpr 10, .gpr 3, .gpr 12] [])) #v[189, 191, 12]
    (.letOp (n := 195) (.out 0x106bf2 (xorR32R32Effect 0x106bf2 3 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 14] []) (.reg (.gpr 5))) #v[79, 185]
    (.letOp (n := 196) (.exec 0x106bf2 (fun s => s.RIP = 0x106bf2) (xorR32R32Effect 0x106bf2 3 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[79, 185]
    (.letOp (n := 197) (.out 0x106bf5 (xorR32R32Effect 0x106bf5 3 5 10) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10] []) (.reg (.gpr 5))) #v[195, 193]
    (.letOp (n := 198) (.exec 0x106bf5 (fun s => s.RIP = 0x106bf5) (xorR32R32Effect 0x106bf5 3 5 10) (Reg.operands [.gpr 5, .gpr 10] [])) #v[195, 193]
    (.letOp (n := 199) (.exec 0x106bf8 (StorePre 0x106bf8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106bf8 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106bf8 5 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[197, 4]
    (.letOp (n := 200) (.out 0x106bfd (xorR32R32Effect 0x106bfd 3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[57, 97]
    (.letOp (n := 201) (.exec 0x106bfd (fun s => s.RIP = 0x106bfd) (xorR32R32Effect 0x106bfd 3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[57, 97]
    (.letOp (n := 202) (.out 0x106c00 (xorR32R32Effect 0x106c00 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[183, 97]
    (.letOp (n := 203) (.exec 0x106c00 (fun s => s.RIP = 0x106c00) (xorR32R32Effect 0x106c00 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[183, 97]
    (.letOp (n := 204) (.out 0x106c03 (movR32R32Effect 0x106c03 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[200]
    (.letOp (n := 205) (.exec 0x106c03 (fun s => s.RIP = 0x106c03) (movR32R32Effect 0x106c03 3 8 2) (Reg.operands [.gpr 2] [])) #v[200]
    (.letOp (n := 206) (.out 0x106c06 (rolR16Effect 0x106c06 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[204]
    (.letOp (n := 207) (.exec 0x106c06 (fun s => s.RIP = 0x106c06) (rolR16Effect 0x106c06 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[204]
    (b_l106ab8_4)))))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_3 : List UInt8 :=
  [0x45, 0x89, 0xF2, 0x66, 0x41, 0xC1, 0xC2, 0x0A, 0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00, 0x44,
    0x89, 0xF0, 0x66, 0xC1, 0xC0, 0x0E, 0x25, 0xCC, 0xCC, 0xFF, 0xFF, 0x44, 0x09, 0xD0, 0x41, 0x31,
    0xE9, 0x41, 0x31, 0xC6, 0x45, 0x89, 0xCA, 0x66, 0x41, 0xC1, 0xC2, 0x08, 0x48, 0x8B, 0x5C, 0x24,
    0x30, 0x66, 0x46, 0x33, 0x54, 0x63, 0x12, 0x44, 0x31, 0xF5, 0x44, 0x31, 0xD5, 0x66, 0x89, 0x6C,
    0x24, 0x08, 0x44, 0x31, 0xC2, 0x45, 0x31, 0xC1, 0x41, 0x89, 0xD0, 0x66, 0x41, 0xC1, 0xC0, 0x08] ++ bytes_l106ab8_4

theorem code_l106ab8_3 : ∀ x ∈ codeRange 0x106bbb bytes_l106ab8_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6bbb 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_4

@[cfg_block] def b_l106ab8_2 : Block Op Label signature Reg.count 132 :=
  .letOp (n := 132) (.out 0x106b5e (andR32Imm32Effect 0x106b5e 7 13 0xffffcccc) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[130]
    (.letOp (n := 133) (.exec 0x106b5e (fun s => s.RIP = 0x106b5e) (andR32Imm32Effect 0x106b5e 7 13 0xffffcccc) (Reg.operands [.gpr 13] [])) #v[130]
    (.letOp (n := 134) (.out 0x106b65 (orR32R32Effect 0x106b65 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[132, 128]
    (.letOp (n := 135) (.exec 0x106b65 (fun s => s.RIP = 0x106b65) (orR32R32Effect 0x106b65 3 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[132, 128]
    (.letOp (n := 136) (.exec 0x106b68 (StorePre 0x106b68 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106b68 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b68 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 137) (.out 0x106b6d (movR32R32Effect 0x106b6d 3 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[63]
    (.letOp (n := 138) (.exec 0x106b6d (fun s => s.RIP = 0x106b6d) (movR32R32Effect 0x106b6d 3 0 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 139) (.out 0x106b70 (rolR16Effect 0x106b70 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[137]
    (.letOp (n := 140) (.exec 0x106b70 (fun s => s.RIP = 0x106b70) (rolR16Effect 0x106b70 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[137]
    (.letOp (n := 141) (.out 0x106b74 (andEaxImm32Effect 0x106b74 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[139]
    (.letOp (n := 142) (.exec 0x106b74 (fun s => s.RIP = 0x106b74) (andEaxImm32Effect 0x106b74 0x3333) (Reg.operands [.gpr 0] [])) #v[139]
    (.letOp (n := 143) (.out 0x106b79 (movR32R32Effect 0x106b79 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[63]
    (.letOp (n := 144) (.exec 0x106b79 (fun s => s.RIP = 0x106b79) (movR32R32Effect 0x106b79 3 11 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 145) (.out 0x106b7c (rolR16Effect 0x106b7c 5 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[143]
    (.letOp (n := 146) (.exec 0x106b7c (fun s => s.RIP = 0x106b7c) (rolR16Effect 0x106b7c 5 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x106b81 (andR32Imm32Effect 0x106b81 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[145]
    (.letOp (n := 148) (.exec 0x106b81 (fun s => s.RIP = 0x106b81) (andR32Imm32Effect 0x106b81 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[145]
    (.letOp (n := 149) (.exec 0x106b88 (StorePre 0x106b88 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106b88 + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106b88 3 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 150) (.out 0x106b8c (movR32R32Effect 0x106b8c 3 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 3] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 151) (.exec 0x106b8c (fun s => s.RIP = 0x106b8c) (movR32R32Effect 0x106b8c 3 10 3) (Reg.operands [.gpr 3] [])) #v[65]
    (.letOp (n := 152) (.out 0x106b8f (rolR16Effect 0x106b8f 5 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[150]
    (.letOp (n := 153) (.exec 0x106b8f (fun s => s.RIP = 0x106b8f) (rolR16Effect 0x106b8f 5 10 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[150]
    (.letOp (n := 154) (.out 0x106b94 (orR32R32Effect 0x106b94 3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[147, 141]
    (.letOp (n := 155) (.exec 0x106b94 (fun s => s.RIP = 0x106b94) (orR32R32Effect 0x106b94 3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[147, 141]
    (.letOp (n := 156) (.exec 0x106b97 (StorePre 0x106b97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106b97 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b97 11 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 157) (.out 0x106b9c (movR32R32Effect 0x106b9c 3 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 3] []) (.reg (.gpr 11))) #v[65]
    (.letOp (n := 158) (.exec 0x106b9c (fun s => s.RIP = 0x106b9c) (movR32R32Effect 0x106b9c 3 11 3) (Reg.operands [.gpr 3] [])) #v[65]
    (.letOp (n := 159) (.out 0x106b9f (rolR16Effect 0x106b9f 5 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[157]
    (.letOp (n := 160) (.exec 0x106b9f (fun s => s.RIP = 0x106b9f) (rolR16Effect 0x106b9f 5 11 14) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[157]
    (.letOp (n := 161) (.out 0x106ba4 (andR32Imm32Effect 0x106ba4 7 10 0x3333) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[152]
    (.letOp (n := 162) (.exec 0x106ba4 (fun s => s.RIP = 0x106ba4) (andR32Imm32Effect 0x106ba4 7 10 0x3333) (Reg.operands [.gpr 10] [])) #v[152]
    (.letOp (n := 163) (.out 0x106bab (andR32Imm32Effect 0x106bab 7 11 0xffffcccc) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[159]
    (.letOp (n := 164) (.exec 0x106bab (fun s => s.RIP = 0x106bab) (andR32Imm32Effect 0x106bab 7 11 0xffffcccc) (Reg.operands [.gpr 11] [])) #v[159]
    (.letOp (n := 165) (.out 0x106bb2 (orR32R32Effect 0x106bb2 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[163, 161]
    (.letOp (n := 166) (.exec 0x106bb2 (fun s => s.RIP = 0x106bb2) (orR32R32Effect 0x106bb2 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[163, 161]
    (.letOp (n := 167) (.out 0x106bb5 (movzxR32M16Effect 0x106bb5 6 14 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[4]
    (.letOp (n := 168) (.exec 0x106bb5 (LoadPre 0x106bb5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106bb5 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106bb5 6 14 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l106ab8_3)))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_2 : List UInt8 :=
  [0x41, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF, 0x41, 0x09, 0xC5, 0x44, 0x89, 0x54, 0x24, 0x20, 0x44,
    0x89, 0xD0, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x45, 0x89, 0xD3, 0x66, 0x41,
    0xC1, 0xC3, 0x0E, 0x41, 0x81, 0xE3, 0xCC, 0xCC, 0xFF, 0xFF, 0x89, 0x5C, 0x24, 0x24, 0x41, 0x89,
    0xDA, 0x66, 0x41, 0xC1, 0xC2, 0x0A, 0x41, 0x09, 0xC3, 0x44, 0x89, 0x5C, 0x24, 0x1C, 0x41, 0x89,
    0xDB, 0x66, 0x41, 0xC1, 0xC3, 0x0E, 0x41, 0x81, 0xE2, 0x33, 0x33, 0x00, 0x00, 0x41, 0x81, 0xE3,
    0xCC, 0xCC, 0xFF, 0xFF, 0x45, 0x09, 0xD3, 0x44, 0x0F, 0xB7, 0x74, 0x24, 0x16] ++ bytes_l106ab8_3

theorem code_l106ab8_2 : ∀ x ∈ codeRange 0x106b5e bytes_l106ab8_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6b5e 93 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_3

@[cfg_block] def b_l106ab8_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x106b10 (movR32R32Effect 0x106b10 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 94) (.exec 0x106b10 (fun s => s.RIP = 0x106b10) (movR32R32Effect 0x106b10 2 6 7) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 95) (.out 0x106b12 (rolR16Effect 0x106b12 4 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[93]
    (.letOp (n := 96) (.exec 0x106b12 (fun s => s.RIP = 0x106b12) (rolR16Effect 0x106b12 4 6 10) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[93]
    (.letOp (n := 97) (.out 0x106b16 (orR32R32Effect 0x106b16 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[91, 85]
    (.letOp (n := 98) (.exec 0x106b16 (fun s => s.RIP = 0x106b16) (orR32R32Effect 0x106b16 3 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[91, 85]
    (.letOp (n := 99) (.out 0x106b19 (movR32R32Effect 0x106b19 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 100) (.exec 0x106b19 (fun s => s.RIP = 0x106b19) (movR32R32Effect 0x106b19 2 1 7) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 101) (.out 0x106b1b (rolR16Effect 0x106b1b 4 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[99]
    (.letOp (n := 102) (.exec 0x106b1b (fun s => s.RIP = 0x106b1b) (rolR16Effect 0x106b1b 4 1 14) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[99]
    (.letOp (n := 103) (.out 0x106b1f (andR32Imm32Effect 0x106b1f 6 6 0x3333) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[95]
    (.letOp (n := 104) (.exec 0x106b1f (fun s => s.RIP = 0x106b1f) (andR32Imm32Effect 0x106b1f 6 6 0x3333) (Reg.operands [.gpr 6] [])) #v[95]
    (.letOp (n := 105) (.out 0x106b25 (andR32Imm32Effect 0x106b25 6 1 0xffffcccc) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[101]
    (.letOp (n := 106) (.exec 0x106b25 (fun s => s.RIP = 0x106b25) (andR32Imm32Effect 0x106b25 6 1 0xffffcccc) (Reg.operands [.gpr 1] [])) #v[101]
    (.letOp (n := 107) (.out 0x106b2b (orR32R32Effect 0x106b2b 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x106b2b (fun s => s.RIP = 0x106b2b) (orR32R32Effect 0x106b2b 2 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x106b2d (movR32R32Effect 0x106b2d 3 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 110) (.exec 0x106b2d (fun s => s.RIP = 0x106b2d) (movR32R32Effect 0x106b2d 3 0 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 111) (.out 0x106b30 (rolR16Effect 0x106b30 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[109]
    (.letOp (n := 112) (.exec 0x106b30 (fun s => s.RIP = 0x106b30) (rolR16Effect 0x106b30 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[109]
    (.letOp (n := 113) (.out 0x106b34 (andEaxImm32Effect 0x106b34 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[111]
    (.letOp (n := 114) (.exec 0x106b34 (fun s => s.RIP = 0x106b34) (andEaxImm32Effect 0x106b34 0x3333) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 115) (.out 0x106b39 (movR32R32Effect 0x106b39 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 116) (.exec 0x106b39 (fun s => s.RIP = 0x106b39) (movR32R32Effect 0x106b39 3 6 15) (Reg.operands [.gpr 15] [])) #v[59]
    (.letOp (n := 117) (.out 0x106b3c (rolR16Effect 0x106b3c 4 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[115]
    (.letOp (n := 118) (.exec 0x106b3c (fun s => s.RIP = 0x106b3c) (rolR16Effect 0x106b3c 4 6 14) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[115]
    (.letOp (n := 119) (.out 0x106b40 (andR32Imm32Effect 0x106b40 6 6 0xffffcccc) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[117]
    (.letOp (n := 120) (.exec 0x106b40 (fun s => s.RIP = 0x106b40) (andR32Imm32Effect 0x106b40 6 6 0xffffcccc) (Reg.operands [.gpr 6] [])) #v[117]
    (.letOp (n := 121) (.out 0x106b46 (orR32R32Effect 0x106b46 2 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[119, 113]
    (.letOp (n := 122) (.exec 0x106b46 (fun s => s.RIP = 0x106b46) (orR32R32Effect 0x106b46 2 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[119, 113]
    (.letOp (n := 123) (.exec 0x106b48 (StorePre 0x106b48 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106b48 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106b48 13 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 124) (.out 0x106b4d (movR32R32Effect 0x106b4d 3 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 125) (.exec 0x106b4d (fun s => s.RIP = 0x106b4d) (movR32R32Effect 0x106b4d 3 0 13) (Reg.operands [.gpr 13] [])) #v[61]
    (.letOp (n := 126) (.out 0x106b50 (rolR16Effect 0x106b50 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[124]
    (.letOp (n := 127) (.exec 0x106b50 (fun s => s.RIP = 0x106b50) (rolR16Effect 0x106b50 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[124]
    (.letOp (n := 128) (.out 0x106b54 (andEaxImm32Effect 0x106b54 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[126]
    (.letOp (n := 129) (.exec 0x106b54 (fun s => s.RIP = 0x106b54) (andEaxImm32Effect 0x106b54 0x3333) (Reg.operands [.gpr 0] [])) #v[126]
    (.letOp (n := 130) (.out 0x106b59 (rolR16Effect 0x106b59 5 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 131) (.exec 0x106b59 (fun s => s.RIP = 0x106b59) (rolR16Effect 0x106b59 5 13 14) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (b_l106ab8_2)))))))))))))))))))))))))))))))))))))))

def bytes_l106ab8_1 : List UInt8 :=
  [0x89, 0xFE, 0x66, 0xC1, 0xC6, 0x0A, 0x41, 0x09, 0xC0, 0x89, 0xF9, 0x66, 0xC1, 0xC1, 0x0E, 0x81,
    0xE6, 0x33, 0x33, 0x00, 0x00, 0x81, 0xE1, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xF1, 0x44, 0x89, 0xF8,
    0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x44, 0x89, 0xFE, 0x66, 0xC1, 0xC6, 0x0E,
    0x81, 0xE6, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC6, 0x44, 0x89, 0x6C, 0x24, 0x28, 0x44, 0x89, 0xE8,
    0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x66, 0x41, 0xC1, 0xC5, 0x0E] ++ bytes_l106ab8_2

theorem code_l106ab8_1 : ∀ x ∈ codeRange 0x106b10 bytes_l106ab8_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6b10 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_2

@[cfg_block] def b_l106ab8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ab8 (movR32M32Effect 0x106ab8 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 54) (.exec 0x106ab8 (LoadPre 0x106ab8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ab8 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106ab8 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106abd (movR32M32LowEffect 0x106abd 7 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 56) (.exec 0x106abd (LoadPre 0x106abd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106abd + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106abd 7 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106ac1 (movzxR32M16Effect 0x106ac1 5 2 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x106ac1 (LoadPre 0x106ac1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106ac1 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106ac1 5 2 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106ac6 (movzxR32M16Effect 0x106ac6 6 15 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 60) (.exec 0x106ac6 (LoadPre 0x106ac6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106ac6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ac6 6 15 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x106acc (movR32M32Effect 0x106acc 13 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 62) (.exec 0x106acc (LoadPre 0x106acc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106acc + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106acc 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x106ad1 (movzxR32M16Effect 0x106ad1 6 10 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 64) (.exec 0x106ad1 (LoadPre 0x106ad1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106ad1 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ad1 6 10 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x106ad7 (movR32M32LowEffect 0x106ad7 3 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 66) (.exec 0x106ad7 (LoadPre 0x106ad7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106ad7 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106ad7 3 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x106adb (movR32R32Effect 0x106adb 3 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x106adb (fun s => s.RIP = 0x106adb) (movR32R32Effect 0x106adb 3 0 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 69) (.out 0x106ade (rolR16Effect 0x106ade 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 70) (.exec 0x106ade (fun s => s.RIP = 0x106ade) (rolR16Effect 0x106ade 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x106ae2 (andEaxImm32Effect 0x106ae2 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 72) (.exec 0x106ae2 (fun s => s.RIP = 0x106ae2) (andEaxImm32Effect 0x106ae2 0x3333) (Reg.operands [.gpr 0] [])) #v[69]
    (.letOp (n := 73) (.out 0x106ae7 (movR32R32Effect 0x106ae7 3 5 9) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 74) (.exec 0x106ae7 (fun s => s.RIP = 0x106ae7) (movR32R32Effect 0x106ae7 3 5 9) (Reg.operands [.gpr 9] [])) #v[53]
    (.letOp (n := 75) (.out 0x106aea (rolR16Effect 0x106aea 4 5 14) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[73]
    (.letOp (n := 76) (.exec 0x106aea (fun s => s.RIP = 0x106aea) (rolR16Effect 0x106aea 4 5 14) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x106aee (andR32Imm32Effect 0x106aee 6 5 0xffffcccc) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5] []) (.reg (.gpr 5))) #v[75]
    (.letOp (n := 78) (.exec 0x106aee (fun s => s.RIP = 0x106aee) (andR32Imm32Effect 0x106aee 6 5 0xffffcccc) (Reg.operands [.gpr 5] [])) #v[75]
    (.letOp (n := 79) (.out 0x106af4 (orR32R32Effect 0x106af4 2 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x106af4 (fun s => s.RIP = 0x106af4) (orR32R32Effect 0x106af4 2 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[77, 71]
    (.letOp (n := 81) (.out 0x106af6 (movR32R32Effect 0x106af6 2 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 82) (.exec 0x106af6 (fun s => s.RIP = 0x106af6) (movR32R32Effect 0x106af6 2 0 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 83) (.out 0x106af8 (rolR16Effect 0x106af8 4 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[81]
    (.letOp (n := 84) (.exec 0x106af8 (fun s => s.RIP = 0x106af8) (rolR16Effect 0x106af8 4 0 10) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x106afc (andEaxImm32Effect 0x106afc 0x3333) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[83]
    (.letOp (n := 86) (.exec 0x106afc (fun s => s.RIP = 0x106afc) (andEaxImm32Effect 0x106afc 0x3333) (Reg.operands [.gpr 0] [])) #v[83]
    (.letOp (n := 87) (.out 0x106b01 (movR32R32Effect 0x106b01 3 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[57]
    (.letOp (n := 88) (.exec 0x106b01 (fun s => s.RIP = 0x106b01) (movR32R32Effect 0x106b01 3 8 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 89) (.out 0x106b04 (rolR16Effect 0x106b04 5 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[87]
    (.letOp (n := 90) (.exec 0x106b04 (fun s => s.RIP = 0x106b04) (rolR16Effect 0x106b04 5 8 14) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x106b09 (andR32Imm32Effect 0x106b09 7 8 0xffffcccc) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[89]
    (.letOp (n := 92) (.exec 0x106b09 (fun s => s.RIP = 0x106b09) (andR32Imm32Effect 0x106b09 7 8 0xffffcccc) (Reg.operands [.gpr 8] [])) #v[89]
    (b_l106ab8_1))))))))))))))))))))))))))))))))))))))))

def bytes_l106ab8 : List UInt8 :=
  [0x44, 0x8B, 0x4C, 0x24, 0x08, 0x8B, 0x7C, 0x24, 0x0C, 0x0F, 0xB7, 0x54, 0x24, 0x0A, 0x44, 0x0F,
    0xB7, 0x7C, 0x24, 0x0E, 0x44, 0x8B, 0x6C, 0x24, 0x10, 0x44, 0x0F, 0xB7, 0x54, 0x24, 0x12, 0x8B,
    0x5C, 0x24, 0x14, 0x44, 0x89, 0xC8, 0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x44,
    0x89, 0xCD, 0x66, 0xC1, 0xC5, 0x0E, 0x81, 0xE5, 0xCC, 0xCC, 0xFF, 0xFF, 0x09, 0xC5, 0x89, 0xD0,
    0x66, 0xC1, 0xC0, 0x0A, 0x25, 0x33, 0x33, 0x00, 0x00, 0x41, 0x89, 0xD0, 0x66, 0x41, 0xC1, 0xC0,
    0x0E, 0x41, 0x81, 0xE0, 0xCC, 0xCC, 0xFF, 0xFF] ++ bytes_l106ab8_1

theorem code_l106ab8 : ∀ x ∈ codeRange 0x106ab8 bytes_l106ab8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6ab8 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ab8_1

@[cfg_block] def b_l106ce3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ce3 (movR64R64Effect 0x106ce3 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 54) (.exec 0x106ce3 (fun s => s.RIP = 0x106ce3) (movR64R64Effect 0x106ce3 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 55) (.out 0x106ce6 (callEffect (fun _ => 0x100580) 0x106ceb) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x106ce6 (PushPre 0x106ce6 5) (callEffect (fun _ => 0x100580) 0x106ceb) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.const ⟨64, 0x106ceb⟩) #v[]
    (.terminate (.call ⟨.l100580, RegMap.args [(3, 3), (4, 55), (5, 5), (7, 53), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 58⟩ { target := .l106ceb, kept := #v[], arity := rfl, guard := some (Fin.last 57) }))))))

def bytes_l106ce3 : List UInt8 :=
  [0x4C, 0x89, 0xF7, 0xE8, 0x95, 0x98, 0xFF, 0xFF]

theorem code_l106ce3 : ∀ x ∈ codeRange 0x106ce3 bytes_l106ce3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ce3 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ceb : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ceb (movzxR32M16Effect 0x106ceb 6 0 (.sib 3 (some 12) 1 (.d8 0x22))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 54) (.exec 0x106ceb (LoadPre 0x106ceb (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x22)) s (0x106ceb + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106ceb 6 0 (.sib 3 (some 12) 1 (.d8 0x22))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 55) (.exec 0x106cf1 (StorePre 0x106cf1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106cf1 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106cf1 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x106cf6 (movzxR32M16Effect 0x106cf6 6 0 (.sib 3 (some 12) 1 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 57) (.exec 0x106cf6 (LoadPre 0x106cf6 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x24)) s (0x106cf6 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106cf6 6 0 (.sib 3 (some 12) 1 (.d8 0x24))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 58) (.exec 0x106cfc (StorePre 0x106cfc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106cfc + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106cfc 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x106d01 (movzxR32M16Effect 0x106d01 6 0 (.sib 3 (some 12) 1 (.d8 0x26))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 60) (.exec 0x106d01 (LoadPre 0x106d01 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x26)) s (0x106d01 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d01 6 0 (.sib 3 (some 12) 1 (.d8 0x26))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 61) (.exec 0x106d07 (StorePre 0x106d07 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d07 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d07 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x106d0c (movzxR32M16Effect 0x106d0c 6 0 (.sib 3 (some 12) 1 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 63) (.exec 0x106d0c (LoadPre 0x106d0c (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x28)) s (0x106d0c + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d0c 6 0 (.sib 3 (some 12) 1 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 64) (.exec 0x106d12 (StorePre 0x106d12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106d12 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d12 5 16 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x106d17 (movzxR32M16Effect 0x106d17 6 0 (.sib 3 (some 12) 1 (.d8 0x2a))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 66) (.exec 0x106d17 (LoadPre 0x106d17 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2a)) s (0x106d17 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d17 6 0 (.sib 3 (some 12) 1 (.d8 0x2a))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 67) (.exec 0x106d1d (StorePre 0x106d1d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106d1d + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d1d 5 16 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x106d22 (movzxR32M16Effect 0x106d22 6 0 (.sib 3 (some 12) 1 (.d8 0x2c))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 69) (.exec 0x106d22 (LoadPre 0x106d22 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2c)) s (0x106d22 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d22 6 0 (.sib 3 (some 12) 1 (.d8 0x2c))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 70) (.exec 0x106d28 (StorePre 0x106d28 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106d28 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d28 5 16 0 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x106d2d (movzxR32M16Effect 0x106d2d 6 0 (.sib 3 (some 12) 1 (.d8 0x2e))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 72) (.exec 0x106d2d (LoadPre 0x106d2d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x2e)) s (0x106d2d + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d2d 6 0 (.sib 3 (some 12) 1 (.d8 0x2e))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 73) (.exec 0x106d33 (StorePre 0x106d33 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106d33 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d33 5 16 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x106d38 (movzxR32M16Effect 0x106d38 6 0 (.sib 3 (some 12) 1 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 12] []) (.reg (.gpr 0))) #v[3, 12]
    (.letOp (n := 75) (.exec 0x106d38 (LoadPre 0x106d38 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x30)) s (0x106d38 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d38 6 0 (.sib 3 (some 12) 1 (.d8 0x30))) (Reg.operands [.gpr 3, .gpr 12] [])) #v[3, 12]
    (.letOp (n := 76) (.exec 0x106d3e (StorePre 0x106d3e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106d3e + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106d3e 5 16 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x106d43 (movR32Imm32Effect 0x106d43 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 78) (.exec 0x106d43 (fun s => s.RIP = 0x106d43) (movR32Imm32Effect 0x106d43 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x106d48 (movR64R64Effect 0x106d48 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[14]
    (.letOp (n := 80) (.exec 0x106d48 (fun s => s.RIP = 0x106d48) (movR64R64Effect 0x106d48 7 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 81) (.out 0x106d4b (callEffect (fun _ => 0x100b10) 0x106d50) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 82) (.exec 0x106d4b (PushPre 0x106d4b 5) (callEffect (fun _ => 0x100b10) 0x106d50) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.const ⟨64, 0x106d50⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 74), (3, 3), (4, 81), (5, 5), (6, 77), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 84⟩ { target := .l106d50, kept := #v[], arity := rfl, guard := some (Fin.last 83) }))))))))))))))))))))))))))))))))

def bytes_l106ceb : List UInt8 :=
  [0x42, 0x0F, 0xB7, 0x44, 0x63, 0x22, 0x66, 0x31, 0x44, 0x24, 0x08, 0x42, 0x0F, 0xB7, 0x44, 0x63,
    0x24, 0x66, 0x31, 0x44, 0x24, 0x0A, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x26, 0x66, 0x31, 0x44, 0x24,
    0x0C, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x28, 0x66, 0x31, 0x44, 0x24, 0x0E, 0x42, 0x0F, 0xB7, 0x44,
    0x63, 0x2A, 0x66, 0x31, 0x44, 0x24, 0x10, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x2C, 0x66, 0x31, 0x44,
    0x24, 0x12, 0x42, 0x0F, 0xB7, 0x44, 0x63, 0x2E, 0x66, 0x31, 0x44, 0x24, 0x14, 0x42, 0x0F, 0xB7,
    0x44, 0x63, 0x30, 0x66, 0x31, 0x44, 0x24, 0x16, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7,
    0xE8, 0xC0, 0x9D, 0xFF, 0xFF]

theorem code_l106ceb : ∀ x ∈ codeRange 0x106ceb bytes_l106ceb, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6ceb 101 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d50_4 : Block Op Label signature Reg.count 202 :=
  .letOp (n := 202) (.out 0x106e85 (xorR32R32Effect 0x106e85 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[156, 200]
    (.letOp (n := 203) (.exec 0x106e85 (fun s => s.RIP = 0x106e85) (xorR32R32Effect 0x106e85 2 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[156, 200]
    (.letOp (n := 204) (.out 0x106e87 (xorR32R32Effect 0x106e87 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[187, 200]
    (.letOp (n := 205) (.exec 0x106e87 (fun s => s.RIP = 0x106e87) (xorR32R32Effect 0x106e87 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[187, 200]
    (.letOp (n := 206) (.out 0x106e89 (movR32R32Effect 0x106e89 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[202]
    (.letOp (n := 207) (.exec 0x106e89 (fun s => s.RIP = 0x106e89) (movR32R32Effect 0x106e89 2 1 7) (Reg.operands [.gpr 7] [])) #v[202]
    (.letOp (n := 208) (.out 0x106e8b (rolR16Effect 0x106e8b 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[206]
    (.letOp (n := 209) (.exec 0x106e8b (fun s => s.RIP = 0x106e8b) (rolR16Effect 0x106e8b 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[206]
    (.letOp (n := 210) (.out 0x106e8f (xorR16M16Effect 0x106e8f 6 1 (.sib 3 (some 12) 1 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[208, 3, 105]
    (.letOp (n := 211) (.exec 0x106e8f (LoadPre 0x106e8f (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3c)) s (0x106e8f + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e8f 6 1 (.sib 3 (some 12) 1 (.d8 0x3c))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[208, 3, 105]
    (.letOp (n := 212) (.out 0x106e95 (xorR32R32Effect 0x106e95 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[204, 210]
    (.letOp (n := 213) (.exec 0x106e95 (fun s => s.RIP = 0x106e95) (xorR32R32Effect 0x106e95 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[204, 210]
    (.letOp (n := 214) (.exec 0x106e97 (StorePre 0x106e97 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106e97 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e97 5 2 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[212, 4]
    (.letOp (n := 215) (.out 0x106e9c (rolR16Effect 0x106e9c 5 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[122]
    (.letOp (n := 216) (.exec 0x106e9c (fun s => s.RIP = 0x106e9c) (rolR16Effect 0x106e9c 5 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[122]
    (.letOp (n := 217) (.out 0x106ea1 (xorR16M16Effect 0x106ea1 6 8 (.sib 3 (some 12) 1 (.d8 0x3e))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .gpr 12] []) (.reg (.gpr 8))) #v[215, 3, 105]
    (.letOp (n := 218) (.exec 0x106ea1 (LoadPre 0x106ea1 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3e)) s (0x106ea1 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106ea1 6 8 (.sib 3 (some 12) 1 (.d8 0x3e))) (Reg.operands [.gpr 8, .gpr 3, .gpr 12] [])) #v[215, 3, 105]
    (.letOp (n := 219) (.out 0x106ea7 (xorR32M32LowEffect 0x106ea7 7 (.sib 4 none 0 (.d8 0x24))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[202, 4]
    (.letOp (n := 220) (.exec 0x106ea7 (LoadPre 0x106ea7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106ea7 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x106ea7 7 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[202, 4]
    (.letOp (n := 221) (.out 0x106eab (xorR32R32Effect 0x106eab 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[219, 217]
    (.letOp (n := 222) (.exec 0x106eab (fun s => s.RIP = 0x106eab) (xorR32R32Effect 0x106eab 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[219, 217]
    (.letOp (n := 223) (.exec 0x106eae (StorePre 0x106eae 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106eae + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106eae 5 7 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[221, 4]
    (.letOp (n := 224) (.out 0x106eb3 (addR64Imm8Effect 0x106eb3 12 0x20) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12] []) (.reg (.gpr 12))) #v[105]
    (.letOp (n := 225) (.exec 0x106eb3 (fun s => s.RIP = 0x106eb3) (addR64Imm8Effect 0x106eb3 12 0x20) (Reg.operands [.gpr 12] [])) #v[105]
    (.terminate (.br ⟨.l1069f0, RegMap.args [(0, 152), (1, 210), (2, 212), (3, 3), (4, 4), (5, 148), (6, 177), (7, 221), (8, 217), (9, 195), (10, 111), (11, 168), (12, 224), (13, 173), (14, 154), (15, 182), (22, 22), (39, 39), (50, 50), (51, 51)] 226⟩)))))))))))))))))))))))))

def bytes_l106d50_4 : List UInt8 :=
  [0x31, 0xCF, 0x31, 0xCA, 0x89, 0xF9, 0x66, 0xC1, 0xC1, 0x08, 0x66, 0x42, 0x33, 0x4C, 0x63, 0x3C,
    0x31, 0xCA, 0x66, 0x89, 0x54, 0x24, 0x12, 0x66, 0x41, 0xC1, 0xC0, 0x08, 0x66, 0x46, 0x33, 0x44,
    0x63, 0x3E, 0x33, 0x7C, 0x24, 0x24, 0x44, 0x31, 0xC7, 0x66, 0x89, 0x7C, 0x24, 0x14, 0x49, 0x83,
    0xC4, 0x20, 0xE9, 0x34, 0xFB, 0xFF, 0xFF]

theorem code_l106d50_4 : ∀ x ∈ codeRange 0x106e85 bytes_l106d50_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6e85 55 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106d50_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x106e2d (xorR16M16Effect 0x106e2d 6 1 (.sib 3 (some 12) 1 (.d8 0x34))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[164, 3, 105]
    (.letOp (n := 167) (.exec 0x106e2d (LoadPre 0x106e2d (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x34)) s (0x106e2d + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e2d 6 1 (.sib 3 (some 12) 1 (.d8 0x34))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[164, 3, 105]
    (.letOp (n := 168) (.out 0x106e33 (xorR32R32Effect 0x106e33 3 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[142, 166]
    (.letOp (n := 169) (.exec 0x106e33 (fun s => s.RIP = 0x106e33) (xorR32R32Effect 0x106e33 3 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[142, 166]
    (.letOp (n := 170) (.exec 0x106e36 (StorePre 0x106e36 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106e36 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e36 6 11 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[168, 4]
    (.letOp (n := 171) (.out 0x106e3c (rolR16Effect 0x106e3c 5 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[130]
    (.letOp (n := 172) (.exec 0x106e3c (fun s => s.RIP = 0x106e3c) (rolR16Effect 0x106e3c 5 13 8) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[130]
    (.letOp (n := 173) (.out 0x106e41 (xorR16M16Effect 0x106e41 6 13 (.sib 3 (some 12) 1 (.d8 0x36))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3, .gpr 12] []) (.reg (.gpr 13))) #v[171, 3, 105]
    (.letOp (n := 174) (.exec 0x106e41 (LoadPre 0x106e41 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x36)) s (0x106e41 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e41 6 13 (.sib 3 (some 12) 1 (.d8 0x36))) (Reg.operands [.gpr 13, .gpr 3, .gpr 12] [])) #v[171, 3, 105]
    (.letOp (n := 175) (.out 0x106e47 (xorR32M32LowEffect 0x106e47 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[160, 4]
    (.letOp (n := 176) (.exec 0x106e47 (LoadPre 0x106e47 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106e47 + BitVec.ofNat 64 4)) 4) (xorR32M32LowEffect 0x106e47 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[160, 4]
    (.letOp (n := 177) (.out 0x106e4b (xorR32R32Effect 0x106e4b 3 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[175, 173]
    (.letOp (n := 178) (.exec 0x106e4b (fun s => s.RIP = 0x106e4b) (xorR32R32Effect 0x106e4b 3 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[175, 173]
    (.letOp (n := 179) (.out 0x106e4e (rolR16Effect 0x106e4e 5 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[134]
    (.letOp (n := 180) (.exec 0x106e4e (fun s => s.RIP = 0x106e4e) (rolR16Effect 0x106e4e 5 15 8) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 181) (.exec 0x106e53 (StorePre 0x106e53 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106e53 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e53 5 6 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[177, 4]
    (.letOp (n := 182) (.out 0x106e58 (xorR16M16Effect 0x106e58 6 15 (.sib 3 (some 12) 1 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3, .gpr 12] []) (.reg (.gpr 15))) #v[179, 3, 105]
    (.letOp (n := 183) (.exec 0x106e58 (LoadPre 0x106e58 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x38)) s (0x106e58 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e58 6 15 (.sib 3 (some 12) 1 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 3, .gpr 12] [])) #v[179, 3, 105]
    (.letOp (n := 184) (.out 0x106e5e (xorR32R32Effect 0x106e5e 3 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[144, 182]
    (.letOp (n := 185) (.exec 0x106e5e (fun s => s.RIP = 0x106e5e) (xorR32R32Effect 0x106e5e 3 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[144, 182]
    (.letOp (n := 186) (.exec 0x106e61 (StorePre 0x106e61 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106e61 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e61 5 2 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[184, 4]
    (.letOp (n := 187) (.out 0x106e66 (movR32M32LowEffect 0x106e66 2 (.sib 4 none 0 (.d8 0x1c))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 188) (.exec 0x106e66 (LoadPre 0x106e66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106e66 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106e66 2 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 189) (.out 0x106e6a (movR32R32Effect 0x106e6a 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[187]
    (.letOp (n := 190) (.exec 0x106e6a (fun s => s.RIP = 0x106e6a) (movR32R32Effect 0x106e6a 2 1 2) (Reg.operands [.gpr 2] [])) #v[187]
    (.letOp (n := 191) (.out 0x106e6c (rolR16Effect 0x106e6c 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[189]
    (.letOp (n := 192) (.exec 0x106e6c (fun s => s.RIP = 0x106e6c) (rolR16Effect 0x106e6c 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[189]
    (.letOp (n := 193) (.out 0x106e70 (xorR16M16Effect 0x106e70 6 1 (.sib 3 (some 12) 1 (.d8 0x3a))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 3, .gpr 12] []) (.reg (.gpr 1))) #v[191, 3, 105]
    (.letOp (n := 194) (.exec 0x106e70 (LoadPre 0x106e70 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x3a)) s (0x106e70 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e70 6 1 (.sib 3 (some 12) 1 (.d8 0x3a))) (Reg.operands [.gpr 1, .gpr 3, .gpr 12] [])) #v[191, 3, 105]
    (.letOp (n := 195) (.out 0x106e76 (xorR32R32Effect 0x106e76 3 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[146, 193]
    (.letOp (n := 196) (.exec 0x106e76 (fun s => s.RIP = 0x106e76) (xorR32R32Effect 0x106e76 3 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[146, 193]
    (.letOp (n := 197) (.exec 0x106e79 (StorePre 0x106e79 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106e79 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e79 6 9 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[195, 4]
    (.letOp (n := 198) (.out 0x106e7f (movR32R32Effect 0x106e7f 2 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 7] []) (.reg (.gpr 1))) #v[156]
    (.letOp (n := 199) (.exec 0x106e7f (fun s => s.RIP = 0x106e7f) (movR32R32Effect 0x106e7f 2 1 7) (Reg.operands [.gpr 7] [])) #v[156]
    (.letOp (n := 200) (.out 0x106e81 (rolR16Effect 0x106e81 4 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[198]
    (.letOp (n := 201) (.exec 0x106e81 (fun s => s.RIP = 0x106e81) (rolR16Effect 0x106e81 4 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[198]
    (b_l106d50_4))))))))))))))))))))))))))))))))))))

def bytes_l106d50_3 : List UInt8 :=
  [0x66, 0x42, 0x33, 0x4C, 0x63, 0x34, 0x41, 0x31, 0xCB, 0x66, 0x44, 0x89, 0x5C, 0x24, 0x0A, 0x66,
    0x41, 0xC1, 0xC5, 0x08, 0x66, 0x46, 0x33, 0x6C, 0x63, 0x36, 0x33, 0x74, 0x24, 0x20, 0x44, 0x31,
    0xEE, 0x66, 0x41, 0xC1, 0xC7, 0x08, 0x66, 0x89, 0x74, 0x24, 0x0C, 0x66, 0x46, 0x33, 0x7C, 0x63,
    0x38, 0x44, 0x31, 0xFA, 0x66, 0x89, 0x54, 0x24, 0x0E, 0x8B, 0x54, 0x24, 0x1C, 0x89, 0xD1, 0x66,
    0xC1, 0xC1, 0x08, 0x66, 0x42, 0x33, 0x4C, 0x63, 0x3A, 0x41, 0x31, 0xC9, 0x66, 0x44, 0x89, 0x4C,
    0x24, 0x10, 0x89, 0xF9, 0x66, 0xC1, 0xC1, 0x0C] ++ bytes_l106d50_4

theorem code_l106d50_3 : ∀ x ∈ codeRange 0x106e2d bytes_l106d50_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6e2d 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106d50_4

@[cfg_block] def b_l106d50_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x106de6 (xorR32R32Effect 0x106de6 3 11 13) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 13] []) (.reg (.gpr 11))) #v[100, 70]
    (.letOp (n := 129) (.exec 0x106de6 (fun s => s.RIP = 0x106de6) (xorR32R32Effect 0x106de6 3 11 13) (Reg.operands [.gpr 11, .gpr 13] [])) #v[100, 70]
    (.letOp (n := 130) (.out 0x106de9 (movR32R32Effect 0x106de9 3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[107]
    (.letOp (n := 131) (.exec 0x106de9 (fun s => s.RIP = 0x106de9) (movR32R32Effect 0x106de9 3 13 2) (Reg.operands [.gpr 2] [])) #v[107]
    (.letOp (n := 132) (.out 0x106dec (xorR32R32Effect 0x106dec 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[107, 111]
    (.letOp (n := 133) (.exec 0x106dec (fun s => s.RIP = 0x106dec) (xorR32R32Effect 0x106dec 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[107, 111]
    (.letOp (n := 134) (.out 0x106def (movR32R32Effect 0x106def 3 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[109]
    (.letOp (n := 135) (.exec 0x106def (fun s => s.RIP = 0x106def) (movR32R32Effect 0x106def 3 15 9) (Reg.operands [.gpr 9] [])) #v[109]
    (.letOp (n := 136) (.out 0x106df2 (xorR32R32Effect 0x106df2 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[109, 113]
    (.letOp (n := 137) (.exec 0x106df2 (fun s => s.RIP = 0x106df2) (xorR32R32Effect 0x106df2 3 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[109, 113]
    (.letOp (n := 138) (.out 0x106df5 (rolR16Effect 0x106df5 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[126]
    (.letOp (n := 139) (.exec 0x106df5 (fun s => s.RIP = 0x106df5) (rolR16Effect 0x106df5 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 140) (.out 0x106df9 (xorR32R32Effect 0x106df9 3 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[61, 120]
    (.letOp (n := 141) (.exec 0x106df9 (fun s => s.RIP = 0x106df9) (xorR32R32Effect 0x106df9 3 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[61, 120]
    (.letOp (n := 142) (.out 0x106dfc (xorR32R32Effect 0x106dfc 3 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[128, 120]
    (.letOp (n := 143) (.exec 0x106dfc (fun s => s.RIP = 0x106dfc) (xorR32R32Effect 0x106dfc 3 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[128, 120]
    (.letOp (n := 144) (.out 0x106dff (xorR32R32Effect 0x106dff 2 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[132, 120]
    (.letOp (n := 145) (.exec 0x106dff (fun s => s.RIP = 0x106dff) (xorR32R32Effect 0x106dff 2 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[132, 120]
    (.letOp (n := 146) (.out 0x106e01 (xorR32R32Effect 0x106e01 3 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[136, 120]
    (.letOp (n := 147) (.exec 0x106e01 (fun s => s.RIP = 0x106e01) (xorR32R32Effect 0x106e01 3 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[136, 120]
    (.letOp (n := 148) (.out 0x106e04 (rolR16Effect 0x106e04 4 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[120]
    (.letOp (n := 149) (.exec 0x106e04 (fun s => s.RIP = 0x106e04) (rolR16Effect 0x106e04 4 5 8) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[120]
    (.letOp (n := 150) (.out 0x106e08 (xorR16M16Effect 0x106e08 6 7 (.sib 3 (some 12) 1 (.d8 0x32))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .gpr 12] []) (.reg (.gpr 7))) #v[138, 3, 105]
    (.letOp (n := 151) (.exec 0x106e08 (LoadPre 0x106e08 (fun s => AddrMode.addr (.sib 3 (some 12) 1 (.d8 0x32)) s (0x106e08 + BitVec.ofNat 64 6)) 2) (xorR16M16Effect 0x106e08 6 7 (.sib 3 (some 12) 1 (.d8 0x32))) (Reg.operands [.gpr 7, .gpr 3, .gpr 12] [])) #v[138, 3, 105]
    (.letOp (n := 152) (.out 0x106e0e (xorR32R32Effect 0x106e0e 2 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[124, 148]
    (.letOp (n := 153) (.exec 0x106e0e (fun s => s.RIP = 0x106e0e) (xorR32R32Effect 0x106e0e 2 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[124, 148]
    (.letOp (n := 154) (.out 0x106e10 (xorR32R32Effect 0x106e10 3 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[140, 150]
    (.letOp (n := 155) (.exec 0x106e10 (fun s => s.RIP = 0x106e10) (xorR32R32Effect 0x106e10 3 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[140, 150]
    (.letOp (n := 156) (.out 0x106e13 (movzxR32M16Effect 0x106e13 5 7 (.sib 4 none 0 (.d8 0x12))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 157) (.exec 0x106e13 (LoadPre 0x106e13 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106e13 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106e13 5 7 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 158) (.exec 0x106e18 (StorePre 0x106e18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106e18 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106e18 5 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[152, 4]
    (.letOp (n := 159) (.exec 0x106e1d (StorePre 0x106e1d 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106e1d + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106e1d 6 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[154, 4]
    (.letOp (n := 160) (.out 0x106e23 (movR32M32LowEffect 0x106e23 6 (.sib 4 none 0 (.d8 0x3c))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 161) (.exec 0x106e23 (LoadPre 0x106e23 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106e23 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106e23 6 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 162) (.out 0x106e27 (movR32R32Effect 0x106e27 2 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[160]
    (.letOp (n := 163) (.exec 0x106e27 (fun s => s.RIP = 0x106e27) (movR32R32Effect 0x106e27 2 1 6) (Reg.operands [.gpr 6] [])) #v[160]
    (.letOp (n := 164) (.out 0x106e29 (rolR16Effect 0x106e29 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x106e29 (fun s => s.RIP = 0x106e29) (rolR16Effect 0x106e29 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[162]
    (b_l106d50_3))))))))))))))))))))))))))))))))))))))

def bytes_l106d50_2 : List UInt8 :=
  [0x45, 0x31, 0xEB, 0x41, 0x89, 0xD5, 0x44, 0x31, 0xD2, 0x45, 0x89, 0xCF, 0x41, 0x31, 0xF1, 0x66,
    0xC1, 0xC7, 0x08, 0x41, 0x31, 0xEE, 0x41, 0x31, 0xEB, 0x31, 0xEA, 0x41, 0x31, 0xE9, 0x66, 0xC1,
    0xC5, 0x08, 0x66, 0x42, 0x33, 0x7C, 0x63, 0x32, 0x31, 0xE8, 0x41, 0x31, 0xFE, 0x0F, 0xB7, 0x7C,
    0x24, 0x12, 0x66, 0x89, 0x44, 0x24, 0x16, 0x66, 0x44, 0x89, 0x74, 0x24, 0x08, 0x8B, 0x74, 0x24,
    0x3C, 0x89, 0xF1, 0x66, 0xC1, 0xC1, 0x08] ++ bytes_l106d50_3

theorem code_l106d50_2 : ∀ x ∈ codeRange 0x106de6 bytes_l106d50_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6de6 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106d50_3

@[cfg_block] def b_l106d50_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x106da6 (movR32R32Effect 0x106da6 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 92) (.exec 0x106da6 (fun s => s.RIP = 0x106da6) (movR32R32Effect 0x106da6 2 1 0) (Reg.operands [.gpr 0] [])) #v[79]
    (.letOp (n := 93) (.out 0x106da8 (rolR16Effect 0x106da8 4 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[91]
    (.letOp (n := 94) (.exec 0x106da8 (fun s => s.RIP = 0x106da8) (rolR16Effect 0x106da8 4 1 12) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[91]
    (.letOp (n := 95) (.exec 0x106dac (StorePre 0x106dac 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x24)) s (0x106dac + BitVec.ofNat 64 4)) 4) (movM32R32LowEffect 0x106dac 1 (.sib 4 none 0 (.d8 0x24))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[93, 4]
    (.letOp (n := 96) (.out 0x106db0 (movR32R32Effect 0x106db0 2 7 5) (EffectPart.reads (.reg (.gpr 7)) [.gpr 5] []) (.reg (.gpr 7))) #v[85]
    (.letOp (n := 97) (.exec 0x106db0 (fun s => s.RIP = 0x106db0) (movR32R32Effect 0x106db0 2 7 5) (Reg.operands [.gpr 5] [])) #v[85]
    (.letOp (n := 98) (.out 0x106db2 (rolR16Effect 0x106db2 4 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[96]
    (.letOp (n := 99) (.exec 0x106db2 (fun s => s.RIP = 0x106db2) (rolR16Effect 0x106db2 4 7 12) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[96]
    (.letOp (n := 100) (.out 0x106db6 (xorR32R32Effect 0x106db6 3 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[53, 61]
    (.letOp (n := 101) (.exec 0x106db6 (fun s => s.RIP = 0x106db6) (xorR32R32Effect 0x106db6 3 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[53, 61]
    (.letOp (n := 102) (.out 0x106db9 (xorR32R32Effect 0x106db9 3 12 13) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 13] []) (.reg (.gpr 12))) #v[68, 70]
    (.letOp (n := 103) (.exec 0x106db9 (fun s => s.RIP = 0x106db9) (xorR32R32Effect 0x106db9 3 12 13) (Reg.operands [.gpr 12, .gpr 13] [])) #v[68, 70]
    (.letOp (n := 104) (.exec 0x106dbc (StorePre 0x106dbc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3c)) s (0x106dbc + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106dbc 12 (.sib 4 none 0 (.d8 0x3c))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 105) (.out 0x106dc1 (movR64M64Effect 0x106dc1 12 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 106) (.exec 0x106dc1 (LoadPre 0x106dc1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106dc1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106dc1 12 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 107) (.out 0x106dc6 (xorR32R32Effect 0x106dc6 3 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[55, 76]
    (.letOp (n := 108) (.exec 0x106dc6 (fun s => s.RIP = 0x106dc6) (xorR32R32Effect 0x106dc6 3 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[55, 76]
    (.letOp (n := 109) (.out 0x106dc9 (xorR32R32Effect 0x106dc9 3 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[63, 83]
    (.letOp (n := 110) (.exec 0x106dc9 (fun s => s.RIP = 0x106dc9) (xorR32R32Effect 0x106dc9 3 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[63, 83]
    (.letOp (n := 111) (.out 0x106dcc (movR32R32Effect 0x106dcc 3 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[83]
    (.letOp (n := 112) (.exec 0x106dcc (fun s => s.RIP = 0x106dcc) (movR32R32Effect 0x106dcc 3 10 6) (Reg.operands [.gpr 6] [])) #v[83]
    (.letOp (n := 113) (.out 0x106dcf (movR32R32Effect 0x106dcf 3 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[89]
    (.letOp (n := 114) (.exec 0x106dcf (fun s => s.RIP = 0x106dcf) (movR32R32Effect 0x106dcf 3 6 15) (Reg.operands [.gpr 15] [])) #v[89]
    (.letOp (n := 115) (.out 0x106dd2 (xorR32R32Effect 0x106dd2 3 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[72, 89]
    (.letOp (n := 116) (.exec 0x106dd2 (fun s => s.RIP = 0x106dd2) (xorR32R32Effect 0x106dd2 3 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[72, 89]
    (.letOp (n := 117) (.exec 0x106dd5 (StorePre 0x106dd5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x106dd5 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106dd5 8 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 118) (.out 0x106dda (xorR32R32Effect 0x106dda 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[79, 93]
    (.letOp (n := 119) (.exec 0x106dda (fun s => s.RIP = 0x106dda) (xorR32R32Effect 0x106dda 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[79, 93]
    (.letOp (n := 120) (.out 0x106ddc (xorR32R32Effect 0x106ddc 2 5 7) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 7] []) (.reg (.gpr 5))) #v[85, 98]
    (.letOp (n := 121) (.exec 0x106ddc (fun s => s.RIP = 0x106ddc) (xorR32R32Effect 0x106ddc 2 5 7) (Reg.operands [.gpr 5, .gpr 7] [])) #v[85, 98]
    (.letOp (n := 122) (.out 0x106dde (movR32R32Effect 0x106dde 3 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[118]
    (.letOp (n := 123) (.exec 0x106dde (fun s => s.RIP = 0x106dde) (movR32R32Effect 0x106dde 3 8 0) (Reg.operands [.gpr 0] [])) #v[118]
    (.letOp (n := 124) (.out 0x106de1 (xorR32R32Effect 0x106de1 2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 7] []) (.reg (.gpr 0))) #v[118, 98]
    (.letOp (n := 125) (.exec 0x106de1 (fun s => s.RIP = 0x106de1) (xorR32R32Effect 0x106de1 2 0 7) (Reg.operands [.gpr 0, .gpr 7] [])) #v[118, 98]
    (.letOp (n := 126) (.out 0x106de3 (movR32R32Effect 0x106de3 3 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 11] []) (.reg (.gpr 7))) #v[100]
    (.letOp (n := 127) (.exec 0x106de3 (fun s => s.RIP = 0x106de3) (movR32R32Effect 0x106de3 3 7 11) (Reg.operands [.gpr 11] [])) #v[100]
    (b_l106d50_2)))))))))))))))))))))))))))))))))))))

def bytes_l106d50_1 : List UInt8 :=
  [0x89, 0xC1, 0x66, 0xC1, 0xC1, 0x0C, 0x89, 0x4C, 0x24, 0x24, 0x89, 0xEF, 0x66, 0xC1, 0xC7, 0x0C,
    0x45, 0x31, 0xF3, 0x45, 0x31, 0xEC, 0x44, 0x89, 0x64, 0x24, 0x3C, 0x4C, 0x8B, 0x64, 0x24, 0x28,
    0x44, 0x31, 0xD2, 0x41, 0x31, 0xF1, 0x41, 0x89, 0xF2, 0x44, 0x89, 0xFE, 0x45, 0x31, 0xF8, 0x44,
    0x89, 0x44, 0x24, 0x1C, 0x31, 0xC8, 0x31, 0xFD, 0x41, 0x89, 0xC0, 0x31, 0xF8, 0x44, 0x89, 0xDF] ++ bytes_l106d50_2

theorem code_l106d50_1 : ∀ x ∈ codeRange 0x106da6 bytes_l106d50_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6da6 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106d50_2

@[cfg_block] def b_l106d50 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106d50 (movR32M32Effect 0x106d50 11 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x106d50 (LoadPre 0x106d50 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106d50 + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106d50 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106d55 (movR32M32LowEffect 0x106d55 2 (.sib 4 none 0 (.d8 0xc))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x106d55 (LoadPre 0x106d55 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106d55 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d55 2 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x106d59 (movzxR32M16Effect 0x106d59 5 0 (.sib 4 none 0 (.d8 0xa))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 58) (.exec 0x106d59 (LoadPre 0x106d59 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106d59 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106d59 5 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x106d5e (movR32R32Effect 0x106d5e 3 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 11] []) (.reg (.gpr 14))) #v[53]
    (.letOp (n := 60) (.exec 0x106d5e (fun s => s.RIP = 0x106d5e) (movR32R32Effect 0x106d5e 3 14 11) (Reg.operands [.gpr 11] [])) #v[53]
    (.letOp (n := 61) (.out 0x106d61 (rolR16Effect 0x106d61 5 14 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[59]
    (.letOp (n := 62) (.exec 0x106d61 (fun s => s.RIP = 0x106d61) (rolR16Effect 0x106d61 5 14 12) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x106d66 (movzxR32M16Effect 0x106d66 6 9 (.sib 4 none 0 (.d8 0xe))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x106d66 (LoadPre 0x106d66 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106d66 + BitVec.ofNat 64 6)) 2) (movzxR32M16Effect 0x106d66 6 9 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x106d6c (movR32R32Effect 0x106d6c 3 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[57]
    (.letOp (n := 66) (.exec 0x106d6c (fun s => s.RIP = 0x106d6c) (movR32R32Effect 0x106d6c 3 13 0) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 67) (.exec 0x106d6f (StorePre 0x106d6f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x106d6f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x106d6f 12 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[12, 4]
    (.letOp (n := 68) (.out 0x106d74 (movR32R32Effect 0x106d74 3 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 69) (.exec 0x106d74 (fun s => s.RIP = 0x106d74) (movR32R32Effect 0x106d74 3 12 0) (Reg.operands [.gpr 0] [])) #v[57]
    (.letOp (n := 70) (.out 0x106d77 (rolR16Effect 0x106d77 5 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 71) (.exec 0x106d77 (fun s => s.RIP = 0x106d77) (rolR16Effect 0x106d77 5 13 12) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 72) (.out 0x106d7c (movR32M32Effect 0x106d7c 8 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 73) (.exec 0x106d7c (LoadPre 0x106d7c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106d7c + BitVec.ofNat 64 5)) 4) (movR32M32Effect 0x106d7c 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 74) (.out 0x106d81 (movR32R32Effect 0x106d81 3 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[55]
    (.letOp (n := 75) (.exec 0x106d81 (fun s => s.RIP = 0x106d81) (movR32R32Effect 0x106d81 3 10 2) (Reg.operands [.gpr 2] [])) #v[55]
    (.letOp (n := 76) (.out 0x106d84 (rolR16Effect 0x106d84 5 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[74]
    (.letOp (n := 77) (.exec 0x106d84 (fun s => s.RIP = 0x106d84) (rolR16Effect 0x106d84 5 10 12) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 78) (.exec 0x106d89 (StorePre 0x106d89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x106d89 + BitVec.ofNat 64 5)) 4) (movM32R32Effect 0x106d89 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x106d8e (movR32M32LowEffect 0x106d8e 0 (.sib 4 none 0 (.d8 0x14))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x106d8e (LoadPre 0x106d8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106d8e + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x106d8e 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x106d92 (movR32R32Effect 0x106d92 3 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[63]
    (.letOp (n := 82) (.exec 0x106d92 (fun s => s.RIP = 0x106d92) (movR32R32Effect 0x106d92 3 6 9) (Reg.operands [.gpr 9] [])) #v[63]
    (.letOp (n := 83) (.out 0x106d95 (rolR16Effect 0x106d95 4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[81]
    (.letOp (n := 84) (.exec 0x106d95 (fun s => s.RIP = 0x106d95) (rolR16Effect 0x106d95 4 6 12) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[81]
    (.letOp (n := 85) (.out 0x106d99 (movzxR32M16Effect 0x106d99 5 5 (.sib 4 none 0 (.d8 0x16))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 86) (.exec 0x106d99 (LoadPre 0x106d99 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106d99 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x106d99 5 5 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 87) (.out 0x106d9e (movR32R32Effect 0x106d9e 3 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[72]
    (.letOp (n := 88) (.exec 0x106d9e (fun s => s.RIP = 0x106d9e) (movR32R32Effect 0x106d9e 3 15 8) (Reg.operands [.gpr 8] [])) #v[72]
    (.letOp (n := 89) (.out 0x106da1 (rolR16Effect 0x106da1 5 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[87]
    (.letOp (n := 90) (.exec 0x106da1 (fun s => s.RIP = 0x106da1) (rolR16Effect 0x106da1 5 15 12) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (b_l106d50_1))))))))))))))))))))))))))))))))))))))

def bytes_l106d50 : List UInt8 :=
  [0x44, 0x8B, 0x5C, 0x24, 0x08, 0x8B, 0x54, 0x24, 0x0C, 0x0F, 0xB7, 0x44, 0x24, 0x0A, 0x45, 0x89,
    0xDE, 0x66, 0x41, 0xC1, 0xC6, 0x0C, 0x44, 0x0F, 0xB7, 0x4C, 0x24, 0x0E, 0x41, 0x89, 0xC5, 0x4C,
    0x89, 0x64, 0x24, 0x28, 0x41, 0x89, 0xC4, 0x66, 0x41, 0xC1, 0xC5, 0x0C, 0x44, 0x8B, 0x44, 0x24,
    0x10, 0x41, 0x89, 0xD2, 0x66, 0x41, 0xC1, 0xC2, 0x0C, 0x44, 0x89, 0x54, 0x24, 0x20, 0x8B, 0x44,
    0x24, 0x14, 0x44, 0x89, 0xCE, 0x66, 0xC1, 0xC6, 0x0C, 0x0F, 0xB7, 0x6C, 0x24, 0x16, 0x45, 0x89,
    0xC7, 0x66, 0x41, 0xC1, 0xC7, 0x0C] ++ bytes_l106d50_1

theorem code_l106d50 : ∀ x ∈ codeRange 0x106d50 bytes_l106d50, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6d50 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106d50_1

@[cfg_block] def b_l106ebc_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x106fa0 (xorR32R32Effect 0x106fa0 2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[0, 164]
    (.letOp (n := 167) (.exec 0x106fa0 (fun s => s.RIP = 0x106fa0) (xorR32R32Effect 0x106fa0 2 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 164]
    (.letOp (n := 168) (.out 0x106fa2 (shlR32Effect 0x106fa2 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[164]
    (.letOp (n := 169) (.exec 0x106fa2 (fun s => s.RIP = 0x106fa2) (shlR32Effect 0x106fa2 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[164]
    (.letOp (n := 170) (.out 0x106fa5 (xorR32R32Effect 0x106fa5 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[168, 166]
    (.letOp (n := 171) (.exec 0x106fa5 (fun s => s.RIP = 0x106fa5) (xorR32R32Effect 0x106fa5 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[168, 166]
    (.letOp (n := 172) (.exec 0x106fa7 (StorePre 0x106fa7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x106fa7 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106fa7 5 1 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[170, 4]
    (.letOp (n := 173) (.out 0x106fac (leaR64Effect 0x106fac 15 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 174) (.exec 0x106fac (fun s => s.RIP = 0x106fac) (leaR64Effect 0x106fac 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 175) (.out 0x106fb1 (movR32Imm32Effect 0x106fb1 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 176) (.exec 0x106fb1 (fun s => s.RIP = 0x106fb1) (movR32Imm32Effect 0x106fb1 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 177) (.out 0x106fb6 (movR64R64Effect 0x106fb6 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[173]
    (.letOp (n := 178) (.exec 0x106fb6 (fun s => s.RIP = 0x106fb6) (movR64R64Effect 0x106fb6 7 15) (Reg.operands [.gpr 15] [])) #v[173]
    (.letOp (n := 179) (.out 0x106fb9 (callEffect (fun _ => 0x100b10) 0x106fbe) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 180) (.exec 0x106fb9 (PushPre 0x106fb9 5) (callEffect (fun _ => 0x100b10) 0x106fbe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 181) (.const ⟨64, 0x106fbe⟩) #v[]
    (.terminate (.call ⟨.l100b10, RegMap.args [(0, 166), (1, 170), (2, 155), (3, 3), (4, 179), (5, 5), (6, 175), (7, 177), (8, 110), (9, 95), (10, 80), (11, 65), (12, 12), (13, 13), (14, 14), (15, 173), (22, 22), (39, 39), (50, 50), (51, 51)] 182⟩ { target := .l106fbe, kept := #v[], arity := rfl, guard := some (Fin.last 181) })))))))))))))))))

def bytes_l106ebc_3 : List UInt8 :=
  [0x31, 0xC8, 0xC1, 0xE1, 0x02, 0x31, 0xC1, 0x66, 0x89, 0x4C, 0x24, 0x16, 0x4C, 0x8D, 0x7C, 0x24,
    0x08, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0xE8, 0x52, 0x9B, 0xFF, 0xFF]

theorem code_l106ebc_3 : ∀ x ∈ codeRange 0x106fa0 bytes_l106ebc_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x6fa0 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106ebc_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x106f5e (movzxR32R16Effect 0x106f5e 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 129) (.exec 0x106f5e (fun s => s.RIP = 0x106f5e) (movzxR32R16Effect 0x106f5e 3 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 130) (.out 0x106f61 (shrR32Effect 0x106f61 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[128]
    (.letOp (n := 131) (.exec 0x106f61 (fun s => s.RIP = 0x106f61) (shrR32Effect 0x106f61 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 132) (.out 0x106f64 (xorR32R32Effect 0x106f64 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[130, 2]
    (.letOp (n := 133) (.exec 0x106f64 (fun s => s.RIP = 0x106f64) (xorR32R32Effect 0x106f64 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[130, 2]
    (.letOp (n := 134) (.out 0x106f66 (andR32Imm32Effect 0x106f66 6 6 0x3030) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[132]
    (.letOp (n := 135) (.exec 0x106f66 (fun s => s.RIP = 0x106f66) (andR32Imm32Effect 0x106f66 6 6 0x3030) (Reg.operands [.gpr 6] [])) #v[132]
    (.letOp (n := 136) (.out 0x106f6c (xorR32R32Effect 0x106f6c 2 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[2, 134]
    (.letOp (n := 137) (.exec 0x106f6c (fun s => s.RIP = 0x106f6c) (xorR32R32Effect 0x106f6c 2 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[2, 134]
    (.letOp (n := 138) (.out 0x106f6e (shlR32Effect 0x106f6e 3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[134]
    (.letOp (n := 139) (.exec 0x106f6e (fun s => s.RIP = 0x106f6e) (shlR32Effect 0x106f6e 3 6 2) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[134]
    (.letOp (n := 140) (.out 0x106f71 (xorR32R32Effect 0x106f71 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[138, 136]
    (.letOp (n := 141) (.exec 0x106f71 (fun s => s.RIP = 0x106f71) (xorR32R32Effect 0x106f71 2 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[138, 136]
    (.letOp (n := 142) (.exec 0x106f73 (StorePre 0x106f73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x106f73 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f73 5 6 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[140, 4]
    (.letOp (n := 143) (.out 0x106f78 (movzxR32R16Effect 0x106f78 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 144) (.exec 0x106f78 (fun s => s.RIP = 0x106f78) (movzxR32R16Effect 0x106f78 3 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 145) (.out 0x106f7b (shrR32Effect 0x106f7b 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[143]
    (.letOp (n := 146) (.exec 0x106f7b (fun s => s.RIP = 0x106f7b) (shrR32Effect 0x106f7b 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[143]
    (.letOp (n := 147) (.out 0x106f7e (xorR32R32Effect 0x106f7e 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[145, 1]
    (.letOp (n := 148) (.exec 0x106f7e (fun s => s.RIP = 0x106f7e) (xorR32R32Effect 0x106f7e 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[145, 1]
    (.letOp (n := 149) (.out 0x106f80 (andR32Imm32Effect 0x106f80 6 2 0x3030) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[147]
    (.letOp (n := 150) (.exec 0x106f80 (fun s => s.RIP = 0x106f80) (andR32Imm32Effect 0x106f80 6 2 0x3030) (Reg.operands [.gpr 2] [])) #v[147]
    (.letOp (n := 151) (.out 0x106f86 (xorR32R32Effect 0x106f86 2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[1, 149]
    (.letOp (n := 152) (.exec 0x106f86 (fun s => s.RIP = 0x106f86) (xorR32R32Effect 0x106f86 2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[1, 149]
    (.letOp (n := 153) (.out 0x106f88 (shlR32Effect 0x106f88 3 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[149]
    (.letOp (n := 154) (.exec 0x106f88 (fun s => s.RIP = 0x106f88) (shlR32Effect 0x106f88 3 2 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[149]
    (.letOp (n := 155) (.out 0x106f8b (xorR32R32Effect 0x106f8b 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[153, 151]
    (.letOp (n := 156) (.exec 0x106f8b (fun s => s.RIP = 0x106f8b) (xorR32R32Effect 0x106f8b 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[153, 151]
    (.letOp (n := 157) (.exec 0x106f8d (StorePre 0x106f8d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x106f8d + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f8d 5 2 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[155, 4]
    (.letOp (n := 158) (.out 0x106f92 (movzxR32R16Effect 0x106f92 3 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 159) (.exec 0x106f92 (fun s => s.RIP = 0x106f92) (movzxR32R16Effect 0x106f92 3 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 160) (.out 0x106f95 (shrR32Effect 0x106f95 3 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[158]
    (.letOp (n := 161) (.exec 0x106f95 (fun s => s.RIP = 0x106f95) (shrR32Effect 0x106f95 3 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[158]
    (.letOp (n := 162) (.out 0x106f98 (xorR32R32Effect 0x106f98 2 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[160, 0]
    (.letOp (n := 163) (.exec 0x106f98 (fun s => s.RIP = 0x106f98) (xorR32R32Effect 0x106f98 2 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[160, 0]
    (.letOp (n := 164) (.out 0x106f9a (andR32Imm32Effect 0x106f9a 6 1 0x3030) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[162]
    (.letOp (n := 165) (.exec 0x106f9a (fun s => s.RIP = 0x106f9a) (andR32Imm32Effect 0x106f9a 6 1 0x3030) (Reg.operands [.gpr 1] [])) #v[162]
    (b_l106ebc_3))))))))))))))))))))))))))))))))))))))

def bytes_l106ebc_2 : List UInt8 :=
  [0x0F, 0xB7, 0xF2, 0xC1, 0xEE, 0x02, 0x31, 0xD6, 0x81, 0xE6, 0x30, 0x30, 0x00, 0x00, 0x31, 0xF2,
    0xC1, 0xE6, 0x02, 0x31, 0xD6, 0x66, 0x89, 0x74, 0x24, 0x12, 0x0F, 0xB7, 0xD1, 0xC1, 0xEA, 0x02,
    0x31, 0xCA, 0x81, 0xE2, 0x30, 0x30, 0x00, 0x00, 0x31, 0xD1, 0xC1, 0xE2, 0x02, 0x31, 0xCA, 0x66,
    0x89, 0x54, 0x24, 0x14, 0x0F, 0xB7, 0xC8, 0xC1, 0xE9, 0x02, 0x31, 0xC1, 0x81, 0xE1, 0x30, 0x30,
    0x00, 0x00] ++ bytes_l106ebc_3

theorem code_l106ebc_2 : ∀ x ∈ codeRange 0x106f5e bytes_l106ebc_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6f5e 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ebc_3

@[cfg_block] def b_l106ebc_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x106f12 (xorR32R32Effect 0x106f12 3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[8, 89]
    (.letOp (n := 92) (.exec 0x106f12 (fun s => s.RIP = 0x106f12) (xorR32R32Effect 0x106f12 3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[8, 89]
    (.letOp (n := 93) (.out 0x106f15 (shlR32Effect 0x106f15 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[89]
    (.letOp (n := 94) (.exec 0x106f15 (fun s => s.RIP = 0x106f15) (shlR32Effect 0x106f15 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[89]
    (.letOp (n := 95) (.out 0x106f19 (xorR32R32Effect 0x106f19 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[93, 91]
    (.letOp (n := 96) (.exec 0x106f19 (fun s => s.RIP = 0x106f19) (xorR32R32Effect 0x106f19 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[93, 91]
    (.letOp (n := 97) (.exec 0x106f1c (StorePre 0x106f1c 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106f1c + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106f1c 6 9 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[95, 4]
    (.letOp (n := 98) (.out 0x106f22 (movzxR32R16Effect 0x106f22 4 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 99) (.exec 0x106f22 (fun s => s.RIP = 0x106f22) (movzxR32R16Effect 0x106f22 4 8 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 100) (.out 0x106f26 (shrR32Effect 0x106f26 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[98]
    (.letOp (n := 101) (.exec 0x106f26 (fun s => s.RIP = 0x106f26) (shrR32Effect 0x106f26 4 8 2) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[98]
    (.letOp (n := 102) (.out 0x106f2a (xorR32R32Effect 0x106f2a 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[100, 7]
    (.letOp (n := 103) (.exec 0x106f2a (fun s => s.RIP = 0x106f2a) (xorR32R32Effect 0x106f2a 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[100, 7]
    (.letOp (n := 104) (.out 0x106f2d (andR32Imm32Effect 0x106f2d 7 8 0x3030) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[102]
    (.letOp (n := 105) (.exec 0x106f2d (fun s => s.RIP = 0x106f2d) (andR32Imm32Effect 0x106f2d 7 8 0x3030) (Reg.operands [.gpr 8] [])) #v[102]
    (.letOp (n := 106) (.out 0x106f34 (xorR32R32Effect 0x106f34 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 8] []) (.reg (.gpr 7))) #v[7, 104]
    (.letOp (n := 107) (.exec 0x106f34 (fun s => s.RIP = 0x106f34) (xorR32R32Effect 0x106f34 3 7 8) (Reg.operands [.gpr 7, .gpr 8] [])) #v[7, 104]
    (.letOp (n := 108) (.out 0x106f37 (shlR32Effect 0x106f37 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[104]
    (.letOp (n := 109) (.exec 0x106f37 (fun s => s.RIP = 0x106f37) (shlR32Effect 0x106f37 4 8 2) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[104]
    (.letOp (n := 110) (.out 0x106f3b (xorR32R32Effect 0x106f3b 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[108, 106]
    (.letOp (n := 111) (.exec 0x106f3b (fun s => s.RIP = 0x106f3b) (xorR32R32Effect 0x106f3b 3 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[108, 106]
    (.letOp (n := 112) (.exec 0x106f3e (StorePre 0x106f3e 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106f3e + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106f3e 6 8 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[110, 4]
    (.letOp (n := 113) (.out 0x106f44 (movzxR32R16Effect 0x106f44 3 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 114) (.exec 0x106f44 (fun s => s.RIP = 0x106f44) (movzxR32R16Effect 0x106f44 3 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 115) (.out 0x106f47 (shrR32Effect 0x106f47 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[113]
    (.letOp (n := 116) (.exec 0x106f47 (fun s => s.RIP = 0x106f47) (shrR32Effect 0x106f47 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[113]
    (.letOp (n := 117) (.out 0x106f4a (xorR32R32Effect 0x106f4a 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[115, 6]
    (.letOp (n := 118) (.exec 0x106f4a (fun s => s.RIP = 0x106f4a) (xorR32R32Effect 0x106f4a 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[115, 6]
    (.letOp (n := 119) (.out 0x106f4c (andR32Imm32Effect 0x106f4c 6 7 0x3030) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[117]
    (.letOp (n := 120) (.exec 0x106f4c (fun s => s.RIP = 0x106f4c) (andR32Imm32Effect 0x106f4c 6 7 0x3030) (Reg.operands [.gpr 7] [])) #v[117]
    (.letOp (n := 121) (.out 0x106f52 (xorR32R32Effect 0x106f52 2 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[6, 119]
    (.letOp (n := 122) (.exec 0x106f52 (fun s => s.RIP = 0x106f52) (xorR32R32Effect 0x106f52 2 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[6, 119]
    (.letOp (n := 123) (.out 0x106f54 (shlR32Effect 0x106f54 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[119]
    (.letOp (n := 124) (.exec 0x106f54 (fun s => s.RIP = 0x106f54) (shlR32Effect 0x106f54 3 7 2) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 125) (.out 0x106f57 (xorR32R32Effect 0x106f57 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x106f57 (fun s => s.RIP = 0x106f57) (xorR32R32Effect 0x106f57 2 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[123, 121]
    (.letOp (n := 127) (.exec 0x106f59 (StorePre 0x106f59 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106f59 + BitVec.ofNat 64 5)) 2) (movM16R16Effect 0x106f59 5 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[125, 4]
    (b_l106ebc_2)))))))))))))))))))))))))))))))))))))

def bytes_l106ebc_1 : List UInt8 :=
  [0x45, 0x31, 0xC8, 0x41, 0xC1, 0xE1, 0x02, 0x45, 0x31, 0xC1, 0x66, 0x44, 0x89, 0x4C, 0x24, 0x0C,
    0x44, 0x0F, 0xB7, 0xC7, 0x41, 0xC1, 0xE8, 0x02, 0x41, 0x31, 0xF8, 0x41, 0x81, 0xE0, 0x30, 0x30,
    0x00, 0x00, 0x44, 0x31, 0xC7, 0x41, 0xC1, 0xE0, 0x02, 0x41, 0x31, 0xF8, 0x66, 0x44, 0x89, 0x44,
    0x24, 0x0E, 0x0F, 0xB7, 0xFE, 0xC1, 0xEF, 0x02, 0x31, 0xF7, 0x81, 0xE7, 0x30, 0x30, 0x00, 0x00,
    0x31, 0xFE, 0xC1, 0xE7, 0x02, 0x31, 0xF7, 0x66, 0x89, 0x7C, 0x24, 0x10] ++ bytes_l106ebc_2

theorem code_l106ebc_1 : ∀ x ∈ codeRange 0x106f12 bytes_l106ebc_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6f12 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ebc_2

@[cfg_block] def b_l106ebc : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106ebc (movzxR32R16Effect 0x106ebc 4 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 54) (.exec 0x106ebc (fun s => s.RIP = 0x106ebc) (movzxR32R16Effect 0x106ebc 4 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 55) (.out 0x106ec0 (shrR32Effect 0x106ec0 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[53]
    (.letOp (n := 56) (.exec 0x106ec0 (fun s => s.RIP = 0x106ec0) (shrR32Effect 0x106ec0 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 57) (.out 0x106ec4 (xorR32R32Effect 0x106ec4 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[55, 10]
    (.letOp (n := 58) (.exec 0x106ec4 (fun s => s.RIP = 0x106ec4) (xorR32R32Effect 0x106ec4 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[55, 10]
    (.letOp (n := 59) (.out 0x106ec7 (andR32Imm32Effect 0x106ec7 7 11 0x3030) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[57]
    (.letOp (n := 60) (.exec 0x106ec7 (fun s => s.RIP = 0x106ec7) (andR32Imm32Effect 0x106ec7 7 11 0x3030) (Reg.operands [.gpr 11] [])) #v[57]
    (.letOp (n := 61) (.out 0x106ece (xorR32R32Effect 0x106ece 3 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[10, 59]
    (.letOp (n := 62) (.exec 0x106ece (fun s => s.RIP = 0x106ece) (xorR32R32Effect 0x106ece 3 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[10, 59]
    (.letOp (n := 63) (.out 0x106ed1 (shlR32Effect 0x106ed1 4 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[59]
    (.letOp (n := 64) (.exec 0x106ed1 (fun s => s.RIP = 0x106ed1) (shlR32Effect 0x106ed1 4 11 2) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 65) (.out 0x106ed5 (xorR32R32Effect 0x106ed5 3 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x106ed5 (fun s => s.RIP = 0x106ed5) (xorR32R32Effect 0x106ed5 3 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[63, 61]
    (.letOp (n := 67) (.exec 0x106ed8 (StorePre 0x106ed8 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106ed8 + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106ed8 6 11 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x106ede (movzxR32R16Effect 0x106ede 4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 69) (.exec 0x106ede (fun s => s.RIP = 0x106ede) (movzxR32R16Effect 0x106ede 4 10 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 70) (.out 0x106ee2 (shrR32Effect 0x106ee2 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[68]
    (.letOp (n := 71) (.exec 0x106ee2 (fun s => s.RIP = 0x106ee2) (shrR32Effect 0x106ee2 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x106ee6 (xorR32R32Effect 0x106ee6 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[70, 9]
    (.letOp (n := 73) (.exec 0x106ee6 (fun s => s.RIP = 0x106ee6) (xorR32R32Effect 0x106ee6 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[70, 9]
    (.letOp (n := 74) (.out 0x106ee9 (andR32Imm32Effect 0x106ee9 7 10 0x3030) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[72]
    (.letOp (n := 75) (.exec 0x106ee9 (fun s => s.RIP = 0x106ee9) (andR32Imm32Effect 0x106ee9 7 10 0x3030) (Reg.operands [.gpr 10] [])) #v[72]
    (.letOp (n := 76) (.out 0x106ef0 (xorR32R32Effect 0x106ef0 3 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[9, 74]
    (.letOp (n := 77) (.exec 0x106ef0 (fun s => s.RIP = 0x106ef0) (xorR32R32Effect 0x106ef0 3 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[9, 74]
    (.letOp (n := 78) (.out 0x106ef3 (shlR32Effect 0x106ef3 4 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[74]
    (.letOp (n := 79) (.exec 0x106ef3 (fun s => s.RIP = 0x106ef3) (shlR32Effect 0x106ef3 4 10 2) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[74]
    (.letOp (n := 80) (.out 0x106ef7 (xorR32R32Effect 0x106ef7 3 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[78, 76]
    (.letOp (n := 81) (.exec 0x106ef7 (fun s => s.RIP = 0x106ef7) (xorR32R32Effect 0x106ef7 3 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[78, 76]
    (.letOp (n := 82) (.exec 0x106efa (StorePre 0x106efa 6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106efa + BitVec.ofNat 64 6)) 2) (movM16R16Effect 0x106efa 6 10 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[80, 4]
    (.letOp (n := 83) (.out 0x106f00 (movzxR32R16Effect 0x106f00 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 84) (.exec 0x106f00 (fun s => s.RIP = 0x106f00) (movzxR32R16Effect 0x106f00 4 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 85) (.out 0x106f04 (shrR32Effect 0x106f04 4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[83]
    (.letOp (n := 86) (.exec 0x106f04 (fun s => s.RIP = 0x106f04) (shrR32Effect 0x106f04 4 9 2) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x106f08 (xorR32R32Effect 0x106f08 3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[85, 8]
    (.letOp (n := 88) (.exec 0x106f08 (fun s => s.RIP = 0x106f08) (xorR32R32Effect 0x106f08 3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[85, 8]
    (.letOp (n := 89) (.out 0x106f0b (andR32Imm32Effect 0x106f0b 7 9 0x3030) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[87]
    (.letOp (n := 90) (.exec 0x106f0b (fun s => s.RIP = 0x106f0b) (andR32Imm32Effect 0x106f0b 7 9 0x3030) (Reg.operands [.gpr 9] [])) #v[87]
    (b_l106ebc_1))))))))))))))))))))))))))))))))))))))

def bytes_l106ebc : List UInt8 :=
  [0x45, 0x0F, 0xB7, 0xDA, 0x41, 0xC1, 0xEB, 0x02, 0x45, 0x31, 0xD3, 0x41, 0x81, 0xE3, 0x30, 0x30,
    0x00, 0x00, 0x45, 0x31, 0xDA, 0x41, 0xC1, 0xE3, 0x02, 0x45, 0x31, 0xD3, 0x66, 0x44, 0x89, 0x5C,
    0x24, 0x08, 0x45, 0x0F, 0xB7, 0xD1, 0x41, 0xC1, 0xEA, 0x02, 0x45, 0x31, 0xCA, 0x41, 0x81, 0xE2,
    0x30, 0x30, 0x00, 0x00, 0x45, 0x31, 0xD1, 0x41, 0xC1, 0xE2, 0x02, 0x45, 0x31, 0xCA, 0x66, 0x44,
    0x89, 0x54, 0x24, 0x0A, 0x45, 0x0F, 0xB7, 0xC8, 0x41, 0xC1, 0xE9, 0x02, 0x45, 0x31, 0xC1, 0x41,
    0x81, 0xE1, 0x30, 0x30, 0x00, 0x00] ++ bytes_l106ebc_1

theorem code_l106ebc : ∀ x ∈ codeRange 0x106ebc bytes_l106ebc, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6ebc 86 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106ebc_1

@[cfg_block] def b_l106fbe_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x107030 (movR64R64Effect 0x107030 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 86) (.exec 0x107030 (fun s => s.RIP = 0x107030) (movR64R64Effect 0x107030 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 87) (.out 0x107033 (callEffect (fun _ => 0x109d90) 0x107038) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 88) (.exec 0x107033 (PushPre 0x107033 5) (callEffect (fun _ => 0x109d90) 0x107038) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 89) (.const ⟨64, 0x107038⟩) #v[]
    (.terminate (.call ⟨.l109d90, RegMap.args [(0, 76), (1, 53), (2, 79), (3, 81), (4, 87), (5, 5), (6, 85), (7, 83), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 90⟩ { target := .l107038, kept := #v[], arity := rfl, guard := some (Fin.last 89) }))))))

def bytes_l106fbe_1 : List UInt8 :=
  [0x4C, 0x89, 0xFE, 0xE8, 0x58, 0x2D, 0x00, 0x00]

theorem code_l106fbe_1 : ∀ x ∈ codeRange 0x107030 bytes_l106fbe_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7030 8 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l106fbe : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x106fbe (movR64M64Effect 0x106fbe 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x106fbe (LoadPre 0x106fbe (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x106fbe + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x106fbe 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x106fc3 (movzxR32M16Effect 0x106fc3 7 0 (.base 1 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x106fc3 (LoadPre 0x106fc3 (fun s => AddrMode.addr (.base 1 (.d32 0xe0)) s (0x106fc3 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fc3 7 0 (.base 1 (.d32 0xe0))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 57) (.exec 0x106fca (StorePre 0x106fca 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x106fca + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fca 5 16 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x106fcf (movzxR32M16Effect 0x106fcf 7 0 (.base 1 (.d32 0xe2))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 59) (.exec 0x106fcf (LoadPre 0x106fcf (fun s => AddrMode.addr (.base 1 (.d32 0xe2)) s (0x106fcf + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fcf 7 0 (.base 1 (.d32 0xe2))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 60) (.exec 0x106fd6 (StorePre 0x106fd6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x106fd6 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fd6 5 16 0 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[58, 4]
    (.letOp (n := 61) (.out 0x106fdb (movzxR32M16Effect 0x106fdb 7 0 (.base 1 (.d32 0xe4))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 62) (.exec 0x106fdb (LoadPre 0x106fdb (fun s => AddrMode.addr (.base 1 (.d32 0xe4)) s (0x106fdb + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fdb 7 0 (.base 1 (.d32 0xe4))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 63) (.exec 0x106fe2 (StorePre 0x106fe2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x106fe2 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fe2 5 16 0 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.out 0x106fe7 (movzxR32M16Effect 0x106fe7 7 0 (.base 1 (.d32 0xe6))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 65) (.exec 0x106fe7 (LoadPre 0x106fe7 (fun s => AddrMode.addr (.base 1 (.d32 0xe6)) s (0x106fe7 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fe7 7 0 (.base 1 (.d32 0xe6))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 66) (.exec 0x106fee (StorePre 0x106fee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x106fee + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106fee 5 16 0 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 67) (.out 0x106ff3 (movzxR32M16Effect 0x106ff3 7 0 (.base 1 (.d32 0xe8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x106ff3 (LoadPre 0x106ff3 (fun s => AddrMode.addr (.base 1 (.d32 0xe8)) s (0x106ff3 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106ff3 7 0 (.base 1 (.d32 0xe8))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 69) (.exec 0x106ffa (StorePre 0x106ffa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x106ffa + BitVec.ofNat 64 5)) 2) (xorMREffect 0x106ffa 5 16 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.out 0x106fff (movzxR32M16Effect 0x106fff 7 0 (.base 1 (.d32 0xea))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 71) (.exec 0x106fff (LoadPre 0x106fff (fun s => AddrMode.addr (.base 1 (.d32 0xea)) s (0x106fff + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x106fff 7 0 (.base 1 (.d32 0xea))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 72) (.exec 0x107006 (StorePre 0x107006 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x107006 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x107006 5 16 0 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[70, 4]
    (.letOp (n := 73) (.out 0x10700b (movzxR32M16Effect 0x10700b 7 0 (.base 1 (.d32 0xec))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 74) (.exec 0x10700b (LoadPre 0x10700b (fun s => AddrMode.addr (.base 1 (.d32 0xec)) s (0x10700b + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x10700b 7 0 (.base 1 (.d32 0xec))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 75) (.exec 0x107012 (StorePre 0x107012 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x107012 + BitVec.ofNat 64 5)) 2) (xorMREffect 0x107012 5 16 0 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.out 0x107017 (movzxR32M16Effect 0x107017 7 0 (.base 1 (.d32 0xee))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 77) (.exec 0x107017 (LoadPre 0x107017 (fun s => AddrMode.addr (.base 1 (.d32 0xee)) s (0x107017 + BitVec.ofNat 64 7)) 2) (movzxR32M16Effect 0x107017 7 0 (.base 1 (.d32 0xee))) (Reg.operands [.gpr 1] [])) #v[53]
    (.letOp (n := 78) (.exec 0x10701e (StorePre 0x10701e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x10701e + BitVec.ofNat 64 5)) 2) (xorMREffect 0x10701e 5 16 0 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[76, 4]
    (.letOp (n := 79) (.out 0x107023 (movR32Imm32Effect 0x107023 5 2 0x8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 80) (.exec 0x107023 (fun s => s.RIP = 0x107023) (movR32Imm32Effect 0x107023 5 2 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 81) (.out 0x107028 (movR64M64Effect 0x107028 3 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 82) (.exec 0x107028 (LoadPre 0x107028 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107028 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x107028 3 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 83) (.out 0x10702d (movR64R64Effect 0x10702d 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[81]
    (.letOp (n := 84) (.exec 0x10702d (fun s => s.RIP = 0x10702d) (movR64R64Effect 0x10702d 7 3) (Reg.operands [.gpr 3] [])) #v[81]
    (b_l106fbe_1))))))))))))))))))))))))))))))))

def bytes_l106fbe : List UInt8 :=
  [0x48, 0x8B, 0x4C, 0x24, 0x30, 0x0F, 0xB7, 0x81, 0xE0, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24,
    0x08, 0x0F, 0xB7, 0x81, 0xE2, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x0A, 0x0F, 0xB7, 0x81,
    0xE4, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x0C, 0x0F, 0xB7, 0x81, 0xE6, 0x00, 0x00, 0x00,
    0x66, 0x31, 0x44, 0x24, 0x0E, 0x0F, 0xB7, 0x81, 0xE8, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24,
    0x10, 0x0F, 0xB7, 0x81, 0xEA, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x12, 0x0F, 0xB7, 0x81,
    0xEC, 0x00, 0x00, 0x00, 0x66, 0x31, 0x44, 0x24, 0x14, 0x0F, 0xB7, 0x81, 0xEE, 0x00, 0x00, 0x00,
    0x66, 0x31, 0x44, 0x24, 0x16, 0xBA, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x40, 0x48,
    0x89, 0xDF] ++ bytes_l106fbe_1

theorem code_l106fbe : ∀ x ∈ codeRange 0x106fbe bytes_l106fbe, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x6fbe 114 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l106fbe_1

@[cfg_block] def b_l107038 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107038 (movR64R64Effect 0x107038 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x107038 (fun s => s.RIP = 0x107038) (movR64R64Effect 0x107038 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10703b (addR64Imm8Effect 0x10703b 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10703b (fun s => s.RIP = 0x10703b) (addR64Imm8Effect 0x10703b 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10703f (popR64Effect 0x10703f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x10703f (popR64Effect 0x10703f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x10703f (PopPre 0x10703f) (popR64Effect 0x10703f 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x107040 (popR64Effect 0x107040 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x107040 (popR64Effect 0x107040 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x107040 (PopPre 0x107040) (popR64Effect 0x107040 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x107042 (popR64Effect 0x107042 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x107042 (popR64Effect 0x107042 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x107042 (PopPre 0x107042) (popR64Effect 0x107042 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x107044 (popR64Effect 0x107044 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x107044 (popR64Effect 0x107044 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x107044 (PopPre 0x107044) (popR64Effect 0x107044 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x107046 (popR64Effect 0x107046 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x107046 (popR64Effect 0x107046 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x107046 (PopPre 0x107046) (popR64Effect 0x107046 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x107048 (popR64Effect 0x107048 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x107048 (popR64Effect 0x107048 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x107048 (PopPre 0x107048) (popR64Effect 0x107048 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x107049 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x107049 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x107049 (RetPre 0x107049) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l107038 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x83, 0xC4, 0x48, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F,
    0x5D, 0xC3]

theorem code_l107038 : ∀ x ∈ codeRange 0x107038 bytes_l107038, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7038 18 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107050 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107050 (pushR64Effect 0x107050 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x107050 (PushPre 0x107050 1) (pushR64Effect 0x107050 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x107051 (pushR64Effect 0x107051 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x107051 (PushPre 0x107051 2) (pushR64Effect 0x107051 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x107053 (pushR64Effect 0x107053 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x107053 (PushPre 0x107053 2) (pushR64Effect 0x107053 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x107055 (pushR64Effect 0x107055 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x107055 (PushPre 0x107055 2) (pushR64Effect 0x107055 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x107057 (pushR64Effect 0x107057 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x107057 (PushPre 0x107057 2) (pushR64Effect 0x107057 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x107059 (pushR64Effect 0x107059 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x107059 (PushPre 0x107059 1) (pushR64Effect 0x107059 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10705a (subR64Imm32Effect 0x10705a 4 0x6d8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10705a (fun s => s.RIP = 0x10705a) (subR64Imm32Effect 0x10705a 4 0x6d8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x107061 (movR64R64Effect 0x107061 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 6] []) (.reg (.gpr 3))) #v[6]
    (.letOp (n := 68) (.exec 0x107061 (fun s => s.RIP = 0x107061) (movR64R64Effect 0x107061 3 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x107064 (movR64M64Effect 0x107064 0 (.base 7 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 70) (.exec 0x107064 (LoadPre 0x107064 (fun s => AddrMode.addr (.base 7 .none) s (0x107064 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107064 0 (.base 7 .none)) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x107067 (xorR32R32Effect 0x107067 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 72) (.exec 0x107067 (fun s => s.RIP = 0x107067) (xorR32R32Effect 0x107067 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 73) (.out 0x107069 (movR64Imm64Effect 0x107069 2 0x1000001000) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 74) (.exec 0x107069 (fun s => s.RIP = 0x107069) (movR64Imm64Effect 0x107069 2 0x1000001000) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x107073 (movR64Imm64Effect 0x107073 6 0xf000f000f000f) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 76) (.exec 0x107073 (fun s => s.RIP = 0x107073) (movR64Imm64Effect 0x107073 6 0xf000f000f000f) (Reg.operands [] [])) #v[]
    (.letOp (n := 77) (.out 0x10707d (movR64Imm64Effect 0x10707d 7 0x1111111111111111) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 78) (.exec 0x10707d (fun s => s.RIP = 0x10707d) (movR64Imm64Effect 0x10707d 7 0x1111111111111111) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.exec 0x107087 (fun s => s.RIP = 0x107087) (fun _ => nopEffect 0x107087 9) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l107090, RegMap.args [(0, 69), (1, 71), (2, 73), (3, 67), (4, 65), (5, 5), (6, 75), (7, 77), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 80⟩))))))))))))))))))))))))))))

def bytes_l107050 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xD8, 0x06, 0x00,
    0x00, 0x48, 0x89, 0xF3, 0x48, 0x8B, 0x07, 0x31, 0xC9, 0x48, 0xBA, 0x00, 0x10, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x48, 0xBE, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x0F, 0x00, 0x48, 0xBF, 0x11,
    0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l107050 : ∀ x ∈ codeRange 0x107050 bytes_l107050, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7050 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107090_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.pure (condOp 5)) #v[90]
    (.terminate (.condBr (Fin.last 92) ⟨.l107090, RegMap.args [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩ ⟨.l1070dd, RegMap.args [(0, 0), (1, 88), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 85), (9, 71), (10, 75), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 93⟩))

def bytes_l107090_1 : List UInt8 :=
  [0x75, 0xB3]

theorem code_l107090_1 : ∀ x ∈ codeRange 0x1070db bytes_l107090_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x70db 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107090 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107090 (movzxR32M16Effect 0x107090 5 8 (.sib 0 (some 1) 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0, .gpr 1] []) (.reg (.gpr 8))) #v[0, 1]
    (.letOp (n := 54) (.exec 0x107090 (LoadPre 0x107090 (fun s => AddrMode.addr (.sib 0 (some 1) 1 .none) s (0x107090 + BitVec.ofNat 64 5)) 2) (movzxR32M16Effect 0x107090 5 8 (.sib 0 (some 1) 1 .none)) (Reg.operands [.gpr 0, .gpr 1] [])) #v[0, 1]
    (.letOp (n := 55) (.out 0x107095 (movR64R64Effect 0x107095 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[53]
    (.letOp (n := 56) (.exec 0x107095 (fun s => s.RIP = 0x107095) (movR64R64Effect 0x107095 9 8) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 57) (.out 0x107098 (shlR64Effect 0x107098 4 9 24) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 58) (.exec 0x107098 (fun s => s.RIP = 0x107098) (shlR64Effect 0x107098 4 9 24) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x10709c (orR64R64Effect 0x10709c 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[57, 53]
    (.letOp (n := 60) (.exec 0x10709c (fun s => s.RIP = 0x10709c) (orR64R64Effect 0x10709c 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[57, 53]
    (.letOp (n := 61) (.out 0x10709f (imulR64R64Effect 0x10709f 4 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[53, 2]
    (.letOp (n := 62) (.exec 0x10709f (fun s => s.RIP = 0x10709f) (imulR64R64Effect 0x10709f 4 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[53, 2]
    (.letOp (n := 63) (.out 0x1070a3 (orR64R64Effect 0x1070a3 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x1070a3 (fun s => s.RIP = 0x1070a3) (orR64R64Effect 0x1070a3 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x1070a6 (andR64R64Effect 0x1070a6 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[63, 6]
    (.letOp (n := 66) (.exec 0x1070a6 (fun s => s.RIP = 0x1070a6) (andR64R64Effect 0x1070a6 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 67) (.out 0x1070a9 (movR64R64Effect 0x1070a9 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[65]
    (.letOp (n := 68) (.exec 0x1070a9 (fun s => s.RIP = 0x1070a9) (movR64R64Effect 0x1070a9 9 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 69) (.out 0x1070ac (shlR64Effect 0x1070ac 4 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 70) (.exec 0x1070ac (fun s => s.RIP = 0x1070ac) (shlR64Effect 0x1070ac 4 9 6) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 71) (.out 0x1070b0 (orR64R64Effect 0x1070b0 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[69, 65]
    (.letOp (n := 72) (.exec 0x1070b0 (fun s => s.RIP = 0x1070b0) (orR64R64Effect 0x1070b0 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[69, 65]
    (.letOp (n := 73) (.out 0x1070b3 (movR64R64Effect 0x1070b3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 74) (.exec 0x1070b3 (fun s => s.RIP = 0x1070b3) (movR64R64Effect 0x1070b3 10 8) (Reg.operands [.gpr 8] [])) #v[65]
    (.letOp (n := 75) (.out 0x1070b6 (shlR64Effect 0x1070b6 4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[73]
    (.letOp (n := 76) (.exec 0x1070b6 (fun s => s.RIP = 0x1070b6) (shlR64Effect 0x1070b6 4 10 9) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x1070ba (leaR64Effect 0x1070ba 8 (.sib 10 (some 8) 3 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10, .gpr 8] []) (.reg (.gpr 8))) #v[75, 65]
    (.letOp (n := 78) (.exec 0x1070ba (fun s => s.RIP = 0x1070ba) (leaR64Effect 0x1070ba 8 (.sib 10 (some 8) 3 .none)) (Reg.operands [.gpr 10, .gpr 8] [])) #v[75, 65]
    (.letOp (n := 79) (.out 0x1070be (orR64R64Effect 0x1070be 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[77, 71]
    (.letOp (n := 80) (.exec 0x1070be (fun s => s.RIP = 0x1070be) (orR64R64Effect 0x1070be 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[77, 71]
    (.letOp (n := 81) (.out 0x1070c1 (andR64R64Effect 0x1070c1 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[79, 7]
    (.letOp (n := 82) (.exec 0x1070c1 (fun s => s.RIP = 0x1070c1) (andR64R64Effect 0x1070c1 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[79, 7]
    (.letOp (n := 83) (.out 0x1070c4 (leaR64Effect 0x1070c4 8 (.sib 8 (some 8) 2 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[81, 81]
    (.letOp (n := 84) (.exec 0x1070c4 (fun s => s.RIP = 0x1070c4) (leaR64Effect 0x1070c4 8 (.sib 8 (some 8) 2 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[81, 81]
    (.letOp (n := 85) (.out 0x1070c8 (leaR64Effect 0x1070c8 8 (.sib 8 (some 8) 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[83, 83]
    (.letOp (n := 86) (.exec 0x1070c8 (fun s => s.RIP = 0x1070c8) (leaR64Effect 0x1070c8 8 (.sib 8 (some 8) 1 .none)) (Reg.operands [.gpr 8, .gpr 8] [])) #v[83, 83]
    (.letOp (n := 87) (.exec 0x1070cc (StorePre 0x1070cc 8 (fun s => AddrMode.addr (.sib 4 (some 1) 3 (.d32 0x418)) s (0x1070cc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070cc 8 (.sib 4 (some 1) 3 (.d32 0x418))) (Reg.operands [.gpr 8, .gpr 4, .gpr 1] [])) #v[85, 4, 1]
    (.letOp (n := 88) (.out 0x1070d4 (incR64Effect 0x1070d4 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 89) (.exec 0x1070d4 (fun s => s.RIP = 0x1070d4) (incR64Effect 0x1070d4 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1]
    (.letOp (n := 90) (.out 0x1070d7 (cmpR64Imm8Effect 0x1070d7 1 0x58) (EffectPart.reads (.flag .ZF) [.gpr 1] []) (.flag .ZF)) #v[88]
    (.letOp (n := 91) (.exec 0x1070d7 (fun s => s.RIP = 0x1070d7) (cmpR64Imm8Effect 0x1070d7 1 0x58) (Reg.operands [.gpr 1] [])) #v[88]
    (b_l107090_1)))))))))))))))))))))))))))))))))))))))

def bytes_l107090 : List UInt8 :=
  [0x44, 0x0F, 0xB7, 0x04, 0x48, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x18, 0x4D, 0x09, 0xC1, 0x4C,
    0x0F, 0xAF, 0xC2, 0x4D, 0x09, 0xC8, 0x49, 0x21, 0xF0, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x06,
    0x4D, 0x09, 0xC1, 0x4D, 0x89, 0xC2, 0x49, 0xC1, 0xE2, 0x09, 0x4F, 0x8D, 0x04, 0xC2, 0x4D, 0x09,
    0xC8, 0x49, 0x21, 0xF8, 0x4F, 0x8D, 0x04, 0x80, 0x4F, 0x8D, 0x04, 0x40, 0x4C, 0x89, 0x84, 0xCC,
    0x18, 0x04, 0x00, 0x00, 0x48, 0xFF, 0xC1, 0x48, 0x83, 0xF9, 0x58] ++ bytes_l107090_1

theorem code_l107090 : ∀ x ∈ codeRange 0x107090 bytes_l107090, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7090 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107090_1

@[cfg_block] def b_l1070dd : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x1070dd (StorePre 0x1070dd 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x150)) s (0x1070dd + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x1070dd 0 (.sib 4 none 0 (.d32 0x150))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x1070e5 (leaR64Effect 0x1070e5 7 (.sib 4 none 0 (.d32 0x158))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 55) (.exec 0x1070e5 (fun s => s.RIP = 0x1070e5) (leaR64Effect 0x1070e5 7 (.sib 4 none 0 (.d32 0x158))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x1070ed (leaR64Effect 0x1070ed 6 (.sib 4 none 0 (.d32 0x418))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 57) (.exec 0x1070ed (fun s => s.RIP = 0x1070ed) (leaR64Effect 0x1070ed 6 (.sib 4 none 0 (.d32 0x418))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x1070f5 (movR32Imm32Effect 0x1070f5 5 2 0x2c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 59) (.exec 0x1070f5 (fun s => s.RIP = 0x1070f5) (movR32Imm32Effect 0x1070f5 5 2 0x2c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x1070fa (callEffect (callMemPtr 0x1070fa (.rip 0xfa108)) (0x1070fa + BitVec.ofNat 64 (callMemLen (.rip 0xfa108)))) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 61) (.exec 0x1070fa (GoesTo (CallMemPre 0x1070fa (.rip 0xfa108)) (callEffect (callMemPtr 0x1070fa (.rip 0xfa108)) (0x1070fa + BitVec.ofNat 64 (callMemLen (.rip 0xfa108)))) 0x103f00) (callEffect (callMemPtr 0x1070fa (.rip 0xfa108)) (0x1070fa + BitVec.ofNat 64 (callMemLen (.rip 0xfa108)))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.const ⟨64, 0x107100⟩) #v[]
    (.terminate (.call ⟨.l103f00, RegMap.args [(0, 0), (2, 58), (3, 3), (4, 60), (5, 5), (6, 56), (7, 54), (9, 9), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 63⟩ { target := .l107100, kept := #v[], arity := rfl, guard := some (Fin.last 62) })))))))))))

def bytes_l1070dd : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0x50, 0x01, 0x00, 0x00, 0x48, 0x8D, 0xBC, 0x24, 0x58, 0x01, 0x00, 0x00,
    0x48, 0x8D, 0xB4, 0x24, 0x18, 0x04, 0x00, 0x00, 0xBA, 0xC0, 0x02, 0x00, 0x00, 0xFF, 0x15, 0x08,
    0xA1, 0x0F, 0x00]

theorem code_l1070dd : ∀ x ∈ codeRange 0x1070dd bytes_l1070dd, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x70dd 35 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107100 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107100 (movR64M64Effect 0x107100 9 (.base 3 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 3] []) (.reg (.gpr 9))) #v[3]
    (.letOp (n := 54) (.exec 0x107100 (LoadPre 0x107100 (fun s => AddrMode.addr (.base 3 .none) s (0x107100 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x107100 9 (.base 3 .none)) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x107103 (movR64M64Effect 0x107103 0 (.base 3 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 56) (.exec 0x107103 (LoadPre 0x107103 (fun s => AddrMode.addr (.base 3 (.d8 0x8)) s (0x107103 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107103 0 (.base 3 (.d8 0x8))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 57) (.exec 0x107107 (StorePre 0x107107 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf0)) s (0x107107 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107107 0 (.sib 4 none 0 (.d32 0xf0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 58) (.out 0x10710f (movR64M64Effect 0x10710f 2 (.base 3 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[3]
    (.letOp (n := 59) (.exec 0x10710f (LoadPre 0x10710f (fun s => AddrMode.addr (.base 3 (.d8 0x10)) s (0x10710f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10710f 2 (.base 3 (.d8 0x10))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 60) (.out 0x107113 (movR64M64Effect 0x107113 0 (.base 3 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 61) (.exec 0x107113 (LoadPre 0x107113 (fun s => AddrMode.addr (.base 3 (.d8 0x18)) s (0x107113 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x107113 0 (.base 3 (.d8 0x18))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 62) (.out 0x107117 (movR64R64Effect 0x107117 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[60]
    (.letOp (n := 63) (.exec 0x107117 (fun s => s.RIP = 0x107117) (movR64R64Effect 0x107117 1 0) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 64) (.out 0x10711a (shrR64Effect 0x10711a 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[62]
    (.letOp (n := 65) (.exec 0x10711a (fun s => s.RIP = 0x10711a) (shrR64Effect 0x10711a 4 1 2) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[62]
    (.letOp (n := 66) (.exec 0x10711e (StorePre 0x10711e 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x140)) s (0x10711e + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10711e 0 (.sib 4 none 0 (.d32 0x140))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[60, 4]
    (.letOp (n := 67) (.out 0x107126 (andR32Imm8Effect 0x107126 3 0 0x3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[60]
    (.letOp (n := 68) (.exec 0x107126 (fun s => s.RIP = 0x107126) (andR32Imm8Effect 0x107126 3 0 0x3) (Reg.operands [.gpr 0] [])) #v[60]
    (.letOp (n := 69) (.exec 0x107129 (StorePre 0x107129 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe8)) s (0x107129 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107129 0 (.sib 4 none 0 (.d32 0xe8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[67, 4]
    (.letOp (n := 70) (.exec 0x107131 (StorePre 0x107131 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x148)) s (0x107131 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107131 1 (.sib 4 none 0 (.d32 0x148))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[64, 4]
    (.letOp (n := 71) (.out 0x107139 (testR64R64Effect 0x107139 1 1) (EffectPart.reads (.flag .ZF) [.gpr 1, .gpr 1] []) (.flag .ZF)) #v[64, 64]
    (.letOp (n := 72) (.exec 0x107139 (fun s => s.RIP = 0x107139) (testR64R64Effect 0x107139 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[64, 64]
    (.letOp (n := 73) (.exec 0x10713c (StorePre 0x10713c 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xf8)) s (0x10713c + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10713c 9 (.sib 4 none 0 (.d32 0xf8))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 74) (.pure (condOp 4)) #v[71]
    (.terminate (.condBr (Fin.last 74) ⟨.l10805f, RegMap.args [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l10714a, RegMap.args [(0, 67), (1, 64), (2, 58), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 53), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 71), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l107100 : List UInt8 :=
  [0x4C, 0x8B, 0x0B, 0x48, 0x8B, 0x43, 0x08, 0x48, 0x89, 0x84, 0x24, 0xF0, 0x00, 0x00, 0x00, 0x48,
    0x8B, 0x53, 0x10, 0x48, 0x8B, 0x43, 0x18, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x02, 0x48, 0x89,
    0x84, 0x24, 0x40, 0x01, 0x00, 0x00, 0x83, 0xE0, 0x03, 0x48, 0x89, 0x84, 0x24, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0x8C, 0x24, 0x48, 0x01, 0x00, 0x00, 0x48, 0x85, 0xC9, 0x4C, 0x89, 0x8C, 0x24,
    0xF8, 0x00, 0x00, 0x00, 0x0F, 0x84, 0x15, 0x0F, 0x00, 0x00]

theorem code_l107100 : ∀ x ∈ codeRange 0x107100 bytes_l107100, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7100 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10714a : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10714a (StorePre 0x10714a 12 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10714a + BitVec.ofNat 64 12)) 8) (movM64Imm32Effect 0x10714a (.sib 4 none 0 (.d32 0xe0)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x107156 (StorePre 0x107156 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x107156 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107156 2 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.terminate (.br ⟨.l107a08, RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (9, 9), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 55⟩)))

def bytes_l10714a : List UInt8 :=
  [0x48, 0xC7, 0x84, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x94, 0x24,
    0xD8, 0x00, 0x00, 0x00, 0xE9, 0xA5, 0x08, 0x00, 0x00]

theorem code_l10714a : ∀ x ∈ codeRange 0x10714a bytes_l10714a, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x714a 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107170_3 : Block Op Label signature Reg.count 166 :=
  .letOp (n := 166) (.out 0x10724f (xorR64R64Effect 0x10724f 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[164, 1]
    (.letOp (n := 167) (.exec 0x10724f (fun s => s.RIP = 0x10724f) (xorR64R64Effect 0x10724f 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[164, 1]
    (.letOp (n := 168) (.out 0x107252 (andR64R64Effect 0x107252 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[166, 64]
    (.letOp (n := 169) (.exec 0x107252 (fun s => s.RIP = 0x107252) (andR64R64Effect 0x107252 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[166, 64]
    (.letOp (n := 170) (.out 0x107255 (movR64R64Effect 0x107255 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[168]
    (.letOp (n := 171) (.exec 0x107255 (fun s => s.RIP = 0x107255) (movR64R64Effect 0x107255 6 2) (Reg.operands [.gpr 2] [])) #v[168]
    (.letOp (n := 172) (.out 0x107258 (shlR64Effect 0x107258 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[170]
    (.letOp (n := 173) (.exec 0x107258 (fun s => s.RIP = 0x107258) (shlR64Effect 0x107258 4 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x10725c (addR64R64Effect 0x10725c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[172, 168]
    (.letOp (n := 175) (.exec 0x10725c (fun s => s.RIP = 0x10725c) (addR64R64Effect 0x10725c 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[172, 168]
    (.letOp (n := 176) (.out 0x10725f (xorR64R64Effect 0x10725f 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[174, 1]
    (.letOp (n := 177) (.exec 0x10725f (fun s => s.RIP = 0x10725f) (xorR64R64Effect 0x10725f 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[174, 1]
    (.letOp (n := 178) (.exec 0x107262 (StorePre 0x107262 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x107262 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107262 6 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[176, 4]
    (.letOp (n := 179) (.out 0x107267 (movR64R64Effect 0x107267 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[0]
    (.letOp (n := 180) (.exec 0x107267 (fun s => s.RIP = 0x107267) (movR64R64Effect 0x107267 1 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 181) (.out 0x10726a (shrR64Effect 0x10726a 4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[179]
    (.letOp (n := 182) (.exec 0x10726a (fun s => s.RIP = 0x10726a) (shrR64Effect 0x10726a 4 1 8) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[179]
    (.letOp (n := 183) (.out 0x10726e (xorR64R64Effect 0x10726e 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[181, 0]
    (.letOp (n := 184) (.exec 0x10726e (fun s => s.RIP = 0x10726e) (xorR64R64Effect 0x10726e 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[181, 0]
    (.letOp (n := 185) (.out 0x107271 (andR64R64Effect 0x107271 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[183, 64]
    (.letOp (n := 186) (.exec 0x107271 (fun s => s.RIP = 0x107271) (andR64R64Effect 0x107271 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[183, 64]
    (.letOp (n := 187) (.out 0x107274 (movR64R64Effect 0x107274 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[185]
    (.letOp (n := 188) (.exec 0x107274 (fun s => s.RIP = 0x107274) (movR64R64Effect 0x107274 2 1) (Reg.operands [.gpr 1] [])) #v[185]
    (.letOp (n := 189) (.out 0x107277 (shlR64Effect 0x107277 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[187]
    (.letOp (n := 190) (.exec 0x107277 (fun s => s.RIP = 0x107277) (shlR64Effect 0x107277 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[187]
    (.letOp (n := 191) (.out 0x10727b (addR64R64Effect 0x10727b 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[189, 185]
    (.letOp (n := 192) (.exec 0x10727b (fun s => s.RIP = 0x10727b) (addR64R64Effect 0x10727b 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[189, 185]
    (.letOp (n := 193) (.out 0x10727e (xorR64R64Effect 0x10727e 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[191, 0]
    (.letOp (n := 194) (.exec 0x10727e (fun s => s.RIP = 0x10727e) (xorR64R64Effect 0x10727e 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[191, 0]
    (.letOp (n := 195) (.exec 0x107281 (StorePre 0x107281 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x107281 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107281 2 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[193, 4]
    (.letOp (n := 196) (.out 0x107286 (movR32Imm32Effect 0x107286 5 6 0x8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 197) (.exec 0x107286 (fun s => s.RIP = 0x107286) (movR32Imm32Effect 0x107286 5 6 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 198) (.out 0x10728b (leaR64Effect 0x10728b 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[4]
    (.letOp (n := 199) (.exec 0x10728b (fun s => s.RIP = 0x10728b) (leaR64Effect 0x10728b 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 200) (.out 0x107290 (movR64R64Effect 0x107290 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[198]
    (.letOp (n := 201) (.exec 0x107290 (fun s => s.RIP = 0x107290) (movR64R64Effect 0x107290 7 3) (Reg.operands [.gpr 3] [])) #v[198]
    (.letOp (n := 202) (.out 0x107293 (callEffect (fun _ => 0x100e90) 0x107298) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 203) (.exec 0x107293 (PushPre 0x107293 5) (callEffect (fun _ => 0x100e90) 0x107298) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 204) (.const ⟨64, 0x107298⟩) #v[]
    (.terminate (.call ⟨.l100e90, RegMap.args [(0, 0), (1, 185), (2, 193), (3, 198), (4, 202), (5, 56), (6, 196), (7, 200), (8, 142), (9, 125), (10, 108), (11, 91), (12, 12), (13, 13), (14, 64), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 205⟩ { target := .l107298, kept := #v[], arity := rfl, guard := some (Fin.last 204) }))))))))))))))))))))))))))))))))))))))))

def bytes_l107170_3 : List UInt8 :=
  [0x48, 0x31, 0xCA, 0x4C, 0x21, 0xF2, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xE6, 0x08, 0x48, 0x01, 0xD6,
    0x48, 0x31, 0xCE, 0x48, 0x89, 0x74, 0x24, 0x38, 0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE9, 0x08, 0x48,
    0x31, 0xC1, 0x4C, 0x21, 0xF1, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xE2, 0x08, 0x48, 0x01, 0xCA, 0x48,
    0x31, 0xC2, 0x48, 0x89, 0x54, 0x24, 0x40, 0xBE, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x5C, 0x24,
    0x08, 0x48, 0x89, 0xDF, 0xE8, 0xF8, 0x9B, 0xFF, 0xFF]

theorem code_l107170_3 : ∀ x ∈ codeRange 0x10724f bytes_l107170_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x724f 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l107170_2 : Block Op Label signature Reg.count 128 :=
  .letOp (n := 128) (.out 0x10720a (movR64R64Effect 0x10720a 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 129) (.exec 0x10720a (fun s => s.RIP = 0x10720a) (movR64R64Effect 0x10720a 7 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 130) (.out 0x10720d (shrR64Effect 0x10720d 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[128]
    (.letOp (n := 131) (.exec 0x10720d (fun s => s.RIP = 0x10720d) (shrR64Effect 0x10720d 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 132) (.out 0x107211 (xorR64R64Effect 0x107211 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[130, 6]
    (.letOp (n := 133) (.exec 0x107211 (fun s => s.RIP = 0x107211) (xorR64R64Effect 0x107211 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[130, 6]
    (.letOp (n := 134) (.out 0x107214 (andR64R64Effect 0x107214 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 14] []) (.reg (.gpr 7))) #v[132, 64]
    (.letOp (n := 135) (.exec 0x107214 (fun s => s.RIP = 0x107214) (andR64R64Effect 0x107214 7 14) (Reg.operands [.gpr 7, .gpr 14] [])) #v[132, 64]
    (.letOp (n := 136) (.out 0x107217 (movR64R64Effect 0x107217 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[134]
    (.letOp (n := 137) (.exec 0x107217 (fun s => s.RIP = 0x107217) (movR64R64Effect 0x107217 8 7) (Reg.operands [.gpr 7] [])) #v[134]
    (.letOp (n := 138) (.out 0x10721a (shlR64Effect 0x10721a 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[136]
    (.letOp (n := 139) (.exec 0x10721a (fun s => s.RIP = 0x10721a) (shlR64Effect 0x10721a 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[136]
    (.letOp (n := 140) (.out 0x10721e (addR64R64Effect 0x10721e 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[138, 134]
    (.letOp (n := 141) (.exec 0x10721e (fun s => s.RIP = 0x10721e) (addR64R64Effect 0x10721e 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[138, 134]
    (.letOp (n := 142) (.out 0x107221 (xorR64R64Effect 0x107221 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[140, 6]
    (.letOp (n := 143) (.exec 0x107221 (fun s => s.RIP = 0x107221) (xorR64R64Effect 0x107221 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[140, 6]
    (.letOp (n := 144) (.exec 0x107224 (StorePre 0x107224 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x107224 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107224 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[142, 4]
    (.letOp (n := 145) (.out 0x107229 (movR64R64Effect 0x107229 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 146) (.exec 0x107229 (fun s => s.RIP = 0x107229) (movR64R64Effect 0x107229 6 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 147) (.out 0x10722c (shrR64Effect 0x10722c 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[145]
    (.letOp (n := 148) (.exec 0x10722c (fun s => s.RIP = 0x10722c) (shrR64Effect 0x10722c 4 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[145]
    (.letOp (n := 149) (.out 0x107230 (xorR64R64Effect 0x107230 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[147, 2]
    (.letOp (n := 150) (.exec 0x107230 (fun s => s.RIP = 0x107230) (xorR64R64Effect 0x107230 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[147, 2]
    (.letOp (n := 151) (.out 0x107233 (andR64R64Effect 0x107233 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[149, 64]
    (.letOp (n := 152) (.exec 0x107233 (fun s => s.RIP = 0x107233) (andR64R64Effect 0x107233 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[149, 64]
    (.letOp (n := 153) (.out 0x107236 (movR64R64Effect 0x107236 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[151]
    (.letOp (n := 154) (.exec 0x107236 (fun s => s.RIP = 0x107236) (movR64R64Effect 0x107236 7 6) (Reg.operands [.gpr 6] [])) #v[151]
    (.letOp (n := 155) (.out 0x107239 (shlR64Effect 0x107239 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[153]
    (.letOp (n := 156) (.exec 0x107239 (fun s => s.RIP = 0x107239) (shlR64Effect 0x107239 4 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 157) (.out 0x10723d (addR64R64Effect 0x10723d 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6] []) (.reg (.gpr 7))) #v[155, 151]
    (.letOp (n := 158) (.exec 0x10723d (fun s => s.RIP = 0x10723d) (addR64R64Effect 0x10723d 7 6) (Reg.operands [.gpr 7, .gpr 6] [])) #v[155, 151]
    (.letOp (n := 159) (.out 0x107240 (xorR64R64Effect 0x107240 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[157, 2]
    (.letOp (n := 160) (.exec 0x107240 (fun s => s.RIP = 0x107240) (xorR64R64Effect 0x107240 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[157, 2]
    (.letOp (n := 161) (.exec 0x107243 (StorePre 0x107243 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x107243 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107243 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[159, 4]
    (.letOp (n := 162) (.out 0x107248 (movR64R64Effect 0x107248 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 163) (.exec 0x107248 (fun s => s.RIP = 0x107248) (movR64R64Effect 0x107248 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 164) (.out 0x10724b (shrR64Effect 0x10724b 4 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[162]
    (.letOp (n := 165) (.exec 0x10724b (fun s => s.RIP = 0x10724b) (shrR64Effect 0x10724b 4 2 8) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[162]
    (b_l107170_3))))))))))))))))))))))))))))))))))))))

def bytes_l107170_2 : List UInt8 :=
  [0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x08, 0x48, 0x31, 0xF7, 0x4C, 0x21, 0xF7, 0x49, 0x89, 0xF8,
    0x49, 0xC1, 0xE0, 0x08, 0x49, 0x01, 0xF8, 0x49, 0x31, 0xF0, 0x4C, 0x89, 0x44, 0x24, 0x28, 0x48,
    0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x08, 0x48, 0x31, 0xD6, 0x4C, 0x21, 0xF6, 0x48, 0x89, 0xF7, 0x48,
    0xC1, 0xE7, 0x08, 0x48, 0x01, 0xF7, 0x48, 0x31, 0xD7, 0x48, 0x89, 0x7C, 0x24, 0x30, 0x48, 0x89,
    0xCA, 0x48, 0xC1, 0xEA, 0x08] ++ bytes_l107170_3

theorem code_l107170_2 : ∀ x ∈ codeRange 0x10720a bytes_l107170_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x720a 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107170_3

@[cfg_block] def b_l107170_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.out 0x1071c4 (xorR64R64Effect 0x1071c4 11 9) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9] []) (.reg (.gpr 11))) #v[89, 9]
    (.letOp (n := 92) (.exec 0x1071c4 (fun s => s.RIP = 0x1071c4) (xorR64R64Effect 0x1071c4 11 9) (Reg.operands [.gpr 11, .gpr 9] [])) #v[89, 9]
    (.letOp (n := 93) (.exec 0x1071c7 (StorePre 0x1071c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1071c7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071c7 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[91, 4]
    (.letOp (n := 94) (.out 0x1071cc (movR64R64Effect 0x1071cc 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[8]
    (.letOp (n := 95) (.exec 0x1071cc (fun s => s.RIP = 0x1071cc) (movR64R64Effect 0x1071cc 9 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 96) (.out 0x1071cf (shrR64Effect 0x1071cf 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[94]
    (.letOp (n := 97) (.exec 0x1071cf (fun s => s.RIP = 0x1071cf) (shrR64Effect 0x1071cf 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[94]
    (.letOp (n := 98) (.out 0x1071d3 (xorR64R64Effect 0x1071d3 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[96, 8]
    (.letOp (n := 99) (.exec 0x1071d3 (fun s => s.RIP = 0x1071d3) (xorR64R64Effect 0x1071d3 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[96, 8]
    (.letOp (n := 100) (.out 0x1071d6 (andR64R64Effect 0x1071d6 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[98, 64]
    (.letOp (n := 101) (.exec 0x1071d6 (fun s => s.RIP = 0x1071d6) (andR64R64Effect 0x1071d6 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[98, 64]
    (.letOp (n := 102) (.out 0x1071d9 (movR64R64Effect 0x1071d9 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[100]
    (.letOp (n := 103) (.exec 0x1071d9 (fun s => s.RIP = 0x1071d9) (movR64R64Effect 0x1071d9 10 9) (Reg.operands [.gpr 9] [])) #v[100]
    (.letOp (n := 104) (.out 0x1071dc (shlR64Effect 0x1071dc 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[102]
    (.letOp (n := 105) (.exec 0x1071dc (fun s => s.RIP = 0x1071dc) (shlR64Effect 0x1071dc 4 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.out 0x1071e0 (addR64R64Effect 0x1071e0 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[104, 100]
    (.letOp (n := 107) (.exec 0x1071e0 (fun s => s.RIP = 0x1071e0) (addR64R64Effect 0x1071e0 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[104, 100]
    (.letOp (n := 108) (.out 0x1071e3 (xorR64R64Effect 0x1071e3 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[106, 8]
    (.letOp (n := 109) (.exec 0x1071e3 (fun s => s.RIP = 0x1071e3) (xorR64R64Effect 0x1071e3 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[106, 8]
    (.letOp (n := 110) (.exec 0x1071e6 (StorePre 0x1071e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1071e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071e6 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 111) (.out 0x1071eb (movR64R64Effect 0x1071eb 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[7]
    (.letOp (n := 112) (.exec 0x1071eb (fun s => s.RIP = 0x1071eb) (movR64R64Effect 0x1071eb 8 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 113) (.out 0x1071ee (shrR64Effect 0x1071ee 4 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[111]
    (.letOp (n := 114) (.exec 0x1071ee (fun s => s.RIP = 0x1071ee) (shrR64Effect 0x1071ee 4 8 8) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[111]
    (.letOp (n := 115) (.out 0x1071f2 (xorR64R64Effect 0x1071f2 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7] []) (.reg (.gpr 8))) #v[113, 7]
    (.letOp (n := 116) (.exec 0x1071f2 (fun s => s.RIP = 0x1071f2) (xorR64R64Effect 0x1071f2 8 7) (Reg.operands [.gpr 8, .gpr 7] [])) #v[113, 7]
    (.letOp (n := 117) (.out 0x1071f5 (andR64R64Effect 0x1071f5 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[115, 64]
    (.letOp (n := 118) (.exec 0x1071f5 (fun s => s.RIP = 0x1071f5) (andR64R64Effect 0x1071f5 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[115, 64]
    (.letOp (n := 119) (.out 0x1071f8 (movR64R64Effect 0x1071f8 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 8] []) (.reg (.gpr 9))) #v[117]
    (.letOp (n := 120) (.exec 0x1071f8 (fun s => s.RIP = 0x1071f8) (movR64R64Effect 0x1071f8 9 8) (Reg.operands [.gpr 8] [])) #v[117]
    (.letOp (n := 121) (.out 0x1071fb (shlR64Effect 0x1071fb 4 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[119]
    (.letOp (n := 122) (.exec 0x1071fb (fun s => s.RIP = 0x1071fb) (shlR64Effect 0x1071fb 4 9 8) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.out 0x1071ff (addR64R64Effect 0x1071ff 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[121, 117]
    (.letOp (n := 124) (.exec 0x1071ff (fun s => s.RIP = 0x1071ff) (addR64R64Effect 0x1071ff 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[121, 117]
    (.letOp (n := 125) (.out 0x107202 (xorR64R64Effect 0x107202 9 7) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 7] []) (.reg (.gpr 9))) #v[123, 7]
    (.letOp (n := 126) (.exec 0x107202 (fun s => s.RIP = 0x107202) (xorR64R64Effect 0x107202 9 7) (Reg.operands [.gpr 9, .gpr 7] [])) #v[123, 7]
    (.letOp (n := 127) (.exec 0x107205 (StorePre 0x107205 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x107205 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x107205 9 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[125, 4]
    (b_l107170_2)))))))))))))))))))))))))))))))))))))

def bytes_l107170_1 : List UInt8 :=
  [0x4D, 0x31, 0xCB, 0x4C, 0x89, 0x5C, 0x24, 0x10, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE9, 0x08, 0x4D,
    0x31, 0xC1, 0x4D, 0x21, 0xF1, 0x4D, 0x89, 0xCA, 0x49, 0xC1, 0xE2, 0x08, 0x4D, 0x01, 0xCA, 0x4D,
    0x31, 0xC2, 0x4C, 0x89, 0x54, 0x24, 0x18, 0x49, 0x89, 0xF8, 0x49, 0xC1, 0xE8, 0x08, 0x49, 0x31,
    0xF8, 0x4D, 0x21, 0xF0, 0x4D, 0x89, 0xC1, 0x49, 0xC1, 0xE1, 0x08, 0x4D, 0x01, 0xC1, 0x49, 0x31,
    0xF9, 0x4C, 0x89, 0x4C, 0x24, 0x20] ++ bytes_l107170_2

theorem code_l107170_1 : ∀ x ∈ codeRange 0x1071c4 bytes_l107170_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x71c4 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107170_2

@[cfg_block] def b_l107170 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107170 (movR64M64Effect 0x107170 5 (.sib 4 none 0 (.d32 0xe0))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 54) (.exec 0x107170 (LoadPre 0x107170 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x107170 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107170 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x107178 (StorePre 0x107178 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x107178 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x107178 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x107180 (shlR64Effect 0x107180 4 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[53]
    (.letOp (n := 57) (.exec 0x107180 (fun s => s.RIP = 0x107180) (shlR64Effect 0x107180 4 5 6) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 58) (.out 0x107184 (movR64R64Effect 0x107184 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[10]
    (.letOp (n := 59) (.exec 0x107184 (fun s => s.RIP = 0x107184) (movR64R64Effect 0x107184 11 10) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 60) (.out 0x107187 (shrR64Effect 0x107187 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[58]
    (.letOp (n := 61) (.exec 0x107187 (fun s => s.RIP = 0x107187) (shrR64Effect 0x107187 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x10718b (xorR64R64Effect 0x10718b 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[60, 10]
    (.letOp (n := 63) (.exec 0x10718b (fun s => s.RIP = 0x10718b) (xorR64R64Effect 0x10718b 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[60, 10]
    (.letOp (n := 64) (.out 0x10718e (movR64Imm64Effect 0x10718e 14 0xff000000ff0000) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 65) (.exec 0x10718e (fun s => s.RIP = 0x10718e) (movR64Imm64Effect 0x10718e 14 0xff000000ff0000) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x107198 (andR64R64Effect 0x107198 11 14) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 14] []) (.reg (.gpr 11))) #v[62, 64]
    (.letOp (n := 67) (.exec 0x107198 (fun s => s.RIP = 0x107198) (andR64R64Effect 0x107198 11 14) (Reg.operands [.gpr 11, .gpr 14] [])) #v[62, 64]
    (.letOp (n := 68) (.out 0x10719b (movR64R64Effect 0x10719b 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 11] []) (.reg (.gpr 3))) #v[66]
    (.letOp (n := 69) (.exec 0x10719b (fun s => s.RIP = 0x10719b) (movR64R64Effect 0x10719b 3 11) (Reg.operands [.gpr 11] [])) #v[66]
    (.letOp (n := 70) (.out 0x10719e (shlR64Effect 0x10719e 4 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 71) (.exec 0x10719e (fun s => s.RIP = 0x10719e) (shlR64Effect 0x10719e 4 3 8) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[68]
    (.letOp (n := 72) (.out 0x1071a2 (addR64R64Effect 0x1071a2 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[70, 66]
    (.letOp (n := 73) (.exec 0x1071a2 (fun s => s.RIP = 0x1071a2) (addR64R64Effect 0x1071a2 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[70, 66]
    (.letOp (n := 74) (.out 0x1071a5 (xorR64R64Effect 0x1071a5 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[72, 10]
    (.letOp (n := 75) (.exec 0x1071a5 (fun s => s.RIP = 0x1071a5) (xorR64R64Effect 0x1071a5 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[72, 10]
    (.letOp (n := 76) (.exec 0x1071a8 (StorePre 0x1071a8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1071a8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1071a8 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x1071ad (movR64R64Effect 0x1071ad 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[9]
    (.letOp (n := 78) (.exec 0x1071ad (fun s => s.RIP = 0x1071ad) (movR64R64Effect 0x1071ad 10 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 79) (.out 0x1071b0 (shrR64Effect 0x1071b0 4 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x1071b0 (fun s => s.RIP = 0x1071b0) (shrR64Effect 0x1071b0 4 10 8) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x1071b4 (xorR64R64Effect 0x1071b4 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 9] []) (.reg (.gpr 10))) #v[79, 9]
    (.letOp (n := 82) (.exec 0x1071b4 (fun s => s.RIP = 0x1071b4) (xorR64R64Effect 0x1071b4 10 9) (Reg.operands [.gpr 10, .gpr 9] [])) #v[79, 9]
    (.letOp (n := 83) (.out 0x1071b7 (andR64R64Effect 0x1071b7 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[81, 64]
    (.letOp (n := 84) (.exec 0x1071b7 (fun s => s.RIP = 0x1071b7) (andR64R64Effect 0x1071b7 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[81, 64]
    (.letOp (n := 85) (.out 0x1071ba (movR64R64Effect 0x1071ba 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 10] []) (.reg (.gpr 11))) #v[83]
    (.letOp (n := 86) (.exec 0x1071ba (fun s => s.RIP = 0x1071ba) (movR64R64Effect 0x1071ba 11 10) (Reg.operands [.gpr 10] [])) #v[83]
    (.letOp (n := 87) (.out 0x1071bd (shlR64Effect 0x1071bd 4 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[85]
    (.letOp (n := 88) (.exec 0x1071bd (fun s => s.RIP = 0x1071bd) (shlR64Effect 0x1071bd 4 11 8) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[85]
    (.letOp (n := 89) (.out 0x1071c1 (addR64R64Effect 0x1071c1 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[87, 83]
    (.letOp (n := 90) (.exec 0x1071c1 (fun s => s.RIP = 0x1071c1) (addR64R64Effect 0x1071c1 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[87, 83]
    (b_l107170_1))))))))))))))))))))))))))))))))))))))

def bytes_l107170 : List UInt8 :=
  [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00,
    0x48, 0xC1, 0xE5, 0x06, 0x4D, 0x89, 0xD3, 0x49, 0xC1, 0xEB, 0x08, 0x4D, 0x31, 0xD3, 0x49, 0xBE,
    0x00, 0x00, 0xFF, 0x00, 0x00, 0x00, 0xFF, 0x00, 0x4D, 0x21, 0xF3, 0x4C, 0x89, 0xDB, 0x48, 0xC1,
    0xE3, 0x08, 0x4C, 0x01, 0xDB, 0x4C, 0x31, 0xD3, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x4D, 0x89, 0xCA,
    0x49, 0xC1, 0xEA, 0x08, 0x4D, 0x31, 0xCA, 0x4D, 0x21, 0xF2, 0x4D, 0x89, 0xD3, 0x49, 0xC1, 0xE3,
    0x08, 0x4D, 0x01, 0xD3] ++ bytes_l107170_1

theorem code_l107170 : ∀ x ∈ codeRange 0x107170 bytes_l107170, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x7170 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l107170_1

@[cfg_block] def b_l107298 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x107298 (movR64M64Effect 0x107298 0 (.sib 4 none 0 (.d32 0x3d8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x107298 (LoadPre 0x107298 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3d8)) s (0x107298 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x107298 0 (.sib 4 none 0 (.d32 0x3d8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x1072a0 (StorePre 0x1072a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1072a0 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072a0 5 64 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[53, 4]
    (.letOp (n := 56) (.out 0x1072a5 (movR64M64Effect 0x1072a5 0 (.sib 4 none 0 (.d32 0x3e0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 57) (.exec 0x1072a5 (LoadPre 0x1072a5 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e0)) s (0x1072a5 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072a5 0 (.sib 4 none 0 (.d32 0x3e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x1072ad (StorePre 0x1072ad 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1072ad + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ad 5 64 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 59) (.out 0x1072b2 (movR64M64Effect 0x1072b2 0 (.sib 4 none 0 (.d32 0x3e8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 60) (.exec 0x1072b2 (LoadPre 0x1072b2 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3e8)) s (0x1072b2 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072b2 0 (.sib 4 none 0 (.d32 0x3e8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x1072ba (StorePre 0x1072ba 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1072ba + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ba 5 64 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 62) (.out 0x1072bf (movR64M64Effect 0x1072bf 0 (.sib 4 none 0 (.d32 0x3f0))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 63) (.exec 0x1072bf (LoadPre 0x1072bf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3f0)) s (0x1072bf + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072bf 0 (.sib 4 none 0 (.d32 0x3f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.exec 0x1072c7 (StorePre 0x1072c7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1072c7 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072c7 5 64 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 65) (.out 0x1072cc (movR64M64Effect 0x1072cc 0 (.sib 4 none 0 (.d32 0x3f8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 66) (.exec 0x1072cc (LoadPre 0x1072cc (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x3f8)) s (0x1072cc + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072cc 0 (.sib 4 none 0 (.d32 0x3f8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.exec 0x1072d4 (StorePre 0x1072d4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1072d4 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072d4 5 64 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 68) (.out 0x1072d9 (movR64M64Effect 0x1072d9 0 (.sib 4 none 0 (.d32 0x400))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 69) (.exec 0x1072d9 (LoadPre 0x1072d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x400)) s (0x1072d9 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072d9 0 (.sib 4 none 0 (.d32 0x400))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.exec 0x1072e1 (StorePre 0x1072e1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x1072e1 + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072e1 5 64 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[68, 4]
    (.letOp (n := 71) (.out 0x1072e6 (movR64M64Effect 0x1072e6 0 (.sib 4 none 0 (.d32 0x408))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 72) (.exec 0x1072e6 (LoadPre 0x1072e6 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x408)) s (0x1072e6 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072e6 0 (.sib 4 none 0 (.d32 0x408))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.exec 0x1072ee (StorePre 0x1072ee 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1072ee + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072ee 5 64 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[71, 4]
    (.letOp (n := 74) (.out 0x1072f3 (movR64M64Effect 0x1072f3 0 (.sib 4 none 0 (.d32 0x410))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 75) (.exec 0x1072f3 (LoadPre 0x1072f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x410)) s (0x1072f3 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x1072f3 0 (.sib 4 none 0 (.d32 0x410))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 76) (.exec 0x1072fb (StorePre 0x1072fb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x1072fb + BitVec.ofNat 64 5)) 8) (xorMREffect 0x1072fb 5 64 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[74, 4]
    (.letOp (n := 77) (.out 0x107300 (movR32Imm32Effect 0x107300 5 2 0x8) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 78) (.exec 0x107300 (fun s => s.RIP = 0x107300) (movR32Imm32Effect 0x107300 5 2 0x8) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x107305 (leaR64Effect 0x107305 7 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 80) (.exec 0x107305 (fun s => s.RIP = 0x107305) (leaR64Effect 0x107305 7 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.out 0x10730d (movR64R64Effect 0x10730d 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 3] []) (.reg (.gpr 6))) #v[3]
    (.letOp (n := 82) (.exec 0x10730d (fun s => s.RIP = 0x10730d) (movR64R64Effect 0x10730d 6 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 83) (.out 0x107310 (callEffect (fun _ => 0x10a210) 0x107315) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 84) (.exec 0x107310 (PushPre 0x107310 5) (callEffect (fun _ => 0x10a210) 0x107315) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.const ⟨64, 0x107315⟩) #v[]
    (.terminate (.call ⟨.l10a210, RegMap.args [(0, 74), (2, 77), (3, 3), (4, 83), (5, 5), (6, 81), (7, 79), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 86⟩ { target := .l107315, kept := #v[], arity := rfl, guard := some (Fin.last 85) }))))))))))))))))))))))))))))))))))

def bytes_l107298 : List UInt8 :=
  [0x48, 0x8B, 0x84, 0x24, 0xD8, 0x03, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x08, 0x48, 0x8B, 0x84,
    0x24, 0xE0, 0x03, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x84, 0x24, 0xE8, 0x03,
    0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x18, 0x48, 0x8B, 0x84, 0x24, 0xF0, 0x03, 0x00, 0x00, 0x48,
    0x31, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x84, 0x24, 0xF8, 0x03, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24,
    0x28, 0x48, 0x8B, 0x84, 0x24, 0x00, 0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x30, 0x48, 0x8B,
    0x84, 0x24, 0x08, 0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x38, 0x48, 0x8B, 0x84, 0x24, 0x10,
    0x04, 0x00, 0x00, 0x48, 0x31, 0x44, 0x24, 0x40, 0xBA, 0x08, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xBC,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDE, 0xE8, 0xFB, 0x2E, 0x00, 0x00]

theorem code_l107298 : ∀ x ∈ codeRange 0x107298 bytes_l107298, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x7298 125 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end AesGcm.Proofs.Machine.LIR
