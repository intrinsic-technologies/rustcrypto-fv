import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Labels
import P256.Proofs.Common.CFG.EvalAttr
import P256.Proofs.Common.Lift.Generated.Footprints

namespace P256.Proofs.Scalar.Multiply.Barrett.Machine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift

@[cfg_block] def b_l118320 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112840 (pushR64Effect 0x112840 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x112840 (PushPre 0x112840 1) (pushR64Effect 0x112840 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x112841 (pushR64Effect 0x112841 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x112841 (PushPre 0x112841 2) (pushR64Effect 0x112841 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x112843 (pushR64Effect 0x112843 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x112843 (PushPre 0x112843 2) (pushR64Effect 0x112843 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x112845 (pushR64Effect 0x112845 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x112845 (PushPre 0x112845 2) (pushR64Effect 0x112845 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x112847 (pushR64Effect 0x112847 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x112847 (PushPre 0x112847 2) (pushR64Effect 0x112847 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x112849 (pushR64Effect 0x112849 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x112849 (PushPre 0x112849 1) (pushR64Effect 0x112849 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11284a (subR64Imm8Effect 0x11284a 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11284a (fun s => s.RIP = 0x11284a) (subR64Imm8Effect 0x11284a 4 0x40) (Reg.operands [.gpr 4] [])) #v[63]
    (.terminate (.br ⟨.l11832e, RegMap.args [(2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 67⟩)))))))))))))))

def bytes_l118320 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x40]

theorem code_l118320 : ∀ x ∈ codeRange 0x112840 bytes_l118320, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12840 14 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11832e_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x1128a6 (mulR64Effect 0x1128a6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[88, 90]
    (.letOp (n := 94) (.out 0x1128a6 (mulR64Effect 0x1128a6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[88, 90]
    (.letOp (n := 95) (.exec 0x1128a6 (fun s => s.RIP = 0x1128a6) (mulR64Effect 0x1128a6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[88, 90]
    (.letOp (n := 96) (.out 0x1128a9 (movR64R64Effect 0x1128a9 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[93]
    (.letOp (n := 97) (.exec 0x1128a9 (fun s => s.RIP = 0x1128a9) (movR64R64Effect 0x1128a9 6 0) (Reg.operands [.gpr 0] [])) #v[93]
    (.letOp (n := 98) (.out 0x1128ac (movR64R64Effect 0x1128ac 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[94]
    (.letOp (n := 99) (.exec 0x1128ac (fun s => s.RIP = 0x1128ac) (movR64R64Effect 0x1128ac 11 2) (Reg.operands [.gpr 2] [])) #v[94]
    (.letOp (n := 100) (.out 0x1128af (addR64R64Effect 0x1128af 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[73, 64]
    (.letOp (n := 101) (.out 0x1128af (addR64R64Effect 0x1128af 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[73, 64]
    (.letOp (n := 102) (.exec 0x1128af (fun s => s.RIP = 0x1128af) (addR64R64Effect 0x1128af 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[73, 64]
    (.letOp (n := 103) (.out 0x1128b2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b2 3 14)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[84, 75, 101]
    (.letOp (n := 104) (.out 0x1128b2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b2 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[84, 75, 101]
    (.letOp (n := 105) (.exec 0x1128b2 (fun s => s.RIP = 0x1128b2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b2 3 14)) (Reg.operands [.gpr 3, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 75, 101]
    (.letOp (n := 106) (.out 0x1128b5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b5 6 15)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[96, 86, 104]
    (.letOp (n := 107) (.out 0x1128b5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b5 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[96, 86, 104]
    (.letOp (n := 108) (.exec 0x1128b5 (fun s => s.RIP = 0x1128b5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b5 6 15)) (Reg.operands [.gpr 6, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[96, 86, 104]
    (.letOp (n := 109) (.out 0x1128b8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b8 11 1)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[98, 56, 107]
    (.letOp (n := 110) (.out 0x1128b8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b8 11 1)) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[98, 56, 107]
    (.letOp (n := 111) (.exec 0x1128b8 (fun s => s.RIP = 0x1128b8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128b8 11 1)) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 56, 107]
    (.terminate (.br ⟨.l11839b, RegMap.args [(0, 93), (1, 56), (2, 94), (3, 103), (4, 4), (5, 77), (6, 106), (7, 7), (8, 64), (9, 58), (10, 100), (11, 109), (12, 53), (13, 66), (14, 75), (15, 86), (16, 110), (22, 22), (39, 39), (51, 51)] 112⟩))))))))))))))))))))

def bytes_l11832e_1 : List UInt8 :=
  [0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD3, 0x4D, 0x01, 0xC2, 0x4C, 0x11, 0xF3, 0x4C,
    0x11, 0xFE, 0x49, 0x11, 0xCB]

theorem code_l11832e_1 : ∀ x ∈ codeRange 0x1128a6 bytes_l11832e_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x128a6 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11832e : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11284e (movR64R64Effect 0x11284e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[2]
    (.letOp (n := 54) (.exec 0x11284e (fun s => s.RIP = 0x11284e) (movR64R64Effect 0x11284e 12 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 55) (.exec 0x112851 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112851 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112851 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112851 6 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 56) (.out 0x112856 (movR64M64Effect 0x112856 1 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 57) (.exec 0x112856 (LoadPre 0x112856 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x112856 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112856 1 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 58) (.out 0x11285a (movR64Imm64Effect 0x11285a 9 0x12ffd85eedf9bfe) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 59) (.exec 0x11285a (fun s => s.RIP = 0x11285a) (movR64Imm64Effect 0x11285a 9 0x12ffd85eedf9bfe) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x112864 (movR64R64Effect 0x112864 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 61) (.exec 0x112864 (fun s => s.RIP = 0x112864) (movR64R64Effect 0x112864 0 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 62) (.out 0x112867 (mulR64Effect 0x112867 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[58, 60]
    (.letOp (n := 63) (.exec 0x112867 (fun s => s.RIP = 0x112867) (mulR64Effect 0x112867 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[58, 60]
    (.letOp (n := 64) (.out 0x11286a (movR64R64Effect 0x11286a 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[62]
    (.letOp (n := 65) (.exec 0x11286a (fun s => s.RIP = 0x11286a) (movR64R64Effect 0x11286a 8 2) (Reg.operands [.gpr 2] [])) #v[62]
    (.letOp (n := 66) (.out 0x11286d (movR64Imm64Effect 0x11286d 13 0x43190552df1a6c21) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 67) (.exec 0x11286d (fun s => s.RIP = 0x11286d) (movR64Imm64Effect 0x11286d 13 0x43190552df1a6c21) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x112877 (movR64R64Effect 0x112877 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 69) (.exec 0x112877 (fun s => s.RIP = 0x112877) (movR64R64Effect 0x112877 0 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 70) (.out 0x11287a (mulR64Effect 0x11287a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[66, 68]
    (.letOp (n := 71) (.out 0x11287a (mulR64Effect 0x11287a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[66, 68]
    (.letOp (n := 72) (.exec 0x11287a (fun s => s.RIP = 0x11287a) (mulR64Effect 0x11287a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[66, 68]
    (.letOp (n := 73) (.out 0x11287d (movR64R64Effect 0x11287d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[70]
    (.letOp (n := 74) (.exec 0x11287d (fun s => s.RIP = 0x11287d) (movR64R64Effect 0x11287d 10 0) (Reg.operands [.gpr 0] [])) #v[70]
    (.letOp (n := 75) (.out 0x112880 (movR64R64Effect 0x112880 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[71]
    (.letOp (n := 76) (.exec 0x112880 (fun s => s.RIP = 0x112880) (movR64R64Effect 0x112880 14 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 77) (.out 0x112883 (movR64Imm64Effect 0x112883 5 0xfffffffeffffffff) (EffectPart.reads (.reg (.gpr 5)) [] []) (.reg (.gpr 5))) #v[]
    (.letOp (n := 78) (.exec 0x112883 (fun s => s.RIP = 0x112883) (movR64Imm64Effect 0x112883 5 0xfffffffeffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x11288d (movR64R64Effect 0x11288d 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 80) (.exec 0x11288d (fun s => s.RIP = 0x11288d) (movR64R64Effect 0x11288d 0 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 81) (.out 0x112890 (mulR64Effect 0x112890 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[77, 79]
    (.letOp (n := 82) (.out 0x112890 (mulR64Effect 0x112890 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[77, 79]
    (.letOp (n := 83) (.exec 0x112890 (fun s => s.RIP = 0x112890) (mulR64Effect 0x112890 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[77, 79]
    (.letOp (n := 84) (.out 0x112893 (movR64R64Effect 0x112893 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[81]
    (.letOp (n := 85) (.exec 0x112893 (fun s => s.RIP = 0x112893) (movR64R64Effect 0x112893 3 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 86) (.out 0x112896 (movR64R64Effect 0x112896 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[82]
    (.letOp (n := 87) (.exec 0x112896 (fun s => s.RIP = 0x112896) (movR64R64Effect 0x112896 15 2) (Reg.operands [.gpr 2] [])) #v[82]
    (.letOp (n := 88) (.out 0x112899 (movR32Imm32Effect 0x112899 5 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 89) (.exec 0x112899 (fun s => s.RIP = 0x112899) (movR32Imm32Effect 0x112899 5 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 90) (.out 0x11289e (movR64R64Effect 0x11289e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[56]
    (.letOp (n := 91) (.exec 0x11289e (fun s => s.RIP = 0x11289e) (movR64R64Effect 0x11289e 0 1) (Reg.operands [.gpr 1] [])) #v[56]
    (.letOp (n := 92) (.exec 0x1128a1 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1128a1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x1128a1 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1128a1 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (b_l11832e_1))))))))))))))))))))))))))))))))))))))))

def bytes_l11832e : List UInt8 :=
  [0x49, 0x89, 0xD4, 0x48, 0x89, 0x74, 0x24, 0x28, 0x48, 0x8B, 0x4E, 0x18, 0x49, 0xB9, 0xFE, 0x9B,
    0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x49,
    0xBD, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE5, 0x49,
    0x89, 0xC2, 0x49, 0x89, 0xD6, 0x48, 0xBD, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0x48,
    0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD7, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF,
    0x48, 0x89, 0xC8, 0x48, 0x89, 0x4C, 0x24, 0x38] ++ bytes_l11832e_1

theorem code_l11832e : ∀ x ∈ codeRange 0x11284e bytes_l11832e, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1284e 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11832e_1

@[cfg_block] def b_l11839b_1 : Block Op Label signature Reg.count 96 :=
  .letOp (n := 96) (.exec 0x112900 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112900 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x112900 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112900 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 97) (.out 0x112905 (movR64R64Effect 0x112905 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 98) (.exec 0x112905 (fun s => s.RIP = 0x112905) (movR64R64Effect 0x112905 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 99) (.out 0x112908 (mulR64Effect 0x112908 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[5, 97]
    (.letOp (n := 100) (.out 0x112908 (mulR64Effect 0x112908 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[5, 97]
    (.letOp (n := 101) (.exec 0x112908 (fun s => s.RIP = 0x112908) (mulR64Effect 0x112908 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[5, 97]
    (.letOp (n := 102) (.out 0x11290b (movR64R64Effect 0x11290b 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[100]
    (.letOp (n := 103) (.exec 0x11290b (fun s => s.RIP = 0x11290b) (movR64R64Effect 0x11290b 12 2) (Reg.operands [.gpr 2] [])) #v[100]
    (.letOp (n := 104) (.out 0x11290e (movR64R64Effect 0x11290e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 105) (.exec 0x11290e (fun s => s.RIP = 0x11290e) (movR64R64Effect 0x11290e 15 0) (Reg.operands [.gpr 0] [])) #v[99]
    (.letOp (n := 106) (.out 0x112911 (addR64R64Effect 0x112911 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[104, 6]
    (.letOp (n := 107) (.out 0x112911 (addR64R64Effect 0x112911 15 6) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 6] []) (.flag .CF)) #v[104, 6]
    (.letOp (n := 108) (.exec 0x112911 (fun s => s.RIP = 0x112911) (addR64R64Effect 0x112911 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[104, 6]
    (.letOp (n := 109) (.out 0x112914 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112914 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[102, 107]
    (.letOp (n := 110) (.exec 0x112914 (fun s => s.RIP = 0x112914) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112914 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[102, 107]
    (.letOp (n := 111) (.out 0x112918 (addR64R64Effect 0x112918 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[106, 94]
    (.letOp (n := 112) (.out 0x112918 (addR64R64Effect 0x112918 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[106, 94]
    (.letOp (n := 113) (.exec 0x112918 (fun s => s.RIP = 0x112918) (addR64R64Effect 0x112918 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[106, 94]
    (.letOp (n := 114) (.out 0x11291b (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11291b 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[109, 112]
    (.letOp (n := 115) (.exec 0x11291b (fun s => s.RIP = 0x11291b) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11291b 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 112]
    (.letOp (n := 116) (.out 0x11291f (movR64R64Effect 0x11291f 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 117) (.exec 0x11291f (fun s => s.RIP = 0x11291f) (movR64R64Effect 0x11291f 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 118) (.out 0x112922 (movR32Imm32Effect 0x112922 5 1 0xffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 119) (.exec 0x112922 (fun s => s.RIP = 0x112922) (movR32Imm32Effect 0x112922 5 1 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 120) (.out 0x112927 (mulR64Effect 0x112927 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[118, 116]
    (.letOp (n := 121) (.out 0x112927 (mulR64Effect 0x112927 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[118, 116]
    (.letOp (n := 122) (.exec 0x112927 (fun s => s.RIP = 0x112927) (mulR64Effect 0x112927 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[118, 116]
    (.letOp (n := 123) (.out 0x11292a (movR64R64Effect 0x11292a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[121]
    (.letOp (n := 124) (.exec 0x11292a (fun s => s.RIP = 0x11292a) (movR64R64Effect 0x11292a 3 2) (Reg.operands [.gpr 2] [])) #v[121]
    (.letOp (n := 125) (.out 0x11292d (movR64R64Effect 0x11292d 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[120]
    (.letOp (n := 126) (.exec 0x11292d (fun s => s.RIP = 0x11292d) (movR64R64Effect 0x11292d 10 0) (Reg.operands [.gpr 0] [])) #v[120]
    (.letOp (n := 127) (.out 0x112930 (addR64R64Effect 0x112930 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[125, 11]
    (.letOp (n := 128) (.out 0x112930 (addR64R64Effect 0x112930 10 11) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 11] []) (.flag .CF)) #v[125, 11]
    (.letOp (n := 129) (.exec 0x112930 (fun s => s.RIP = 0x112930) (addR64R64Effect 0x112930 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[125, 11]
    (.letOp (n := 130) (.out 0x112933 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112933 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[123, 128]
    (.letOp (n := 131) (.exec 0x112933 (fun s => s.RIP = 0x112933) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112933 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[123, 128]
    (.letOp (n := 132) (.out 0x112937 (movR64M64Effect 0x112937 13 (.base 8 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 133) (.exec 0x112937 (LoadPre 0x112937 (fun s => AddrMode.addr (.base 8 (.d8 0x8)) s (0x112937 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112937 13 (.base 8 (.d8 0x8))) (Reg.operands [.gpr 8] [])) #v[53]
    (.letOp (n := 134) (.exec 0x11293b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x11293b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11293b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11293b 8 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[53, 4]
    (.terminate (.br ⟨.l118420, RegMap.args [(0, 120), (1, 118), (2, 121), (3, 130), (4, 4), (5, 5), (6, 6), (7, 7), (8, 53), (9, 9), (10, 127), (11, 11), (12, 114), (13, 132), (14, 91), (15, 111), (22, 22), (39, 39), (51, 51)] 135⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l11839b_1 : List UInt8 :=
  [0x48, 0x89, 0x4C, 0x24, 0x30, 0x48, 0x89, 0xC8, 0x48, 0xF7, 0xE5, 0x49, 0x89, 0xD4, 0x49, 0x89,
    0xC7, 0x49, 0x01, 0xF7, 0x49, 0x83, 0xD4, 0x00, 0x4D, 0x01, 0xEF, 0x49, 0x83, 0xD4, 0x00, 0x48,
    0x89, 0xC8, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xD3, 0x49, 0x89, 0xC2,
    0x4D, 0x01, 0xDA, 0x48, 0x83, 0xD3, 0x00, 0x4D, 0x8B, 0x68, 0x08, 0x4C, 0x89, 0x44, 0x24, 0x10]

theorem code_l11839b_1 : ∀ x ∈ codeRange 0x112900 bytes_l11839b_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12900 64 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11839b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1128bb (movR64R64Effect 0x1128bb 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[12]
    (.letOp (n := 54) (.exec 0x1128bb (fun s => s.RIP = 0x1128bb) (movR64R64Effect 0x1128bb 8 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 55) (.out 0x1128be (movR64M64Effect 0x1128be 1 (.sib 12 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[12]
    (.letOp (n := 56) (.exec 0x1128be (LoadPre 0x1128be (fun s => AddrMode.addr (.sib 12 none 0 .none) s (0x1128be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1128be 1 (.sib 12 none 0 .none)) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 57) (.out 0x1128c2 (movR64R64Effect 0x1128c2 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 58) (.exec 0x1128c2 (fun s => s.RIP = 0x1128c2) (movR64R64Effect 0x1128c2 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 59) (.out 0x1128c5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128c5 0 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[57, 16]
    (.letOp (n := 60) (.out 0x1128c5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128c5 0 0x0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[57, 16]
    (.letOp (n := 61) (.exec 0x1128c5 (fun s => s.RIP = 0x1128c5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128c5 0 0x0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[57, 16]
    (.letOp (n := 62) (.exec 0x1128c9 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x1128c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1128c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1128c9 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[59, 4]
    (.letOp (n := 63) (.exec 0x1128ce (StorePre 0x1128ce 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1128ce + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x1128ce 5 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 60]
    (.letOp (n := 64) (.out 0x1128d3 (movR64R64Effect 0x1128d3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 65) (.exec 0x1128d3 (fun s => s.RIP = 0x1128d3) (movR64R64Effect 0x1128d3 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 66) (.out 0x1128d6 (mulR64Effect 0x1128d6 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 64]
    (.letOp (n := 67) (.out 0x1128d6 (mulR64Effect 0x1128d6 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 64]
    (.letOp (n := 68) (.exec 0x1128d6 (fun s => s.RIP = 0x1128d6) (mulR64Effect 0x1128d6 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 64]
    (.letOp (n := 69) (.out 0x1128d9 (movR64R64Effect 0x1128d9 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[66]
    (.letOp (n := 70) (.exec 0x1128d9 (fun s => s.RIP = 0x1128d9) (movR64R64Effect 0x1128d9 15 0) (Reg.operands [.gpr 0] [])) #v[66]
    (.letOp (n := 71) (.out 0x1128dc (movR64R64Effect 0x1128dc 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 72) (.exec 0x1128dc (fun s => s.RIP = 0x1128dc) (movR64R64Effect 0x1128dc 12 2) (Reg.operands [.gpr 2] [])) #v[67]
    (.letOp (n := 73) (.out 0x1128df (andR64Imm8Effect 0x1128df 10 0xfe) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[10]
    (.letOp (n := 74) (.exec 0x1128df (fun s => s.RIP = 0x1128df) (andR64Imm8Effect 0x1128df 10 0xfe) (Reg.operands [.gpr 10] [])) #v[10]
    (.letOp (n := 75) (.out 0x1128e3 (movR64R64Effect 0x1128e3 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 76) (.exec 0x1128e3 (fun s => s.RIP = 0x1128e3) (movR64R64Effect 0x1128e3 0 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 77) (.out 0x1128e6 (mulR64Effect 0x1128e6 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[13, 75]
    (.letOp (n := 78) (.out 0x1128e6 (mulR64Effect 0x1128e6 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[13, 75]
    (.letOp (n := 79) (.exec 0x1128e6 (fun s => s.RIP = 0x1128e6) (mulR64Effect 0x1128e6 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[13, 75]
    (.letOp (n := 80) (.out 0x1128e9 (movR64R64Effect 0x1128e9 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[78]
    (.letOp (n := 81) (.exec 0x1128e9 (fun s => s.RIP = 0x1128e9) (movR64R64Effect 0x1128e9 13 2) (Reg.operands [.gpr 2] [])) #v[78]
    (.letOp (n := 82) (.out 0x1128ec (movR64R64Effect 0x1128ec 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[77]
    (.letOp (n := 83) (.exec 0x1128ec (fun s => s.RIP = 0x1128ec) (movR64R64Effect 0x1128ec 14 0) (Reg.operands [.gpr 0] [])) #v[77]
    (.letOp (n := 84) (.out 0x1128ef (addR64R64Effect 0x1128ef 14 3) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 3] []) (.reg (.gpr 14))) #v[82, 3]
    (.letOp (n := 85) (.out 0x1128ef (addR64R64Effect 0x1128ef 14 3) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 3] []) (.flag .CF)) #v[82, 3]
    (.letOp (n := 86) (.exec 0x1128ef (fun s => s.RIP = 0x1128ef) (addR64R64Effect 0x1128ef 14 3) (Reg.operands [.gpr 14, .gpr 3] [])) #v[82, 3]
    (.letOp (n := 87) (.out 0x1128f2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128f2 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[80, 85]
    (.letOp (n := 88) (.exec 0x1128f2 (fun s => s.RIP = 0x1128f2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128f2 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[80, 85]
    (.letOp (n := 89) (.out 0x1128f6 (addR64R64Effect 0x1128f6 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[69, 73]
    (.letOp (n := 90) (.exec 0x1128f6 (fun s => s.RIP = 0x1128f6) (addR64R64Effect 0x1128f6 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[69, 73]
    (.letOp (n := 91) (.out 0x1128f9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128f9 14 12)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[84, 71, 89]
    (.letOp (n := 92) (.out 0x1128f9 (atFlags StatusFlags.CF (adcR64R64Effect 0x1128f9 14 12)) (Reg.operands [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[84, 71, 89]
    (.letOp (n := 93) (.exec 0x1128f9 (fun s => s.RIP = 0x1128f9) (atFlags StatusFlags.CF (adcR64R64Effect 0x1128f9 14 12)) (Reg.operands [.gpr 14, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[84, 71, 89]
    (.letOp (n := 94) (.out 0x1128fc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128fc 13 0x0)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[87, 92]
    (.letOp (n := 95) (.exec 0x1128fc (fun s => s.RIP = 0x1128fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1128fc 13 0x0)) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[87, 92]
    (b_l11839b_1)))))))))))))))))))))))))))))))))))))))))))

def bytes_l11839b : List UInt8 :=
  [0x4D, 0x89, 0xE0, 0x49, 0x8B, 0x0C, 0x24, 0x48, 0x89, 0xC8, 0x48, 0x83, 0xD0, 0x00, 0x48, 0x89,
    0x44, 0x24, 0x18, 0x0F, 0x92, 0x44, 0x24, 0x08, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE1, 0x49, 0x89,
    0xC7, 0x49, 0x89, 0xD4, 0x49, 0x83, 0xE2, 0xFE, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE5, 0x49, 0x89,
    0xD5, 0x49, 0x89, 0xC6, 0x49, 0x01, 0xDE, 0x49, 0x83, 0xD5, 0x00, 0x4D, 0x01, 0xD7, 0x4D, 0x11,
    0xE6, 0x49, 0x83, 0xD5, 0x00] ++ bytes_l11839b_1

theorem code_l11839b : ∀ x ∈ codeRange 0x1128bb bytes_l11839b, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x128bb 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11839b_1

@[cfg_block] def b_l118420_1 : Block Op Label signature Reg.count 99 :=
  .letOp (n := 99) (.out 0x11298d (atFlags StatusFlags.CF (adcR64M64Effect 0x11298d 3 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 3))) #v[3, 4, 97]
    (.letOp (n := 100) (.out 0x11298d (atFlags StatusFlags.CF (adcR64M64Effect 0x11298d 3 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[3, 4, 97]
    (.letOp (n := 101) (.exec 0x11298d (LoadPre 0x11298d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11298d + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11298d 3 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[3, 4, 97]
    (.letOp (n := 102) (.out 0x112992 (movzxR32M8Effect 0x112992 5 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 103) (.exec 0x112992 (LoadPre 0x112992 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112992 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x112992 5 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 104) (.out 0x112997 (atFlags StatusFlags.CF (adcR64R64Effect 0x112997 1 13)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[102, 13, 100]
    (.letOp (n := 105) (.out 0x112997 (atFlags StatusFlags.CF (adcR64R64Effect 0x112997 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[102, 13, 100]
    (.letOp (n := 106) (.exec 0x112997 (fun s => s.RIP = 0x112997) (atFlags StatusFlags.CF (adcR64R64Effect 0x112997 1 13)) (Reg.operands [.gpr 1, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[102, 13, 100]
    (.letOp (n := 107) (.exec 0x11299a (StorePre 0x11299a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11299a + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x11299a 5 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[4, 105]
    (.letOp (n := 108) (.out 0x11299f (addR64R64Effect 0x11299f 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[96, 91]
    (.letOp (n := 109) (.out 0x11299f (addR64R64Effect 0x11299f 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[96, 91]
    (.letOp (n := 110) (.exec 0x11299f (fun s => s.RIP = 0x11299f) (addR64R64Effect 0x11299f 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[96, 91]
    (.letOp (n := 111) (.out 0x1129a2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a2 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[94, 109]
    (.letOp (n := 112) (.exec 0x1129a2 (fun s => s.RIP = 0x1129a2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a2 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[94, 109]
    (.letOp (n := 113) (.out 0x1129a6 (addR64R64Effect 0x1129a6 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[108, 85]
    (.letOp (n := 114) (.out 0x1129a6 (addR64R64Effect 0x1129a6 10 6) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[108, 85]
    (.letOp (n := 115) (.exec 0x1129a6 (fun s => s.RIP = 0x1129a6) (addR64R64Effect 0x1129a6 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[108, 85]
    (.letOp (n := 116) (.out 0x1129a9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a9 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[111, 114]
    (.letOp (n := 117) (.exec 0x1129a9 (fun s => s.RIP = 0x1129a9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129a9 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[111, 114]
    (.letOp (n := 118) (.out 0x1129ad (movR64R64Effect 0x1129ad 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 119) (.exec 0x1129ad (fun s => s.RIP = 0x1129ad) (movR64R64Effect 0x1129ad 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 120) (.out 0x1129b0 (movR32Imm32Effect 0x1129b0 5 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 121) (.exec 0x1129b0 (fun s => s.RIP = 0x1129b0) (movR32Imm32Effect 0x1129b0 5 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 122) (.out 0x1129b5 (mulR64Effect 0x1129b5 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[120, 118]
    (.letOp (n := 123) (.out 0x1129b5 (mulR64Effect 0x1129b5 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[120, 118]
    (.letOp (n := 124) (.exec 0x1129b5 (fun s => s.RIP = 0x1129b5) (mulR64Effect 0x1129b5 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[120, 118]
    (.letOp (n := 125) (.out 0x1129b8 (movR64R64Effect 0x1129b8 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[123]
    (.letOp (n := 126) (.exec 0x1129b8 (fun s => s.RIP = 0x1129b8) (movR64R64Effect 0x1129b8 14 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 127) (.out 0x1129bb (movR64R64Effect 0x1129bb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[122]
    (.letOp (n := 128) (.exec 0x1129bb (fun s => s.RIP = 0x1129bb) (movR64R64Effect 0x1129bb 13 0) (Reg.operands [.gpr 0] [])) #v[122]
    (.letOp (n := 129) (.out 0x1129be (addR64R64Effect 0x1129be 13 3) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 3] []) (.reg (.gpr 13))) #v[127, 99]
    (.letOp (n := 130) (.out 0x1129be (addR64R64Effect 0x1129be 13 3) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 3] []) (.flag .CF)) #v[127, 99]
    (.letOp (n := 131) (.exec 0x1129be (fun s => s.RIP = 0x1129be) (addR64R64Effect 0x1129be 13 3) (Reg.operands [.gpr 13, .gpr 3] [])) #v[127, 99]
    (.letOp (n := 132) (.out 0x1129c1 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129c1 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[125, 130]
    (.letOp (n := 133) (.exec 0x1129c1 (fun s => s.RIP = 0x1129c1) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129c1 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[125, 130]
    (.letOp (n := 134) (.out 0x1129c5 (movR64M64Effect 0x1129c5 12 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 8] []) (.reg (.gpr 12))) #v[8]
    (.letOp (n := 135) (.exec 0x1129c5 (LoadPre 0x1129c5 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x1129c5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1129c5 12 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 136) (.out 0x1129c9 (movR64R64Effect 0x1129c9 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[134]
    (.letOp (n := 137) (.exec 0x1129c9 (fun s => s.RIP = 0x1129c9) (movR64R64Effect 0x1129c9 0 12) (Reg.operands [.gpr 12] [])) #v[134]
    (.terminate (.br ⟨.l1184ac, RegMap.args [(0, 136), (1, 104), (2, 123), (3, 99), (4, 4), (6, 85), (7, 7), (8, 8), (9, 60), (10, 113), (11, 82), (12, 134), (13, 129), (14, 132), (15, 116), (22, 22), (39, 39), (51, 51)] 138⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l118420_1 : List UInt8 :=
  [0x48, 0x13, 0x5C, 0x24, 0x18, 0x0F, 0xB6, 0x4C, 0x24, 0x08, 0x4C, 0x11, 0xE9, 0x0F, 0x92, 0x44,
    0x24, 0x08, 0x49, 0x01, 0xC2, 0x49, 0x83, 0xD7, 0x00, 0x49, 0x01, 0xF2, 0x49, 0x83, 0xD7, 0x00,
    0x4C, 0x89, 0xE8, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD6, 0x49, 0x89,
    0xC5, 0x49, 0x01, 0xDD, 0x49, 0x83, 0xD6, 0x00, 0x4D, 0x8B, 0x60, 0x10, 0x4C, 0x89, 0xE0]

theorem code_l118420_1 : ∀ x ∈ codeRange 0x11298d bytes_l118420_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1298d 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118420 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112940 (movR64R64Effect 0x112940 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 54) (.exec 0x112940 (fun s => s.RIP = 0x112940) (movR64R64Effect 0x112940 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 55) (.out 0x112943 (mulR64Effect 0x112943 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 53]
    (.letOp (n := 56) (.out 0x112943 (mulR64Effect 0x112943 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 53]
    (.letOp (n := 57) (.exec 0x112943 (fun s => s.RIP = 0x112943) (mulR64Effect 0x112943 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 53]
    (.letOp (n := 58) (.out 0x112946 (movR64R64Effect 0x112946 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[55]
    (.letOp (n := 59) (.exec 0x112946 (fun s => s.RIP = 0x112946) (movR64R64Effect 0x112946 5 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 60) (.out 0x112949 (movR64R64Effect 0x112949 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[56]
    (.letOp (n := 61) (.exec 0x112949 (fun s => s.RIP = 0x112949) (movR64R64Effect 0x112949 9 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 62) (.out 0x11294c (andR64Imm8Effect 0x11294c 14 0xfe) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[14]
    (.letOp (n := 63) (.exec 0x11294c (fun s => s.RIP = 0x11294c) (andR64Imm8Effect 0x11294c 14 0xfe) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 64) (.out 0x112950 (movR64R64Effect 0x112950 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 65) (.exec 0x112950 (fun s => s.RIP = 0x112950) (movR64R64Effect 0x112950 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 66) (.out 0x112953 (movR64Imm64Effect 0x112953 1 0x43190552df1a6c21) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 67) (.exec 0x112953 (fun s => s.RIP = 0x112953) (movR64Imm64Effect 0x112953 1 0x43190552df1a6c21) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x11295d (mulR64Effect 0x11295d 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[66, 64]
    (.letOp (n := 69) (.out 0x11295d (mulR64Effect 0x11295d 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[66, 64]
    (.letOp (n := 70) (.exec 0x11295d (fun s => s.RIP = 0x11295d) (mulR64Effect 0x11295d 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[66, 64]
    (.letOp (n := 71) (.out 0x112960 (movR64R64Effect 0x112960 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x112960 (fun s => s.RIP = 0x112960) (movR64R64Effect 0x112960 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x112963 (movR64R64Effect 0x112963 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[68]
    (.letOp (n := 74) (.exec 0x112963 (fun s => s.RIP = 0x112963) (movR64R64Effect 0x112963 11 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 75) (.out 0x112966 (addR64R64Effect 0x112966 11 15) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 15] []) (.reg (.gpr 11))) #v[73, 15]
    (.letOp (n := 76) (.out 0x112966 (addR64R64Effect 0x112966 11 15) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 15] []) (.flag .CF)) #v[73, 15]
    (.letOp (n := 77) (.exec 0x112966 (fun s => s.RIP = 0x112966) (addR64R64Effect 0x112966 11 15) (Reg.operands [.gpr 11, .gpr 15] [])) #v[73, 15]
    (.letOp (n := 78) (.out 0x112969 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112969 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[71, 76]
    (.letOp (n := 79) (.exec 0x112969 (fun s => s.RIP = 0x112969) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112969 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[71, 76]
    (.letOp (n := 80) (.out 0x11296d (addR64R64Effect 0x11296d 5 14) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 14] []) (.flag .CF)) #v[58, 62]
    (.letOp (n := 81) (.exec 0x11296d (fun s => s.RIP = 0x11296d) (addR64R64Effect 0x11296d 5 14) (Reg.operands [.gpr 5, .gpr 14] [])) #v[58, 62]
    (.letOp (n := 82) (.out 0x112970 (atFlags StatusFlags.CF (adcR64R64Effect 0x112970 11 9)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[75, 60, 80]
    (.letOp (n := 83) (.out 0x112970 (atFlags StatusFlags.CF (adcR64R64Effect 0x112970 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[75, 60, 80]
    (.letOp (n := 84) (.exec 0x112970 (fun s => s.RIP = 0x112970) (atFlags StatusFlags.CF (adcR64R64Effect 0x112970 11 9)) (Reg.operands [.gpr 11, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[75, 60, 80]
    (.letOp (n := 85) (.out 0x112973 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112973 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[78, 83]
    (.letOp (n := 86) (.exec 0x112973 (fun s => s.RIP = 0x112973) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112973 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[78, 83]
    (.letOp (n := 87) (.out 0x112977 (movR64R64Effect 0x112977 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[13]
    (.letOp (n := 88) (.exec 0x112977 (fun s => s.RIP = 0x112977) (movR64R64Effect 0x112977 0 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 89) (.out 0x11297a (movR64Imm64Effect 0x11297a 1 0xfffffffeffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 90) (.exec 0x11297a (fun s => s.RIP = 0x11297a) (movR64Imm64Effect 0x11297a 1 0xfffffffeffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 91) (.out 0x112984 (mulR64Effect 0x112984 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[89, 87]
    (.letOp (n := 92) (.out 0x112984 (mulR64Effect 0x112984 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[89, 87]
    (.letOp (n := 93) (.exec 0x112984 (fun s => s.RIP = 0x112984) (mulR64Effect 0x112984 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[89, 87]
    (.letOp (n := 94) (.out 0x112987 (movR64R64Effect 0x112987 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[92]
    (.letOp (n := 95) (.exec 0x112987 (fun s => s.RIP = 0x112987) (movR64R64Effect 0x112987 15 2) (Reg.operands [.gpr 2] [])) #v[92]
    (.letOp (n := 96) (.out 0x11298a (addR64R64Effect 0x11298a 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[10, 12]
    (.letOp (n := 97) (.out 0x11298a (addR64R64Effect 0x11298a 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[10, 12]
    (.letOp (n := 98) (.exec 0x11298a (fun s => s.RIP = 0x11298a) (addR64R64Effect 0x11298a 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[10, 12]
    (b_l118420_1))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118420 : List UInt8 :=
  [0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xC5, 0x49, 0x89, 0xD1, 0x49, 0x83, 0xE6, 0xFE,
    0x4C, 0x89, 0xE8, 0x48, 0xB9, 0x21, 0x6C, 0x1A, 0xDF, 0x52, 0x05, 0x19, 0x43, 0x48, 0xF7, 0xE1,
    0x48, 0x89, 0xD6, 0x49, 0x89, 0xC3, 0x4D, 0x01, 0xFB, 0x48, 0x83, 0xD6, 0x00, 0x4C, 0x01, 0xF5,
    0x4D, 0x11, 0xCB, 0x48, 0x83, 0xD6, 0x00, 0x4C, 0x89, 0xE8, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFE, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD7, 0x4D, 0x01, 0xE2] ++ bytes_l118420_1

theorem code_l118420 : ∀ x ∈ codeRange 0x112940 bytes_l118420, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12940 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118420_1

@[cfg_block] def b_l1184ac_1 : Block Op Label signature Reg.count 98 :=
  .letOp (n := 98) (.out 0x112a20 (addR64R64Effect 0x112a20 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[13, 15]
    (.letOp (n := 99) (.out 0x112a20 (addR64R64Effect 0x112a20 13 15) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 15] []) (.flag .CF)) #v[13, 15]
    (.letOp (n := 100) (.exec 0x112a20 (fun s => s.RIP = 0x112a20) (addR64R64Effect 0x112a20 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[13, 15]
    (.letOp (n := 101) (.out 0x112a23 (atFlags StatusFlags.CF (adcR64R64Effect 0x112a23 14 1)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[14, 1, 99]
    (.letOp (n := 102) (.out 0x112a23 (atFlags StatusFlags.CF (adcR64R64Effect 0x112a23 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[14, 1, 99]
    (.letOp (n := 103) (.exec 0x112a23 (fun s => s.RIP = 0x112a23) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a23 14 1)) (Reg.operands [.gpr 14, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[14, 1, 99]
    (.letOp (n := 104) (.out 0x112a26 (movzxR32M8Effect 0x112a26 6 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 105) (.exec 0x112a26 (LoadPre 0x112a26 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112a26 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x112a26 6 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x112a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x112a2c 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[104, 12, 102]
    (.letOp (n := 107) (.out 0x112a2c (atFlags StatusFlags.CF (adcR64R64Effect 0x112a2c 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[104, 12, 102]
    (.letOp (n := 108) (.exec 0x112a2c (fun s => s.RIP = 0x112a2c) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a2c 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[104, 12, 102]
    (.letOp (n := 109) (.out 0x112a2f (atFlags (condHolds 2) (setccR8Effect 0x112a2f 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1, 107]
    (.letOp (n := 110) (.exec 0x112a2f (fun s => s.RIP = 0x112a2f) (atFlags (condHolds 2) (setccR8Effect 0x112a2f 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1, 107]
    (.letOp (n := 111) (.out 0x112a32 (addR64R64Effect 0x112a32 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[94, 98]
    (.letOp (n := 112) (.out 0x112a32 (addR64R64Effect 0x112a32 5 13) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 13] []) (.flag .CF)) #v[94, 98]
    (.letOp (n := 113) (.exec 0x112a32 (fun s => s.RIP = 0x112a32) (addR64R64Effect 0x112a32 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[94, 98]
    (.letOp (n := 114) (.out 0x112a35 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a35 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[96, 112]
    (.letOp (n := 115) (.exec 0x112a35 (fun s => s.RIP = 0x112a35) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a35 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[96, 112]
    (.letOp (n := 116) (.out 0x112a39 (addR64R64Effect 0x112a39 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[111, 85]
    (.letOp (n := 117) (.out 0x112a39 (addR64R64Effect 0x112a39 5 6) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 6] []) (.flag .CF)) #v[111, 85]
    (.letOp (n := 118) (.exec 0x112a39 (fun s => s.RIP = 0x112a39) (addR64R64Effect 0x112a39 5 6) (Reg.operands [.gpr 5, .gpr 6] [])) #v[111, 85]
    (.letOp (n := 119) (.out 0x112a3c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a3c 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[114, 117]
    (.letOp (n := 120) (.exec 0x112a3c (fun s => s.RIP = 0x112a3c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a3c 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[114, 117]
    (.letOp (n := 121) (.out 0x112a40 (movR64R64Effect 0x112a40 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 122) (.exec 0x112a40 (fun s => s.RIP = 0x112a40) (movR64R64Effect 0x112a40 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 123) (.out 0x112a43 (movR32Imm32Effect 0x112a43 5 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 124) (.exec 0x112a43 (fun s => s.RIP = 0x112a43) (movR32Imm32Effect 0x112a43 5 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 125) (.out 0x112a48 (mulR64Effect 0x112a48 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[123, 121]
    (.letOp (n := 126) (.out 0x112a48 (mulR64Effect 0x112a48 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[123, 121]
    (.letOp (n := 127) (.exec 0x112a48 (fun s => s.RIP = 0x112a48) (mulR64Effect 0x112a48 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[123, 121]
    (.letOp (n := 128) (.out 0x112a4b (movR64R64Effect 0x112a4b 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[126]
    (.letOp (n := 129) (.exec 0x112a4b (fun s => s.RIP = 0x112a4b) (movR64R64Effect 0x112a4b 11 2) (Reg.operands [.gpr 2] [])) #v[126]
    (.letOp (n := 130) (.out 0x112a4e (movR64R64Effect 0x112a4e 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[125]
    (.letOp (n := 131) (.exec 0x112a4e (fun s => s.RIP = 0x112a4e) (movR64R64Effect 0x112a4e 15 0) (Reg.operands [.gpr 0] [])) #v[125]
    (.letOp (n := 132) (.out 0x112a51 (addR64R64Effect 0x112a51 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[130, 101]
    (.letOp (n := 133) (.out 0x112a51 (addR64R64Effect 0x112a51 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[130, 101]
    (.letOp (n := 134) (.exec 0x112a51 (fun s => s.RIP = 0x112a51) (addR64R64Effect 0x112a51 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[130, 101]
    (.letOp (n := 135) (.out 0x112a54 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a54 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[128, 133]
    (.letOp (n := 136) (.exec 0x112a54 (fun s => s.RIP = 0x112a54) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a54 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[128, 133]
    (.letOp (n := 137) (.out 0x112a58 (movR64M64Effect 0x112a58 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 138) (.exec 0x112a58 (LoadPre 0x112a58 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112a58 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112a58 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 139) (.out 0x112a5d (movR64M64Effect 0x112a5d 9 (.base 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[137]
    (.letOp (n := 140) (.exec 0x112a5d (LoadPre 0x112a5d (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x112a5d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112a5d 9 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 0] [])) #v[137]
    (.letOp (n := 141) (.out 0x112a61 (movR64R64Effect 0x112a61 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[139]
    (.letOp (n := 142) (.exec 0x112a61 (fun s => s.RIP = 0x112a61) (movR64R64Effect 0x112a61 0 9) (Reg.operands [.gpr 9] [])) #v[139]
    (.terminate (.br ⟨.l118544, RegMap.args [(0, 141), (1, 109), (2, 126), (3, 82), (4, 4), (5, 116), (6, 85), (7, 7), (8, 106), (9, 139), (10, 119), (11, 135), (12, 12), (13, 98), (14, 101), (15, 132), (22, 22), (39, 39), (51, 51)] 143⟩))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1184ac_1 : List UInt8 :=
  [0x4D, 0x01, 0xFD, 0x49, 0x11, 0xCE, 0x44, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x4D, 0x11, 0xE0, 0x0F,
    0x92, 0xC1, 0x4C, 0x01, 0xED, 0x49, 0x83, 0xD2, 0x00, 0x48, 0x01, 0xF5, 0x49, 0x83, 0xD2, 0x00,
    0x4C, 0x89, 0xE0, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD3, 0x49, 0x89,
    0xC7, 0x4D, 0x01, 0xF7, 0x49, 0x83, 0xD3, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x4C, 0x8B, 0x48,
    0x18, 0x4C, 0x89, 0xC8]

theorem code_l1184ac_1 : ∀ x ∈ codeRange 0x112a20 bytes_l1184ac_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12a20 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1184ac : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1129cc (movR64Imm64Effect 0x1129cc 2 0x12ffd85eedf9bfe) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x1129cc (fun s => s.RIP = 0x1129cc) (movR64Imm64Effect 0x1129cc 2 0x12ffd85eedf9bfe) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x1129d6 (mulR64Effect 0x1129d6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[53, 0]
    (.letOp (n := 56) (.out 0x1129d6 (mulR64Effect 0x1129d6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 0]
    (.letOp (n := 57) (.exec 0x1129d6 (fun s => s.RIP = 0x1129d6) (mulR64Effect 0x1129d6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 58) (.out 0x1129d9 (movR64R64Effect 0x1129d9 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[55]
    (.letOp (n := 59) (.exec 0x1129d9 (fun s => s.RIP = 0x1129d9) (movR64R64Effect 0x1129d9 9 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 60) (.out 0x1129dc (movR64R64Effect 0x1129dc 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[56]
    (.letOp (n := 61) (.exec 0x1129dc (fun s => s.RIP = 0x1129dc) (movR64R64Effect 0x1129dc 5 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 62) (.out 0x1129df (andR64Imm8Effect 0x1129df 11 0xfe) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11] []) (.reg (.gpr 11))) #v[11]
    (.letOp (n := 63) (.exec 0x1129df (fun s => s.RIP = 0x1129df) (andR64Imm8Effect 0x1129df 11 0xfe) (Reg.operands [.gpr 11] [])) #v[11]
    (.letOp (n := 64) (.out 0x1129e3 (movR64R64Effect 0x1129e3 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 65) (.exec 0x1129e3 (fun s => s.RIP = 0x1129e3) (movR64R64Effect 0x1129e3 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 66) (.out 0x1129e6 (movR64Imm64Effect 0x1129e6 2 0x43190552df1a6c21) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 67) (.exec 0x1129e6 (fun s => s.RIP = 0x1129e6) (movR64Imm64Effect 0x1129e6 2 0x43190552df1a6c21) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x1129f0 (mulR64Effect 0x1129f0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[66, 64]
    (.letOp (n := 69) (.out 0x1129f0 (mulR64Effect 0x1129f0 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[66, 64]
    (.letOp (n := 70) (.exec 0x1129f0 (fun s => s.RIP = 0x1129f0) (mulR64Effect 0x1129f0 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[66, 64]
    (.letOp (n := 71) (.out 0x1129f3 (movR64R64Effect 0x1129f3 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x1129f3 (fun s => s.RIP = 0x1129f3) (movR64R64Effect 0x1129f3 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x1129f6 (movR64R64Effect 0x1129f6 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[68]
    (.letOp (n := 74) (.exec 0x1129f6 (fun s => s.RIP = 0x1129f6) (movR64R64Effect 0x1129f6 3 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 75) (.out 0x1129f9 (addR64R64Effect 0x1129f9 3 10) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 10] []) (.reg (.gpr 3))) #v[73, 10]
    (.letOp (n := 76) (.out 0x1129f9 (addR64R64Effect 0x1129f9 3 10) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 10] []) (.flag .CF)) #v[73, 10]
    (.letOp (n := 77) (.exec 0x1129f9 (fun s => s.RIP = 0x1129f9) (addR64R64Effect 0x1129f9 3 10) (Reg.operands [.gpr 3, .gpr 10] [])) #v[73, 10]
    (.letOp (n := 78) (.out 0x1129fc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129fc 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[71, 76]
    (.letOp (n := 79) (.exec 0x1129fc (fun s => s.RIP = 0x1129fc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1129fc 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[71, 76]
    (.letOp (n := 80) (.out 0x112a00 (addR64R64Effect 0x112a00 9 11) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 11] []) (.flag .CF)) #v[58, 62]
    (.letOp (n := 81) (.exec 0x112a00 (fun s => s.RIP = 0x112a00) (addR64R64Effect 0x112a00 9 11) (Reg.operands [.gpr 9, .gpr 11] [])) #v[58, 62]
    (.letOp (n := 82) (.out 0x112a03 (atFlags StatusFlags.CF (adcR64R64Effect 0x112a03 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[75, 60, 80]
    (.letOp (n := 83) (.out 0x112a03 (atFlags StatusFlags.CF (adcR64R64Effect 0x112a03 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[75, 60, 80]
    (.letOp (n := 84) (.exec 0x112a03 (fun s => s.RIP = 0x112a03) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a03 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[75, 60, 80]
    (.letOp (n := 85) (.out 0x112a06 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a06 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[78, 83]
    (.letOp (n := 86) (.exec 0x112a06 (fun s => s.RIP = 0x112a06) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a06 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[78, 83]
    (.letOp (n := 87) (.out 0x112a0a (movR64R64Effect 0x112a0a 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[12]
    (.letOp (n := 88) (.exec 0x112a0a (fun s => s.RIP = 0x112a0a) (movR64R64Effect 0x112a0a 0 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 89) (.out 0x112a0d (movR64Imm64Effect 0x112a0d 2 0xfffffffeffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 90) (.exec 0x112a0d (fun s => s.RIP = 0x112a0d) (movR64Imm64Effect 0x112a0d 2 0xfffffffeffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 91) (.out 0x112a17 (mulR64Effect 0x112a17 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[89, 87]
    (.letOp (n := 92) (.out 0x112a17 (mulR64Effect 0x112a17 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[89, 87]
    (.letOp (n := 93) (.exec 0x112a17 (fun s => s.RIP = 0x112a17) (mulR64Effect 0x112a17 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[89, 87]
    (.letOp (n := 94) (.out 0x112a1a (movR64R64Effect 0x112a1a 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[91]
    (.letOp (n := 95) (.exec 0x112a1a (fun s => s.RIP = 0x112a1a) (movR64R64Effect 0x112a1a 5 0) (Reg.operands [.gpr 0] [])) #v[91]
    (.letOp (n := 96) (.out 0x112a1d (movR64R64Effect 0x112a1d 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[92]
    (.letOp (n := 97) (.exec 0x112a1d (fun s => s.RIP = 0x112a1d) (movR64R64Effect 0x112a1d 10 2) (Reg.operands [.gpr 2] [])) #v[92]
    (b_l1184ac_1)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1184ac : List UInt8 :=
  [0x48, 0xBA, 0xFE, 0x9B, 0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC1,
    0x48, 0x89, 0xD5, 0x49, 0x83, 0xE3, 0xFE, 0x4C, 0x89, 0xE0, 0x48, 0xBA, 0x21, 0x6C, 0x1A, 0xDF,
    0x52, 0x05, 0x19, 0x43, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x48, 0x89, 0xC3, 0x4C, 0x01, 0xD3,
    0x48, 0x83, 0xD6, 0x00, 0x4D, 0x01, 0xD9, 0x48, 0x11, 0xEB, 0x48, 0x83, 0xD6, 0x00, 0x4C, 0x89,
    0xE0, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x48, 0x89,
    0xC5, 0x49, 0x89, 0xD2] ++ bytes_l1184ac_1

theorem code_l1184ac : ∀ x ∈ codeRange 0x1129cc bytes_l1184ac, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x129cc 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1184ac_1

@[cfg_block] def b_l118544_1 : Block Op Label signature Reg.count 98 :=
  .letOp (n := 98) (.out 0x112ab8 (addR64R64Effect 0x112ab8 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[15, 10]
    (.letOp (n := 99) (.out 0x112ab8 (addR64R64Effect 0x112ab8 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[15, 10]
    (.letOp (n := 100) (.exec 0x112ab8 (fun s => s.RIP = 0x112ab8) (addR64R64Effect 0x112ab8 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[15, 10]
    (.letOp (n := 101) (.out 0x112abb (movzxR32R8Effect 0x112abb 3 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 102) (.exec 0x112abb (fun s => s.RIP = 0x112abb) (movzxR32R8Effect 0x112abb 3 1 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 103) (.out 0x112abe (atFlags StatusFlags.CF (adcR64R64Effect 0x112abe 11 8)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[11, 8, 99]
    (.letOp (n := 104) (.out 0x112abe (atFlags StatusFlags.CF (adcR64R64Effect 0x112abe 11 8)) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[11, 8, 99]
    (.letOp (n := 105) (.exec 0x112abe (fun s => s.RIP = 0x112abe) (atFlags StatusFlags.CF (adcR64R64Effect 0x112abe 11 8)) (Reg.operands [.gpr 11, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[11, 8, 99]
    (.letOp (n := 106) (.out 0x112ac1 (atFlags StatusFlags.CF (adcR64R64Effect 0x112ac1 1 9)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[101, 9, 104]
    (.letOp (n := 107) (.out 0x112ac1 (atFlags StatusFlags.CF (adcR64R64Effect 0x112ac1 1 9)) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[101, 9, 104]
    (.letOp (n := 108) (.exec 0x112ac1 (fun s => s.RIP = 0x112ac1) (atFlags StatusFlags.CF (adcR64R64Effect 0x112ac1 1 9)) (Reg.operands [.gpr 1, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[101, 9, 104]
    (.letOp (n := 109) (.out 0x112ac4 (atFlags (condHolds 2) (setccR8Effect 0x112ac4 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[8, 107]
    (.letOp (n := 110) (.exec 0x112ac4 (fun s => s.RIP = 0x112ac4) (atFlags (condHolds 2) (setccR8Effect 0x112ac4 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[8, 107]
    (.letOp (n := 111) (.out 0x112ac8 (addR64R64Effect 0x112ac8 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[94, 98]
    (.letOp (n := 112) (.out 0x112ac8 (addR64R64Effect 0x112ac8 3 15) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 15] []) (.flag .CF)) #v[94, 98]
    (.letOp (n := 113) (.exec 0x112ac8 (fun s => s.RIP = 0x112ac8) (addR64R64Effect 0x112ac8 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[94, 98]
    (.letOp (n := 114) (.out 0x112acb (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112acb 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[96, 112]
    (.letOp (n := 115) (.exec 0x112acb (fun s => s.RIP = 0x112acb) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112acb 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[96, 112]
    (.letOp (n := 116) (.out 0x112acf (addR64R64Effect 0x112acf 3 6) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[111, 85]
    (.letOp (n := 117) (.out 0x112acf (addR64R64Effect 0x112acf 3 6) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 6] []) (.flag .CF)) #v[111, 85]
    (.letOp (n := 118) (.exec 0x112acf (fun s => s.RIP = 0x112acf) (addR64R64Effect 0x112acf 3 6) (Reg.operands [.gpr 3, .gpr 6] [])) #v[111, 85]
    (.letOp (n := 119) (.out 0x112ad2 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ad2 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[114, 117]
    (.letOp (n := 120) (.exec 0x112ad2 (fun s => s.RIP = 0x112ad2) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ad2 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[114, 117]
    (.letOp (n := 121) (.out 0x112ad6 (movR64R64Effect 0x112ad6 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 122) (.exec 0x112ad6 (fun s => s.RIP = 0x112ad6) (movR64R64Effect 0x112ad6 0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 123) (.out 0x112ad9 (movR32Imm32Effect 0x112ad9 5 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 124) (.exec 0x112ad9 (fun s => s.RIP = 0x112ad9) (movR32Imm32Effect 0x112ad9 5 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 125) (.out 0x112ade (mulR64Effect 0x112ade 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[123, 121]
    (.letOp (n := 126) (.out 0x112ade (mulR64Effect 0x112ade 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[123, 121]
    (.letOp (n := 127) (.exec 0x112ade (fun s => s.RIP = 0x112ade) (mulR64Effect 0x112ade 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[123, 121]
    (.letOp (n := 128) (.out 0x112ae1 (movR64R64Effect 0x112ae1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[125]
    (.letOp (n := 129) (.exec 0x112ae1 (fun s => s.RIP = 0x112ae1) (movR64R64Effect 0x112ae1 15 0) (Reg.operands [.gpr 0] [])) #v[125]
    (.letOp (n := 130) (.out 0x112ae4 (addR64R64Effect 0x112ae4 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[128, 103]
    (.letOp (n := 131) (.out 0x112ae4 (addR64R64Effect 0x112ae4 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[128, 103]
    (.letOp (n := 132) (.exec 0x112ae4 (fun s => s.RIP = 0x112ae4) (addR64R64Effect 0x112ae4 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[128, 103]
    (.letOp (n := 133) (.out 0x112ae7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ae7 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[126, 131]
    (.letOp (n := 134) (.exec 0x112ae7 (fun s => s.RIP = 0x112ae7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ae7 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[126, 131]
    (.letOp (n := 135) (.out 0x112aeb (addR64R64Effect 0x112aeb 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[130, 119]
    (.letOp (n := 136) (.out 0x112aeb (addR64R64Effect 0x112aeb 15 12) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 12] []) (.flag .CF)) #v[130, 119]
    (.letOp (n := 137) (.exec 0x112aeb (fun s => s.RIP = 0x112aeb) (addR64R64Effect 0x112aeb 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[130, 119]
    (.letOp (n := 138) (.out 0x112aee (movzxR32R8Effect 0x112aee 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[109]
    (.letOp (n := 139) (.exec 0x112aee (fun s => s.RIP = 0x112aee) (movzxR32R8Effect 0x112aee 4 6 8) (Reg.operands [.gpr 8] [])) #v[109]
    (.terminate (.br ⟨.l1185d2, RegMap.args [(0, 125), (1, 106), (2, 133), (3, 116), (4, 4), (5, 5), (6, 138), (7, 7), (8, 109), (9, 9), (10, 10), (11, 103), (12, 119), (13, 60), (14, 82), (15, 135), (16, 136), (22, 22), (39, 39), (51, 51)] 140⟩)))))))))))))))))))))))))))))))))))))))))))

def bytes_l118544_1 : List UInt8 :=
  [0x4D, 0x01, 0xD7, 0x0F, 0xB6, 0xC9, 0x4D, 0x11, 0xC3, 0x4C, 0x11, 0xC9, 0x41, 0x0F, 0x92, 0xC0,
    0x4C, 0x01, 0xFB, 0x49, 0x83, 0xD4, 0x00, 0x48, 0x01, 0xF3, 0x49, 0x83, 0xD4, 0x00, 0x4C, 0x89,
    0xC8, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC7, 0x4D, 0x01, 0xDF, 0x48,
    0x83, 0xD2, 0x00, 0x4D, 0x01, 0xE7, 0x41, 0x0F, 0xB6, 0xF0]

theorem code_l118544_1 : ∀ x ∈ codeRange 0x112ab8 bytes_l118544_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12ab8 58 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118544 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112a64 (movR64Imm64Effect 0x112a64 2 0x12ffd85eedf9bfe) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 54) (.exec 0x112a64 (fun s => s.RIP = 0x112a64) (movR64Imm64Effect 0x112a64 2 0x12ffd85eedf9bfe) (Reg.operands [] [])) #v[]
    (.letOp (n := 55) (.out 0x112a6e (mulR64Effect 0x112a6e 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[53, 0]
    (.letOp (n := 56) (.out 0x112a6e (mulR64Effect 0x112a6e 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[53, 0]
    (.letOp (n := 57) (.exec 0x112a6e (fun s => s.RIP = 0x112a6e) (mulR64Effect 0x112a6e 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 58) (.out 0x112a71 (movR64R64Effect 0x112a71 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[55]
    (.letOp (n := 59) (.exec 0x112a71 (fun s => s.RIP = 0x112a71) (movR64R64Effect 0x112a71 12 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 60) (.out 0x112a74 (movR64R64Effect 0x112a74 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[56]
    (.letOp (n := 61) (.exec 0x112a74 (fun s => s.RIP = 0x112a74) (movR64R64Effect 0x112a74 13 2) (Reg.operands [.gpr 2] [])) #v[56]
    (.letOp (n := 62) (.out 0x112a77 (andR64Imm8Effect 0x112a77 3 0xfe) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[3]
    (.letOp (n := 63) (.exec 0x112a77 (fun s => s.RIP = 0x112a77) (andR64Imm8Effect 0x112a77 3 0xfe) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 64) (.out 0x112a7b (movR64R64Effect 0x112a7b 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 65) (.exec 0x112a7b (fun s => s.RIP = 0x112a7b) (movR64R64Effect 0x112a7b 0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 66) (.out 0x112a7e (movR64Imm64Effect 0x112a7e 2 0x43190552df1a6c21) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 67) (.exec 0x112a7e (fun s => s.RIP = 0x112a7e) (movR64Imm64Effect 0x112a7e 2 0x43190552df1a6c21) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.out 0x112a88 (mulR64Effect 0x112a88 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[66, 64]
    (.letOp (n := 69) (.out 0x112a88 (mulR64Effect 0x112a88 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[66, 64]
    (.letOp (n := 70) (.exec 0x112a88 (fun s => s.RIP = 0x112a88) (mulR64Effect 0x112a88 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[66, 64]
    (.letOp (n := 71) (.out 0x112a8b (movR64R64Effect 0x112a8b 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x112a8b (fun s => s.RIP = 0x112a8b) (movR64R64Effect 0x112a8b 6 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 73) (.out 0x112a8e (movR64R64Effect 0x112a8e 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[68]
    (.letOp (n := 74) (.exec 0x112a8e (fun s => s.RIP = 0x112a8e) (movR64R64Effect 0x112a8e 14 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 75) (.out 0x112a91 (addR64R64Effect 0x112a91 14 5) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 5] []) (.reg (.gpr 14))) #v[73, 5]
    (.letOp (n := 76) (.out 0x112a91 (addR64R64Effect 0x112a91 14 5) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 5] []) (.flag .CF)) #v[73, 5]
    (.letOp (n := 77) (.exec 0x112a91 (fun s => s.RIP = 0x112a91) (addR64R64Effect 0x112a91 14 5) (Reg.operands [.gpr 14, .gpr 5] [])) #v[73, 5]
    (.letOp (n := 78) (.out 0x112a94 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a94 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[71, 76]
    (.letOp (n := 79) (.exec 0x112a94 (fun s => s.RIP = 0x112a94) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a94 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[71, 76]
    (.letOp (n := 80) (.out 0x112a98 (addR64R64Effect 0x112a98 12 3) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 3] []) (.flag .CF)) #v[58, 62]
    (.letOp (n := 81) (.exec 0x112a98 (fun s => s.RIP = 0x112a98) (addR64R64Effect 0x112a98 12 3) (Reg.operands [.gpr 12, .gpr 3] [])) #v[58, 62]
    (.letOp (n := 82) (.out 0x112a9b (atFlags StatusFlags.CF (adcR64R64Effect 0x112a9b 14 13)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[75, 60, 80]
    (.letOp (n := 83) (.out 0x112a9b (atFlags StatusFlags.CF (adcR64R64Effect 0x112a9b 14 13)) (Reg.operands [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[75, 60, 80]
    (.letOp (n := 84) (.exec 0x112a9b (fun s => s.RIP = 0x112a9b) (atFlags StatusFlags.CF (adcR64R64Effect 0x112a9b 14 13)) (Reg.operands [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[75, 60, 80]
    (.letOp (n := 85) (.out 0x112a9e (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a9e 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[78, 83]
    (.letOp (n := 86) (.exec 0x112a9e (fun s => s.RIP = 0x112a9e) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112a9e 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[78, 83]
    (.letOp (n := 87) (.out 0x112aa2 (movR64R64Effect 0x112aa2 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[9]
    (.letOp (n := 88) (.exec 0x112aa2 (fun s => s.RIP = 0x112aa2) (movR64R64Effect 0x112aa2 0 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 89) (.out 0x112aa5 (movR64Imm64Effect 0x112aa5 2 0xfffffffeffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 90) (.exec 0x112aa5 (fun s => s.RIP = 0x112aa5) (movR64Imm64Effect 0x112aa5 2 0xfffffffeffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 91) (.out 0x112aaf (mulR64Effect 0x112aaf 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[89, 87]
    (.letOp (n := 92) (.out 0x112aaf (mulR64Effect 0x112aaf 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[89, 87]
    (.letOp (n := 93) (.exec 0x112aaf (fun s => s.RIP = 0x112aaf) (mulR64Effect 0x112aaf 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[89, 87]
    (.letOp (n := 94) (.out 0x112ab2 (movR64R64Effect 0x112ab2 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[91]
    (.letOp (n := 95) (.exec 0x112ab2 (fun s => s.RIP = 0x112ab2) (movR64R64Effect 0x112ab2 3 0) (Reg.operands [.gpr 0] [])) #v[91]
    (.letOp (n := 96) (.out 0x112ab5 (movR64R64Effect 0x112ab5 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[92]
    (.letOp (n := 97) (.exec 0x112ab5 (fun s => s.RIP = 0x112ab5) (movR64R64Effect 0x112ab5 12 2) (Reg.operands [.gpr 2] [])) #v[92]
    (b_l118544_1)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118544 : List UInt8 :=
  [0x48, 0xBA, 0xFE, 0x9B, 0xDF, 0xEE, 0x85, 0xFD, 0x2F, 0x01, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC4,
    0x49, 0x89, 0xD5, 0x48, 0x83, 0xE3, 0xFE, 0x4C, 0x89, 0xC8, 0x48, 0xBA, 0x21, 0x6C, 0x1A, 0xDF,
    0x52, 0x05, 0x19, 0x43, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x49, 0x89, 0xC6, 0x49, 0x01, 0xEE,
    0x48, 0x83, 0xD6, 0x00, 0x49, 0x01, 0xDC, 0x4D, 0x11, 0xEE, 0x48, 0x83, 0xD6, 0x00, 0x4C, 0x89,
    0xC8, 0x48, 0xBA, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x48, 0x89,
    0xC3, 0x49, 0x89, 0xD4] ++ bytes_l118544_1

theorem code_l118544 : ∀ x ∈ codeRange 0x112a64 bytes_l118544, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12a64 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118544_1

@[cfg_block] def b_l1185d2_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x112b4a (imulR64R64Effect 0x112b4a 4 10 11) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11] []) (.reg (.gpr 10))) #v[91, 67]
    (.letOp (n := 94) (.exec 0x112b4a (fun s => s.RIP = 0x112b4a) (imulR64R64Effect 0x112b4a 4 10 11) (Reg.operands [.gpr 10, .gpr 11] [])) #v[91, 67]
    (.letOp (n := 95) (.out 0x112b4e (addR64R64Effect 0x112b4e 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[89, 15]
    (.letOp (n := 96) (.exec 0x112b4e (fun s => s.RIP = 0x112b4e) (addR64R64Effect 0x112b4e 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[89, 15]
    (.letOp (n := 97) (.out 0x112b51 (subR64R64Effect 0x112b51 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[93, 95]
    (.letOp (n := 98) (.exec 0x112b51 (fun s => s.RIP = 0x112b51) (subR64R64Effect 0x112b51 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[93, 95]
    (.letOp (n := 99) (.out 0x112b54 (movR64Imm64Effect 0x112b54 2 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 100) (.exec 0x112b54 (fun s => s.RIP = 0x112b54) (movR64Imm64Effect 0x112b54 2 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x112b5e (movR64R64Effect 0x112b5e 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 102) (.exec 0x112b5e (fun s => s.RIP = 0x112b5e) (movR64R64Effect 0x112b5e 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 103) (.out 0x112b61 (mulR64Effect 0x112b61 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[99, 101]
    (.letOp (n := 104) (.out 0x112b61 (mulR64Effect 0x112b61 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[99, 101]
    (.letOp (n := 105) (.exec 0x112b61 (fun s => s.RIP = 0x112b61) (mulR64Effect 0x112b61 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[99, 101]
    (.letOp (n := 106) (.out 0x112b64 (movR64R64Effect 0x112b64 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[103]
    (.letOp (n := 107) (.exec 0x112b64 (fun s => s.RIP = 0x112b64) (movR64R64Effect 0x112b64 11 0) (Reg.operands [.gpr 0] [])) #v[103]
    (.letOp (n := 108) (.out 0x112b67 (movR64R64Effect 0x112b67 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[104]
    (.letOp (n := 109) (.exec 0x112b67 (fun s => s.RIP = 0x112b67) (movR64R64Effect 0x112b67 14 2) (Reg.operands [.gpr 2] [])) #v[104]
    (.letOp (n := 110) (.out 0x112b6a (imulR64R64Effect 0x112b6a 4 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[56, 58]
    (.letOp (n := 111) (.exec 0x112b6a (fun s => s.RIP = 0x112b6a) (imulR64R64Effect 0x112b6a 4 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[56, 58]
    (.letOp (n := 112) (.out 0x112b6e (addR64R64Effect 0x112b6e 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[97, 110]
    (.letOp (n := 113) (.exec 0x112b6e (fun s => s.RIP = 0x112b6e) (addR64R64Effect 0x112b6e 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[97, 110]
    (.letOp (n := 114) (.out 0x112b71 (movR64R64Effect 0x112b71 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 115) (.exec 0x112b71 (fun s => s.RIP = 0x112b71) (movR64R64Effect 0x112b71 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.terminate (.br ⟨.l118654, RegMap.args [(0, 114), (1, 53), (2, 104), (3, 3), (4, 4), (6, 110), (7, 7), (8, 58), (9, 74), (10, 112), (11, 106), (12, 84), (14, 108), (15, 15), (22, 22), (39, 39), (51, 51)] 116⟩))))))))))))))))))))))))

def bytes_l1185d2_1 : List UInt8 :=
  [0x4D, 0x0F, 0xAF, 0xD3, 0x4C, 0x01, 0xF8, 0x49, 0x29, 0xC2, 0x48, 0xBA, 0x00, 0x00, 0x00, 0x00,
    0xFF, 0xFF, 0xFF, 0xFF, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC3, 0x49, 0x89, 0xD6,
    0x49, 0x0F, 0xAF, 0xF0, 0x49, 0x01, 0xF2, 0x48, 0x89, 0xD8]

theorem code_l1185d2_1 : ∀ x ∈ codeRange 0x112b4a bytes_l1185d2_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12b4a 42 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1185d2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x112af2 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[1, 2, 16]
    (.letOp (n := 54) (.out 0x112af2 (atFlags StatusFlags.CF (adcR64R64Effect 0x112af2 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[1, 2, 16]
    (.letOp (n := 55) (.exec 0x112af2 (fun s => s.RIP = 0x112af2) (atFlags StatusFlags.CF (adcR64R64Effect 0x112af2 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1, 2, 16]
    (.letOp (n := 56) (.out 0x112af5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112af5 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[6, 54]
    (.letOp (n := 57) (.exec 0x112af5 (fun s => s.RIP = 0x112af5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112af5 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[6, 54]
    (.letOp (n := 58) (.out 0x112af9 (movR64Imm64Effect 0x112af9 8 0xf3b9cac2fc632551) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 59) (.exec 0x112af9 (fun s => s.RIP = 0x112af9) (movR64Imm64Effect 0x112af9 8 0xf3b9cac2fc632551) (Reg.operands [] [])) #v[]
    (.letOp (n := 60) (.out 0x112b03 (movR64R64Effect 0x112b03 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 61) (.exec 0x112b03 (fun s => s.RIP = 0x112b03) (movR64R64Effect 0x112b03 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 62) (.out 0x112b06 (mulR64Effect 0x112b06 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[58, 60]
    (.letOp (n := 63) (.out 0x112b06 (mulR64Effect 0x112b06 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[58, 60]
    (.letOp (n := 64) (.exec 0x112b06 (fun s => s.RIP = 0x112b06) (mulR64Effect 0x112b06 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[58, 60]
    (.letOp (n := 65) (.exec 0x112b09 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b09 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112b09 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b09 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[62, 4]
    (.letOp (n := 66) (.exec 0x112b0e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b0e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112b0e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b0e 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 67) (.out 0x112b13 (movR64Imm64Effect 0x112b13 11 0xbce6faada7179e84) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 68) (.exec 0x112b13 (fun s => s.RIP = 0x112b13) (movR64Imm64Effect 0x112b13 11 0xbce6faada7179e84) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x112b1d (movR64R64Effect 0x112b1d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 70) (.exec 0x112b1d (fun s => s.RIP = 0x112b1d) (movR64R64Effect 0x112b1d 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 71) (.out 0x112b20 (mulR64Effect 0x112b20 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[67, 69]
    (.letOp (n := 72) (.out 0x112b20 (mulR64Effect 0x112b20 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[67, 69]
    (.letOp (n := 73) (.exec 0x112b20 (fun s => s.RIP = 0x112b20) (mulR64Effect 0x112b20 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[67, 69]
    (.letOp (n := 74) (.out 0x112b23 (movR64R64Effect 0x112b23 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[71]
    (.letOp (n := 75) (.exec 0x112b23 (fun s => s.RIP = 0x112b23) (movR64R64Effect 0x112b23 9 0) (Reg.operands [.gpr 0] [])) #v[71]
    (.letOp (n := 76) (.exec 0x112b26 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b26 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112b26 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b26 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[72, 4]
    (.letOp (n := 77) (.out 0x112b2b (movR64Imm32Effect 0x112b2b 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 78) (.exec 0x112b2b (fun s => s.RIP = 0x112b2b) (movR64Imm32Effect 0x112b2b 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x112b32 (movR64R64Effect 0x112b32 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[14]
    (.letOp (n := 80) (.exec 0x112b32 (fun s => s.RIP = 0x112b32) (movR64R64Effect 0x112b32 0 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 81) (.out 0x112b35 (mulR64Effect 0x112b35 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[77, 79]
    (.letOp (n := 82) (.out 0x112b35 (mulR64Effect 0x112b35 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[77, 79]
    (.letOp (n := 83) (.exec 0x112b35 (fun s => s.RIP = 0x112b35) (mulR64Effect 0x112b35 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[77, 79]
    (.letOp (n := 84) (.out 0x112b38 (movR64R64Effect 0x112b38 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[81]
    (.letOp (n := 85) (.exec 0x112b38 (fun s => s.RIP = 0x112b38) (movR64R64Effect 0x112b38 12 0) (Reg.operands [.gpr 0] [])) #v[81]
    (.letOp (n := 86) (.exec 0x112b3b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112b3b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112b3b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x112b3b 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[82, 4]
    (.letOp (n := 87) (.out 0x112b40 (movR64R64Effect 0x112b40 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 88) (.exec 0x112b40 (fun s => s.RIP = 0x112b40) (movR64R64Effect 0x112b40 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 89) (.out 0x112b43 (shlR64Effect 0x112b43 4 0 32) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[87]
    (.letOp (n := 90) (.exec 0x112b43 (fun s => s.RIP = 0x112b43) (shlR64Effect 0x112b43 4 0 32) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.out 0x112b47 (movR64R64Effect 0x112b47 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 1] []) (.reg (.gpr 10))) #v[53]
    (.letOp (n := 92) (.exec 0x112b47 (fun s => s.RIP = 0x112b47) (movR64R64Effect 0x112b47 10 1) (Reg.operands [.gpr 1] [])) #v[53]
    (b_l1185d2_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1185d2 : List UInt8 :=
  [0x48, 0x11, 0xD1, 0x48, 0x83, 0xD6, 0x00, 0x49, 0xB8, 0x51, 0x25, 0x63, 0xFC, 0xC2, 0xCA, 0xB9,
    0xF3, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0x54, 0x24,
    0x18, 0x49, 0xBB, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC, 0x4C, 0x89, 0xF0, 0x49, 0xF7,
    0xE3, 0x49, 0x89, 0xC1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0xC7, 0xC2, 0xFF, 0xFF, 0xFF, 0xFF,
    0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xC4, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0x89,
    0xD8, 0x48, 0xC1, 0xE0, 0x20, 0x49, 0x89, 0xCA] ++ bytes_l1185d2_1

theorem code_l1185d2 : ∀ x ∈ codeRange 0x112af2 bytes_l1185d2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12af2 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1185d2_1

@[cfg_block] def b_l118654_2 : Block Op Label signature Reg.count 150 :=
  .letOp (n := 150) (.out 0x112c08 (atFlags StatusFlags.CF (adcR64R64Effect 0x112c08 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[135, 130, 148]
    (.letOp (n := 151) (.exec 0x112c08 (fun s => s.RIP = 0x112c08) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c08 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[135, 130, 148]
    (.letOp (n := 152) (.out 0x112c0b (movR64M64Effect 0x112c0b 1 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 153) (.exec 0x112c0b (LoadPre 0x112c0b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x112c0b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112c0b 1 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 154) (.out 0x112c10 (movR64M64Effect 0x112c10 8 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[152]
    (.letOp (n := 155) (.exec 0x112c10 (LoadPre 0x112c10 (fun s => AddrMode.addr (.base 1 .none) s (0x112c10 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x112c10 8 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[152]
    (.terminate (.br ⟨.l1186f3, RegMap.args [(0, 139), (1, 152), (2, 140), (3, 150), (4, 4), (5, 130), (6, 91), (7, 7), (8, 154), (9, 85), (10, 78), (11, 114), (12, 88), (13, 144), (14, 147), (15, 142), (22, 22), (39, 39), (51, 51)] 156⟩)))))))

def bytes_l118654_2 : List UInt8 :=
  [0x48, 0x11, 0xEB, 0x48, 0x8B, 0x4C, 0x24, 0x28, 0x4C, 0x8B, 0x01]

theorem code_l118654_2 : ∀ x ∈ codeRange 0x112c08 bytes_l118654_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12c08 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118654_1 : Block Op Label signature Reg.count 102 :=
  .letOp (n := 102) (.out 0x112bc3 (movR64R64Effect 0x112bc3 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[97]
    (.letOp (n := 103) (.exec 0x112bc3 (fun s => s.RIP = 0x112bc3) (movR64R64Effect 0x112bc3 14 0) (Reg.operands [.gpr 0] [])) #v[97]
    (.letOp (n := 104) (.out 0x112bc6 (addR64R64Effect 0x112bc6 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[102, 75]
    (.letOp (n := 105) (.out 0x112bc6 (addR64R64Effect 0x112bc6 14 11) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 11] []) (.flag .CF)) #v[102, 75]
    (.letOp (n := 106) (.exec 0x112bc6 (fun s => s.RIP = 0x112bc6) (addR64R64Effect 0x112bc6 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[102, 75]
    (.letOp (n := 107) (.out 0x112bc9 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bc9 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[100, 105]
    (.letOp (n := 108) (.exec 0x112bc9 (fun s => s.RIP = 0x112bc9) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bc9 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[100, 105]
    (.letOp (n := 109) (.out 0x112bcd (movR64R64Effect 0x112bcd 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 110) (.exec 0x112bcd (fun s => s.RIP = 0x112bcd) (movR64R64Effect 0x112bcd 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 111) (.out 0x112bd0 (mulR64Effect 0x112bd0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[8, 109]
    (.letOp (n := 112) (.out 0x112bd0 (mulR64Effect 0x112bd0 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[8, 109]
    (.letOp (n := 113) (.exec 0x112bd0 (fun s => s.RIP = 0x112bd0) (mulR64Effect 0x112bd0 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 109]
    (.letOp (n := 114) (.out 0x112bd3 (movR64R64Effect 0x112bd3 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[112]
    (.letOp (n := 115) (.exec 0x112bd3 (fun s => s.RIP = 0x112bd3) (movR64R64Effect 0x112bd3 11 2) (Reg.operands [.gpr 2] [])) #v[112]
    (.letOp (n := 116) (.out 0x112bd6 (movR64R64Effect 0x112bd6 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[111]
    (.letOp (n := 117) (.exec 0x112bd6 (fun s => s.RIP = 0x112bd6) (movR64R64Effect 0x112bd6 13 0) (Reg.operands [.gpr 0] [])) #v[111]
    (.letOp (n := 118) (.out 0x112bd9 (movR64R64Effect 0x112bd9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[15]
    (.letOp (n := 119) (.exec 0x112bd9 (fun s => s.RIP = 0x112bd9) (movR64R64Effect 0x112bd9 0 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 120) (.out 0x112bdc (movR64Imm64Effect 0x112bdc 2 0xbce6faada7179e84) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 121) (.exec 0x112bdc (fun s => s.RIP = 0x112bdc) (movR64Imm64Effect 0x112bdc 2 0xbce6faada7179e84) (Reg.operands [] [])) #v[]
    (.letOp (n := 122) (.out 0x112be6 (mulR64Effect 0x112be6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[120, 118]
    (.letOp (n := 123) (.out 0x112be6 (mulR64Effect 0x112be6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[120, 118]
    (.letOp (n := 124) (.exec 0x112be6 (fun s => s.RIP = 0x112be6) (mulR64Effect 0x112be6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[120, 118]
    (.letOp (n := 125) (.out 0x112be9 (movR64R64Effect 0x112be9 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[123]
    (.letOp (n := 126) (.exec 0x112be9 (fun s => s.RIP = 0x112be9) (movR64R64Effect 0x112be9 3 2) (Reg.operands [.gpr 2] [])) #v[123]
    (.letOp (n := 127) (.out 0x112bec (addR64R64Effect 0x112bec 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[104, 91]
    (.letOp (n := 128) (.out 0x112bec (addR64R64Effect 0x112bec 14 6) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[104, 91]
    (.letOp (n := 129) (.exec 0x112bec (fun s => s.RIP = 0x112bec) (addR64R64Effect 0x112bec 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[104, 91]
    (.letOp (n := 130) (.out 0x112bef (atFlags StatusFlags.CF (adcR64R64Effect 0x112bef 5 10)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[107, 78, 128]
    (.letOp (n := 131) (.exec 0x112bef (fun s => s.RIP = 0x112bef) (atFlags StatusFlags.CF (adcR64R64Effect 0x112bef 5 10)) (Reg.operands [.gpr 5, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[107, 78, 128]
    (.letOp (n := 132) (.out 0x112bf2 (addR64R64Effect 0x112bf2 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[127, 122]
    (.letOp (n := 133) (.out 0x112bf2 (addR64R64Effect 0x112bf2 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[127, 122]
    (.letOp (n := 134) (.exec 0x112bf2 (fun s => s.RIP = 0x112bf2) (addR64R64Effect 0x112bf2 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[127, 122]
    (.letOp (n := 135) (.out 0x112bf5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bf5 3 0x0)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[125, 133]
    (.letOp (n := 136) (.exec 0x112bf5 (fun s => s.RIP = 0x112bf5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112bf5 3 0x0)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[125, 133]
    (.letOp (n := 137) (.out 0x112bf9 (movR64R64Effect 0x112bf9 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 138) (.exec 0x112bf9 (fun s => s.RIP = 0x112bf9) (movR64R64Effect 0x112bf9 0 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 139) (.out 0x112bfc (mulR64Effect 0x112bfc 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[8, 137]
    (.letOp (n := 140) (.out 0x112bfc (mulR64Effect 0x112bfc 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[8, 137]
    (.letOp (n := 141) (.exec 0x112bfc (fun s => s.RIP = 0x112bfc) (mulR64Effect 0x112bfc 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 137]
    (.letOp (n := 142) (.out 0x112bff (movR64R64Effect 0x112bff 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 8] []) (.reg (.gpr 15))) #v[8]
    (.letOp (n := 143) (.exec 0x112bff (fun s => s.RIP = 0x112bff) (movR64R64Effect 0x112bff 15 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 144) (.out 0x112c02 (addR64R64Effect 0x112c02 13 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 12] []) (.reg (.gpr 13))) #v[116, 88]
    (.letOp (n := 145) (.out 0x112c02 (addR64R64Effect 0x112c02 13 12) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 12] []) (.flag .CF)) #v[116, 88]
    (.letOp (n := 146) (.exec 0x112c02 (fun s => s.RIP = 0x112c02) (addR64R64Effect 0x112c02 13 12) (Reg.operands [.gpr 13, .gpr 12] [])) #v[116, 88]
    (.letOp (n := 147) (.out 0x112c05 (atFlags StatusFlags.CF (adcR64R64Effect 0x112c05 14 11)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[132, 114, 145]
    (.letOp (n := 148) (.out 0x112c05 (atFlags StatusFlags.CF (adcR64R64Effect 0x112c05 14 11)) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[132, 114, 145]
    (.letOp (n := 149) (.exec 0x112c05 (fun s => s.RIP = 0x112c05) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c05 14 11)) (Reg.operands [.gpr 14, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[132, 114, 145]
    (b_l118654_2))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118654_1 : List UInt8 :=
  [0x49, 0x89, 0xC6, 0x4D, 0x01, 0xDE, 0x48, 0x83, 0xD5, 0x00, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE0,
    0x49, 0x89, 0xD3, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xF8, 0x48, 0xBA, 0x84, 0x9E, 0x17, 0xA7, 0xAD,
    0xFA, 0xE6, 0xBC, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD3, 0x49, 0x01, 0xF6, 0x4C, 0x11, 0xD5, 0x49,
    0x01, 0xC6, 0x48, 0x83, 0xD3, 0x00, 0x48, 0x89, 0xC8, 0x49, 0xF7, 0xE0, 0x4D, 0x89, 0xC7, 0x4D,
    0x01, 0xE5, 0x4D, 0x11, 0xDE] ++ bytes_l118654_2

theorem code_l118654_1 : ∀ x ∈ codeRange 0x112bc3 bytes_l118654_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12bc3 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118654_2

@[cfg_block] def b_l118654 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112b74 (mulR64Effect 0x112b74 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[8, 0]
    (.letOp (n := 54) (.out 0x112b74 (mulR64Effect 0x112b74 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[8, 0]
    (.letOp (n := 55) (.exec 0x112b74 (fun s => s.RIP = 0x112b74) (mulR64Effect 0x112b74 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[8, 0]
    (.letOp (n := 56) (.out 0x112b77 (movR64R64Effect 0x112b77 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[54]
    (.letOp (n := 57) (.exec 0x112b77 (fun s => s.RIP = 0x112b77) (movR64R64Effect 0x112b77 5 2) (Reg.operands [.gpr 2] [])) #v[54]
    (.letOp (n := 58) (.out 0x112b7a (movR64R64Effect 0x112b7a 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[53]
    (.letOp (n := 59) (.exec 0x112b7a (fun s => s.RIP = 0x112b7a) (movR64R64Effect 0x112b7a 13 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 60) (.out 0x112b7d (movR64R64Effect 0x112b7d 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 61) (.exec 0x112b7d (fun s => s.RIP = 0x112b7d) (movR64R64Effect 0x112b7d 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 62) (.out 0x112b80 (movR64Imm64Effect 0x112b80 2 0xbce6faada7179e84) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 63) (.exec 0x112b80 (fun s => s.RIP = 0x112b80) (movR64Imm64Effect 0x112b80 2 0xbce6faada7179e84) (Reg.operands [] [])) #v[]
    (.letOp (n := 64) (.out 0x112b8a (mulR64Effect 0x112b8a 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[62, 60]
    (.letOp (n := 65) (.out 0x112b8a (mulR64Effect 0x112b8a 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[62, 60]
    (.letOp (n := 66) (.exec 0x112b8a (fun s => s.RIP = 0x112b8a) (mulR64Effect 0x112b8a 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[62, 60]
    (.letOp (n := 67) (.out 0x112b8d (movR64R64Effect 0x112b8d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x112b8d (fun s => s.RIP = 0x112b8d) (movR64R64Effect 0x112b8d 6 2) (Reg.operands [.gpr 2] [])) #v[65]
    (.letOp (n := 69) (.out 0x112b90 (addR64M64Effect 0x112b90 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[9, 4]
    (.letOp (n := 70) (.out 0x112b90 (addR64M64Effect 0x112b90 9 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 4] []) (.flag .CF)) #v[9, 4]
    (.letOp (n := 71) (.exec 0x112b90 (LoadPre 0x112b90 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x112b90 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x112b90 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 72) (.out 0x112b95 (atFlags StatusFlags.CF (adcR64M64Effect 0x112b95 12 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[12, 4, 70]
    (.letOp (n := 73) (.out 0x112b95 (atFlags StatusFlags.CF (adcR64M64Effect 0x112b95 12 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[12, 4, 70]
    (.letOp (n := 74) (.exec 0x112b95 (LoadPre 0x112b95 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x112b95 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112b95 12 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[12, 4, 70]
    (.letOp (n := 75) (.out 0x112b9a (atFlags StatusFlags.CF (adcR64M64Effect 0x112b9a 11 (.sib 4 none 0 (.d8 0x20)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[11, 4, 73]
    (.letOp (n := 76) (.out 0x112b9a (atFlags StatusFlags.CF (adcR64M64Effect 0x112b9a 11 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.flag .CF)) #v[11, 4, 73]
    (.letOp (n := 77) (.exec 0x112b9a (LoadPre 0x112b9a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x112b9a + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x112b9a 11 (.sib 4 none 0 (.d8 0x20)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[11, 4, 73]
    (.letOp (n := 78) (.out 0x112b9f (atFlags StatusFlags.CF (adcR64R64Effect 0x112b9f 10 14)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[10, 14, 76]
    (.letOp (n := 79) (.exec 0x112b9f (fun s => s.RIP = 0x112b9f) (atFlags StatusFlags.CF (adcR64R64Effect 0x112b9f 10 14)) (Reg.operands [.gpr 10, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[10, 14, 76]
    (.letOp (n := 80) (.out 0x112ba2 (addR64R64Effect 0x112ba2 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[72, 64]
    (.letOp (n := 81) (.out 0x112ba2 (addR64R64Effect 0x112ba2 12 0) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 0] []) (.flag .CF)) #v[72, 64]
    (.letOp (n := 82) (.exec 0x112ba2 (fun s => s.RIP = 0x112ba2) (addR64R64Effect 0x112ba2 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[72, 64]
    (.letOp (n := 83) (.out 0x112ba5 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ba5 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[67, 81]
    (.letOp (n := 84) (.exec 0x112ba5 (fun s => s.RIP = 0x112ba5) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112ba5 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[67, 81]
    (.letOp (n := 85) (.out 0x112ba9 (addR64R64Effect 0x112ba9 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[69, 58]
    (.letOp (n := 86) (.out 0x112ba9 (addR64R64Effect 0x112ba9 9 13) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 13] []) (.flag .CF)) #v[69, 58]
    (.letOp (n := 87) (.exec 0x112ba9 (fun s => s.RIP = 0x112ba9) (addR64R64Effect 0x112ba9 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[69, 58]
    (.letOp (n := 88) (.out 0x112bac (atFlags StatusFlags.CF (adcR64R64Effect 0x112bac 12 5)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[80, 56, 86]
    (.letOp (n := 89) (.out 0x112bac (atFlags StatusFlags.CF (adcR64R64Effect 0x112bac 12 5)) (Reg.operands [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[80, 56, 86]
    (.letOp (n := 90) (.exec 0x112bac (fun s => s.RIP = 0x112bac) (atFlags StatusFlags.CF (adcR64R64Effect 0x112bac 12 5)) (Reg.operands [.gpr 12, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[80, 56, 86]
    (.letOp (n := 91) (.out 0x112baf (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112baf 6 0x0)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[83, 89]
    (.letOp (n := 92) (.exec 0x112baf (fun s => s.RIP = 0x112baf) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112baf 6 0x0)) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[83, 89]
    (.letOp (n := 93) (.out 0x112bb3 (movR64R64Effect 0x112bb3 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 94) (.exec 0x112bb3 (fun s => s.RIP = 0x112bb3) (movR64R64Effect 0x112bb3 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 95) (.out 0x112bb6 (movR64Imm32Effect 0x112bb6 2 0xffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 96) (.exec 0x112bb6 (fun s => s.RIP = 0x112bb6) (movR64Imm32Effect 0x112bb6 2 0xffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 97) (.out 0x112bbd (mulR64Effect 0x112bbd 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[95, 93]
    (.letOp (n := 98) (.out 0x112bbd (mulR64Effect 0x112bbd 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[95, 93]
    (.letOp (n := 99) (.exec 0x112bbd (fun s => s.RIP = 0x112bbd) (mulR64Effect 0x112bbd 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[95, 93]
    (.letOp (n := 100) (.out 0x112bc0 (movR64R64Effect 0x112bc0 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[98]
    (.letOp (n := 101) (.exec 0x112bc0 (fun s => s.RIP = 0x112bc0) (movR64R64Effect 0x112bc0 5 2) (Reg.operands [.gpr 2] [])) #v[98]
    (b_l118654_1)))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l118654 : List UInt8 :=
  [0x49, 0xF7, 0xE0, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xD8, 0x48, 0xBA, 0x84, 0x9E,
    0x17, 0xA7, 0xAD, 0xFA, 0xE6, 0xBC, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD6, 0x4C, 0x03, 0x4C, 0x24,
    0x18, 0x4C, 0x13, 0x64, 0x24, 0x10, 0x4C, 0x13, 0x5C, 0x24, 0x20, 0x4D, 0x11, 0xF2, 0x49, 0x01,
    0xC4, 0x48, 0x83, 0xD6, 0x00, 0x4D, 0x01, 0xE9, 0x49, 0x11, 0xEC, 0x48, 0x83, 0xD6, 0x00, 0x48,
    0x89, 0xD8, 0x48, 0xC7, 0xC2, 0xFF, 0xFF, 0xFF, 0xFF, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xD5] ++ bytes_l118654_1

theorem code_l118654 : ∀ x ∈ codeRange 0x112b74 bytes_l118654, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x12b74 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l118654_1

@[cfg_block] def b_l1186f3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112c13 (addR64R64Effect 0x112c13 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[14, 0]
    (.letOp (n := 54) (.out 0x112c13 (addR64R64Effect 0x112c13 14 0) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 0] []) (.flag .CF)) #v[14, 0]
    (.letOp (n := 55) (.exec 0x112c13 (fun s => s.RIP = 0x112c13) (addR64R64Effect 0x112c13 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[14, 0]
    (.letOp (n := 56) (.out 0x112c16 (atFlags StatusFlags.CF (adcR64R64Effect 0x112c16 3 2)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[3, 2, 54]
    (.letOp (n := 57) (.exec 0x112c16 (fun s => s.RIP = 0x112c16) (atFlags StatusFlags.CF (adcR64R64Effect 0x112c16 3 2)) (Reg.operands [.gpr 3, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[3, 2, 54]
    (.letOp (n := 58) (.out 0x112c19 (movR64R64Effect 0x112c19 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[8]
    (.letOp (n := 59) (.exec 0x112c19 (fun s => s.RIP = 0x112c19) (movR64R64Effect 0x112c19 0 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 60) (.out 0x112c1c (movR64M64Effect 0x112c1c 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 61) (.exec 0x112c1c (LoadPre 0x112c1c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x112c1c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112c1c 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x112c21 (subR64R64Effect 0x112c21 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[58, 60]
    (.letOp (n := 63) (.exec 0x112c21 (fun s => s.RIP = 0x112c21) (subR64R64Effect 0x112c21 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[58, 60]
    (.letOp (n := 64) (.out 0x112c24 (notR64Effect 0x112c24 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[8]
    (.letOp (n := 65) (.exec 0x112c24 (fun s => s.RIP = 0x112c24) (notR64Effect 0x112c24 8) (Reg.operands [.gpr 8] [])) #v[8]
    (.letOp (n := 66) (.out 0x112c27 (movR64R64Effect 0x112c27 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[60]
    (.letOp (n := 67) (.exec 0x112c27 (fun s => s.RIP = 0x112c27) (movR64R64Effect 0x112c27 2 6) (Reg.operands [.gpr 6] [])) #v[60]
    (.letOp (n := 68) (.out 0x112c2a (andR64R64Effect 0x112c2a 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[66, 64]
    (.letOp (n := 69) (.exec 0x112c2a (fun s => s.RIP = 0x112c2a) (andR64R64Effect 0x112c2a 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[66, 64]
    (.letOp (n := 70) (.out 0x112c2d (orR64R64Effect 0x112c2d 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[64, 60]
    (.letOp (n := 71) (.exec 0x112c2d (fun s => s.RIP = 0x112c2d) (orR64R64Effect 0x112c2d 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[64, 60]
    (.letOp (n := 72) (.out 0x112c30 (movR64M64Effect 0x112c30 6 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 73) (.exec 0x112c30 (LoadPre 0x112c30 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x112c30 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112c30 6 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 74) (.out 0x112c34 (movR64M64Effect 0x112c34 1 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 75) (.exec 0x112c34 (LoadPre 0x112c34 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x112c34 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112c34 1 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 76) (.out 0x112c38 (andR64R64Effect 0x112c38 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[70, 62]
    (.letOp (n := 77) (.exec 0x112c38 (fun s => s.RIP = 0x112c38) (andR64R64Effect 0x112c38 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[70, 62]
    (.letOp (n := 78) (.out 0x112c3b (orR64R64Effect 0x112c3b 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2] []) (.reg (.gpr 8))) #v[76, 68]
    (.letOp (n := 79) (.exec 0x112c3b (fun s => s.RIP = 0x112c3b) (orR64R64Effect 0x112c3b 8 2) (Reg.operands [.gpr 8, .gpr 2] [])) #v[76, 68]
    (.letOp (n := 80) (.out 0x112c3e (shrR64Effect 0x112c3e 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[78]
    (.letOp (n := 81) (.exec 0x112c3e (fun s => s.RIP = 0x112c3e) (shrR64Effect 0x112c3e 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.terminate (.br ⟨.l118722, RegMap.args [(0, 62), (1, 74), (2, 68), (3, 56), (4, 4), (6, 72), (7, 7), (8, 80), (9, 9), (13, 13), (14, 53), (15, 15), (22, 22), (39, 39), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l1186f3 : List UInt8 :=
  [0x49, 0x01, 0xC6, 0x48, 0x11, 0xD3, 0x4C, 0x89, 0xC0, 0x48, 0x8B, 0x74, 0x24, 0x08, 0x48, 0x29,
    0xF0, 0x49, 0xF7, 0xD0, 0x48, 0x89, 0xF2, 0x4C, 0x21, 0xC2, 0x49, 0x09, 0xF0, 0x48, 0x8B, 0x71,
    0x08, 0x48, 0x8B, 0x49, 0x10, 0x49, 0x21, 0xC0, 0x49, 0x09, 0xD0, 0x49, 0xC1, 0xE8, 0x3F]

theorem code_l1186f3 : ∀ x ∈ codeRange 0x112c13 bytes_l1186f3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12c13 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118722 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112c42 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112c42 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c42 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112c42 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 54) (.out 0x112c46 (movR64R64Effect 0x112c46 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 55) (.exec 0x112c46 (fun s => s.RIP = 0x112c46) (movR64R64Effect 0x112c46 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x112c49 (xorR32R32Effect 0x112c49 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[54, 54]
    (.letOp (n := 57) (.exec 0x112c49 (fun s => s.RIP = 0x112c49) (xorR32R32Effect 0x112c49 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[54, 54]
    (.letOp (n := 58) (.out 0x112c4b (subR64M64Effect 0x112c4b 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[56, 4]
    (.letOp (n := 59) (.exec 0x112c4b (LoadPre 0x112c4b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c4b + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112c4b 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x112c4f (movR64R64Effect 0x112c4f 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 61) (.exec 0x112c4f (fun s => s.RIP = 0x112c4f) (movR64R64Effect 0x112c4f 8 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 62) (.out 0x112c52 (subR64R64Effect 0x112c52 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[60, 9]
    (.letOp (n := 63) (.exec 0x112c52 (fun s => s.RIP = 0x112c52) (subR64R64Effect 0x112c52 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[60, 9]
    (.letOp (n := 64) (.out 0x112c55 (sarR64Effect 0x112c55 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[58]
    (.letOp (n := 65) (.exec 0x112c55 (fun s => s.RIP = 0x112c55) (sarR64Effect 0x112c55 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 66) (.out 0x112c59 (addR64R64Effect 0x112c59 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x112c59 (fun s => s.RIP = 0x112c59) (addR64R64Effect 0x112c59 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x112c5c (notR64Effect 0x112c5c 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 69) (.exec 0x112c5c (fun s => s.RIP = 0x112c5c) (notR64Effect 0x112c5c 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x112c5f (movR64R64Effect 0x112c5f 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 9] []) (.reg (.gpr 8))) #v[9]
    (.letOp (n := 71) (.exec 0x112c5f (fun s => s.RIP = 0x112c5f) (movR64R64Effect 0x112c5f 8 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 72) (.out 0x112c62 (andR64R64Effect 0x112c62 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x112c62 (fun s => s.RIP = 0x112c62) (andR64R64Effect 0x112c62 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[70, 68]
    (.letOp (n := 74) (.out 0x112c65 (orR64R64Effect 0x112c65 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[68, 9]
    (.letOp (n := 75) (.exec 0x112c65 (fun s => s.RIP = 0x112c65) (orR64R64Effect 0x112c65 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[68, 9]
    (.letOp (n := 76) (.out 0x112c68 (andR64R64Effect 0x112c68 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[74, 66]
    (.letOp (n := 77) (.exec 0x112c68 (fun s => s.RIP = 0x112c68) (andR64R64Effect 0x112c68 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[74, 66]
    (.letOp (n := 78) (.out 0x112c6b (orR64R64Effect 0x112c6b 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[76, 72]
    (.letOp (n := 79) (.exec 0x112c6b (fun s => s.RIP = 0x112c6b) (orR64R64Effect 0x112c6b 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[76, 72]
    (.letOp (n := 80) (.out 0x112c6e (shrR64Effect 0x112c6e 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[78]
    (.letOp (n := 81) (.exec 0x112c6e (fun s => s.RIP = 0x112c6e) (shrR64Effect 0x112c6e 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.terminate (.br ⟨.l118752, RegMap.args [(0, 0), (1, 1), (2, 66), (3, 3), (4, 4), (6, 80), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l118722 : List UInt8 :=
  [0x4C, 0x89, 0x04, 0x24, 0x48, 0x89, 0xE2, 0x31, 0xD2, 0x48, 0x2B, 0x14, 0x24, 0x49, 0x89, 0xF0,
    0x4D, 0x29, 0xC8, 0x48, 0xC1, 0xFA, 0x3F, 0x4C, 0x01, 0xC2, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xC8,
    0x49, 0x21, 0xF0, 0x4C, 0x09, 0xCE, 0x48, 0x21, 0xD6, 0x4C, 0x09, 0xC6, 0x48, 0xC1, 0xEE, 0x3F]

theorem code_l118722 : ∀ x ∈ codeRange 0x112c42 bytes_l118722, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12c42 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118752 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112c72 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112c72 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c72 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112c72 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.out 0x112c76 (movR64R64Effect 0x112c76 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 55) (.exec 0x112c76 (fun s => s.RIP = 0x112c76) (movR64R64Effect 0x112c76 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x112c79 (xorR32R32Effect 0x112c79 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[54, 54]
    (.letOp (n := 57) (.exec 0x112c79 (fun s => s.RIP = 0x112c79) (xorR32R32Effect 0x112c79 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[54, 54]
    (.letOp (n := 58) (.out 0x112c7b (subR64M64Effect 0x112c7b 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[56, 4]
    (.letOp (n := 59) (.exec 0x112c7b (LoadPre 0x112c7b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112c7b + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112c7b 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x112c7f (movR64R64Effect 0x112c7f 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[1]
    (.letOp (n := 61) (.exec 0x112c7f (fun s => s.RIP = 0x112c7f) (movR64R64Effect 0x112c7f 8 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 62) (.out 0x112c82 (subR64R64Effect 0x112c82 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13] []) (.reg (.gpr 8))) #v[60, 13]
    (.letOp (n := 63) (.exec 0x112c82 (fun s => s.RIP = 0x112c82) (subR64R64Effect 0x112c82 8 13) (Reg.operands [.gpr 8, .gpr 13] [])) #v[60, 13]
    (.letOp (n := 64) (.out 0x112c85 (sarR64Effect 0x112c85 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[58]
    (.letOp (n := 65) (.exec 0x112c85 (fun s => s.RIP = 0x112c85) (sarR64Effect 0x112c85 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 66) (.out 0x112c89 (addR64R64Effect 0x112c89 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x112c89 (fun s => s.RIP = 0x112c89) (addR64R64Effect 0x112c89 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x112c8c (notR64Effect 0x112c8c 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 69) (.exec 0x112c8c (fun s => s.RIP = 0x112c8c) (notR64Effect 0x112c8c 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 70) (.out 0x112c8f (movR64R64Effect 0x112c8f 8 13) (EffectPart.reads (.reg (.gpr 8)) [.gpr 13] []) (.reg (.gpr 8))) #v[13]
    (.letOp (n := 71) (.exec 0x112c8f (fun s => s.RIP = 0x112c8f) (movR64R64Effect 0x112c8f 8 13) (Reg.operands [.gpr 13] [])) #v[13]
    (.letOp (n := 72) (.out 0x112c92 (andR64R64Effect 0x112c92 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[70, 68]
    (.letOp (n := 73) (.exec 0x112c92 (fun s => s.RIP = 0x112c92) (andR64R64Effect 0x112c92 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[70, 68]
    (.letOp (n := 74) (.out 0x112c95 (orR64R64Effect 0x112c95 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[68, 13]
    (.letOp (n := 75) (.exec 0x112c95 (fun s => s.RIP = 0x112c95) (orR64R64Effect 0x112c95 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[68, 13]
    (.letOp (n := 76) (.out 0x112c98 (andR64R64Effect 0x112c98 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[74, 66]
    (.letOp (n := 77) (.exec 0x112c98 (fun s => s.RIP = 0x112c98) (andR64R64Effect 0x112c98 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[74, 66]
    (.letOp (n := 78) (.out 0x112c9b (orR64R64Effect 0x112c9b 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[76, 72]
    (.letOp (n := 79) (.exec 0x112c9b (fun s => s.RIP = 0x112c9b) (orR64R64Effect 0x112c9b 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[76, 72]
    (.letOp (n := 80) (.out 0x112c9e (shrR64Effect 0x112c9e 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[78]
    (.letOp (n := 81) (.exec 0x112c9e (fun s => s.RIP = 0x112c9e) (shrR64Effect 0x112c9e 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.terminate (.br ⟨.l118782, RegMap.args [(0, 0), (1, 80), (2, 2), (3, 3), (4, 4), (6, 66), (7, 7), (8, 72), (9, 9), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 82⟩))))))))))))))))))))))))))))))

def bytes_l118752 : List UInt8 :=
  [0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xE6, 0x31, 0xF6, 0x48, 0x2B, 0x34, 0x24, 0x49, 0x89, 0xC8,
    0x4D, 0x29, 0xE8, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xC6, 0x48, 0xF7, 0xD1, 0x4D, 0x89, 0xE8,
    0x49, 0x21, 0xC8, 0x4C, 0x09, 0xE9, 0x48, 0x21, 0xF1, 0x4C, 0x09, 0xC1, 0x48, 0xC1, 0xE9, 0x3F]

theorem code_l118752 : ∀ x ∈ codeRange 0x112c72 bytes_l118752, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12c72 48 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118782 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112ca2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112ca2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112ca2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112ca2 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.exec 0x112ca6 (fun s => s.RIP = 0x112ca6) (movR64R64Effect 0x112ca6 1 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112ca9 (xorR32R32Effect 0x112ca9 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[9, 9]
    (.letOp (n := 56) (.exec 0x112ca9 (fun s => s.RIP = 0x112ca9) (xorR32R32Effect 0x112ca9 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[9, 9]
    (.letOp (n := 57) (.out 0x112cac (subR64M64Effect 0x112cac 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112cac (LoadPre 0x112cac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112cac + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112cac 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112cb0 (movR64M64Effect 0x112cb0 8 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 60) (.exec 0x112cb0 (LoadPre 0x112cb0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x112cb0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112cb0 8 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x112cb5 (movR64R64Effect 0x112cb5 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 8] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 62) (.exec 0x112cb5 (fun s => s.RIP = 0x112cb5) (movR64R64Effect 0x112cb5 1 8) (Reg.operands [.gpr 8] [])) #v[59]
    (.letOp (n := 63) (.out 0x112cb8 (subR64R64Effect 0x112cb8 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 14] []) (.reg (.gpr 1))) #v[61, 14]
    (.letOp (n := 64) (.exec 0x112cb8 (fun s => s.RIP = 0x112cb8) (subR64R64Effect 0x112cb8 1 14) (Reg.operands [.gpr 1, .gpr 14] [])) #v[61, 14]
    (.letOp (n := 65) (.out 0x112cbb (sarR64Effect 0x112cbb 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 66) (.exec 0x112cbb (fun s => s.RIP = 0x112cbb) (sarR64Effect 0x112cbb 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 67) (.out 0x112cbf (addR64R64Effect 0x112cbf 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[65, 63]
    (.letOp (n := 68) (.exec 0x112cbf (fun s => s.RIP = 0x112cbf) (addR64R64Effect 0x112cbf 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[65, 63]
    (.letOp (n := 69) (.out 0x112cc2 (notR64Effect 0x112cc2 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[59]
    (.letOp (n := 70) (.exec 0x112cc2 (fun s => s.RIP = 0x112cc2) (notR64Effect 0x112cc2 8) (Reg.operands [.gpr 8] [])) #v[59]
    (.letOp (n := 71) (.out 0x112cc5 (movR64R64Effect 0x112cc5 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[14]
    (.letOp (n := 72) (.exec 0x112cc5 (fun s => s.RIP = 0x112cc5) (movR64R64Effect 0x112cc5 1 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x112cc8 (andR64R64Effect 0x112cc8 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[71, 69]
    (.letOp (n := 74) (.exec 0x112cc8 (fun s => s.RIP = 0x112cc8) (andR64R64Effect 0x112cc8 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[71, 69]
    (.letOp (n := 75) (.out 0x112ccb (orR64R64Effect 0x112ccb 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[69, 14]
    (.letOp (n := 76) (.exec 0x112ccb (fun s => s.RIP = 0x112ccb) (orR64R64Effect 0x112ccb 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[69, 14]
    (.letOp (n := 77) (.out 0x112cce (andR64R64Effect 0x112cce 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[75, 67]
    (.letOp (n := 78) (.exec 0x112cce (fun s => s.RIP = 0x112cce) (andR64R64Effect 0x112cce 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[75, 67]
    (.letOp (n := 79) (.out 0x112cd1 (orR64R64Effect 0x112cd1 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[77, 73]
    (.letOp (n := 80) (.exec 0x112cd1 (fun s => s.RIP = 0x112cd1) (orR64R64Effect 0x112cd1 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[77, 73]
    (.letOp (n := 81) (.out 0x112cd4 (shrR64Effect 0x112cd4 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[79]
    (.letOp (n := 82) (.exec 0x112cd4 (fun s => s.RIP = 0x112cd4) (shrR64Effect 0x112cd4 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.terminate (.br ⟨.l1187b8, RegMap.args [(0, 0), (1, 73), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 81), (9, 67), (14, 14), (15, 15), (22, 22), (39, 39), (51, 51)] 83⟩)))))))))))))))))))))))))))))))

def bytes_l118782 : List UInt8 :=
  [0x48, 0x89, 0x0C, 0x24, 0x48, 0x89, 0xE1, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x0C, 0x24, 0x4C, 0x8B,
    0x44, 0x24, 0x38, 0x4C, 0x89, 0xC1, 0x4C, 0x29, 0xF1, 0x49, 0xC1, 0xF9, 0x3F, 0x49, 0x01, 0xC9,
    0x49, 0xF7, 0xD0, 0x4C, 0x89, 0xF1, 0x4C, 0x21, 0xC1, 0x4D, 0x09, 0xF0, 0x4D, 0x21, 0xC8, 0x49,
    0x09, 0xC8, 0x49, 0xC1, 0xE8, 0x3F]

theorem code_l118782 : ∀ x ∈ codeRange 0x112ca2 bytes_l118782, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12ca2 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1187b8 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112cd8 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112cd8 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112cd8 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112cd8 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 8, .gpr 4] [])) #v[8, 4]
    (.letOp (n := 54) (.out 0x112cdc (movR64R64Effect 0x112cdc 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 55) (.exec 0x112cdc (fun s => s.RIP = 0x112cdc) (movR64R64Effect 0x112cdc 1 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x112cdf (xorR32R32Effect 0x112cdf 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[54, 54]
    (.letOp (n := 57) (.exec 0x112cdf (fun s => s.RIP = 0x112cdf) (xorR32R32Effect 0x112cdf 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[54, 54]
    (.letOp (n := 58) (.out 0x112ce1 (subR64M64Effect 0x112ce1 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[56, 4]
    (.letOp (n := 59) (.exec 0x112ce1 (LoadPre 0x112ce1 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112ce1 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112ce1 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x112ce5 (movR64M64Effect 0x112ce5 10 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 61) (.exec 0x112ce5 (LoadPre 0x112ce5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x112ce5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x112ce5 10 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.out 0x112cea (movR64R64Effect 0x112cea 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[60]
    (.letOp (n := 63) (.exec 0x112cea (fun s => s.RIP = 0x112cea) (movR64R64Effect 0x112cea 8 10) (Reg.operands [.gpr 10] [])) #v[60]
    (.letOp (n := 64) (.out 0x112ced (subR64R64Effect 0x112ced 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3] []) (.reg (.gpr 8))) #v[62, 3]
    (.letOp (n := 65) (.exec 0x112ced (fun s => s.RIP = 0x112ced) (subR64R64Effect 0x112ced 8 3) (Reg.operands [.gpr 8, .gpr 3] [])) #v[62, 3]
    (.letOp (n := 66) (.out 0x112cf0 (sarR64Effect 0x112cf0 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[58]
    (.letOp (n := 67) (.exec 0x112cf0 (fun s => s.RIP = 0x112cf0) (sarR64Effect 0x112cf0 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 68) (.out 0x112cf4 (addR64R64Effect 0x112cf4 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[66, 64]
    (.letOp (n := 69) (.exec 0x112cf4 (fun s => s.RIP = 0x112cf4) (addR64R64Effect 0x112cf4 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[66, 64]
    (.letOp (n := 70) (.out 0x112cf7 (notR64Effect 0x112cf7 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[60]
    (.letOp (n := 71) (.exec 0x112cf7 (fun s => s.RIP = 0x112cf7) (notR64Effect 0x112cf7 10) (Reg.operands [.gpr 10] [])) #v[60]
    (.letOp (n := 72) (.out 0x112cfa (movR64R64Effect 0x112cfa 8 3) (EffectPart.reads (.reg (.gpr 8)) [.gpr 3] []) (.reg (.gpr 8))) #v[3]
    (.letOp (n := 73) (.exec 0x112cfa (fun s => s.RIP = 0x112cfa) (movR64R64Effect 0x112cfa 8 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 74) (.out 0x112cfd (andR64R64Effect 0x112cfd 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[72, 70]
    (.letOp (n := 75) (.exec 0x112cfd (fun s => s.RIP = 0x112cfd) (andR64R64Effect 0x112cfd 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[72, 70]
    (.letOp (n := 76) (.out 0x112d00 (orR64R64Effect 0x112d00 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[70, 3]
    (.letOp (n := 77) (.exec 0x112d00 (fun s => s.RIP = 0x112d00) (orR64R64Effect 0x112d00 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[70, 3]
    (.letOp (n := 78) (.out 0x112d03 (andR64R64Effect 0x112d03 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[76, 68]
    (.letOp (n := 79) (.exec 0x112d03 (fun s => s.RIP = 0x112d03) (andR64R64Effect 0x112d03 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[76, 68]
    (.letOp (n := 80) (.out 0x112d06 (orR64R64Effect 0x112d06 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[78, 74]
    (.letOp (n := 81) (.exec 0x112d06 (fun s => s.RIP = 0x112d06) (orR64R64Effect 0x112d06 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[78, 74]
    (.letOp (n := 82) (.out 0x112d09 (shrR64Effect 0x112d09 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[80]
    (.letOp (n := 83) (.exec 0x112d09 (fun s => s.RIP = 0x112d09) (shrR64Effect 0x112d09 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (.terminate (.br ⟨.l1187ed, RegMap.args [(0, 0), (1, 68), (2, 2), (3, 3), (4, 4), (6, 6), (7, 7), (8, 74), (9, 9), (10, 82), (15, 15), (22, 22), (39, 39), (51, 51)] 84⟩))))))))))))))))))))))))))))))))

def bytes_l1187b8 : List UInt8 :=
  [0x4C, 0x89, 0x04, 0x24, 0x48, 0x89, 0xE1, 0x31, 0xC9, 0x48, 0x2B, 0x0C, 0x24, 0x4C, 0x8B, 0x54,
    0x24, 0x30, 0x4D, 0x89, 0xD0, 0x49, 0x29, 0xD8, 0x48, 0xC1, 0xF9, 0x3F, 0x4C, 0x01, 0xC1, 0x49,
    0xF7, 0xD2, 0x49, 0x89, 0xD8, 0x4D, 0x21, 0xD0, 0x49, 0x09, 0xDA, 0x49, 0x21, 0xCA, 0x4D, 0x09,
    0xC2, 0x49, 0xC1, 0xEA, 0x3F]

theorem code_l1187b8 : ∀ x ∈ codeRange 0x112cd8 bytes_l1187b8, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12cd8 53 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1187ed : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112d0d (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d0d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d0d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d0d 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[10, 4]
    (.letOp (n := 54) (.exec 0x112d11 (fun s => s.RIP = 0x112d11) (movR64R64Effect 0x112d11 8 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112d14 (movR64Imm64Effect 0x112d14 8 0xc46353d039cdaaf) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 56) (.exec 0x112d14 (fun s => s.RIP = 0x112d14) (movR64Imm64Effect 0x112d14 8 0xc46353d039cdaaf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x112d1e (addR64R64Effect 0x112d1e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[55, 0]
    (.letOp (n := 58) (.exec 0x112d1e (fun s => s.RIP = 0x112d1e) (addR64R64Effect 0x112d1e 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[55, 0]
    (.letOp (n := 59) (.out 0x112d21 (notR64Effect 0x112d21 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 60) (.exec 0x112d21 (fun s => s.RIP = 0x112d21) (notR64Effect 0x112d21 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 61) (.out 0x112d24 (orR64R64Effect 0x112d24 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[59, 57]
    (.letOp (n := 62) (.exec 0x112d24 (fun s => s.RIP = 0x112d24) (orR64R64Effect 0x112d24 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[59, 57]
    (.letOp (n := 63) (.out 0x112d27 (shrR64Effect 0x112d27 4 0 63) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[61]
    (.letOp (n := 64) (.exec 0x112d27 (fun s => s.RIP = 0x112d27) (shrR64Effect 0x112d27 4 0 63) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.terminate (.br ⟨.l11880b, RegMap.args [(0, 63), (1, 1), (2, 2), (4, 4), (6, 6), (7, 7), (8, 57), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)] 65⟩)))))))))))))

def bytes_l1187ed : List UInt8 :=
  [0x4C, 0x89, 0x14, 0x24, 0x49, 0x89, 0xE0, 0x49, 0xB8, 0xAF, 0xDA, 0x9C, 0x03, 0x3D, 0x35, 0x46,
    0x0C, 0x49, 0x01, 0xC0, 0x48, 0xF7, 0xD0, 0x4C, 0x09, 0xC0, 0x48, 0xC1, 0xE8, 0x3F]

theorem code_l1187ed : ∀ x ∈ codeRange 0x112d0d bytes_l1187ed, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d0d 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11880b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112d2b (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d2b 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x112d2f (fun s => s.RIP = 0x112d2f) (movR64R64Effect 0x112d2f 0 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112d32 (xorR32R32Effect 0x112d32 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 56) (.exec 0x112d32 (fun s => s.RIP = 0x112d32) (xorR32R32Effect 0x112d32 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 57) (.out 0x112d35 (subR64M64Effect 0x112d35 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112d35 (LoadPre 0x112d35 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d35 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112d35 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112d39 (sarR64Effect 0x112d39 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x112d39 (fun s => s.RIP = 0x112d39) (sarR64Effect 0x112d39 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x112d3d (movR64Imm64Effect 0x112d3d 0 0x4319055258e8617c) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 62) (.exec 0x112d3d (fun s => s.RIP = 0x112d3d) (movR64Imm64Effect 0x112d3d 0 0x4319055258e8617c) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x112d47 (addR64R64Effect 0x112d47 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x112d47 (fun s => s.RIP = 0x112d47) (addR64R64Effect 0x112d47 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x112d4a (addR64R64Effect 0x112d4a 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[63, 2]
    (.letOp (n := 66) (.exec 0x112d4a (fun s => s.RIP = 0x112d4a) (addR64R64Effect 0x112d4a 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[63, 2]
    (.letOp (n := 67) (.out 0x112d4d (notR64Effect 0x112d4d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 68) (.exec 0x112d4d (fun s => s.RIP = 0x112d4d) (notR64Effect 0x112d4d 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x112d50 (orR64R64Effect 0x112d50 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[67, 65]
    (.letOp (n := 70) (.exec 0x112d50 (fun s => s.RIP = 0x112d50) (orR64R64Effect 0x112d50 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[67, 65]
    (.letOp (n := 71) (.out 0x112d53 (shrR64Effect 0x112d53 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[69]
    (.letOp (n := 72) (.exec 0x112d53 (fun s => s.RIP = 0x112d53) (shrR64Effect 0x112d53 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.terminate (.br ⟨.l118837, RegMap.args [(0, 65), (1, 1), (2, 71), (4, 4), (6, 6), (7, 7), (8, 8), (9, 9), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l11880b : List UInt8 :=
  [0x48, 0x89, 0x04, 0x24, 0x48, 0x89, 0xE0, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x14, 0x24, 0x49, 0xC1,
    0xFA, 0x3F, 0x48, 0xB8, 0x7C, 0x61, 0xE8, 0x58, 0x52, 0x05, 0x19, 0x43, 0x4C, 0x01, 0xD0, 0x48,
    0x01, 0xD0, 0x48, 0xF7, 0xD2, 0x48, 0x09, 0xC2, 0x48, 0xC1, 0xEA, 0x3F]

theorem code_l11880b : ∀ x ∈ codeRange 0x112d2b bytes_l11880b, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d2b 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118837 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112d57 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d57 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d57 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[2, 4]
    (.letOp (n := 54) (.exec 0x112d5b (fun s => s.RIP = 0x112d5b) (movR64R64Effect 0x112d5b 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112d5e (movR64M64Effect 0x112d5e 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 56) (.exec 0x112d5e (LoadPre 0x112d5e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d5e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112d5e 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x112d62 (decR64Effect 0x112d62 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[55]
    (.letOp (n := 58) (.exec 0x112d62 (fun s => s.RIP = 0x112d62) (decR64Effect 0x112d62 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 59) (.out 0x112d65 (shrR64Effect 0x112d65 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 60) (.exec 0x112d65 (fun s => s.RIP = 0x112d65) (shrR64Effect 0x112d65 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x112d69 (addR64R64Effect 0x112d69 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[59, 6]
    (.letOp (n := 62) (.exec 0x112d69 (fun s => s.RIP = 0x112d69) (addR64R64Effect 0x112d69 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[59, 6]
    (.letOp (n := 63) (.out 0x112d6c (notR64Effect 0x112d6c 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 64) (.exec 0x112d6c (fun s => s.RIP = 0x112d6c) (notR64Effect 0x112d6c 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x112d6f (orR64R64Effect 0x112d6f 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[63, 61]
    (.letOp (n := 66) (.exec 0x112d6f (fun s => s.RIP = 0x112d6f) (orR64R64Effect 0x112d6f 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[63, 61]
    (.letOp (n := 67) (.out 0x112d72 (shrR64Effect 0x112d72 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 68) (.exec 0x112d72 (fun s => s.RIP = 0x112d72) (shrR64Effect 0x112d72 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.terminate (.br ⟨.l118856, RegMap.args [(0, 0), (1, 1), (2, 61), (4, 4), (6, 67), (7, 7), (8, 8), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l118837 : List UInt8 :=
  [0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0xE2, 0x48, 0x8B, 0x14, 0x24, 0x48, 0xFF, 0xCA, 0x48, 0xC1,
    0xEA, 0x3F, 0x48, 0x01, 0xF2, 0x48, 0xF7, 0xD6, 0x48, 0x09, 0xD6, 0x48, 0xC1, 0xEE, 0x3F]

theorem code_l118837 : ∀ x ∈ codeRange 0x112d57 bytes_l118837, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d57 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118856 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112d76 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112d76 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d76 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112d76 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[6, 4]
    (.letOp (n := 54) (.exec 0x112d7a (fun s => s.RIP = 0x112d7a) (movR64R64Effect 0x112d7a 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112d7d (xorR32R32Effect 0x112d7d 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 56) (.exec 0x112d7d (fun s => s.RIP = 0x112d7d) (xorR32R32Effect 0x112d7d 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 57) (.out 0x112d80 (subR64M64Effect 0x112d80 10 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x112d80 (LoadPre 0x112d80 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112d80 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112d80 10 (.sib 4 none 0 .none)) (Reg.operands [.gpr 10, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x112d84 (sarR64Effect 0x112d84 4 10 63) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 60) (.exec 0x112d84 (fun s => s.RIP = 0x112d84) (sarR64Effect 0x112d84 4 10 63) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x112d88 (movR64Imm64Effect 0x112d88 6 0x100000000) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 62) (.exec 0x112d88 (fun s => s.RIP = 0x112d88) (movR64Imm64Effect 0x112d88 6 0x100000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 63) (.out 0x112d92 (addR64R64Effect 0x112d92 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[61, 59]
    (.letOp (n := 64) (.exec 0x112d92 (fun s => s.RIP = 0x112d92) (addR64R64Effect 0x112d92 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[61, 59]
    (.letOp (n := 65) (.out 0x112d95 (addR64R64Effect 0x112d95 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[63, 9]
    (.letOp (n := 66) (.exec 0x112d95 (fun s => s.RIP = 0x112d95) (addR64R64Effect 0x112d95 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[63, 9]
    (.letOp (n := 67) (.out 0x112d98 (notR64Effect 0x112d98 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 68) (.exec 0x112d98 (fun s => s.RIP = 0x112d98) (notR64Effect 0x112d98 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 69) (.out 0x112d9b (orR64R64Effect 0x112d9b 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[67, 65]
    (.letOp (n := 70) (.exec 0x112d9b (fun s => s.RIP = 0x112d9b) (orR64R64Effect 0x112d9b 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[67, 65]
    (.letOp (n := 71) (.out 0x112d9e (shrR64Effect 0x112d9e 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 72) (.exec 0x112d9e (fun s => s.RIP = 0x112d9e) (shrR64Effect 0x112d9e 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.terminate (.br ⟨.l118882, RegMap.args [(0, 0), (1, 1), (2, 2), (4, 4), (6, 65), (7, 7), (8, 8), (9, 71), (10, 59), (15, 15), (22, 22), (39, 39), (51, 51)] 73⟩)))))))))))))))))))))

def bytes_l118856 : List UInt8 :=
  [0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xE6, 0x45, 0x31, 0xD2, 0x4C, 0x2B, 0x14, 0x24, 0x49, 0xC1,
    0xFA, 0x3F, 0x48, 0xBE, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xD6, 0x4C,
    0x01, 0xCE, 0x49, 0xF7, 0xD1, 0x49, 0x09, 0xF1, 0x49, 0xC1, 0xE9, 0x3F]

theorem code_l118856 : ∀ x ∈ codeRange 0x112d76 bytes_l118856, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12d76 44 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l118882 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112da2 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112da2 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112da2 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112da2 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[9, 4]
    (.letOp (n := 54) (.out 0x112da6 (movR64R64Effect 0x112da6 9 4) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 55) (.exec 0x112da6 (fun s => s.RIP = 0x112da6) (movR64R64Effect 0x112da6 9 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x112da9 (xorR32R32Effect 0x112da9 3 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[54, 54]
    (.letOp (n := 57) (.exec 0x112da9 (fun s => s.RIP = 0x112da9) (xorR32R32Effect 0x112da9 3 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[54, 54]
    (.letOp (n := 58) (.out 0x112dac (subR64M64Effect 0x112dac 9 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 4] []) (.reg (.gpr 9))) #v[56, 4]
    (.letOp (n := 59) (.exec 0x112dac (LoadPre 0x112dac (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dac + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x112dac 9 (.sib 4 none 0 .none)) (Reg.operands [.gpr 9, .gpr 4] [])) #v[56, 4]
    (.letOp (n := 60) (.out 0x112db0 (sarR64Effect 0x112db0 4 9 63) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[58]
    (.letOp (n := 61) (.exec 0x112db0 (fun s => s.RIP = 0x112db0) (sarR64Effect 0x112db0 4 9 63) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[58]
    (.letOp (n := 62) (.out 0x112db4 (addR64R64Effect 0x112db4 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[60, 1]
    (.letOp (n := 63) (.exec 0x112db4 (fun s => s.RIP = 0x112db4) (addR64R64Effect 0x112db4 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[60, 1]
    (.letOp (n := 64) (.out 0x112db7 (notR64Effect 0x112db7 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 65) (.exec 0x112db7 (fun s => s.RIP = 0x112db7) (notR64Effect 0x112db7 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 66) (.out 0x112dba (andR64R64Effect 0x112dba 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[64, 62]
    (.letOp (n := 67) (.exec 0x112dba (fun s => s.RIP = 0x112dba) (andR64R64Effect 0x112dba 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[64, 62]
    (.letOp (n := 68) (.out 0x112dbd (shrR64Effect 0x112dbd 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 69) (.exec 0x112dbd (fun s => s.RIP = 0x112dbd) (shrR64Effect 0x112dbd 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.terminate (.br ⟨.l1188a1, RegMap.args [(0, 0), (1, 68), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 62), (15, 15), (22, 22), (39, 39), (51, 51)] 70⟩))))))))))))))))))

def bytes_l118882 : List UInt8 :=
  [0x4C, 0x89, 0x0C, 0x24, 0x49, 0x89, 0xE1, 0x45, 0x31, 0xC9, 0x4C, 0x2B, 0x0C, 0x24, 0x49, 0xC1,
    0xF9, 0x3F, 0x49, 0x01, 0xC9, 0x48, 0xF7, 0xD1, 0x4C, 0x21, 0xC9, 0x48, 0xC1, 0xE9, 0x3F]

theorem code_l118882 : ∀ x ∈ codeRange 0x112da2 bytes_l118882, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12da2 31 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1188a1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112dc1 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112dc1 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dc1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112dc1 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1, 4]
    (.letOp (n := 54) (.exec 0x112dc5 (fun s => s.RIP = 0x112dc5) (movR64R64Effect 0x112dc5 1 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x112dc8 (movR64M64Effect 0x112dc8 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x112dc8 (LoadPre 0x112dc8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x112dc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x112dc8 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x112dcc (movR64R64Effect 0x112dcc 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 58) (.exec 0x112dcc (fun s => s.RIP = 0x112dcc) (movR64R64Effect 0x112dcc 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 59) (.out 0x112dcf (subR64R64Effect 0x112dcf 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[57, 55]
    (.letOp (n := 60) (.exec 0x112dcf (fun s => s.RIP = 0x112dcf) (subR64R64Effect 0x112dcf 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[57, 55]
    (.letOp (n := 61) (.out 0x112dd2 (negR64Effect 0x112dd2 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 62) (.exec 0x112dd2 (fun s => s.RIP = 0x112dd2) (negR64Effect 0x112dd2 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 63) (.out 0x112dd5 (andR64R64Effect 0x112dd5 15 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 1] []) (.reg (.gpr 15))) #v[15, 61]
    (.letOp (n := 64) (.exec 0x112dd5 (fun s => s.RIP = 0x112dd5) (andR64R64Effect 0x112dd5 15 1) (Reg.operands [.gpr 15, .gpr 1] [])) #v[15, 61]
    (.letOp (n := 65) (.out 0x112dd8 (movR64Imm64Effect 0x112dd8 11 0xbce6faada7179e84) (EffectPart.reads (.reg (.gpr 11)) [] []) (.reg (.gpr 11))) #v[]
    (.letOp (n := 66) (.exec 0x112dd8 (fun s => s.RIP = 0x112dd8) (movR64Imm64Effect 0x112dd8 11 0xbce6faada7179e84) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x112de2 (andR64R64Effect 0x112de2 11 1) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1] []) (.reg (.gpr 11))) #v[65, 61]
    (.letOp (n := 68) (.exec 0x112de2 (fun s => s.RIP = 0x112de2) (andR64R64Effect 0x112de2 11 1) (Reg.operands [.gpr 11, .gpr 1] [])) #v[65, 61]
    (.terminate (.br ⟨.l1188c5, RegMap.args [(0, 0), (1, 61), (2, 2), (4, 4), (6, 6), (7, 7), (8, 8), (9, 59), (11, 67), (15, 63), (22, 22), (39, 39), (51, 51)] 69⟩)))))))))))))))))

def bytes_l1188a1 : List UInt8 :=
  [0x48, 0x89, 0x0C, 0x24, 0x48, 0x89, 0xE1, 0x48, 0x8B, 0x0C, 0x24, 0x49, 0x89, 0xD1, 0x49, 0x29,
    0xC9, 0x48, 0xF7, 0xD9, 0x49, 0x21, 0xCF, 0x49, 0xBB, 0x84, 0x9E, 0x17, 0xA7, 0xAD, 0xFA, 0xE6,
    0xBC, 0x49, 0x21, 0xCB]

theorem code_l1188a1 : ∀ x ∈ codeRange 0x112dc1 bytes_l1188a1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12dc1 36 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1188c5 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x112de5 (addR64R64Effect 0x112de5 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[15, 8]
    (.letOp (n := 54) (.out 0x112de5 (addR64R64Effect 0x112de5 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[15, 8]
    (.letOp (n := 55) (.exec 0x112de5 (fun s => s.RIP = 0x112de5) (addR64R64Effect 0x112de5 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[15, 8]
    (.letOp (n := 56) (.out 0x112de8 (atFlags StatusFlags.CF (adcR64R64Effect 0x112de8 11 0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[11, 0, 54]
    (.letOp (n := 57) (.out 0x112de8 (atFlags StatusFlags.CF (adcR64R64Effect 0x112de8 11 0)) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[11, 0, 54]
    (.letOp (n := 58) (.exec 0x112de8 (fun s => s.RIP = 0x112de8) (atFlags StatusFlags.CF (adcR64R64Effect 0x112de8 11 0)) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[11, 0, 54]
    (.letOp (n := 59) (.out 0x112deb (atFlags (condHolds 2) (setccR8Effect 0x112deb 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 57]
    (.letOp (n := 60) (.exec 0x112deb (fun s => s.RIP = 0x112deb) (atFlags (condHolds 2) (setccR8Effect 0x112deb 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 57]
    (.letOp (n := 61) (.out 0x112dee (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112dee 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[9, 57]
    (.letOp (n := 62) (.exec 0x112dee (fun s => s.RIP = 0x112dee) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x112dee 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[9, 57]
    (.letOp (n := 63) (.out 0x112df2 (movR64Imm64Effect 0x112df2 8 0xffffffff00000000) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 64) (.exec 0x112df2 (fun s => s.RIP = 0x112df2) (movR64Imm64Effect 0x112df2 8 0xffffffff00000000) (Reg.operands [] [])) #v[]
    (.letOp (n := 65) (.out 0x112dfc (andR64R64Effect 0x112dfc 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[63, 1]
    (.letOp (n := 66) (.exec 0x112dfc (fun s => s.RIP = 0x112dfc) (andR64R64Effect 0x112dfc 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[63, 1]
    (.letOp (n := 67) (.out 0x112dff (addAlImm8Effect 0x112dff 0xff) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[59]
    (.letOp (n := 68) (.out 0x112dff (addAlImm8Effect 0x112dff 0xff) (EffectPart.reads (.flag .CF) [.gpr 0] []) (.flag .CF)) #v[59]
    (.letOp (n := 69) (.exec 0x112dff (fun s => s.RIP = 0x112dff) (addAlImm8Effect 0x112dff 0xff) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 70) (.out 0x112e01 (atFlags StatusFlags.CF (adcR64R64Effect 0x112e01 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[1, 2, 68]
    (.letOp (n := 71) (.exec 0x112e01 (fun s => s.RIP = 0x112e01) (atFlags StatusFlags.CF (adcR64R64Effect 0x112e01 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1, 2, 68]
    (.letOp (n := 72) (.out 0x112e04 (atFlags StatusFlags.CF (adcR64R64Effect 0x112e04 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[65, 6, 70]
    (.letOp (n := 73) (.exec 0x112e04 (fun s => s.RIP = 0x112e04) (atFlags StatusFlags.CF (adcR64R64Effect 0x112e04 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[65, 6, 70]
    (.terminate (.br ⟨.l1188e7, RegMap.args [(0, 67), (2, 2), (4, 4), (6, 6), (7, 7), (8, 72), (9, 61), (11, 56), (15, 53), (22, 22), (39, 39), (51, 51)] 74⟩))))))))))))))))))))))

def bytes_l1188c5 : List UInt8 :=
  [0x4D, 0x01, 0xC7, 0x49, 0x11, 0xC3, 0x0F, 0x92, 0xC0, 0x49, 0x83, 0xD1, 0x00, 0x49, 0xB8, 0x00,
    0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0x49, 0x21, 0xC8, 0x04, 0xFF, 0x48, 0x11, 0xD1, 0x49,
    0x11, 0xF0]

theorem code_l1188c5 : ∀ x ∈ codeRange 0x112de5 bytes_l1188c5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12de5 34 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1188e7 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x112e07 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e07 3 (fun s => AddrMode.addr (.base 7 .none) s (0x112e07 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x112e07 15 (.base 7 .none)) (Reg.operands [.gpr 15, .gpr 7] [])) #v[15, 7]
    (.letOp (n := 54) (.exec 0x112e0a (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e0a 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x112e0a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e0a 11 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[11, 7]
    (.letOp (n := 55) (.exec 0x112e0e (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e0e 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x112e0e + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e0e 9 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[9, 7]
    (.letOp (n := 56) (.exec 0x112e12 (P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StorePre 0x112e12 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x112e12 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x112e12 8 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 8, .gpr 7] [])) #v[8, 7]
    (.letOp (n := 57) (.out 0x112e16 (addR64Imm8Effect 0x112e16 4 0x40) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x112e16 (fun s => s.RIP = 0x112e16) (addR64Imm8Effect 0x112e16 4 0x40) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x112e1a (popR64Effect 0x112e1a 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[57]
    (.letOp (n := 60) (.out 0x112e1a (popR64Effect 0x112e1a 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x112e1a (PopPre 0x112e1a) (popR64Effect 0x112e1a 1 3) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x112e1b (popR64Effect 0x112e1b 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[60]
    (.letOp (n := 63) (.out 0x112e1b (popR64Effect 0x112e1b 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x112e1b (PopPre 0x112e1b) (popR64Effect 0x112e1b 2 12) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x112e1d (popR64Effect 0x112e1d 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[63]
    (.letOp (n := 66) (.out 0x112e1d (popR64Effect 0x112e1d 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x112e1d (PopPre 0x112e1d) (popR64Effect 0x112e1d 2 13) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x112e1f (popR64Effect 0x112e1f 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[66]
    (.letOp (n := 69) (.out 0x112e1f (popR64Effect 0x112e1f 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x112e1f (PopPre 0x112e1f) (popR64Effect 0x112e1f 2 14) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x112e21 (popR64Effect 0x112e21 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 72) (.out 0x112e21 (popR64Effect 0x112e21 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x112e21 (PopPre 0x112e21) (popR64Effect 0x112e21 2 15) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x112e23 (popR64Effect 0x112e23 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[72]
    (.letOp (n := 75) (.out 0x112e23 (popR64Effect 0x112e23 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x112e23 (PopPre 0x112e23) (popR64Effect 0x112e23 1 5) (Reg.operands [.gpr 4] [])) #v[72]
    (.letOp (n := 77) (.out 0x112e24 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[75]
    (.letOp (n := 78) (.out 0x112e24 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[75]
    (.letOp (n := 79) (.exec 0x112e24 (RetPre 0x112e24) (retEffect) (Reg.operands [.gpr 4] [])) #v[75]
    (.terminate (.ret (RegMap.args [(0, 0), (2, 2), (3, 59), (4, 78), (5, 74), (7, 7), (8, 8), (9, 9), (11, 11), (12, 62), (13, 65), (14, 68), (15, 71), (22, 22), (39, 39), (51, 51)] 80) (some ⟨77, by decide⟩)))))))))))))))))))))))))))))

def bytes_l1188e7 : List UInt8 :=
  [0x4C, 0x89, 0x3F, 0x4C, 0x89, 0x5F, 0x08, 0x4C, 0x89, 0x4F, 0x10, 0x4C, 0x89, 0x47, 0x18, 0x48,
    0x83, 0xC4, 0x40, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1188e7 : ∀ x ∈ codeRange 0x112e07 bytes_l1188e7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x12e07 30 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

end P256.Proofs.Scalar.Multiply.Barrett.Machine
