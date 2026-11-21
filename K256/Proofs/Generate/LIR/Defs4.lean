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

def b_l10e4c0_24 : Block Op Label signature Reg.count 1081 :=
  .letOp (n := 1081) (.out 0x10ec62 (andR64R64Effect 0x10ec62 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[1061, 1074]
    (.letOp (n := 1082) (.exec 0x10ec62 (fun s => s.RIP = 0x10ec62) (andR64R64Effect 0x10ec62 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[1061, 1074]
    (.letOp (n := 1083) (.out 0x10ec65 (movR64Imm64Effect 0x10ec65 0 0xffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 1084) (.exec 0x10ec65 (fun s => s.RIP = 0x10ec65) (movR64Imm64Effect 0x10ec65 0 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 1085) (.out 0x10ec6f (andR64R64Effect 0x10ec6f 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[760, 1083]
    (.letOp (n := 1086) (.exec 0x10ec6f (fun s => s.RIP = 0x10ec6f) (andR64R64Effect 0x10ec6f 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[760, 1083]
    (.letOp (n := 1087) (.out 0x10ec72 (addR64R64Effect 0x10ec72 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[1085, 1079]
    (.letOp (n := 1088) (.exec 0x10ec72 (fun s => s.RIP = 0x10ec72) (addR64R64Effect 0x10ec72 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[1085, 1079]
    (.letOp (n := 1089) (.exec 0x10ec75 (StorePre 0x10ec75 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc0)) s (0x10ec75 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec75 11 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[894, 65]
    (.letOp (n := 1090) (.exec 0x10ec7d (StorePre 0x10ec7d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xc8)) s (0x10ec7d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec7d 7 (.sib 4 none 0 (.d32 0xc8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[986, 65]
    (.letOp (n := 1091) (.exec 0x10ec85 (StorePre 0x10ec85 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd0)) s (0x10ec85 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec85 15 (.sib 4 none 0 (.d32 0xd0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[1063, 65]
    (.letOp (n := 1092) (.exec 0x10ec8d (StorePre 0x10ec8d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xd8)) s (0x10ec8d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec8d 1 (.sib 4 none 0 (.d32 0xd8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[1081, 65]
    (.letOp (n := 1093) (.exec 0x10ec95 (StorePre 0x10ec95 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xe0)) s (0x10ec95 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec95 5 (.sib 4 none 0 (.d32 0xe0))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[1087, 65]
    (.letOp (n := 1094) (.out 0x10ec9d (leaR64Effect 0x10ec9d 6 (.sib 4 none 0 (.d32 0x98))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 1095) (.exec 0x10ec9d (fun s => s.RIP = 0x10ec9d) (leaR64Effect 0x10ec9d 6 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1096) (.out 0x10eca5 (movR64M64Effect 0x10eca5 3 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 1097) (.exec 0x10eca5 (LoadPre 0x10eca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eca5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eca5 3 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1098) (.out 0x10ecaa (movR64R64Effect 0x10ecaa 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[1096]
    (.letOp (n := 1099) (.exec 0x10ecaa (fun s => s.RIP = 0x10ecaa) (movR64R64Effect 0x10ecaa 7 3) (Reg.operands [.gpr 3] [])) #v[1096]
    (.letOp (n := 1100) (.out 0x10ecad (callEffect (fun _ => 0x114930) 0x10ecb2) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 1101) (.exec 0x10ecad (PushPre 0x10ecad 5) (callEffect (fun _ => 0x114930) 0x10ecb2) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1102) (.const ⟨64, 0x10ecb2⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(0, 1083), (1, 1081), (2, 1079), (3, 1096), (4, 1100), (5, 1087), (6, 1094), (7, 1098), (8, 1018), (9, 1049), (10, 1009), (11, 894), (12, 1051), (13, 980), (14, 957), (15, 1063), (22, 22), (39, 39), (50, 50), (51, 51)] 1103⟩ { target := .l10ecb2, kept := #v[], arity := rfl, guard := some (Fin.last 1102) })))))))))))))))))))))))

def bytes_l10e4c0_24 : List UInt8 :=
  [0x48, 0x21, 0xF1, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x21, 0xC5,
    0x48, 0x01, 0xD5, 0x4C, 0x89, 0x9C, 0x24, 0xC0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xBC, 0x24, 0xC8,
    0x00, 0x00, 0x00, 0x4C, 0x89, 0xBC, 0x24, 0xD0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24, 0xD8,
    0x00, 0x00, 0x00, 0x48, 0x89, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00, 0x48, 0x8D, 0xB4, 0x24, 0x98,
    0x00, 0x00, 0x00, 0x48, 0x8B, 0x5C, 0x24, 0x60, 0x48, 0x89, 0xDF, 0xE8, 0x7E, 0x5C, 0x00, 0x00]

theorem code_l10e4c0_24 : ∀ x ∈ codeRange 0x10ec62 bytes_l10e4c0_24, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xec62 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

def b_l10e4c0_23 : Block Op Label signature Reg.count 1039 :=
  .letOp (n := 1039) (.out 0x10ec0a (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec0a 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1034, 1021, 1037]
    (.letOp (n := 1040) (.exec 0x10ec0a (fun s => s.RIP = 0x10ec0a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec0a 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1034, 1021, 1037]
    (.letOp (n := 1041) (.out 0x10ec0d (movR64M64Effect 0x10ec0d 0 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1042) (.exec 0x10ec0d (LoadPre 0x10ec0d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ec0d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ec0d 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1043) (.exec 0x10ec12 (StorePre 0x10ec12 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10ec12 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec12 0 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1041, 65]
    (.letOp (n := 1044) (.out 0x10ec1a (addR64R64Effect 0x10ec1a 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[1036, 957]
    (.letOp (n := 1045) (.out 0x10ec1a (addR64R64Effect 0x10ec1a 15 14) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 14] []) (.flag .CF)) #v[1036, 957]
    (.letOp (n := 1046) (.exec 0x10ec1a (fun s => s.RIP = 0x10ec1a) (addR64R64Effect 0x10ec1a 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[1036, 957]
    (.letOp (n := 1047) (.out 0x10ec1d (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec1d 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1039, 1045]
    (.letOp (n := 1048) (.exec 0x10ec1d (fun s => s.RIP = 0x10ec1d) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec1d 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1039, 1045]
    (.letOp (n := 1049) (.out 0x10ec21 (shldR64R64Effect 0x10ec21 5 9 10 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[1012, 1009]
    (.letOp (n := 1050) (.exec 0x10ec21 (fun s => s.RIP = 0x10ec21) (shldR64R64Effect 0x10ec21 5 9 10 12) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1012, 1009]
    (.letOp (n := 1051) (.out 0x10ec26 (shldR64R64Effect 0x10ec26 5 12 15 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[1047, 1044]
    (.letOp (n := 1052) (.exec 0x10ec26 (fun s => s.RIP = 0x10ec26) (shldR64R64Effect 0x10ec26 5 12 15 12) (Reg.operands [.gpr 12, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1047, 1044]
    (.letOp (n := 1053) (.out 0x10ec2b (movR64M64Effect 0x10ec2b 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 1054) (.exec 0x10ec2b (LoadPre 0x10ec2b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10ec2b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ec2b 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1055) (.exec 0x10ec30 (StorePre 0x10ec30 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb8)) s (0x10ec30 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ec30 0 (.sib 4 none 0 (.d32 0xb8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[1053, 65]
    (.letOp (n := 1056) (.out 0x10ec38 (movR64R64Effect 0x10ec38 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[1049]
    (.letOp (n := 1057) (.exec 0x10ec38 (fun s => s.RIP = 0x10ec38) (movR64R64Effect 0x10ec38 0 9) (Reg.operands [.gpr 9] [])) #v[1049]
    (.letOp (n := 1058) (.out 0x10ec3b (mulR64Effect 0x10ec3b 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1018, 1056]
    (.letOp (n := 1059) (.out 0x10ec3b (mulR64Effect 0x10ec3b 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1018, 1056]
    (.letOp (n := 1060) (.exec 0x10ec3b (fun s => s.RIP = 0x10ec3b) (mulR64Effect 0x10ec3b 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1018, 1056]
    (.letOp (n := 1061) (.out 0x10ec3e (movR64R64Effect 0x10ec3e 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[984]
    (.letOp (n := 1062) (.exec 0x10ec3e (fun s => s.RIP = 0x10ec3e) (movR64R64Effect 0x10ec3e 1 6) (Reg.operands [.gpr 6] [])) #v[984]
    (.letOp (n := 1063) (.out 0x10ec41 (andR64R64Effect 0x10ec41 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[1044, 984]
    (.letOp (n := 1064) (.exec 0x10ec41 (fun s => s.RIP = 0x10ec41) (andR64R64Effect 0x10ec41 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[1044, 984]
    (.letOp (n := 1065) (.out 0x10ec44 (movR64M64Effect 0x10ec44 6 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 1066) (.exec 0x10ec44 (LoadPre 0x10ec44 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10ec44 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10ec44 6 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1067) (.out 0x10ec4c (andR64R64Effect 0x10ec4c 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[1065, 1061]
    (.letOp (n := 1068) (.exec 0x10ec4c (fun s => s.RIP = 0x10ec4c) (andR64R64Effect 0x10ec4c 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[1065, 1061]
    (.letOp (n := 1069) (.out 0x10ec4f (addR64R64Effect 0x10ec4f 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[1067, 1058]
    (.letOp (n := 1070) (.out 0x10ec4f (addR64R64Effect 0x10ec4f 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[1067, 1058]
    (.letOp (n := 1071) (.exec 0x10ec4f (fun s => s.RIP = 0x10ec4f) (addR64R64Effect 0x10ec4f 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[1067, 1058]
    (.letOp (n := 1072) (.out 0x10ec52 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec52 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1059, 1070]
    (.letOp (n := 1073) (.exec 0x10ec52 (fun s => s.RIP = 0x10ec52) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec52 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1059, 1070]
    (.letOp (n := 1074) (.out 0x10ec56 (addR64R64Effect 0x10ec56 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12] []) (.reg (.gpr 6))) #v[1069, 1051]
    (.letOp (n := 1075) (.out 0x10ec56 (addR64R64Effect 0x10ec56 6 12) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 12] []) (.flag .CF)) #v[1069, 1051]
    (.letOp (n := 1076) (.exec 0x10ec56 (fun s => s.RIP = 0x10ec56) (addR64R64Effect 0x10ec56 6 12) (Reg.operands [.gpr 6, .gpr 12] [])) #v[1069, 1051]
    (.letOp (n := 1077) (.out 0x10ec59 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec59 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[1072, 1075]
    (.letOp (n := 1078) (.exec 0x10ec59 (fun s => s.RIP = 0x10ec59) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ec59 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1072, 1075]
    (.letOp (n := 1079) (.out 0x10ec5d (shldR64R64Effect 0x10ec5d 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[1077, 1074]
    (.letOp (n := 1080) (.exec 0x10ec5d (fun s => s.RIP = 0x10ec5d) (shldR64R64Effect 0x10ec5d 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[1077, 1074]
    (b_l10e4c0_24))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_23 : List UInt8 :=
  [0x49, 0x11, 0xD4, 0x48, 0x8B, 0x44, 0x24, 0x78, 0x48, 0x89, 0x84, 0x24, 0xB0, 0x00, 0x00, 0x00,
    0x4D, 0x01, 0xF7, 0x49, 0x83, 0xD4, 0x00, 0x4D, 0x0F, 0xA4, 0xD1, 0x0C, 0x4D, 0x0F, 0xA4, 0xFC,
    0x0C, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24, 0xB8, 0x00, 0x00, 0x00, 0x4C, 0x89,
    0xC8, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0xF1, 0x49, 0x21, 0xF7, 0x48, 0x8B, 0xB4, 0x24, 0x90, 0x00,
    0x00, 0x00, 0x48, 0x21, 0xCE, 0x48, 0x01, 0xC6, 0x48, 0x83, 0xD2, 0x00, 0x4C, 0x01, 0xE6, 0x48,
    0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xF2, 0x0C] ++ bytes_l10e4c0_24

theorem code_l10e4c0_23 : ∀ x ∈ codeRange 0x10ec0a bytes_l10e4c0_23, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xec0a 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_24

def b_l10e4c0_22 : Block Op Label signature Reg.count 993 :=
  .letOp (n := 993) (.out 0x10ebb7 (movR64R64Effect 0x10ebb7 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[991]
    (.letOp (n := 994) (.exec 0x10ebb7 (fun s => s.RIP = 0x10ebb7) (movR64R64Effect 0x10ebb7 9 2) (Reg.operands [.gpr 2] [])) #v[991]
    (.letOp (n := 995) (.out 0x10ebba (movR64R64Effect 0x10ebba 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[990]
    (.letOp (n := 996) (.exec 0x10ebba (fun s => s.RIP = 0x10ebba) (movR64R64Effect 0x10ebba 3 0) (Reg.operands [.gpr 0] [])) #v[990]
    (.letOp (n := 997) (.out 0x10ebbd (movR64M64Effect 0x10ebbd 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 998) (.exec 0x10ebbd (LoadPre 0x10ebbd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10ebbd + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebbd 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 999) (.out 0x10ebc2 (mulM64Effect 0x10ebc2 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[997, 65]
    (.letOp (n := 1000) (.out 0x10ebc2 (mulM64Effect 0x10ebc2 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[997, 65]
    (.letOp (n := 1001) (.exec 0x10ebc2 (LoadPre 0x10ebc2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ebc2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ebc2 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[997, 65]
    (.letOp (n := 1002) (.out 0x10ebc7 (movR64R64Effect 0x10ebc7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[999]
    (.letOp (n := 1003) (.exec 0x10ebc7 (fun s => s.RIP = 0x10ebc7) (movR64R64Effect 0x10ebc7 10 0) (Reg.operands [.gpr 0] [])) #v[999]
    (.letOp (n := 1004) (.out 0x10ebca (addR64R64Effect 0x10ebca 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[1002, 995]
    (.letOp (n := 1005) (.out 0x10ebca (addR64R64Effect 0x10ebca 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[1002, 995]
    (.letOp (n := 1006) (.exec 0x10ebca (fun s => s.RIP = 0x10ebca) (addR64R64Effect 0x10ebca 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[1002, 995]
    (.letOp (n := 1007) (.out 0x10ebcd (atFlags StatusFlags.CF (adcR64R64Effect 0x10ebcd 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[993, 1000, 1005]
    (.letOp (n := 1008) (.exec 0x10ebcd (fun s => s.RIP = 0x10ebcd) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ebcd 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[993, 1000, 1005]
    (.letOp (n := 1009) (.out 0x10ebd0 (addR64R64Effect 0x10ebd0 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[1004, 927]
    (.letOp (n := 1010) (.out 0x10ebd0 (addR64R64Effect 0x10ebd0 10 8) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 8] []) (.flag .CF)) #v[1004, 927]
    (.letOp (n := 1011) (.exec 0x10ebd0 (fun s => s.RIP = 0x10ebd0) (addR64R64Effect 0x10ebd0 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[1004, 927]
    (.letOp (n := 1012) (.out 0x10ebd3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ebd3 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[1007, 1010]
    (.letOp (n := 1013) (.exec 0x10ebd3 (fun s => s.RIP = 0x10ebd3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ebd3 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1007, 1010]
    (.letOp (n := 1014) (.out 0x10ebd7 (movR64R64Effect 0x10ebd7 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[1009]
    (.letOp (n := 1015) (.exec 0x10ebd7 (fun s => s.RIP = 0x10ebd7) (movR64R64Effect 0x10ebd7 0 10) (Reg.operands [.gpr 10] [])) #v[1009]
    (.letOp (n := 1016) (.out 0x10ebda (andR64R64Effect 0x10ebda 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[1014, 984]
    (.letOp (n := 1017) (.exec 0x10ebda (fun s => s.RIP = 0x10ebda) (andR64R64Effect 0x10ebda 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[1014, 984]
    (.letOp (n := 1018) (.out 0x10ebdd (movR64Imm64Effect 0x10ebdd 8 0x1000003d10) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 1019) (.exec 0x10ebdd (fun s => s.RIP = 0x10ebdd) (movR64Imm64Effect 0x10ebdd 8 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 1020) (.out 0x10ebe7 (mulR64Effect 0x10ebe7 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[1018, 1016]
    (.letOp (n := 1021) (.out 0x10ebe7 (mulR64Effect 0x10ebe7 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[1018, 1016]
    (.letOp (n := 1022) (.exec 0x10ebe7 (fun s => s.RIP = 0x10ebe7) (mulR64Effect 0x10ebe7 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[1018, 1016]
    (.letOp (n := 1023) (.out 0x10ebea (movR64M64Effect 0x10ebea 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 1024) (.exec 0x10ebea (LoadPre 0x10ebea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ebea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebea 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 1025) (.exec 0x10ebef (StorePre 0x10ebef 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa8)) s (0x10ebef + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10ebef 3 (.sib 4 none 0 (.d32 0xa8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[1023, 65]
    (.letOp (n := 1026) (.out 0x10ebf7 (addR64M64Effect 0x10ebf7 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[973, 65]
    (.letOp (n := 1027) (.out 0x10ebf7 (addR64M64Effect 0x10ebf7 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 4] []) (.flag .CF)) #v[973, 65]
    (.letOp (n := 1028) (.exec 0x10ebf7 (LoadPre 0x10ebf7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ebf7 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10ebf7 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[973, 65]
    (.letOp (n := 1029) (.out 0x10ebfc (atFlags StatusFlags.CF (adcR64M64Effect 0x10ebfc 12 (.sib 4 none 0 (.d8 0x30)))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 12))) #v[971, 65, 1027]
    (.letOp (n := 1030) (.exec 0x10ebfc (LoadPre 0x10ebfc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ebfc + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10ebfc 12 (.sib 4 none 0 (.d8 0x30)))) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[971, 65, 1027]
    (.letOp (n := 1031) (.out 0x10ec01 (addR64R64Effect 0x10ec01 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[1026, 980]
    (.letOp (n := 1032) (.out 0x10ec01 (addR64R64Effect 0x10ec01 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[1026, 980]
    (.letOp (n := 1033) (.exec 0x10ec01 (fun s => s.RIP = 0x10ec01) (addR64R64Effect 0x10ec01 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[1026, 980]
    (.letOp (n := 1034) (.out 0x10ec04 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec04 12 1)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[1029, 982, 1032]
    (.letOp (n := 1035) (.exec 0x10ec04 (fun s => s.RIP = 0x10ec04) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ec04 12 1)) (Reg.operands [.gpr 12, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[1029, 982, 1032]
    (.letOp (n := 1036) (.out 0x10ec07 (addR64R64Effect 0x10ec07 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[1031, 1020]
    (.letOp (n := 1037) (.out 0x10ec07 (addR64R64Effect 0x10ec07 15 0) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 0] []) (.flag .CF)) #v[1031, 1020]
    (.letOp (n := 1038) (.exec 0x10ec07 (fun s => s.RIP = 0x10ec07) (addR64R64Effect 0x10ec07 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[1031, 1020]
    (b_l10e4c0_23))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_22 : List UInt8 :=
  [0x49, 0x89, 0xD1, 0x48, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0xF7, 0x64, 0x24, 0x50,
    0x49, 0x89, 0xC2, 0x49, 0x01, 0xDA, 0x49, 0x11, 0xD1, 0x4D, 0x01, 0xC2, 0x49, 0x83, 0xD1, 0x00,
    0x4C, 0x89, 0xD0, 0x48, 0x21, 0xF0, 0x49, 0xB8, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x49, 0xF7, 0xE0, 0x48, 0x8B, 0x5C, 0x24, 0x08, 0x48, 0x89, 0x9C, 0x24, 0xA8, 0x00, 0x00, 0x00,
    0x4C, 0x03, 0x7C, 0x24, 0x20, 0x4C, 0x13, 0x64, 0x24, 0x30, 0x4D, 0x01, 0xEF, 0x49, 0x11, 0xCC,
    0x49, 0x01, 0xC7] ++ bytes_l10e4c0_23

theorem code_l10e4c0_22 : ∀ x ∈ codeRange 0x10ebb7 bytes_l10e4c0_22, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xebb7 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_23

def b_l10e4c0_21 : Block Op Label signature Reg.count 952 :=
  .letOp (n := 952) (.out 0x10eb5f (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb5f 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[944, 950]
    (.letOp (n := 953) (.exec 0x10eb5f (fun s => s.RIP = 0x10eb5f) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb5f 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[944, 950]
    (.letOp (n := 954) (.out 0x10eb63 (movR64M64Effect 0x10eb63 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 955) (.exec 0x10eb63 (LoadPre 0x10eb63 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10eb63 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb63 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 956) (.exec 0x10eb68 (StorePre 0x10eb68 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xa0)) s (0x10eb68 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eb68 0 (.sib 4 none 0 (.d32 0xa0))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[954, 65]
    (.letOp (n := 957) (.out 0x10eb70 (shldR64R64Effect 0x10eb70 5 14 7 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[952, 949]
    (.letOp (n := 958) (.exec 0x10eb70 (fun s => s.RIP = 0x10eb70) (shldR64R64Effect 0x10eb70 5 14 7 12) (Reg.operands [.gpr 14, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[952, 949]
    (.letOp (n := 959) (.out 0x10eb75 (movR64R64Effect 0x10eb75 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[865]
    (.letOp (n := 960) (.exec 0x10eb75 (fun s => s.RIP = 0x10eb75) (movR64R64Effect 0x10eb75 0 15) (Reg.operands [.gpr 15] [])) #v[865]
    (.letOp (n := 961) (.out 0x10eb78 (mulR64Effect 0x10eb78 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[907, 959]
    (.letOp (n := 962) (.out 0x10eb78 (mulR64Effect 0x10eb78 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[907, 959]
    (.letOp (n := 963) (.exec 0x10eb78 (fun s => s.RIP = 0x10eb78) (mulR64Effect 0x10eb78 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[907, 959]
    (.letOp (n := 964) (.exec 0x10eb7b (StorePre 0x10eb7b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10eb7b + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eb7b 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[962, 65]
    (.letOp (n := 965) (.exec 0x10eb80 (StorePre 0x10eb80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10eb80 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eb80 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[961, 65]
    (.letOp (n := 966) (.out 0x10eb85 (movR64M64Effect 0x10eb85 0 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 967) (.exec 0x10eb85 (LoadPre 0x10eb85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10eb85 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb85 0 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 968) (.out 0x10eb8a (mulM64Effect 0x10eb8a 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[966, 65]
    (.letOp (n := 969) (.out 0x10eb8a (mulM64Effect 0x10eb8a 5 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[966, 65]
    (.letOp (n := 970) (.exec 0x10eb8a (LoadPre 0x10eb8a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10eb8a + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eb8a 5 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[966, 65]
    (.letOp (n := 971) (.out 0x10eb8f (movR64R64Effect 0x10eb8f 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[969]
    (.letOp (n := 972) (.exec 0x10eb8f (fun s => s.RIP = 0x10eb8f) (movR64R64Effect 0x10eb8f 12 2) (Reg.operands [.gpr 2] [])) #v[969]
    (.letOp (n := 973) (.out 0x10eb92 (movR64R64Effect 0x10eb92 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[968]
    (.letOp (n := 974) (.exec 0x10eb92 (fun s => s.RIP = 0x10eb92) (movR64R64Effect 0x10eb92 15 0) (Reg.operands [.gpr 0] [])) #v[968]
    (.letOp (n := 975) (.out 0x10eb95 (movR64M64Effect 0x10eb95 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 976) (.exec 0x10eb95 (LoadPre 0x10eb95 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eb95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eb95 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 977) (.out 0x10eb99 (mulM64Effect 0x10eb99 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[975, 65]
    (.letOp (n := 978) (.out 0x10eb99 (mulM64Effect 0x10eb99 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[975, 65]
    (.letOp (n := 979) (.exec 0x10eb99 (LoadPre 0x10eb99 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eb99 + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10eb99 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[975, 65]
    (.letOp (n := 980) (.out 0x10eba1 (movR64R64Effect 0x10eba1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[977]
    (.letOp (n := 981) (.exec 0x10eba1 (fun s => s.RIP = 0x10eba1) (movR64R64Effect 0x10eba1 13 0) (Reg.operands [.gpr 0] [])) #v[977]
    (.letOp (n := 982) (.out 0x10eba4 (movR64R64Effect 0x10eba4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[978]
    (.letOp (n := 983) (.exec 0x10eba4 (fun s => s.RIP = 0x10eba4) (movR64R64Effect 0x10eba4 1 2) (Reg.operands [.gpr 2] [])) #v[978]
    (.letOp (n := 984) (.out 0x10eba7 (movR64R64Effect 0x10eba7 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 10] []) (.reg (.gpr 6))) #v[892]
    (.letOp (n := 985) (.exec 0x10eba7 (fun s => s.RIP = 0x10eba7) (movR64R64Effect 0x10eba7 6 10) (Reg.operands [.gpr 10] [])) #v[892]
    (.letOp (n := 986) (.out 0x10ebaa (andR64R64Effect 0x10ebaa 7 10) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 10] []) (.reg (.gpr 7))) #v[949, 892]
    (.letOp (n := 987) (.exec 0x10ebaa (fun s => s.RIP = 0x10ebaa) (andR64R64Effect 0x10ebaa 7 10) (Reg.operands [.gpr 7, .gpr 10] [])) #v[949, 892]
    (.letOp (n := 988) (.out 0x10ebad (movR64M64Effect 0x10ebad 0 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 989) (.exec 0x10ebad (LoadPre 0x10ebad (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ebad + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ebad 0 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 990) (.out 0x10ebb2 (mulM64Effect 0x10ebb2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[988, 65]
    (.letOp (n := 991) (.out 0x10ebb2 (mulM64Effect 0x10ebb2 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[988, 65]
    (.letOp (n := 992) (.exec 0x10ebb2 (LoadPre 0x10ebb2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ebb2 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ebb2 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[988, 65]
    (b_l10e4c0_22)))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_21 : List UInt8 :=
  [0x49, 0x83, 0xD6, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x10, 0x48, 0x89, 0x84, 0x24, 0xA0, 0x00, 0x00,
    0x00, 0x49, 0x0F, 0xA4, 0xFE, 0x0C, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24,
    0x30, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8B, 0x44, 0x24, 0x70, 0x48, 0xF7, 0x64, 0x24, 0x48,
    0x49, 0x89, 0xD4, 0x49, 0x89, 0xC7, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00,
    0x00, 0x00, 0x49, 0x89, 0xC5, 0x48, 0x89, 0xD1, 0x4C, 0x89, 0xD6, 0x4C, 0x21, 0xD7, 0x48, 0x8B,
    0x44, 0x24, 0x68, 0x48, 0xF7, 0x64, 0x24, 0x38] ++ bytes_l10e4c0_22

theorem code_l10e4c0_21 : ∀ x ∈ codeRange 0x10eb5f bytes_l10e4c0_21, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xeb5f 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_22

def b_l10e4c0_20 : Block Op Label signature Reg.count 905 :=
  .letOp (n := 905) (.out 0x10eb07 (movR64M64Effect 0x10eb07 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 906) (.exec 0x10eb07 (LoadPre 0x10eb07 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10eb07 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb07 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 907) (.out 0x10eb0c (movR64M64Effect 0x10eb0c 6 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 908) (.exec 0x10eb0c (LoadPre 0x10eb0c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10eb0c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb0c 6 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 909) (.out 0x10eb11 (mulR64Effect 0x10eb11 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[907, 905]
    (.letOp (n := 910) (.out 0x10eb11 (mulR64Effect 0x10eb11 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[907, 905]
    (.letOp (n := 911) (.exec 0x10eb11 (fun s => s.RIP = 0x10eb11) (mulR64Effect 0x10eb11 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[907, 905]
    (.letOp (n := 912) (.out 0x10eb14 (addR64R64Effect 0x10eb14 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[903, 888]
    (.letOp (n := 913) (.out 0x10eb14 (addR64R64Effect 0x10eb14 13 1) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 1] []) (.flag .CF)) #v[903, 888]
    (.letOp (n := 914) (.exec 0x10eb14 (fun s => s.RIP = 0x10eb14) (addR64R64Effect 0x10eb14 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[903, 888]
    (.letOp (n := 915) (.out 0x10eb17 (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb17 8 3)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[901, 890, 913]
    (.letOp (n := 916) (.exec 0x10eb17 (fun s => s.RIP = 0x10eb17) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb17 8 3)) (Reg.operands [.gpr 8, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[901, 890, 913]
    (.letOp (n := 917) (.out 0x10eb1a (addR64R64Effect 0x10eb1a 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[909, 912]
    (.letOp (n := 918) (.out 0x10eb1a (addR64R64Effect 0x10eb1a 0 13) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 13] []) (.flag .CF)) #v[909, 912]
    (.letOp (n := 919) (.exec 0x10eb1a (fun s => s.RIP = 0x10eb1a) (addR64R64Effect 0x10eb1a 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[909, 912]
    (.letOp (n := 920) (.out 0x10eb1d (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb1d 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[915, 910, 918]
    (.letOp (n := 921) (.exec 0x10eb1d (fun s => s.RIP = 0x10eb1d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb1d 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[915, 910, 918]
    (.letOp (n := 922) (.out 0x10eb20 (addR64R64Effect 0x10eb20 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[917, 838]
    (.letOp (n := 923) (.out 0x10eb20 (addR64R64Effect 0x10eb20 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[917, 838]
    (.letOp (n := 924) (.exec 0x10eb20 (fun s => s.RIP = 0x10eb20) (addR64R64Effect 0x10eb20 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[917, 838]
    (.letOp (n := 925) (.out 0x10eb23 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb23 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[920, 923]
    (.letOp (n := 926) (.exec 0x10eb23 (fun s => s.RIP = 0x10eb23) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10eb23 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[920, 923]
    (.letOp (n := 927) (.out 0x10eb27 (shldR64R64Effect 0x10eb27 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[925, 922]
    (.letOp (n := 928) (.exec 0x10eb27 (fun s => s.RIP = 0x10eb27) (shldR64R64Effect 0x10eb27 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[925, 922]
    (.letOp (n := 929) (.out 0x10eb2c (andR64R64Effect 0x10eb2c 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[922, 892]
    (.letOp (n := 930) (.exec 0x10eb2c (fun s => s.RIP = 0x10eb2c) (andR64R64Effect 0x10eb2c 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[922, 892]
    (.letOp (n := 931) (.out 0x10eb2f (movR64Imm64Effect 0x10eb2f 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 932) (.exec 0x10eb2f (fun s => s.RIP = 0x10eb2f) (movR64Imm64Effect 0x10eb2f 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 933) (.out 0x10eb39 (mulR64Effect 0x10eb39 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[931, 929]
    (.letOp (n := 934) (.out 0x10eb39 (mulR64Effect 0x10eb39 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[931, 929]
    (.letOp (n := 935) (.exec 0x10eb39 (fun s => s.RIP = 0x10eb39) (mulR64Effect 0x10eb39 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[931, 929]
    (.letOp (n := 936) (.out 0x10eb3c (addR64M64Effect 0x10eb3c 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[881, 65]
    (.letOp (n := 937) (.out 0x10eb3c (addR64M64Effect 0x10eb3c 7 (.sib 4 none 0 (.d32 0x88))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[881, 65]
    (.letOp (n := 938) (.exec 0x10eb3c (LoadPre 0x10eb3c (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eb3c + BitVec.ofNat 64 8)) 8) (addR64M64Effect 0x10eb3c 7 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[881, 65]
    (.letOp (n := 939) (.out 0x10eb44 (atFlags StatusFlags.CF (adcR64M64Effect 0x10eb44 14 (.sib 4 none 0 (.d8 0x58)))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 14))) #v[879, 65, 937]
    (.letOp (n := 940) (.exec 0x10eb44 (LoadPre 0x10eb44 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eb44 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10eb44 14 (.sib 4 none 0 (.d8 0x58)))) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[879, 65, 937]
    (.letOp (n := 941) (.out 0x10eb49 (addR64R64Effect 0x10eb49 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[936, 933]
    (.letOp (n := 942) (.out 0x10eb49 (addR64R64Effect 0x10eb49 7 0) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 0] []) (.flag .CF)) #v[936, 933]
    (.letOp (n := 943) (.exec 0x10eb49 (fun s => s.RIP = 0x10eb49) (addR64R64Effect 0x10eb49 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[936, 933]
    (.letOp (n := 944) (.out 0x10eb4c (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb4c 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[939, 934, 942]
    (.letOp (n := 945) (.exec 0x10eb4c (fun s => s.RIP = 0x10eb4c) (atFlags StatusFlags.CF (adcR64R64Effect 0x10eb4c 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[939, 934, 942]
    (.letOp (n := 946) (.out 0x10eb4f (movR64M64Effect 0x10eb4f 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 947) (.exec 0x10eb4f (LoadPre 0x10eb4f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10eb4f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eb4f 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 948) (.exec 0x10eb54 (StorePre 0x10eb54 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10eb54 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eb54 0 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[946, 65]
    (.letOp (n := 949) (.out 0x10eb5c (addR64R64Effect 0x10eb5c 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[941, 863]
    (.letOp (n := 950) (.out 0x10eb5c (addR64R64Effect 0x10eb5c 7 9) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 9] []) (.flag .CF)) #v[941, 863]
    (.letOp (n := 951) (.exec 0x10eb5c (fun s => s.RIP = 0x10eb5c) (addR64R64Effect 0x10eb5c 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[941, 863]
    (b_l10e4c0_21)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_20 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x8B, 0x74, 0x24, 0x30, 0x48, 0xF7, 0xE6, 0x49, 0x01, 0xCD,
    0x49, 0x11, 0xD8, 0x4C, 0x01, 0xE8, 0x49, 0x11, 0xD0, 0x4C, 0x01, 0xE0, 0x49, 0x83, 0xD0, 0x00,
    0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x4C, 0x21, 0xD0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x48, 0xF7, 0xE1, 0x48, 0x03, 0xBC, 0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x13, 0x74,
    0x24, 0x58, 0x48, 0x01, 0xC7, 0x49, 0x11, 0xD6, 0x48, 0x8B, 0x44, 0x24, 0x18, 0x48, 0x89, 0x84,
    0x24, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xCF] ++ bytes_l10e4c0_21

theorem code_l10e4c0_20 : ∀ x ∈ codeRange 0x10eb07 bytes_l10e4c0_20, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xeb07 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_21

def b_l10e4c0_19 : Block Op Label signature Reg.count 863 :=
  .letOp (n := 863) (.out 0x10eaaf (shldR64R64Effect 0x10eaaf 5 9 11 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[860, 857]
    (.letOp (n := 864) (.exec 0x10eaaf (fun s => s.RIP = 0x10eaaf) (shldR64R64Effect 0x10eaaf 5 9 11 12) (Reg.operands [.gpr 9, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[860, 857]
    (.letOp (n := 865) (.out 0x10eab4 (movR64M64Effect 0x10eab4 15 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 866) (.exec 0x10eab4 (LoadPre 0x10eab4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10eab4 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10eab4 15 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 867) (.out 0x10eab9 (movR64R64Effect 0x10eab9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[865]
    (.letOp (n := 868) (.exec 0x10eab9 (fun s => s.RIP = 0x10eab9) (movR64R64Effect 0x10eab9 0 15) (Reg.operands [.gpr 15] [])) #v[865]
    (.letOp (n := 869) (.out 0x10eabc (mulR64Effect 0x10eabc 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[813, 867]
    (.letOp (n := 870) (.out 0x10eabc (mulR64Effect 0x10eabc 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[813, 867]
    (.letOp (n := 871) (.exec 0x10eabc (fun s => s.RIP = 0x10eabc) (mulR64Effect 0x10eabc 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[813, 867]
    (.letOp (n := 872) (.exec 0x10eabf (StorePre 0x10eabf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eabf + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eabf 2 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[870, 65]
    (.letOp (n := 873) (.exec 0x10eac4 (StorePre 0x10eac4 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eac4 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eac4 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[869, 65]
    (.letOp (n := 874) (.out 0x10eacc (movR64R64Effect 0x10eacc 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[778]
    (.letOp (n := 875) (.exec 0x10eacc (fun s => s.RIP = 0x10eacc) (movR64R64Effect 0x10eacc 0 6) (Reg.operands [.gpr 6] [])) #v[778]
    (.letOp (n := 876) (.out 0x10eacf (mulM64Effect 0x10eacf 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[874, 65]
    (.letOp (n := 877) (.out 0x10eacf (mulM64Effect 0x10eacf 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[874, 65]
    (.letOp (n := 878) (.exec 0x10eacf (LoadPre 0x10eacf (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eacf + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10eacf 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[874, 65]
    (.letOp (n := 879) (.out 0x10ead7 (movR64R64Effect 0x10ead7 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[877]
    (.letOp (n := 880) (.exec 0x10ead7 (fun s => s.RIP = 0x10ead7) (movR64R64Effect 0x10ead7 14 2) (Reg.operands [.gpr 2] [])) #v[877]
    (.letOp (n := 881) (.out 0x10eada (movR64R64Effect 0x10eada 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[876]
    (.letOp (n := 882) (.exec 0x10eada (fun s => s.RIP = 0x10eada) (movR64R64Effect 0x10eada 7 0) (Reg.operands [.gpr 0] [])) #v[876]
    (.letOp (n := 883) (.out 0x10eadd (movR64M64Effect 0x10eadd 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 884) (.exec 0x10eadd (LoadPre 0x10eadd (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eadd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eadd 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 885) (.out 0x10eae1 (mulM64Effect 0x10eae1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[883, 65]
    (.letOp (n := 886) (.out 0x10eae1 (mulM64Effect 0x10eae1 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[883, 65]
    (.letOp (n := 887) (.exec 0x10eae1 (LoadPre 0x10eae1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10eae1 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eae1 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[883, 65]
    (.letOp (n := 888) (.out 0x10eae6 (movR64R64Effect 0x10eae6 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[885]
    (.letOp (n := 889) (.exec 0x10eae6 (fun s => s.RIP = 0x10eae6) (movR64R64Effect 0x10eae6 1 0) (Reg.operands [.gpr 0] [])) #v[885]
    (.letOp (n := 890) (.out 0x10eae9 (movR64R64Effect 0x10eae9 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[886]
    (.letOp (n := 891) (.exec 0x10eae9 (fun s => s.RIP = 0x10eae9) (movR64R64Effect 0x10eae9 3 2) (Reg.operands [.gpr 2] [])) #v[886]
    (.letOp (n := 892) (.out 0x10eaec (movR64Imm64Effect 0x10eaec 10 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 893) (.exec 0x10eaec (fun s => s.RIP = 0x10eaec) (movR64Imm64Effect 0x10eaec 10 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 894) (.out 0x10eaf6 (andR64R64Effect 0x10eaf6 11 10) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 10] []) (.reg (.gpr 11))) #v[857, 892]
    (.letOp (n := 895) (.exec 0x10eaf6 (fun s => s.RIP = 0x10eaf6) (andR64R64Effect 0x10eaf6 11 10) (Reg.operands [.gpr 11, .gpr 10] [])) #v[857, 892]
    (.letOp (n := 896) (.out 0x10eaf9 (movR64R64Effect 0x10eaf9 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[800]
    (.letOp (n := 897) (.exec 0x10eaf9 (fun s => s.RIP = 0x10eaf9) (movR64R64Effect 0x10eaf9 0 8) (Reg.operands [.gpr 8] [])) #v[800]
    (.letOp (n := 898) (.out 0x10eafc (mulM64Effect 0x10eafc 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[896, 65]
    (.letOp (n := 899) (.out 0x10eafc (mulM64Effect 0x10eafc 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[896, 65]
    (.letOp (n := 900) (.exec 0x10eafc (LoadPre 0x10eafc (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10eafc + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10eafc 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[896, 65]
    (.letOp (n := 901) (.out 0x10eb01 (movR64R64Effect 0x10eb01 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[899]
    (.letOp (n := 902) (.exec 0x10eb01 (fun s => s.RIP = 0x10eb01) (movR64R64Effect 0x10eb01 8 2) (Reg.operands [.gpr 2] [])) #v[899]
    (.letOp (n := 903) (.out 0x10eb04 (movR64R64Effect 0x10eb04 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[898]
    (.letOp (n := 904) (.exec 0x10eb04 (fun s => s.RIP = 0x10eb04) (movR64R64Effect 0x10eb04 13 0) (Reg.operands [.gpr 0] [])) #v[898]
    (b_l10e4c0_20))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_19 : List UInt8 :=
  [0x4D, 0x0F, 0xA4, 0xD9, 0x0C, 0x4C, 0x8B, 0x7C, 0x24, 0x20, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE6,
    0x48, 0x89, 0x54, 0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0xF0,
    0x48, 0xF7, 0xA4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xC7, 0x48, 0x8B,
    0x04, 0x24, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xD3, 0x49, 0xBA, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4D, 0x21, 0xD3, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0x64,
    0x24, 0x50, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC5] ++ bytes_l10e4c0_20

theorem code_l10e4c0_19 : ∀ x ∈ codeRange 0x10eaaf bytes_l10e4c0_19, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xeaaf 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_20

def b_l10e4c0_18 : Block Op Label signature Reg.count 818 :=
  .letOp (n := 818) (.out 0x10ea5b (addR64R64Effect 0x10ea5b 10 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1] []) (.reg (.gpr 10))) #v[798, 785]
    (.letOp (n := 819) (.out 0x10ea5b (addR64R64Effect 0x10ea5b 10 1) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 1] []) (.flag .CF)) #v[798, 785]
    (.letOp (n := 820) (.exec 0x10ea5b (fun s => s.RIP = 0x10ea5b) (addR64R64Effect 0x10ea5b 10 1) (Reg.operands [.gpr 10, .gpr 1] [])) #v[798, 785]
    (.letOp (n := 821) (.out 0x10ea5e (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea5e 12 9)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[796, 787, 819]
    (.letOp (n := 822) (.exec 0x10ea5e (fun s => s.RIP = 0x10ea5e) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea5e 12 9)) (Reg.operands [.gpr 12, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[796, 787, 819]
    (.letOp (n := 823) (.out 0x10ea61 (addR64R64Effect 0x10ea61 10 15) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 15] []) (.reg (.gpr 10))) #v[818, 809]
    (.letOp (n := 824) (.out 0x10ea61 (addR64R64Effect 0x10ea61 10 15) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 15] []) (.flag .CF)) #v[818, 809]
    (.letOp (n := 825) (.exec 0x10ea61 (fun s => s.RIP = 0x10ea61) (addR64R64Effect 0x10ea61 10 15) (Reg.operands [.gpr 10, .gpr 15] [])) #v[818, 809]
    (.letOp (n := 826) (.out 0x10ea64 (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea64 12 3)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[821, 807, 824]
    (.letOp (n := 827) (.exec 0x10ea64 (fun s => s.RIP = 0x10ea64) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea64 12 3)) (Reg.operands [.gpr 12, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[821, 807, 824]
    (.letOp (n := 828) (.out 0x10ea67 (addR64R64Effect 0x10ea67 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[815, 823]
    (.letOp (n := 829) (.out 0x10ea67 (addR64R64Effect 0x10ea67 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[815, 823]
    (.letOp (n := 830) (.exec 0x10ea67 (fun s => s.RIP = 0x10ea67) (addR64R64Effect 0x10ea67 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[815, 823]
    (.letOp (n := 831) (.out 0x10ea6a (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea6a 12 2)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[826, 816, 829]
    (.letOp (n := 832) (.exec 0x10ea6a (fun s => s.RIP = 0x10ea6a) (atFlags StatusFlags.CF (adcR64R64Effect 0x10ea6a 12 2)) (Reg.operands [.gpr 12, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[826, 816, 829]
    (.letOp (n := 833) (.out 0x10ea6d (addR64R64Effect 0x10ea6d 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[828, 765]
    (.letOp (n := 834) (.out 0x10ea6d (addR64R64Effect 0x10ea6d 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[828, 765]
    (.letOp (n := 835) (.exec 0x10ea6d (fun s => s.RIP = 0x10ea6d) (addR64R64Effect 0x10ea6d 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[828, 765]
    (.letOp (n := 836) (.out 0x10ea70 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ea70 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[831, 834]
    (.letOp (n := 837) (.exec 0x10ea70 (fun s => s.RIP = 0x10ea70) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10ea70 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[831, 834]
    (.letOp (n := 838) (.out 0x10ea74 (shldR64R64Effect 0x10ea74 5 12 0 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[836, 833]
    (.letOp (n := 839) (.exec 0x10ea74 (fun s => s.RIP = 0x10ea74) (shldR64R64Effect 0x10ea74 5 12 0 12) (Reg.operands [.gpr 12, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[836, 833]
    (.letOp (n := 840) (.out 0x10ea79 (shlR64Effect 0x10ea79 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[833]
    (.letOp (n := 841) (.exec 0x10ea79 (fun s => s.RIP = 0x10ea79) (shlR64Effect 0x10ea79 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[833]
    (.letOp (n := 842) (.out 0x10ea7d (movR64Imm64Effect 0x10ea7d 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 843) (.exec 0x10ea7d (fun s => s.RIP = 0x10ea7d) (movR64Imm64Effect 0x10ea7d 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 844) (.out 0x10ea87 (andR64R64Effect 0x10ea87 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[840, 842]
    (.letOp (n := 845) (.exec 0x10ea87 (fun s => s.RIP = 0x10ea87) (andR64R64Effect 0x10ea87 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[840, 842]
    (.letOp (n := 846) (.out 0x10ea8a (orR64R64Effect 0x10ea8a 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 13] []) (.reg (.gpr 0))) #v[844, 789]
    (.letOp (n := 847) (.exec 0x10ea8a (fun s => s.RIP = 0x10ea8a) (orR64R64Effect 0x10ea8a 0 13) (Reg.operands [.gpr 0, .gpr 13] [])) #v[844, 789]
    (.letOp (n := 848) (.out 0x10ea8d (movR64Imm64Effect 0x10ea8d 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 849) (.exec 0x10ea8d (fun s => s.RIP = 0x10ea8d) (movR64Imm64Effect 0x10ea8d 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 850) (.out 0x10ea97 (mulR64Effect 0x10ea97 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[848, 846]
    (.letOp (n := 851) (.out 0x10ea97 (mulR64Effect 0x10ea97 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[848, 846]
    (.letOp (n := 852) (.exec 0x10ea97 (fun s => s.RIP = 0x10ea97) (mulR64Effect 0x10ea97 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[848, 846]
    (.letOp (n := 853) (.out 0x10ea9a (movR64R64Effect 0x10ea9a 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[851]
    (.letOp (n := 854) (.exec 0x10ea9a (fun s => s.RIP = 0x10ea9a) (movR64R64Effect 0x10ea9a 9 2) (Reg.operands [.gpr 2] [])) #v[851]
    (.letOp (n := 855) (.out 0x10ea9d (movR64R64Effect 0x10ea9d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[850]
    (.letOp (n := 856) (.exec 0x10ea9d (fun s => s.RIP = 0x10ea9d) (movR64R64Effect 0x10ea9d 11 0) (Reg.operands [.gpr 0] [])) #v[850]
    (.letOp (n := 857) (.out 0x10eaa0 (addR64M64Effect 0x10eaa0 11 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 4] []) (.reg (.gpr 11))) #v[855, 65]
    (.letOp (n := 858) (.out 0x10eaa0 (addR64M64Effect 0x10eaa0 11 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 4] []) (.flag .CF)) #v[855, 65]
    (.letOp (n := 859) (.exec 0x10eaa0 (LoadPre 0x10eaa0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10eaa0 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10eaa0 11 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[855, 65]
    (.letOp (n := 860) (.out 0x10eaa5 (atFlags StatusFlags.CF (adcR64M64Effect 0x10eaa5 9 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[853, 65, 858]
    (.letOp (n := 861) (.exec 0x10eaa5 (LoadPre 0x10eaa5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eaa5 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10eaa5 9 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[853, 65, 858]
    (.letOp (n := 862) (.exec 0x10eaaa (StorePre 0x10eaaa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10eaaa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10eaaa 7 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (b_l10e4c0_19)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_18 : List UInt8 :=
  [0x49, 0x01, 0xCA, 0x4D, 0x11, 0xCC, 0x4D, 0x01, 0xFA, 0x49, 0x11, 0xDC, 0x4C, 0x01, 0xD0, 0x49,
    0x11, 0xD4, 0x4C, 0x01, 0xD8, 0x49, 0x83, 0xD4, 0x00, 0x49, 0x0F, 0xA4, 0xC4, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8, 0x4C,
    0x09, 0xE8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1, 0x49,
    0x89, 0xD1, 0x49, 0x89, 0xC3, 0x4C, 0x03, 0x5C, 0x24, 0x58, 0x4C, 0x13, 0x4C, 0x24, 0x60, 0x48,
    0x89, 0x7C, 0x24, 0x60] ++ bytes_l10e4c0_19

theorem code_l10e4c0_18 : ∀ x ∈ codeRange 0x10ea5b bytes_l10e4c0_18, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xea5b 84 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_19

def b_l10e4c0_17 : Block Op Label signature Reg.count 776 :=
  .letOp (n := 776) (.exec 0x10ea0d (StorePre 0x10ea0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ea0d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ea0d 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[774, 65]
    (.letOp (n := 777) (.exec 0x10ea12 (StorePre 0x10ea12 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ea12 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ea12 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[773, 65]
    (.letOp (n := 778) (.out 0x10ea17 (movR64M64Effect 0x10ea17 6 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 779) (.exec 0x10ea17 (LoadPre 0x10ea17 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ea17 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea17 6 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 780) (.out 0x10ea1c (movR64R64Effect 0x10ea1c 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[778]
    (.letOp (n := 781) (.exec 0x10ea1c (fun s => s.RIP = 0x10ea1c) (movR64R64Effect 0x10ea1c 0 6) (Reg.operands [.gpr 6] [])) #v[778]
    (.letOp (n := 782) (.out 0x10ea1f (mulM64Effect 0x10ea1f 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[780, 65]
    (.letOp (n := 783) (.out 0x10ea1f (mulM64Effect 0x10ea1f 5 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[780, 65]
    (.letOp (n := 784) (.exec 0x10ea1f (LoadPre 0x10ea1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10ea1f + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea1f 5 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[780, 65]
    (.letOp (n := 785) (.out 0x10ea24 (movR64R64Effect 0x10ea24 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[782]
    (.letOp (n := 786) (.exec 0x10ea24 (fun s => s.RIP = 0x10ea24) (movR64R64Effect 0x10ea24 1 0) (Reg.operands [.gpr 0] [])) #v[782]
    (.letOp (n := 787) (.out 0x10ea27 (movR64R64Effect 0x10ea27 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[783]
    (.letOp (n := 788) (.exec 0x10ea27 (fun s => s.RIP = 0x10ea27) (movR64R64Effect 0x10ea27 9 2) (Reg.operands [.gpr 2] [])) #v[783]
    (.letOp (n := 789) (.out 0x10ea2a (andR32Imm8Effect 0x10ea2a 4 13 0xf) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[769]
    (.letOp (n := 790) (.exec 0x10ea2a (fun s => s.RIP = 0x10ea2a) (andR32Imm8Effect 0x10ea2a 4 13 0xf) (Reg.operands [.gpr 13] [])) #v[769]
    (.letOp (n := 791) (.out 0x10ea2e (movR64M64Effect 0x10ea2e 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 792) (.exec 0x10ea2e (LoadPre 0x10ea2e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ea2e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10ea2e 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 793) (.out 0x10ea32 (mulM64Effect 0x10ea32 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[791, 65]
    (.letOp (n := 794) (.out 0x10ea32 (mulM64Effect 0x10ea32 5 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[791, 65]
    (.letOp (n := 795) (.exec 0x10ea32 (LoadPre 0x10ea32 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10ea32 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea32 5 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[791, 65]
    (.letOp (n := 796) (.out 0x10ea37 (movR64R64Effect 0x10ea37 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[794]
    (.letOp (n := 797) (.exec 0x10ea37 (fun s => s.RIP = 0x10ea37) (movR64R64Effect 0x10ea37 12 2) (Reg.operands [.gpr 2] [])) #v[794]
    (.letOp (n := 798) (.out 0x10ea3a (movR64R64Effect 0x10ea3a 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[793]
    (.letOp (n := 799) (.exec 0x10ea3a (fun s => s.RIP = 0x10ea3a) (movR64R64Effect 0x10ea3a 10 0) (Reg.operands [.gpr 0] [])) #v[793]
    (.letOp (n := 800) (.out 0x10ea3d (movR64M64Effect 0x10ea3d 8 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 801) (.exec 0x10ea3d (LoadPre 0x10ea3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ea3d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea3d 8 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 802) (.out 0x10ea42 (movR64R64Effect 0x10ea42 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[800]
    (.letOp (n := 803) (.exec 0x10ea42 (fun s => s.RIP = 0x10ea42) (movR64R64Effect 0x10ea42 0 8) (Reg.operands [.gpr 8] [])) #v[800]
    (.letOp (n := 804) (.out 0x10ea45 (mulM64Effect 0x10ea45 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[802, 65]
    (.letOp (n := 805) (.out 0x10ea45 (mulM64Effect 0x10ea45 5 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[802, 65]
    (.letOp (n := 806) (.exec 0x10ea45 (LoadPre 0x10ea45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10ea45 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10ea45 5 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[802, 65]
    (.letOp (n := 807) (.out 0x10ea4a (movR64R64Effect 0x10ea4a 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[805]
    (.letOp (n := 808) (.exec 0x10ea4a (fun s => s.RIP = 0x10ea4a) (movR64R64Effect 0x10ea4a 3 2) (Reg.operands [.gpr 2] [])) #v[805]
    (.letOp (n := 809) (.out 0x10ea4d (movR64R64Effect 0x10ea4d 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[804]
    (.letOp (n := 810) (.exec 0x10ea4d (fun s => s.RIP = 0x10ea4d) (movR64R64Effect 0x10ea4d 15 0) (Reg.operands [.gpr 0] [])) #v[804]
    (.letOp (n := 811) (.out 0x10ea50 (movR64R64Effect 0x10ea50 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[649]
    (.letOp (n := 812) (.exec 0x10ea50 (fun s => s.RIP = 0x10ea50) (movR64R64Effect 0x10ea50 0 14) (Reg.operands [.gpr 14] [])) #v[649]
    (.letOp (n := 813) (.out 0x10ea53 (movR64M64Effect 0x10ea53 14 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 814) (.exec 0x10ea53 (LoadPre 0x10ea53 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10ea53 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ea53 14 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 815) (.out 0x10ea58 (mulR64Effect 0x10ea58 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[813, 811]
    (.letOp (n := 816) (.out 0x10ea58 (mulR64Effect 0x10ea58 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[813, 811]
    (.letOp (n := 817) (.exec 0x10ea58 (fun s => s.RIP = 0x10ea58) (mulR64Effect 0x10ea58 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[813, 811]
    (b_l10e4c0_18))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_17 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x8B, 0x74, 0x24, 0x70, 0x48,
    0x89, 0xF0, 0x48, 0xF7, 0x64, 0x24, 0x38, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD1, 0x41, 0x83, 0xE5,
    0x0F, 0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0x64, 0x24, 0x50, 0x49, 0x89, 0xD4, 0x49, 0x89, 0xC2,
    0x4C, 0x8B, 0x44, 0x24, 0x68, 0x4C, 0x89, 0xC0, 0x48, 0xF7, 0x64, 0x24, 0x30, 0x48, 0x89, 0xD3,
    0x49, 0x89, 0xC7, 0x4C, 0x89, 0xF0, 0x4C, 0x8B, 0x74, 0x24, 0x48, 0x49, 0xF7, 0xE6] ++ bytes_l10e4c0_18

theorem code_l10e4c0_17 : ∀ x ∈ codeRange 0x10ea0d bytes_l10e4c0_17, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xea0d 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_18

def b_l10e4c0_16 : Block Op Label signature Reg.count 728 :=
  .letOp (n := 728) (.out 0x10e9bd (movR64R64Effect 0x10e9bd 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[660]
    (.letOp (n := 729) (.exec 0x10e9bd (fun s => s.RIP = 0x10e9bd) (movR64R64Effect 0x10e9bd 0 9) (Reg.operands [.gpr 9] [])) #v[660]
    (.letOp (n := 730) (.out 0x10e9c0 (movR64Imm64Effect 0x10e9c0 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 731) (.exec 0x10e9c0 (fun s => s.RIP = 0x10e9c0) (movR64Imm64Effect 0x10e9c0 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 732) (.out 0x10e9ca (mulR64Effect 0x10e9ca 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[730, 728]
    (.letOp (n := 733) (.out 0x10e9ca (mulR64Effect 0x10e9ca 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[730, 728]
    (.letOp (n := 734) (.exec 0x10e9ca (fun s => s.RIP = 0x10e9ca) (mulR64Effect 0x10e9ca 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[730, 728]
    (.letOp (n := 735) (.out 0x10e9cd (addR64M64Effect 0x10e9cd 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[697, 65]
    (.letOp (n := 736) (.out 0x10e9cd (addR64M64Effect 0x10e9cd 5 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 4] []) (.flag .CF)) #v[697, 65]
    (.letOp (n := 737) (.exec 0x10e9cd (LoadPre 0x10e9cd (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10e9cd + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e9cd 5 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[697, 65]
    (.letOp (n := 738) (.out 0x10e9d2 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9d2 11 (.sib 4 none 0 (.d8 0x60)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[695, 65, 736]
    (.letOp (n := 739) (.exec 0x10e9d2 (LoadPre 0x10e9d2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10e9d2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9d2 11 (.sib 4 none 0 (.d8 0x60)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[695, 65, 736]
    (.letOp (n := 740) (.out 0x10e9d7 (addR64R64Effect 0x10e9d7 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15] []) (.reg (.gpr 5))) #v[735, 705]
    (.letOp (n := 741) (.out 0x10e9d7 (addR64R64Effect 0x10e9d7 5 15) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 15] []) (.flag .CF)) #v[735, 705]
    (.letOp (n := 742) (.exec 0x10e9d7 (fun s => s.RIP = 0x10e9d7) (addR64R64Effect 0x10e9d7 5 15) (Reg.operands [.gpr 5, .gpr 15] [])) #v[735, 705]
    (.letOp (n := 743) (.out 0x10e9da (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9da 11 (.sib 4 none 0 (.d32 0x88)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[738, 65, 741]
    (.letOp (n := 744) (.exec 0x10e9da (LoadPre 0x10e9da (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10e9da + BitVec.ofNat 64 8)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e9da 11 (.sib 4 none 0 (.d32 0x88)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[738, 65, 741]
    (.letOp (n := 745) (.out 0x10e9e2 (addR64R64Effect 0x10e9e2 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[740, 714]
    (.letOp (n := 746) (.out 0x10e9e2 (addR64R64Effect 0x10e9e2 5 13) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 13] []) (.flag .CF)) #v[740, 714]
    (.letOp (n := 747) (.exec 0x10e9e2 (fun s => s.RIP = 0x10e9e2) (addR64R64Effect 0x10e9e2 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[740, 714]
    (.letOp (n := 748) (.out 0x10e9e5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9e5 11 12)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[743, 712, 746]
    (.letOp (n := 749) (.exec 0x10e9e5 (fun s => s.RIP = 0x10e9e5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9e5 11 12)) (Reg.operands [.gpr 11, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[743, 712, 746]
    (.letOp (n := 750) (.out 0x10e9e8 (addR64R64Effect 0x10e9e8 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 3] []) (.reg (.gpr 5))) #v[745, 726]
    (.letOp (n := 751) (.out 0x10e9e8 (addR64R64Effect 0x10e9e8 5 3) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 3] []) (.flag .CF)) #v[745, 726]
    (.letOp (n := 752) (.exec 0x10e9e8 (fun s => s.RIP = 0x10e9e8) (addR64R64Effect 0x10e9e8 5 3) (Reg.operands [.gpr 5, .gpr 3] [])) #v[745, 726]
    (.letOp (n := 753) (.out 0x10e9eb (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9eb 11 1)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[748, 724, 751]
    (.letOp (n := 754) (.exec 0x10e9eb (fun s => s.RIP = 0x10e9eb) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9eb 11 1)) (Reg.operands [.gpr 11, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[748, 724, 751]
    (.letOp (n := 755) (.out 0x10e9ee (addR64R64Effect 0x10e9ee 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[750, 732]
    (.letOp (n := 756) (.out 0x10e9ee (addR64R64Effect 0x10e9ee 5 0) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 0] []) (.flag .CF)) #v[750, 732]
    (.letOp (n := 757) (.exec 0x10e9ee (fun s => s.RIP = 0x10e9ee) (addR64R64Effect 0x10e9ee 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[750, 732]
    (.letOp (n := 758) (.out 0x10e9f1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9f1 11 2)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[753, 733, 756]
    (.letOp (n := 759) (.exec 0x10e9f1 (fun s => s.RIP = 0x10e9f1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e9f1 11 2)) (Reg.operands [.gpr 11, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[753, 733, 756]
    (.letOp (n := 760) (.out 0x10e9f4 (addR64R64Effect 0x10e9f4 5 8) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 8] []) (.reg (.gpr 5))) #v[755, 679]
    (.letOp (n := 761) (.out 0x10e9f4 (addR64R64Effect 0x10e9f4 5 8) (EffectPart.reads (.flag .CF) [.gpr 5, .gpr 8] []) (.flag .CF)) #v[755, 679]
    (.letOp (n := 762) (.exec 0x10e9f4 (fun s => s.RIP = 0x10e9f4) (addR64R64Effect 0x10e9f4 5 8) (Reg.operands [.gpr 5, .gpr 8] [])) #v[755, 679]
    (.letOp (n := 763) (.out 0x10e9f7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e9f7 11 0x0)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[758, 761]
    (.letOp (n := 764) (.exec 0x10e9f7 (fun s => s.RIP = 0x10e9f7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e9f7 11 0x0)) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[758, 761]
    (.letOp (n := 765) (.out 0x10e9fb (shldR64R64Effect 0x10e9fb 5 11 5 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[763, 760]
    (.letOp (n := 766) (.exec 0x10e9fb (fun s => s.RIP = 0x10e9fb) (shldR64R64Effect 0x10e9fb 5 11 5 12) (Reg.operands [.gpr 11, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[763, 760]
    (.letOp (n := 767) (.out 0x10ea00 (movR64R64Effect 0x10ea00 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 5] []) (.reg (.gpr 13))) #v[760]
    (.letOp (n := 768) (.exec 0x10ea00 (fun s => s.RIP = 0x10ea00) (movR64R64Effect 0x10ea00 13 5) (Reg.operands [.gpr 5] [])) #v[760]
    (.letOp (n := 769) (.out 0x10ea03 (shrR64Effect 0x10ea03 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[767]
    (.letOp (n := 770) (.exec 0x10ea03 (fun s => s.RIP = 0x10ea03) (shrR64Effect 0x10ea03 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[767]
    (.letOp (n := 771) (.out 0x10ea07 (movR64R64Effect 0x10ea07 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[681]
    (.letOp (n := 772) (.exec 0x10ea07 (fun s => s.RIP = 0x10ea07) (movR64R64Effect 0x10ea07 0 6) (Reg.operands [.gpr 6] [])) #v[681]
    (.letOp (n := 773) (.out 0x10ea0a (mulR64Effect 0x10ea0a 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[719, 771]
    (.letOp (n := 774) (.out 0x10ea0a (mulR64Effect 0x10ea0a 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[719, 771]
    (.letOp (n := 775) (.exec 0x10ea0a (fun s => s.RIP = 0x10ea0a) (mulR64Effect 0x10ea0a 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[719, 771]
    (b_l10e4c0_17))))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_16 : List UInt8 :=
  [0x4C, 0x89, 0xC8, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2,
    0x48, 0x03, 0x6C, 0x24, 0x58, 0x4C, 0x13, 0x5C, 0x24, 0x60, 0x4C, 0x01, 0xFD, 0x4C, 0x13, 0x9C,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x4C, 0x01, 0xED, 0x4D, 0x11, 0xE3, 0x48, 0x01, 0xDD, 0x49, 0x11,
    0xCB, 0x48, 0x01, 0xC5, 0x49, 0x11, 0xD3, 0x4C, 0x01, 0xC5, 0x49, 0x83, 0xD3, 0x00, 0x49, 0x0F,
    0xA4, 0xEB, 0x0C, 0x49, 0x89, 0xED, 0x49, 0xC1, 0xED, 0x30, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2] ++ bytes_l10e4c0_17

theorem code_l10e4c0_16 : ∀ x ∈ codeRange 0x10e9bd bytes_l10e4c0_16, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe9bd 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_17

def b_l10e4c0_15 : Block Op Label signature Reg.count 688 :=
  .letOp (n := 688) (.exec 0x10e970 (StorePre 0x10e970 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10e970 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e970 2 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[686, 65]
    (.letOp (n := 689) (.exec 0x10e975 (StorePre 0x10e975 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10e975 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e975 0 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[685, 65]
    (.letOp (n := 690) (.out 0x10e97a (movR64R64Effect 0x10e97a 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[596]
    (.letOp (n := 691) (.exec 0x10e97a (fun s => s.RIP = 0x10e97a) (movR64R64Effect 0x10e97a 0 5) (Reg.operands [.gpr 5] [])) #v[596]
    (.letOp (n := 692) (.out 0x10e97d (mulR64Effect 0x10e97d 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[584, 690]
    (.letOp (n := 693) (.out 0x10e97d (mulR64Effect 0x10e97d 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[584, 690]
    (.letOp (n := 694) (.exec 0x10e97d (fun s => s.RIP = 0x10e97d) (mulR64Effect 0x10e97d 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[584, 690]
    (.letOp (n := 695) (.out 0x10e980 (movR64R64Effect 0x10e980 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[693]
    (.letOp (n := 696) (.exec 0x10e980 (fun s => s.RIP = 0x10e980) (movR64R64Effect 0x10e980 11 2) (Reg.operands [.gpr 2] [])) #v[693]
    (.letOp (n := 697) (.out 0x10e983 (movR64R64Effect 0x10e983 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[692]
    (.letOp (n := 698) (.exec 0x10e983 (fun s => s.RIP = 0x10e983) (movR64R64Effect 0x10e983 5 0) (Reg.operands [.gpr 0] [])) #v[692]
    (.letOp (n := 699) (.out 0x10e986 (movR64M64Effect 0x10e986 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 700) (.exec 0x10e986 (LoadPre 0x10e986 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e986 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e986 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 701) (.out 0x10e98a (mulR64Effect 0x10e98a 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[601, 699]
    (.letOp (n := 702) (.out 0x10e98a (mulR64Effect 0x10e98a 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[601, 699]
    (.letOp (n := 703) (.exec 0x10e98a (fun s => s.RIP = 0x10e98a) (mulR64Effect 0x10e98a 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[601, 699]
    (.letOp (n := 704) (.exec 0x10e98d (StorePre 0x10e98d 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10e98d + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e98d 2 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[702, 65]
    (.letOp (n := 705) (.out 0x10e995 (movR64R64Effect 0x10e995 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[701]
    (.letOp (n := 706) (.exec 0x10e995 (fun s => s.RIP = 0x10e995) (movR64R64Effect 0x10e995 15 0) (Reg.operands [.gpr 0] [])) #v[701]
    (.letOp (n := 707) (.out 0x10e998 (movR64R64Effect 0x10e998 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[632]
    (.letOp (n := 708) (.exec 0x10e998 (fun s => s.RIP = 0x10e998) (movR64R64Effect 0x10e998 0 13) (Reg.operands [.gpr 13] [])) #v[632]
    (.letOp (n := 709) (.out 0x10e99b (mulR64Effect 0x10e99b 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[618, 707]
    (.letOp (n := 710) (.out 0x10e99b (mulR64Effect 0x10e99b 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[618, 707]
    (.letOp (n := 711) (.exec 0x10e99b (fun s => s.RIP = 0x10e99b) (mulR64Effect 0x10e99b 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[618, 707]
    (.letOp (n := 712) (.out 0x10e99e (movR64R64Effect 0x10e99e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[710]
    (.letOp (n := 713) (.exec 0x10e99e (fun s => s.RIP = 0x10e99e) (movR64R64Effect 0x10e99e 12 2) (Reg.operands [.gpr 2] [])) #v[710]
    (.letOp (n := 714) (.out 0x10e9a1 (movR64R64Effect 0x10e9a1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[709]
    (.letOp (n := 715) (.exec 0x10e9a1 (fun s => s.RIP = 0x10e9a1) (movR64R64Effect 0x10e9a1 13 0) (Reg.operands [.gpr 0] [])) #v[709]
    (.letOp (n := 716) (.out 0x10e9a4 (movR64R64Effect 0x10e9a4 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[649]
    (.letOp (n := 717) (.exec 0x10e9a4 (fun s => s.RIP = 0x10e9a4) (movR64R64Effect 0x10e9a4 0 14) (Reg.operands [.gpr 14] [])) #v[649]
    (.letOp (n := 718) (.exec 0x10e9a7 (StorePre 0x10e9a7 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e9a7 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e9a7 14 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[649, 65]
    (.letOp (n := 719) (.out 0x10e9ac (movR64M64Effect 0x10e9ac 10 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[65]
    (.letOp (n := 720) (.exec 0x10e9ac (LoadPre 0x10e9ac (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e9ac + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e9ac 10 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 721) (.out 0x10e9b4 (mulR64Effect 0x10e9b4 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[719, 716]
    (.letOp (n := 722) (.out 0x10e9b4 (mulR64Effect 0x10e9b4 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[719, 716]
    (.letOp (n := 723) (.exec 0x10e9b4 (fun s => s.RIP = 0x10e9b4) (mulR64Effect 0x10e9b4 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[719, 716]
    (.letOp (n := 724) (.out 0x10e9b7 (movR64R64Effect 0x10e9b7 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[722]
    (.letOp (n := 725) (.exec 0x10e9b7 (fun s => s.RIP = 0x10e9b7) (movR64R64Effect 0x10e9b7 1 2) (Reg.operands [.gpr 2] [])) #v[722]
    (.letOp (n := 726) (.out 0x10e9ba (movR64R64Effect 0x10e9ba 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[721]
    (.letOp (n := 727) (.exec 0x10e9ba (fun s => s.RIP = 0x10e9ba) (movR64R64Effect 0x10e9ba 3 0) (Reg.operands [.gpr 0] [])) #v[721]
    (b_l10e4c0_16))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_15 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x58, 0x48, 0x89, 0xE8, 0x48, 0xF7, 0xE3,
    0x49, 0x89, 0xD3, 0x48, 0x89, 0xC5, 0x48, 0x8B, 0x04, 0x24, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0x94,
    0x24, 0x88, 0x00, 0x00, 0x00, 0x49, 0x89, 0xC7, 0x4C, 0x89, 0xE8, 0x49, 0xF7, 0xE4, 0x49, 0x89,
    0xD4, 0x49, 0x89, 0xC5, 0x4C, 0x89, 0xF0, 0x4C, 0x89, 0x74, 0x24, 0x40, 0x4C, 0x8B, 0x94, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC3] ++ bytes_l10e4c0_16

theorem code_l10e4c0_15 : ∀ x ∈ codeRange 0x10e970 bytes_l10e4c0_15, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe970 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_16

def b_l10e4c0_14 : Block Op Label signature Reg.count 644 :=
  .letOp (n := 644) (.out 0x10e918 (addR64R64Effect 0x10e918 11 6) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[642, 627]
    (.letOp (n := 645) (.out 0x10e918 (addR64R64Effect 0x10e918 11 6) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[642, 627]
    (.letOp (n := 646) (.exec 0x10e918 (fun s => s.RIP = 0x10e918) (addR64R64Effect 0x10e918 11 6) (Reg.operands [.gpr 11, .gpr 6] [])) #v[642, 627]
    (.letOp (n := 647) (.out 0x10e91b (atFlags StatusFlags.CF (adcR64R64Effect 0x10e91b 10 1)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[640, 630, 645]
    (.letOp (n := 648) (.exec 0x10e91b (fun s => s.RIP = 0x10e91b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e91b 10 1)) (Reg.operands [.gpr 10, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[640, 630, 645]
    (.letOp (n := 649) (.out 0x10e91e (movR64M64Effect 0x10e91e 14 (.base 14 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14] []) (.reg (.gpr 14))) #v[579]
    (.letOp (n := 650) (.exec 0x10e91e (LoadPre 0x10e91e (fun s => AddrMode.addr (.base 14 (.d8 0x48)) s (0x10e91e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e91e 14 (.base 14 (.d8 0x48))) (Reg.operands [.gpr 14] [])) #v[579]
    (.letOp (n := 651) (.out 0x10e922 (movR64R64Effect 0x10e922 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[649]
    (.letOp (n := 652) (.exec 0x10e922 (fun s => s.RIP = 0x10e922) (movR64R64Effect 0x10e922 0 14) (Reg.operands [.gpr 14] [])) #v[649]
    (.letOp (n := 653) (.out 0x10e925 (movR64M64Effect 0x10e925 1 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 654) (.exec 0x10e925 (LoadPre 0x10e925 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e925 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e925 1 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 655) (.out 0x10e92a (mulR64Effect 0x10e92a 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[653, 651]
    (.letOp (n := 656) (.out 0x10e92a (mulR64Effect 0x10e92a 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[653, 651]
    (.letOp (n := 657) (.exec 0x10e92a (fun s => s.RIP = 0x10e92a) (mulR64Effect 0x10e92a 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[653, 651]
    (.letOp (n := 658) (.out 0x10e92d (movR64R64Effect 0x10e92d 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[656]
    (.letOp (n := 659) (.exec 0x10e92d (fun s => s.RIP = 0x10e92d) (movR64R64Effect 0x10e92d 9 2) (Reg.operands [.gpr 2] [])) #v[656]
    (.letOp (n := 660) (.out 0x10e930 (shldR64R64Effect 0x10e930 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[658, 655]
    (.letOp (n := 661) (.exec 0x10e930 (fun s => s.RIP = 0x10e930) (shldR64R64Effect 0x10e930 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[658, 655]
    (.letOp (n := 662) (.out 0x10e935 (movR64Imm64Effect 0x10e935 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 663) (.exec 0x10e935 (fun s => s.RIP = 0x10e935) (movR64Imm64Effect 0x10e935 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 664) (.out 0x10e93f (andR64R64Effect 0x10e93f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[655, 662]
    (.letOp (n := 665) (.exec 0x10e93f (fun s => s.RIP = 0x10e93f) (andR64R64Effect 0x10e93f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[655, 662]
    (.letOp (n := 666) (.out 0x10e942 (movR64Imm64Effect 0x10e942 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 667) (.exec 0x10e942 (fun s => s.RIP = 0x10e942) (movR64Imm64Effect 0x10e942 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 668) (.out 0x10e94c (mulR64Effect 0x10e94c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[666, 664]
    (.letOp (n := 669) (.out 0x10e94c (mulR64Effect 0x10e94c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[666, 664]
    (.letOp (n := 670) (.exec 0x10e94c (fun s => s.RIP = 0x10e94c) (mulR64Effect 0x10e94c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[666, 664]
    (.letOp (n := 671) (.out 0x10e94f (movR64R64Effect 0x10e94f 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[669]
    (.letOp (n := 672) (.exec 0x10e94f (fun s => s.RIP = 0x10e94f) (movR64R64Effect 0x10e94f 8 2) (Reg.operands [.gpr 2] [])) #v[669]
    (.letOp (n := 673) (.out 0x10e952 (addR64R64Effect 0x10e952 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[668, 644]
    (.letOp (n := 674) (.out 0x10e952 (addR64R64Effect 0x10e952 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[668, 644]
    (.letOp (n := 675) (.exec 0x10e952 (fun s => s.RIP = 0x10e952) (addR64R64Effect 0x10e952 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[668, 644]
    (.letOp (n := 676) (.exec 0x10e955 (StorePre 0x10e955 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e955 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e955 0 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[673, 65]
    (.letOp (n := 677) (.out 0x10e95d (atFlags StatusFlags.CF (adcR64R64Effect 0x10e95d 8 10)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[671, 647, 674]
    (.letOp (n := 678) (.exec 0x10e95d (fun s => s.RIP = 0x10e95d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e95d 8 10)) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[671, 647, 674]
    (.letOp (n := 679) (.out 0x10e960 (shldR64R64Effect 0x10e960 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[677, 673]
    (.letOp (n := 680) (.exec 0x10e960 (fun s => s.RIP = 0x10e960) (shldR64R64Effect 0x10e960 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[677, 673]
    (.letOp (n := 681) (.out 0x10e965 (movR64M64Effect 0x10e965 6 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 682) (.exec 0x10e965 (LoadPre 0x10e965 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e965 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e965 6 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 683) (.out 0x10e96a (movR64R64Effect 0x10e96a 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[681]
    (.letOp (n := 684) (.exec 0x10e96a (fun s => s.RIP = 0x10e96a) (movR64R64Effect 0x10e96a 0 6) (Reg.operands [.gpr 6] [])) #v[681]
    (.letOp (n := 685) (.out 0x10e96d (mulR64Effect 0x10e96d 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[653, 683]
    (.letOp (n := 686) (.out 0x10e96d (mulR64Effect 0x10e96d 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[653, 683]
    (.letOp (n := 687) (.exec 0x10e96d (fun s => s.RIP = 0x10e96d) (mulR64Effect 0x10e96d 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[653, 683]
    (b_l10e4c0_15))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_14 : List UInt8 :=
  [0x49, 0x01, 0xF3, 0x49, 0x11, 0xCA, 0x4D, 0x8B, 0x76, 0x48, 0x4C, 0x89, 0xF0, 0x48, 0x8B, 0x4C,
    0x24, 0x38, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD1, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xBA, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00,
    0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89, 0xD0, 0x4C, 0x01, 0xD8, 0x48, 0x89, 0x84,
    0x24, 0x90, 0x00, 0x00, 0x00, 0x4D, 0x11, 0xD0, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x48, 0x8B, 0x74,
    0x24, 0x20, 0x48, 0x89, 0xF0, 0x48, 0xF7, 0xE1] ++ bytes_l10e4c0_15

theorem code_l10e4c0_14 : ∀ x ∈ codeRange 0x10e918 bytes_l10e4c0_14, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe918 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_15

def b_l10e4c0_13 : Block Op Label signature Reg.count 601 :=
  .letOp (n := 601) (.out 0x10e8ce (movR64M64Effect 0x10e8ce 15 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 602) (.exec 0x10e8ce (LoadPre 0x10e8ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e8ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e8ce 15 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 603) (.out 0x10e8d3 (mulR64Effect 0x10e8d3 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[601, 598]
    (.letOp (n := 604) (.out 0x10e8d3 (mulR64Effect 0x10e8d3 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[601, 598]
    (.letOp (n := 605) (.exec 0x10e8d3 (fun s => s.RIP = 0x10e8d3) (mulR64Effect 0x10e8d3 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[601, 598]
    (.letOp (n := 606) (.out 0x10e8d6 (movR64R64Effect 0x10e8d6 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[604]
    (.letOp (n := 607) (.exec 0x10e8d6 (fun s => s.RIP = 0x10e8d6) (movR64R64Effect 0x10e8d6 8 2) (Reg.operands [.gpr 2] [])) #v[604]
    (.letOp (n := 608) (.out 0x10e8d9 (movR64R64Effect 0x10e8d9 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[603]
    (.letOp (n := 609) (.exec 0x10e8d9 (fun s => s.RIP = 0x10e8d9) (movR64R64Effect 0x10e8d9 9 0) (Reg.operands [.gpr 0] [])) #v[603]
    (.letOp (n := 610) (.out 0x10e8dc (addR64R64Effect 0x10e8dc 9 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1] []) (.reg (.gpr 9))) #v[608, 589]
    (.letOp (n := 611) (.out 0x10e8dc (addR64R64Effect 0x10e8dc 9 1) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 1] []) (.flag .CF)) #v[608, 589]
    (.letOp (n := 612) (.exec 0x10e8dc (fun s => s.RIP = 0x10e8dc) (addR64R64Effect 0x10e8dc 9 1) (Reg.operands [.gpr 9, .gpr 1] [])) #v[608, 589]
    (.letOp (n := 613) (.out 0x10e8df (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8df 8 6)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[606, 591, 611]
    (.letOp (n := 614) (.exec 0x10e8df (fun s => s.RIP = 0x10e8df) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8df 8 6)) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[606, 591, 611]
    (.letOp (n := 615) (.out 0x10e8e2 (movR64M64Effect 0x10e8e2 0 (.base 14 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[579]
    (.letOp (n := 616) (.exec 0x10e8e2 (LoadPre 0x10e8e2 (fun s => AddrMode.addr (.base 14 (.d8 0x38)) s (0x10e8e2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8e2 0 (.base 14 (.d8 0x38))) (Reg.operands [.gpr 14] [])) #v[579]
    (.letOp (n := 617) (.exec 0x10e8e6 (StorePre 0x10e8e6 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e8e6 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e8e6 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[615, 65]
    (.letOp (n := 618) (.out 0x10e8ea (movR64M64Effect 0x10e8ea 12 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[65]
    (.letOp (n := 619) (.exec 0x10e8ea (LoadPre 0x10e8ea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e8ea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e8ea 12 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 620) (.out 0x10e8ef (mulR64Effect 0x10e8ef 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[618, 615]
    (.letOp (n := 621) (.out 0x10e8ef (mulR64Effect 0x10e8ef 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[618, 615]
    (.letOp (n := 622) (.exec 0x10e8ef (fun s => s.RIP = 0x10e8ef) (mulR64Effect 0x10e8ef 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[618, 615]
    (.letOp (n := 623) (.out 0x10e8f2 (movR64R64Effect 0x10e8f2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[621]
    (.letOp (n := 624) (.exec 0x10e8f2 (fun s => s.RIP = 0x10e8f2) (movR64R64Effect 0x10e8f2 1 2) (Reg.operands [.gpr 2] [])) #v[621]
    (.letOp (n := 625) (.out 0x10e8f5 (movR64R64Effect 0x10e8f5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[620]
    (.letOp (n := 626) (.exec 0x10e8f5 (fun s => s.RIP = 0x10e8f5) (movR64R64Effect 0x10e8f5 6 0) (Reg.operands [.gpr 0] [])) #v[620]
    (.letOp (n := 627) (.out 0x10e8f8 (addR64R64Effect 0x10e8f8 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[625, 610]
    (.letOp (n := 628) (.out 0x10e8f8 (addR64R64Effect 0x10e8f8 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[625, 610]
    (.letOp (n := 629) (.exec 0x10e8f8 (fun s => s.RIP = 0x10e8f8) (addR64R64Effect 0x10e8f8 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[625, 610]
    (.letOp (n := 630) (.out 0x10e8fb (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8fb 1 8)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[623, 613, 628]
    (.letOp (n := 631) (.exec 0x10e8fb (fun s => s.RIP = 0x10e8fb) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e8fb 1 8)) (Reg.operands [.gpr 1, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[623, 613, 628]
    (.letOp (n := 632) (.out 0x10e8fe (movR64M64Effect 0x10e8fe 13 (.base 14 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[579]
    (.letOp (n := 633) (.exec 0x10e8fe (LoadPre 0x10e8fe (fun s => AddrMode.addr (.base 14 (.d8 0x40)) s (0x10e8fe + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8fe 13 (.base 14 (.d8 0x40))) (Reg.operands [.gpr 14] [])) #v[579]
    (.letOp (n := 634) (.out 0x10e902 (movR64R64Effect 0x10e902 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[632]
    (.letOp (n := 635) (.exec 0x10e902 (fun s => s.RIP = 0x10e902) (movR64R64Effect 0x10e902 0 13) (Reg.operands [.gpr 13] [])) #v[632]
    (.letOp (n := 636) (.exec 0x10e905 (StorePre 0x10e905 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e905 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e905 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[632, 65]
    (.letOp (n := 637) (.out 0x10e90a (mulM64Effect 0x10e90a 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[634, 65]
    (.letOp (n := 638) (.out 0x10e90a (mulM64Effect 0x10e90a 8 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[634, 65]
    (.letOp (n := 639) (.exec 0x10e90a (LoadPre 0x10e90a (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e90a + BitVec.ofNat 64 8)) 8) (mulM64Effect 0x10e90a 8 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[634, 65]
    (.letOp (n := 640) (.out 0x10e912 (movR64R64Effect 0x10e912 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[638]
    (.letOp (n := 641) (.exec 0x10e912 (fun s => s.RIP = 0x10e912) (movR64R64Effect 0x10e912 10 2) (Reg.operands [.gpr 2] [])) #v[638]
    (.letOp (n := 642) (.out 0x10e915 (movR64R64Effect 0x10e915 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[637]
    (.letOp (n := 643) (.exec 0x10e915 (fun s => s.RIP = 0x10e915) (movR64R64Effect 0x10e915 11 0) (Reg.operands [.gpr 0] [])) #v[637]
    (b_l10e4c0_14)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_13 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x30, 0x49, 0xF7, 0xE7, 0x49, 0x89, 0xD0, 0x49, 0x89, 0xC1, 0x49, 0x01,
    0xC9, 0x49, 0x11, 0xF0, 0x49, 0x8B, 0x46, 0x38, 0x48, 0x89, 0x04, 0x24, 0x4C, 0x8B, 0x64, 0x24,
    0x48, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC6, 0x4C, 0x01, 0xCE, 0x4C, 0x11, 0xC1,
    0x4D, 0x8B, 0x6E, 0x40, 0x4C, 0x89, 0xE8, 0x4C, 0x89, 0x6C, 0x24, 0x68, 0x48, 0xF7, 0xA4, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC3] ++ bytes_l10e4c0_14

theorem code_l10e4c0_13 : ∀ x ∈ codeRange 0x10e8ce bytes_l10e4c0_13, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe8ce 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_14

def b_l10e4c0_12 : Block Op Label signature Reg.count 564 :=
  .letOp (n := 564) (.out 0x10e877 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e877 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[559, 562]
    (.letOp (n := 565) (.exec 0x10e877 (fun s => s.RIP = 0x10e877) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e877 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[559, 562]
    (.letOp (n := 566) (.out 0x10e87b (shldR64R64Effect 0x10e87b 5 2 6 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[564, 561]
    (.letOp (n := 567) (.exec 0x10e87b (fun s => s.RIP = 0x10e87b) (shldR64R64Effect 0x10e87b 5 2 6 12) (Reg.operands [.gpr 2, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[564, 561]
    (.letOp (n := 568) (.out 0x10e880 (movR64R64Effect 0x10e880 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[561]
    (.letOp (n := 569) (.exec 0x10e880 (fun s => s.RIP = 0x10e880) (movR64R64Effect 0x10e880 9 6) (Reg.operands [.gpr 6] [])) #v[561]
    (.letOp (n := 570) (.out 0x10e883 (movR64Imm64Effect 0x10e883 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 571) (.exec 0x10e883 (fun s => s.RIP = 0x10e883) (movR64Imm64Effect 0x10e883 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 572) (.out 0x10e88d (movR64M64Effect 0x10e88d 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 573) (.exec 0x10e88d (LoadPre 0x10e88d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e88d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e88d 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 574) (.out 0x10e892 (andR64R64Effect 0x10e892 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[572, 570]
    (.letOp (n := 575) (.exec 0x10e892 (fun s => s.RIP = 0x10e892) (andR64R64Effect 0x10e892 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[572, 570]
    (.letOp (n := 576) (.out 0x10e895 (addR64R64Effect 0x10e895 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[574, 566]
    (.letOp (n := 577) (.exec 0x10e895 (fun s => s.RIP = 0x10e895) (addR64R64Effect 0x10e895 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[574, 566]
    (.letOp (n := 578) (.exec 0x10e898 (StorePre 0x10e898 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e898 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e898 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[576, 65]
    (.letOp (n := 579) (.out 0x10e89d (movR64M64Effect 0x10e89d 14 (.sib 4 none 0 (.d32 0x90))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 580) (.exec 0x10e89d (LoadPre 0x10e89d (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e89d + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e89d 14 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 581) (.out 0x10e8a5 (movR64M64Effect 0x10e8a5 0 (.base 14 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[579]
    (.letOp (n := 582) (.exec 0x10e8a5 (LoadPre 0x10e8a5 (fun s => AddrMode.addr (.base 14 (.d8 0x28)) s (0x10e8a5 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8a5 0 (.base 14 (.d8 0x28))) (Reg.operands [.gpr 14] [])) #v[579]
    (.letOp (n := 583) (.exec 0x10e8a9 (StorePre 0x10e8a9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e8a9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8a9 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[581, 65]
    (.letOp (n := 584) (.out 0x10e8ae (movR64R64Effect 0x10e8ae 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 15] []) (.reg (.gpr 3))) #v[492]
    (.letOp (n := 585) (.exec 0x10e8ae (fun s => s.RIP = 0x10e8ae) (movR64R64Effect 0x10e8ae 3 15) (Reg.operands [.gpr 15] [])) #v[492]
    (.letOp (n := 586) (.out 0x10e8b1 (mulR64Effect 0x10e8b1 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[492, 581]
    (.letOp (n := 587) (.out 0x10e8b1 (mulR64Effect 0x10e8b1 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[492, 581]
    (.letOp (n := 588) (.exec 0x10e8b1 (fun s => s.RIP = 0x10e8b1) (mulR64Effect 0x10e8b1 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[492, 581]
    (.letOp (n := 589) (.out 0x10e8b4 (movR64R64Effect 0x10e8b4 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[586]
    (.letOp (n := 590) (.exec 0x10e8b4 (fun s => s.RIP = 0x10e8b4) (movR64R64Effect 0x10e8b4 1 0) (Reg.operands [.gpr 0] [])) #v[586]
    (.letOp (n := 591) (.out 0x10e8b7 (movR64R64Effect 0x10e8b7 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[587]
    (.letOp (n := 592) (.exec 0x10e8b7 (fun s => s.RIP = 0x10e8b7) (movR64R64Effect 0x10e8b7 6 2) (Reg.operands [.gpr 2] [])) #v[587]
    (.letOp (n := 593) (.out 0x10e8ba (andR64R64Effect 0x10e8ba 9 5) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 5] []) (.reg (.gpr 9))) #v[568, 478]
    (.letOp (n := 594) (.exec 0x10e8ba (fun s => s.RIP = 0x10e8ba) (andR64R64Effect 0x10e8ba 9 5) (Reg.operands [.gpr 9, .gpr 5] [])) #v[568, 478]
    (.letOp (n := 595) (.exec 0x10e8bd (StorePre 0x10e8bd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e8bd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8bd 9 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[593, 65]
    (.letOp (n := 596) (.out 0x10e8c2 (movR64M64Effect 0x10e8c2 5 (.base 14 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 14] []) (.reg (.gpr 5))) #v[579]
    (.letOp (n := 597) (.exec 0x10e8c2 (LoadPre 0x10e8c2 (fun s => AddrMode.addr (.base 14 (.d8 0x30)) s (0x10e8c2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e8c2 5 (.base 14 (.d8 0x30))) (Reg.operands [.gpr 14] [])) #v[579]
    (.letOp (n := 598) (.out 0x10e8c6 (movR64R64Effect 0x10e8c6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[596]
    (.letOp (n := 599) (.exec 0x10e8c6 (fun s => s.RIP = 0x10e8c6) (movR64R64Effect 0x10e8c6 0 5) (Reg.operands [.gpr 5] [])) #v[596]
    (.letOp (n := 600) (.exec 0x10e8c9 (StorePre 0x10e8c9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e8c9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e8c9 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[596, 65]
    (b_l10e4c0_13)))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_12 : List UInt8 :=
  [0x48, 0x83, 0xD2, 0x00, 0x48, 0x0F, 0xA4, 0xF2, 0x0C, 0x49, 0x89, 0xF1, 0x48, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x48, 0x21, 0xC8, 0x48, 0x01,
    0xD0, 0x48, 0x89, 0x44, 0x24, 0x28, 0x4C, 0x8B, 0xB4, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x8B,
    0x46, 0x28, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x89, 0xFB, 0x49, 0xF7, 0xE7, 0x48, 0x89, 0xC1,
    0x48, 0x89, 0xD6, 0x49, 0x21, 0xE9, 0x4C, 0x89, 0x4C, 0x24, 0x78, 0x49, 0x8B, 0x6E, 0x30, 0x48,
    0x89, 0xE8, 0x48, 0x89, 0x6C, 0x24, 0x70] ++ bytes_l10e4c0_13

theorem code_l10e4c0_12 : ∀ x ∈ codeRange 0x10e877 bytes_l10e4c0_12, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe877 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_13

def b_l10e4c0_11 : Block Op Label signature Reg.count 517 :=
  .letOp (n := 517) (.out 0x10e830 (mulR64Effect 0x10e830 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[515, 513]
    (.letOp (n := 518) (.out 0x10e830 (mulR64Effect 0x10e830 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[515, 513]
    (.letOp (n := 519) (.exec 0x10e830 (fun s => s.RIP = 0x10e830) (mulR64Effect 0x10e830 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[515, 513]
    (.letOp (n := 520) (.out 0x10e833 (addR64R64Effect 0x10e833 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 1] []) (.reg (.gpr 3))) #v[474, 467]
    (.letOp (n := 521) (.out 0x10e833 (addR64R64Effect 0x10e833 3 1) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 1] []) (.flag .CF)) #v[474, 467]
    (.letOp (n := 522) (.exec 0x10e833 (fun s => s.RIP = 0x10e833) (addR64R64Effect 0x10e833 3 1) (Reg.operands [.gpr 3, .gpr 1] [])) #v[474, 467]
    (.letOp (n := 523) (.out 0x10e836 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e836 9 12)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[476, 465, 521]
    (.letOp (n := 524) (.exec 0x10e836 (fun s => s.RIP = 0x10e836) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e836 9 12)) (Reg.operands [.gpr 9, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[476, 465, 521]
    (.letOp (n := 525) (.out 0x10e839 (addR64R64Effect 0x10e839 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[520, 458]
    (.letOp (n := 526) (.out 0x10e839 (addR64R64Effect 0x10e839 3 11) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 11] []) (.flag .CF)) #v[520, 458]
    (.letOp (n := 527) (.exec 0x10e839 (fun s => s.RIP = 0x10e839) (addR64R64Effect 0x10e839 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[520, 458]
    (.letOp (n := 528) (.out 0x10e83c (atFlags StatusFlags.CF (adcR64M64Effect 0x10e83c 9 (.sib 4 none 0 .none))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[523, 65, 526]
    (.letOp (n := 529) (.exec 0x10e83c (LoadPre 0x10e83c (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e83c + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e83c 9 (.sib 4 none 0 .none))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[523, 65, 526]
    (.letOp (n := 530) (.out 0x10e840 (addR64R64Effect 0x10e840 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[525, 517]
    (.letOp (n := 531) (.out 0x10e840 (addR64R64Effect 0x10e840 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[525, 517]
    (.letOp (n := 532) (.exec 0x10e840 (fun s => s.RIP = 0x10e840) (addR64R64Effect 0x10e840 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[525, 517]
    (.letOp (n := 533) (.out 0x10e843 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e843 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[528, 518, 531]
    (.letOp (n := 534) (.exec 0x10e843 (fun s => s.RIP = 0x10e843) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e843 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[528, 518, 531]
    (.letOp (n := 535) (.out 0x10e846 (addR64R64Effect 0x10e846 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[530, 450]
    (.letOp (n := 536) (.out 0x10e846 (addR64R64Effect 0x10e846 3 8) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 8] []) (.flag .CF)) #v[530, 450]
    (.letOp (n := 537) (.exec 0x10e846 (fun s => s.RIP = 0x10e846) (addR64R64Effect 0x10e846 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[530, 450]
    (.letOp (n := 538) (.out 0x10e849 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e849 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[533, 536]
    (.letOp (n := 539) (.exec 0x10e849 (fun s => s.RIP = 0x10e849) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e849 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[533, 536]
    (.letOp (n := 540) (.out 0x10e84d (shldR64R64Effect 0x10e84d 5 14 13 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[509, 506]
    (.letOp (n := 541) (.exec 0x10e84d (fun s => s.RIP = 0x10e84d) (shldR64R64Effect 0x10e84d 5 14 13 12) (Reg.operands [.gpr 14, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[509, 506]
    (.letOp (n := 542) (.out 0x10e852 (shldR64R64Effect 0x10e852 5 9 3 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[538, 535]
    (.letOp (n := 543) (.exec 0x10e852 (fun s => s.RIP = 0x10e852) (shldR64R64Effect 0x10e852 5 9 3 12) (Reg.operands [.gpr 9, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[538, 535]
    (.letOp (n := 544) (.out 0x10e857 (movR64R64Effect 0x10e857 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[540]
    (.letOp (n := 545) (.exec 0x10e857 (fun s => s.RIP = 0x10e857) (movR64R64Effect 0x10e857 0 14) (Reg.operands [.gpr 14] [])) #v[540]
    (.letOp (n := 546) (.out 0x10e85a (mulR64Effect 0x10e85a 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[515, 544]
    (.letOp (n := 547) (.out 0x10e85a (mulR64Effect 0x10e85a 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[515, 544]
    (.letOp (n := 548) (.exec 0x10e85a (fun s => s.RIP = 0x10e85a) (mulR64Effect 0x10e85a 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[515, 544]
    (.letOp (n := 549) (.out 0x10e85d (andR64R64Effect 0x10e85d 3 5) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5] []) (.reg (.gpr 3))) #v[535, 478]
    (.letOp (n := 550) (.exec 0x10e85d (fun s => s.RIP = 0x10e85d) (andR64R64Effect 0x10e85d 3 5) (Reg.operands [.gpr 3, .gpr 5] [])) #v[535, 478]
    (.letOp (n := 551) (.exec 0x10e860 (StorePre 0x10e860 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e860 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e860 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[549, 65]
    (.letOp (n := 552) (.out 0x10e865 (movR64M64Effect 0x10e865 6 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 553) (.exec 0x10e865 (LoadPre 0x10e865 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e865 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e865 6 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 554) (.out 0x10e86a (andR64R64Effect 0x10e86a 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[552, 478]
    (.letOp (n := 555) (.exec 0x10e86a (fun s => s.RIP = 0x10e86a) (andR64R64Effect 0x10e86a 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[552, 478]
    (.letOp (n := 556) (.out 0x10e86d (addR64R64Effect 0x10e86d 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[554, 546]
    (.letOp (n := 557) (.out 0x10e86d (addR64R64Effect 0x10e86d 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[554, 546]
    (.letOp (n := 558) (.exec 0x10e86d (fun s => s.RIP = 0x10e86d) (addR64R64Effect 0x10e86d 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[554, 546]
    (.letOp (n := 559) (.out 0x10e870 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e870 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[547, 557]
    (.letOp (n := 560) (.exec 0x10e870 (fun s => s.RIP = 0x10e870) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e870 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[547, 557]
    (.letOp (n := 561) (.out 0x10e874 (addR64R64Effect 0x10e874 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[556, 542]
    (.letOp (n := 562) (.out 0x10e874 (addR64R64Effect 0x10e874 6 9) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 9] []) (.flag .CF)) #v[556, 542]
    (.letOp (n := 563) (.exec 0x10e874 (fun s => s.RIP = 0x10e874) (addR64R64Effect 0x10e874 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[556, 542]
    (b_l10e4c0_12)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_11 : List UInt8 :=
  [0x48, 0xF7, 0xE6, 0x48, 0x01, 0xCB, 0x4D, 0x11, 0xE1, 0x4C, 0x01, 0xDB, 0x4C, 0x13, 0x0C, 0x24,
    0x48, 0x01, 0xC3, 0x49, 0x11, 0xD1, 0x4C, 0x01, 0xC3, 0x49, 0x83, 0xD1, 0x00, 0x4D, 0x0F, 0xA4,
    0xEE, 0x0C, 0x49, 0x0F, 0xA4, 0xD9, 0x0C, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE6, 0x48, 0x21, 0xEB,
    0x48, 0x89, 0x5C, 0x24, 0x08, 0x48, 0x8B, 0x74, 0x24, 0x78, 0x48, 0x21, 0xEE, 0x48, 0x01, 0xC6,
    0x48, 0x83, 0xD2, 0x00, 0x4C, 0x01, 0xCE] ++ bytes_l10e4c0_12

theorem code_l10e4c0_11 : ∀ x ∈ codeRange 0x10e830 bytes_l10e4c0_11, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe830 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_12

def b_l10e4c0_10 : Block Op Label signature Reg.count 474 :=
  .letOp (n := 474) (.out 0x10e7e4 (movR64R64Effect 0x10e7e4 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[471]
    (.letOp (n := 475) (.exec 0x10e7e4 (fun s => s.RIP = 0x10e7e4) (movR64R64Effect 0x10e7e4 3 0) (Reg.operands [.gpr 0] [])) #v[471]
    (.letOp (n := 476) (.out 0x10e7e7 (movR64R64Effect 0x10e7e7 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[472]
    (.letOp (n := 477) (.exec 0x10e7e7 (fun s => s.RIP = 0x10e7e7) (movR64R64Effect 0x10e7e7 9 2) (Reg.operands [.gpr 2] [])) #v[472]
    (.letOp (n := 478) (.out 0x10e7ea (movR64R64Effect 0x10e7ea 5 6) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[426]
    (.letOp (n := 479) (.exec 0x10e7ea (fun s => s.RIP = 0x10e7ea) (movR64R64Effect 0x10e7ea 5 6) (Reg.operands [.gpr 6] [])) #v[426]
    (.letOp (n := 480) (.out 0x10e7ed (andR64R64Effect 0x10e7ed 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[445, 426]
    (.letOp (n := 481) (.exec 0x10e7ed (fun s => s.RIP = 0x10e7ed) (andR64R64Effect 0x10e7ed 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[445, 426]
    (.letOp (n := 482) (.exec 0x10e7f0 (StorePre 0x10e7f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e7f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e7f0 13 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[480, 65]
    (.letOp (n := 483) (.out 0x10e7f5 (movR64M64Effect 0x10e7f5 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 484) (.exec 0x10e7f5 (LoadPre 0x10e7f5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e7f5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e7f5 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 485) (.out 0x10e7fa (mulR64Effect 0x10e7fa 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[393, 483]
    (.letOp (n := 486) (.out 0x10e7fa (mulR64Effect 0x10e7fa 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[393, 483]
    (.letOp (n := 487) (.exec 0x10e7fa (fun s => s.RIP = 0x10e7fa) (mulR64Effect 0x10e7fa 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[393, 483]
    (.letOp (n := 488) (.out 0x10e7fd (movR64R64Effect 0x10e7fd 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[486]
    (.letOp (n := 489) (.exec 0x10e7fd (fun s => s.RIP = 0x10e7fd) (movR64R64Effect 0x10e7fd 14 2) (Reg.operands [.gpr 2] [])) #v[486]
    (.letOp (n := 490) (.out 0x10e800 (movR64R64Effect 0x10e800 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[485]
    (.letOp (n := 491) (.exec 0x10e800 (fun s => s.RIP = 0x10e800) (movR64R64Effect 0x10e800 6 0) (Reg.operands [.gpr 0] [])) #v[485]
    (.letOp (n := 492) (.out 0x10e803 (movR64M64Effect 0x10e803 15 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 493) (.exec 0x10e803 (LoadPre 0x10e803 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e803 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e803 15 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 494) (.out 0x10e808 (movR64R64Effect 0x10e808 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[492]
    (.letOp (n := 495) (.exec 0x10e808 (fun s => s.RIP = 0x10e808) (movR64R64Effect 0x10e808 0 15) (Reg.operands [.gpr 15] [])) #v[492]
    (.letOp (n := 496) (.out 0x10e80b (mulM64Effect 0x10e80b 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[494, 65]
    (.letOp (n := 497) (.out 0x10e80b (mulM64Effect 0x10e80b 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[494, 65]
    (.letOp (n := 498) (.exec 0x10e80b (LoadPre 0x10e80b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e80b + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e80b 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[494, 65]
    (.letOp (n := 499) (.out 0x10e810 (movR64R64Effect 0x10e810 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[496]
    (.letOp (n := 500) (.exec 0x10e810 (fun s => s.RIP = 0x10e810) (movR64R64Effect 0x10e810 13 0) (Reg.operands [.gpr 0] [])) #v[496]
    (.letOp (n := 501) (.out 0x10e813 (addR64R64Effect 0x10e813 13 6) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[499, 490]
    (.letOp (n := 502) (.out 0x10e813 (addR64R64Effect 0x10e813 13 6) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 6] []) (.flag .CF)) #v[499, 490]
    (.letOp (n := 503) (.exec 0x10e813 (fun s => s.RIP = 0x10e813) (addR64R64Effect 0x10e813 13 6) (Reg.operands [.gpr 13, .gpr 6] [])) #v[499, 490]
    (.letOp (n := 504) (.out 0x10e816 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e816 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[488, 497, 502]
    (.letOp (n := 505) (.exec 0x10e816 (fun s => s.RIP = 0x10e816) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e816 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[488, 497, 502]
    (.letOp (n := 506) (.out 0x10e819 (addR64R64Effect 0x10e819 13 10) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 10] []) (.reg (.gpr 13))) #v[501, 424]
    (.letOp (n := 507) (.out 0x10e819 (addR64R64Effect 0x10e819 13 10) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 10] []) (.flag .CF)) #v[501, 424]
    (.letOp (n := 508) (.exec 0x10e819 (fun s => s.RIP = 0x10e819) (addR64R64Effect 0x10e819 13 10) (Reg.operands [.gpr 13, .gpr 10] [])) #v[501, 424]
    (.letOp (n := 509) (.out 0x10e81c (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e81c 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[504, 507]
    (.letOp (n := 510) (.exec 0x10e81c (fun s => s.RIP = 0x10e81c) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e81c 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[504, 507]
    (.letOp (n := 511) (.out 0x10e820 (movR64R64Effect 0x10e820 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[506]
    (.letOp (n := 512) (.exec 0x10e820 (fun s => s.RIP = 0x10e820) (movR64R64Effect 0x10e820 0 13) (Reg.operands [.gpr 13] [])) #v[506]
    (.letOp (n := 513) (.out 0x10e823 (andR64R64Effect 0x10e823 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[511, 478]
    (.letOp (n := 514) (.exec 0x10e823 (fun s => s.RIP = 0x10e823) (andR64R64Effect 0x10e823 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[511, 478]
    (.letOp (n := 515) (.out 0x10e826 (movR64Imm64Effect 0x10e826 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 516) (.exec 0x10e826 (fun s => s.RIP = 0x10e826) (movR64Imm64Effect 0x10e826 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (b_l10e4c0_11)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_10 : List UInt8 :=
  [0x48, 0x89, 0xC3, 0x49, 0x89, 0xD1, 0x48, 0x89, 0xF5, 0x49, 0x21, 0xF5, 0x4C, 0x89, 0x6C, 0x24,
    0x10, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x49, 0xF7, 0xE6, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xC6, 0x4C,
    0x8B, 0x7C, 0x24, 0x50, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0x64, 0x24, 0x40, 0x49, 0x89, 0xC5, 0x49,
    0x01, 0xF5, 0x49, 0x11, 0xD6, 0x4D, 0x01, 0xD5, 0x49, 0x83, 0xD6, 0x00, 0x4C, 0x89, 0xE8, 0x48,
    0x21, 0xE8, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00] ++ bytes_l10e4c0_11

theorem code_l10e4c0_10 : ∀ x ∈ codeRange 0x10e7e4 bytes_l10e4c0_10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe7e4 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_11

def b_l10e4c0_9 : Block Op Label signature Reg.count 428 :=
  .letOp (n := 428) (.out 0x10e794 (andR64R64Effect 0x10e794 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[419, 426]
    (.letOp (n := 429) (.exec 0x10e794 (fun s => s.RIP = 0x10e794) (andR64R64Effect 0x10e794 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[419, 426]
    (.letOp (n := 430) (.out 0x10e797 (movR64Imm64Effect 0x10e797 1 0x1000003d10) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 431) (.exec 0x10e797 (fun s => s.RIP = 0x10e797) (movR64Imm64Effect 0x10e797 1 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 432) (.out 0x10e7a1 (mulR64Effect 0x10e7a1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[430, 428]
    (.letOp (n := 433) (.out 0x10e7a1 (mulR64Effect 0x10e7a1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[430, 428]
    (.letOp (n := 434) (.exec 0x10e7a1 (fun s => s.RIP = 0x10e7a1) (mulR64Effect 0x10e7a1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[430, 428]
    (.letOp (n := 435) (.out 0x10e7a4 (addR64M64Effect 0x10e7a4 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[373, 65]
    (.letOp (n := 436) (.out 0x10e7a4 (addR64M64Effect 0x10e7a4 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 4] []) (.flag .CF)) #v[373, 65]
    (.letOp (n := 437) (.exec 0x10e7a4 (LoadPre 0x10e7a4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e7a4 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e7a4 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[373, 65]
    (.letOp (n := 438) (.out 0x10e7a9 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e7a9 8 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[371, 65, 436]
    (.letOp (n := 439) (.exec 0x10e7a9 (LoadPre 0x10e7a9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e7a9 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e7a9 8 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[371, 65, 436]
    (.letOp (n := 440) (.out 0x10e7ae (addR64R64Effect 0x10e7ae 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[435, 432]
    (.letOp (n := 441) (.out 0x10e7ae (addR64R64Effect 0x10e7ae 13 0) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 0] []) (.flag .CF)) #v[435, 432]
    (.letOp (n := 442) (.exec 0x10e7ae (fun s => s.RIP = 0x10e7ae) (addR64R64Effect 0x10e7ae 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[435, 432]
    (.letOp (n := 443) (.out 0x10e7b1 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e7b1 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[438, 433, 441]
    (.letOp (n := 444) (.exec 0x10e7b1 (fun s => s.RIP = 0x10e7b1) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e7b1 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[438, 433, 441]
    (.letOp (n := 445) (.out 0x10e7b4 (addR64R64Effect 0x10e7b4 13 11) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 11] []) (.reg (.gpr 13))) #v[440, 355]
    (.letOp (n := 446) (.out 0x10e7b4 (addR64R64Effect 0x10e7b4 13 11) (EffectPart.reads (.flag .CF) [.gpr 13, .gpr 11] []) (.flag .CF)) #v[440, 355]
    (.letOp (n := 447) (.exec 0x10e7b4 (fun s => s.RIP = 0x10e7b4) (addR64R64Effect 0x10e7b4 13 11) (Reg.operands [.gpr 13, .gpr 11] [])) #v[440, 355]
    (.letOp (n := 448) (.out 0x10e7b7 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e7b7 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[443, 446]
    (.letOp (n := 449) (.exec 0x10e7b7 (fun s => s.RIP = 0x10e7b7) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e7b7 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[443, 446]
    (.letOp (n := 450) (.out 0x10e7bb (shldR64R64Effect 0x10e7bb 5 8 13 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[448, 445]
    (.letOp (n := 451) (.exec 0x10e7bb (fun s => s.RIP = 0x10e7bb) (shldR64R64Effect 0x10e7bb 5 8 13 12) (Reg.operands [.gpr 8, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[448, 445]
    (.letOp (n := 452) (.out 0x10e7c0 (movR64R64Effect 0x10e7c0 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[402]
    (.letOp (n := 453) (.exec 0x10e7c0 (fun s => s.RIP = 0x10e7c0) (movR64R64Effect 0x10e7c0 0 3) (Reg.operands [.gpr 3] [])) #v[402]
    (.letOp (n := 454) (.out 0x10e7c3 (mulM64Effect 0x10e7c3 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[452, 65]
    (.letOp (n := 455) (.out 0x10e7c3 (mulM64Effect 0x10e7c3 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[452, 65]
    (.letOp (n := 456) (.exec 0x10e7c3 (LoadPre 0x10e7c3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e7c3 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10e7c3 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[452, 65]
    (.letOp (n := 457) (.exec 0x10e7c7 (StorePre 0x10e7c7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e7c7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e7c7 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[455, 65]
    (.letOp (n := 458) (.out 0x10e7cb (movR64R64Effect 0x10e7cb 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[454]
    (.letOp (n := 459) (.exec 0x10e7cb (fun s => s.RIP = 0x10e7cb) (movR64R64Effect 0x10e7cb 11 0) (Reg.operands [.gpr 0] [])) #v[454]
    (.letOp (n := 460) (.out 0x10e7ce (movR64M64Effect 0x10e7ce 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 461) (.exec 0x10e7ce (LoadPre 0x10e7ce (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e7ce + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e7ce 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 462) (.out 0x10e7d3 (mulM64Effect 0x10e7d3 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[460, 65]
    (.letOp (n := 463) (.out 0x10e7d3 (mulM64Effect 0x10e7d3 5 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[460, 65]
    (.letOp (n := 464) (.exec 0x10e7d3 (LoadPre 0x10e7d3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e7d3 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e7d3 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[460, 65]
    (.letOp (n := 465) (.out 0x10e7d8 (movR64R64Effect 0x10e7d8 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[463]
    (.letOp (n := 466) (.exec 0x10e7d8 (fun s => s.RIP = 0x10e7d8) (movR64R64Effect 0x10e7d8 12 2) (Reg.operands [.gpr 2] [])) #v[463]
    (.letOp (n := 467) (.out 0x10e7db (movR64R64Effect 0x10e7db 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[462]
    (.letOp (n := 468) (.exec 0x10e7db (fun s => s.RIP = 0x10e7db) (movR64R64Effect 0x10e7db 1 0) (Reg.operands [.gpr 0] [])) #v[462]
    (.letOp (n := 469) (.out 0x10e7de (movR64R64Effect 0x10e7de 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[265]
    (.letOp (n := 470) (.exec 0x10e7de (fun s => s.RIP = 0x10e7de) (movR64R64Effect 0x10e7de 0 5) (Reg.operands [.gpr 5] [])) #v[265]
    (.letOp (n := 471) (.out 0x10e7e1 (mulR64Effect 0x10e7e1 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[377, 469]
    (.letOp (n := 472) (.out 0x10e7e1 (mulR64Effect 0x10e7e1 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[377, 469]
    (.letOp (n := 473) (.exec 0x10e7e1 (fun s => s.RIP = 0x10e7e1) (mulR64Effect 0x10e7e1 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[377, 469]
    (b_l10e4c0_10))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_9 : List UInt8 :=
  [0x48, 0x21, 0xF0, 0x48, 0xB9, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x4C, 0x03, 0x6C, 0x24, 0x08, 0x4C, 0x13, 0x44, 0x24, 0x10, 0x49, 0x01, 0xC5, 0x49, 0x11, 0xD0,
    0x4D, 0x01, 0xDD, 0x49, 0x83, 0xD0, 0x00, 0x4D, 0x0F, 0xA4, 0xE8, 0x0C, 0x48, 0x89, 0xD8, 0x48,
    0xF7, 0x24, 0x24, 0x48, 0x89, 0x14, 0x24, 0x49, 0x89, 0xC3, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48,
    0xF7, 0x64, 0x24, 0x20, 0x49, 0x89, 0xD4, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE7] ++ bytes_l10e4c0_10

theorem code_l10e4c0_9 : ∀ x ∈ codeRange 0x10e794 bytes_l10e4c0_9, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe794 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_10

def b_l10e4c0_8 : Block Op Label signature Reg.count 384 :=
  .letOp (n := 384) (.out 0x10e73f (movR64R64Effect 0x10e73f 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[380]
    (.letOp (n := 385) (.exec 0x10e73f (fun s => s.RIP = 0x10e73f) (movR64R64Effect 0x10e73f 6 2) (Reg.operands [.gpr 2] [])) #v[380]
    (.letOp (n := 386) (.out 0x10e742 (movR64Imm64Effect 0x10e742 0 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 387) (.exec 0x10e742 (fun s => s.RIP = 0x10e742) (movR64Imm64Effect 0x10e742 0 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 388) (.out 0x10e74c (andR64R64Effect 0x10e74c 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[357, 386]
    (.letOp (n := 389) (.exec 0x10e74c (fun s => s.RIP = 0x10e74c) (andR64R64Effect 0x10e74c 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[357, 386]
    (.letOp (n := 390) (.exec 0x10e74f (StorePre 0x10e74f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e74f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e74f 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[388, 65]
    (.letOp (n := 391) (.out 0x10e754 (movR64R64Effect 0x10e754 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[284]
    (.letOp (n := 392) (.exec 0x10e754 (fun s => s.RIP = 0x10e754) (movR64R64Effect 0x10e754 0 14) (Reg.operands [.gpr 14] [])) #v[284]
    (.letOp (n := 393) (.out 0x10e757 (movR64M64Effect 0x10e757 14 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 394) (.exec 0x10e757 (LoadPre 0x10e757 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e757 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e757 14 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 395) (.out 0x10e75c (mulR64Effect 0x10e75c 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[393, 391]
    (.letOp (n := 396) (.out 0x10e75c (mulR64Effect 0x10e75c 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[393, 391]
    (.letOp (n := 397) (.exec 0x10e75c (fun s => s.RIP = 0x10e75c) (mulR64Effect 0x10e75c 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[393, 391]
    (.letOp (n := 398) (.out 0x10e75f (movR64R64Effect 0x10e75f 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[396]
    (.letOp (n := 399) (.exec 0x10e75f (fun s => s.RIP = 0x10e75f) (movR64R64Effect 0x10e75f 10 2) (Reg.operands [.gpr 2] [])) #v[396]
    (.letOp (n := 400) (.out 0x10e762 (movR64R64Effect 0x10e762 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[395]
    (.letOp (n := 401) (.exec 0x10e762 (fun s => s.RIP = 0x10e762) (movR64R64Effect 0x10e762 12 0) (Reg.operands [.gpr 0] [])) #v[395]
    (.letOp (n := 402) (.out 0x10e765 (movR64M64Effect 0x10e765 3 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 403) (.exec 0x10e765 (LoadPre 0x10e765 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e765 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e765 3 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 404) (.out 0x10e76a (movR64R64Effect 0x10e76a 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[402]
    (.letOp (n := 405) (.exec 0x10e76a (fun s => s.RIP = 0x10e76a) (movR64R64Effect 0x10e76a 0 3) (Reg.operands [.gpr 3] [])) #v[402]
    (.letOp (n := 406) (.out 0x10e76d (mulM64Effect 0x10e76d 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[404, 65]
    (.letOp (n := 407) (.out 0x10e76d (mulM64Effect 0x10e76d 5 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[404, 65]
    (.letOp (n := 408) (.exec 0x10e76d (LoadPre 0x10e76d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e76d + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e76d 5 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[404, 65]
    (.letOp (n := 409) (.out 0x10e772 (addR64R64Effect 0x10e772 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[406, 400]
    (.letOp (n := 410) (.out 0x10e772 (addR64R64Effect 0x10e772 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[406, 400]
    (.letOp (n := 411) (.exec 0x10e772 (fun s => s.RIP = 0x10e772) (addR64R64Effect 0x10e772 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[406, 400]
    (.letOp (n := 412) (.out 0x10e775 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e775 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[398, 407, 410]
    (.letOp (n := 413) (.exec 0x10e775 (fun s => s.RIP = 0x10e775) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e775 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[398, 407, 410]
    (.letOp (n := 414) (.out 0x10e778 (addR64R64Effect 0x10e778 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[409, 382]
    (.letOp (n := 415) (.out 0x10e778 (addR64R64Effect 0x10e778 0 1) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 1] []) (.flag .CF)) #v[409, 382]
    (.letOp (n := 416) (.exec 0x10e778 (fun s => s.RIP = 0x10e778) (addR64R64Effect 0x10e778 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[409, 382]
    (.letOp (n := 417) (.out 0x10e77b (atFlags StatusFlags.CF (adcR64R64Effect 0x10e77b 10 6)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[412, 384, 415]
    (.letOp (n := 418) (.exec 0x10e77b (fun s => s.RIP = 0x10e77b) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e77b 10 6)) (Reg.operands [.gpr 10, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[412, 384, 415]
    (.letOp (n := 419) (.out 0x10e77e (addR64R64Effect 0x10e77e 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 9] []) (.reg (.gpr 0))) #v[414, 333]
    (.letOp (n := 420) (.out 0x10e77e (addR64R64Effect 0x10e77e 0 9) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 9] []) (.flag .CF)) #v[414, 333]
    (.letOp (n := 421) (.exec 0x10e77e (fun s => s.RIP = 0x10e77e) (addR64R64Effect 0x10e77e 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[414, 333]
    (.letOp (n := 422) (.out 0x10e781 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e781 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[417, 420]
    (.letOp (n := 423) (.exec 0x10e781 (fun s => s.RIP = 0x10e781) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e781 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[417, 420]
    (.letOp (n := 424) (.out 0x10e785 (shldR64R64Effect 0x10e785 5 10 0 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[422, 419]
    (.letOp (n := 425) (.exec 0x10e785 (fun s => s.RIP = 0x10e785) (shldR64R64Effect 0x10e785 5 10 0 12) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[422, 419]
    (.letOp (n := 426) (.out 0x10e78a (movR64Imm64Effect 0x10e78a 6 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 427) (.exec 0x10e78a (fun s => s.RIP = 0x10e78a) (movR64Imm64Effect 0x10e78a 6 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l10e4c0_9))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_8 : List UInt8 :=
  [0x48, 0x89, 0xD6, 0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC2,
    0x4C, 0x89, 0x54, 0x24, 0x18, 0x4C, 0x89, 0xF0, 0x4C, 0x8B, 0x74, 0x24, 0x70, 0x49, 0xF7, 0xE6,
    0x49, 0x89, 0xD2, 0x49, 0x89, 0xC4, 0x48, 0x8B, 0x5C, 0x24, 0x30, 0x48, 0x89, 0xD8, 0x48, 0xF7,
    0x64, 0x24, 0x40, 0x4C, 0x01, 0xE0, 0x49, 0x11, 0xD2, 0x48, 0x01, 0xC8, 0x49, 0x11, 0xF2, 0x4C,
    0x01, 0xC8, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xC2, 0x0C, 0x48, 0xBE, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00] ++ bytes_l10e4c0_9

theorem code_l10e4c0_8 : ∀ x ∈ codeRange 0x10e73f bytes_l10e4c0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe73f 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_9

def b_l10e4c0_7 : Block Op Label signature Reg.count 341 :=
  .letOp (n := 341) (.out 0x10e6ed (orR64R64Effect 0x10e6ed 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 3] []) (.reg (.gpr 0))) #v[339, 295]
    (.letOp (n := 342) (.exec 0x10e6ed (fun s => s.RIP = 0x10e6ed) (orR64R64Effect 0x10e6ed 0 3) (Reg.operands [.gpr 0, .gpr 3] [])) #v[339, 295]
    (.letOp (n := 343) (.out 0x10e6f0 (movR64Imm64Effect 0x10e6f0 1 0x1000003d1) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 344) (.exec 0x10e6f0 (fun s => s.RIP = 0x10e6f0) (movR64Imm64Effect 0x10e6f0 1 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 345) (.out 0x10e6fa (mulR64Effect 0x10e6fa 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[343, 341]
    (.letOp (n := 346) (.out 0x10e6fa (mulR64Effect 0x10e6fa 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[343, 341]
    (.letOp (n := 347) (.exec 0x10e6fa (fun s => s.RIP = 0x10e6fa) (mulR64Effect 0x10e6fa 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[343, 341]
    (.letOp (n := 348) (.out 0x10e6fd (movR64R64Effect 0x10e6fd 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[346]
    (.letOp (n := 349) (.exec 0x10e6fd (fun s => s.RIP = 0x10e6fd) (movR64R64Effect 0x10e6fd 11 2) (Reg.operands [.gpr 2] [])) #v[346]
    (.letOp (n := 350) (.out 0x10e700 (addR64M64Effect 0x10e700 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[345, 65]
    (.letOp (n := 351) (.out 0x10e700 (addR64M64Effect 0x10e700 0 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 4] []) (.flag .CF)) #v[345, 65]
    (.letOp (n := 352) (.exec 0x10e700 (LoadPre 0x10e700 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e700 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e700 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[345, 65]
    (.letOp (n := 353) (.out 0x10e705 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e705 11 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 11))) #v[348, 65, 351]
    (.letOp (n := 354) (.exec 0x10e705 (LoadPre 0x10e705 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e705 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e705 11 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[348, 65, 351]
    (.letOp (n := 355) (.out 0x10e70a (shldR64R64Effect 0x10e70a 5 11 0 12) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[353, 350]
    (.letOp (n := 356) (.exec 0x10e70a (fun s => s.RIP = 0x10e70a) (shldR64R64Effect 0x10e70a 5 11 0 12) (Reg.operands [.gpr 11, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[353, 350]
    (.letOp (n := 357) (.out 0x10e70f (movR64R64Effect 0x10e70f 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[350]
    (.letOp (n := 358) (.exec 0x10e70f (fun s => s.RIP = 0x10e70f) (movR64R64Effect 0x10e70f 10 0) (Reg.operands [.gpr 0] [])) #v[350]
    (.letOp (n := 359) (.out 0x10e712 (movR64R64Effect 0x10e712 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[306]
    (.letOp (n := 360) (.exec 0x10e712 (fun s => s.RIP = 0x10e712) (movR64R64Effect 0x10e712 0 13) (Reg.operands [.gpr 13] [])) #v[306]
    (.letOp (n := 361) (.out 0x10e715 (mulM64Effect 0x10e715 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[359, 65]
    (.letOp (n := 362) (.out 0x10e715 (mulM64Effect 0x10e715 4 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[359, 65]
    (.letOp (n := 363) (.exec 0x10e715 (LoadPre 0x10e715 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e715 + BitVec.ofNat 64 4)) 8) (mulM64Effect 0x10e715 4 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[359, 65]
    (.letOp (n := 364) (.exec 0x10e719 (StorePre 0x10e719 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e719 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e719 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[362, 65]
    (.letOp (n := 365) (.exec 0x10e71e (StorePre 0x10e71e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e71e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e71e 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[361, 65]
    (.letOp (n := 366) (.out 0x10e723 (movR64R64Effect 0x10e723 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[265]
    (.letOp (n := 367) (.exec 0x10e723 (fun s => s.RIP = 0x10e723) (movR64R64Effect 0x10e723 0 5) (Reg.operands [.gpr 5] [])) #v[265]
    (.letOp (n := 368) (.out 0x10e726 (mulR64Effect 0x10e726 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[276, 366]
    (.letOp (n := 369) (.out 0x10e726 (mulR64Effect 0x10e726 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[276, 366]
    (.letOp (n := 370) (.exec 0x10e726 (fun s => s.RIP = 0x10e726) (mulR64Effect 0x10e726 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[276, 366]
    (.letOp (n := 371) (.out 0x10e729 (movR64R64Effect 0x10e729 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[369]
    (.letOp (n := 372) (.exec 0x10e729 (fun s => s.RIP = 0x10e729) (movR64R64Effect 0x10e729 8 2) (Reg.operands [.gpr 2] [])) #v[369]
    (.letOp (n := 373) (.out 0x10e72c (movR64R64Effect 0x10e72c 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[368]
    (.letOp (n := 374) (.exec 0x10e72c (fun s => s.RIP = 0x10e72c) (movR64R64Effect 0x10e72c 13 0) (Reg.operands [.gpr 0] [])) #v[368]
    (.letOp (n := 375) (.out 0x10e72f (movR64M64Effect 0x10e72f 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 376) (.exec 0x10e72f (LoadPre 0x10e72f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e72f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e72f 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 377) (.out 0x10e734 (movR64M64Effect 0x10e734 15 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 378) (.exec 0x10e734 (LoadPre 0x10e734 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e734 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e734 15 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 379) (.out 0x10e739 (mulR64Effect 0x10e739 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[377, 375]
    (.letOp (n := 380) (.out 0x10e739 (mulR64Effect 0x10e739 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[377, 375]
    (.letOp (n := 381) (.exec 0x10e739 (fun s => s.RIP = 0x10e739) (mulR64Effect 0x10e739 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[377, 375]
    (.letOp (n := 382) (.out 0x10e73c (movR64R64Effect 0x10e73c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[379]
    (.letOp (n := 383) (.exec 0x10e73c (fun s => s.RIP = 0x10e73c) (movR64R64Effect 0x10e73c 1 0) (Reg.operands [.gpr 0] [])) #v[379]
    (b_l10e4c0_8)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_7 : List UInt8 :=
  [0x48, 0x09, 0xD8, 0x48, 0xB9, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE1,
    0x49, 0x89, 0xD3, 0x48, 0x03, 0x44, 0x24, 0x10, 0x4C, 0x13, 0x5C, 0x24, 0x18, 0x49, 0x0F, 0xA4,
    0xC3, 0x0C, 0x49, 0x89, 0xC2, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0x24, 0x24, 0x48, 0x89, 0x54, 0x24,
    0x10, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xE8, 0x49, 0xF7, 0xE0, 0x49, 0x89, 0xD0, 0x49,
    0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x7C, 0x24, 0x68, 0x49, 0xF7, 0xE7, 0x48,
    0x89, 0xC1] ++ bytes_l10e4c0_8

theorem code_l10e4c0_7 : ∀ x ∈ codeRange 0x10e6ed bytes_l10e4c0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe6ed 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_8

def b_l10e4c0_6 : Block Op Label signature Reg.count 295 :=
  .letOp (n := 295) (.out 0x10e69e (andR32Imm8Effect 0x10e69e 3 3 0xf) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[263]
    (.letOp (n := 296) (.exec 0x10e69e (fun s => s.RIP = 0x10e69e) (andR32Imm8Effect 0x10e69e 3 3 0xf) (Reg.operands [.gpr 3] [])) #v[263]
    (.letOp (n := 297) (.out 0x10e6a1 (movR64M64Effect 0x10e6a1 0 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 298) (.exec 0x10e6a1 (LoadPre 0x10e6a1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e6a1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e6a1 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 299) (.out 0x10e6a6 (mulM64Effect 0x10e6a6 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[297, 65]
    (.letOp (n := 300) (.out 0x10e6a6 (mulM64Effect 0x10e6a6 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 4] []) (.reg (.gpr 2))) #v[297, 65]
    (.letOp (n := 301) (.exec 0x10e6a6 (LoadPre 0x10e6a6 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e6a6 + BitVec.ofNat 64 5)) 8) (mulM64Effect 0x10e6a6 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[297, 65]
    (.letOp (n := 302) (.out 0x10e6ab (movR64R64Effect 0x10e6ab 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[300]
    (.letOp (n := 303) (.exec 0x10e6ab (fun s => s.RIP = 0x10e6ab) (movR64R64Effect 0x10e6ab 9 2) (Reg.operands [.gpr 2] [])) #v[300]
    (.letOp (n := 304) (.out 0x10e6ae (movR64R64Effect 0x10e6ae 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[299]
    (.letOp (n := 305) (.exec 0x10e6ae (fun s => s.RIP = 0x10e6ae) (movR64R64Effect 0x10e6ae 12 0) (Reg.operands [.gpr 0] [])) #v[299]
    (.letOp (n := 306) (.out 0x10e6b1 (movR64M64Effect 0x10e6b1 13 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[65]
    (.letOp (n := 307) (.exec 0x10e6b1 (LoadPre 0x10e6b1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e6b1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e6b1 13 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 308) (.out 0x10e6b6 (movR64R64Effect 0x10e6b6 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[306]
    (.letOp (n := 309) (.exec 0x10e6b6 (fun s => s.RIP = 0x10e6b6) (movR64R64Effect 0x10e6b6 0 13) (Reg.operands [.gpr 13] [])) #v[306]
    (.letOp (n := 310) (.out 0x10e6b9 (mulR64Effect 0x10e6b9 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[214, 308]
    (.letOp (n := 311) (.out 0x10e6b9 (mulR64Effect 0x10e6b9 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[214, 308]
    (.letOp (n := 312) (.exec 0x10e6b9 (fun s => s.RIP = 0x10e6b9) (mulR64Effect 0x10e6b9 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[214, 308]
    (.letOp (n := 313) (.out 0x10e6bc (addR64R64Effect 0x10e6bc 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[310, 304]
    (.letOp (n := 314) (.out 0x10e6bc (addR64R64Effect 0x10e6bc 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[310, 304]
    (.letOp (n := 315) (.exec 0x10e6bc (fun s => s.RIP = 0x10e6bc) (addR64R64Effect 0x10e6bc 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[310, 304]
    (.letOp (n := 316) (.out 0x10e6bf (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6bf 9 2)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[302, 311, 314]
    (.letOp (n := 317) (.exec 0x10e6bf (fun s => s.RIP = 0x10e6bf) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6bf 9 2)) (Reg.operands [.gpr 9, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[302, 311, 314]
    (.letOp (n := 318) (.out 0x10e6c2 (addR64R64Effect 0x10e6c2 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[313, 291]
    (.letOp (n := 319) (.out 0x10e6c2 (addR64R64Effect 0x10e6c2 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[313, 291]
    (.letOp (n := 320) (.exec 0x10e6c2 (fun s => s.RIP = 0x10e6c2) (addR64R64Effect 0x10e6c2 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[313, 291]
    (.letOp (n := 321) (.out 0x10e6c5 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6c5 9 15)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[316, 293, 319]
    (.letOp (n := 322) (.exec 0x10e6c5 (fun s => s.RIP = 0x10e6c5) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e6c5 9 15)) (Reg.operands [.gpr 9, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[316, 293, 319]
    (.letOp (n := 323) (.out 0x10e6c8 (addR64R64Effect 0x10e6c8 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[318, 282]
    (.letOp (n := 324) (.out 0x10e6c8 (addR64R64Effect 0x10e6c8 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[318, 282]
    (.letOp (n := 325) (.exec 0x10e6c8 (fun s => s.RIP = 0x10e6c8) (addR64R64Effect 0x10e6c8 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[318, 282]
    (.letOp (n := 326) (.out 0x10e6cb (atFlags StatusFlags.CF (adcR64M64Effect 0x10e6cb 9 (.sib 4 none 0 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 9))) #v[321, 65, 324]
    (.letOp (n := 327) (.exec 0x10e6cb (LoadPre 0x10e6cb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e6cb + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e6cb 9 (.sib 4 none 0 (.d8 0x8)))) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[321, 65, 324]
    (.letOp (n := 328) (.out 0x10e6d0 (addR64R64Effect 0x10e6d0 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[323, 261]
    (.letOp (n := 329) (.out 0x10e6d0 (addR64R64Effect 0x10e6d0 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[323, 261]
    (.letOp (n := 330) (.exec 0x10e6d0 (fun s => s.RIP = 0x10e6d0) (addR64R64Effect 0x10e6d0 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[323, 261]
    (.letOp (n := 331) (.out 0x10e6d3 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e6d3 9 0x0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[326, 329]
    (.letOp (n := 332) (.exec 0x10e6d3 (fun s => s.RIP = 0x10e6d3) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e6d3 9 0x0)) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[326, 329]
    (.letOp (n := 333) (.out 0x10e6d7 (shldR64R64Effect 0x10e6d7 5 9 0 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[331, 328]
    (.letOp (n := 334) (.exec 0x10e6d7 (fun s => s.RIP = 0x10e6d7) (shldR64R64Effect 0x10e6d7 5 9 0 12) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[331, 328]
    (.letOp (n := 335) (.out 0x10e6dc (shlR64Effect 0x10e6dc 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[328]
    (.letOp (n := 336) (.exec 0x10e6dc (fun s => s.RIP = 0x10e6dc) (shlR64Effect 0x10e6dc 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[328]
    (.letOp (n := 337) (.out 0x10e6e0 (movR64Imm64Effect 0x10e6e0 1 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 338) (.exec 0x10e6e0 (fun s => s.RIP = 0x10e6e0) (movR64Imm64Effect 0x10e6e0 1 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 339) (.out 0x10e6ea (andR64R64Effect 0x10e6ea 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[335, 337]
    (.letOp (n := 340) (.exec 0x10e6ea (fun s => s.RIP = 0x10e6ea) (andR64R64Effect 0x10e6ea 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[335, 337]
    (b_l10e4c0_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_6 : List UInt8 :=
  [0x83, 0xE3, 0x0F, 0x48, 0x8B, 0x44, 0x24, 0x30, 0x48, 0xF7, 0x64, 0x24, 0x70, 0x49, 0x89, 0xD1,
    0x49, 0x89, 0xC4, 0x4C, 0x8B, 0x6C, 0x24, 0x48, 0x4C, 0x89, 0xE8, 0x48, 0xF7, 0xE1, 0x4C, 0x01,
    0xE0, 0x49, 0x11, 0xD1, 0x48, 0x01, 0xF0, 0x4D, 0x11, 0xF9, 0x4C, 0x01, 0xD8, 0x4C, 0x13, 0x4C,
    0x24, 0x08, 0x4C, 0x01, 0xD0, 0x49, 0x83, 0xD1, 0x00, 0x49, 0x0F, 0xA4, 0xC1, 0x0C, 0x48, 0xC1,
    0xE0, 0x04, 0x48, 0xB9, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xC8] ++ bytes_l10e4c0_7

theorem code_l10e4c0_6 : ∀ x ∈ codeRange 0x10e69e bytes_l10e4c0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe69e 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_7

def b_l10e4c0_5 : Block Op Label signature Reg.count 255 :=
  .letOp (n := 255) (.out 0x10e650 (addR64R64Effect 0x10e650 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[250, 172]
    (.letOp (n := 256) (.out 0x10e650 (addR64R64Effect 0x10e650 3 8) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 8] []) (.flag .CF)) #v[250, 172]
    (.letOp (n := 257) (.exec 0x10e650 (fun s => s.RIP = 0x10e650) (addR64R64Effect 0x10e650 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[250, 172]
    (.letOp (n := 258) (.exec 0x10e653 (StorePre 0x10e653 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e653 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e653 3 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[255, 65]
    (.letOp (n := 259) (.out 0x10e658 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e658 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[253, 256]
    (.letOp (n := 260) (.exec 0x10e658 (fun s => s.RIP = 0x10e658) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x10e658 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[253, 256]
    (.letOp (n := 261) (.out 0x10e65c (shldR64R64Effect 0x10e65c 5 10 3 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[259, 255]
    (.letOp (n := 262) (.exec 0x10e65c (fun s => s.RIP = 0x10e65c) (shldR64R64Effect 0x10e65c 5 10 3 12) (Reg.operands [.gpr 10, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[259, 255]
    (.letOp (n := 263) (.out 0x10e661 (shrR64Effect 0x10e661 4 3 48) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[255]
    (.letOp (n := 264) (.exec 0x10e661 (fun s => s.RIP = 0x10e661) (shrR64Effect 0x10e661 4 3 48) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[255]
    (.letOp (n := 265) (.out 0x10e665 (movR64R64Effect 0x10e665 5 15) (EffectPart.reads (.reg (.gpr 5)) [.gpr 15] []) (.reg (.gpr 5))) #v[210]
    (.letOp (n := 266) (.exec 0x10e665 (fun s => s.RIP = 0x10e665) (movR64R64Effect 0x10e665 5 15) (Reg.operands [.gpr 15] [])) #v[210]
    (.letOp (n := 267) (.out 0x10e668 (movR64R64Effect 0x10e668 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[210]
    (.letOp (n := 268) (.exec 0x10e668 (fun s => s.RIP = 0x10e668) (movR64R64Effect 0x10e668 0 15) (Reg.operands [.gpr 15] [])) #v[210]
    (.letOp (n := 269) (.out 0x10e66b (mulR64Effect 0x10e66b 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[176, 267]
    (.letOp (n := 270) (.out 0x10e66b (mulR64Effect 0x10e66b 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[176, 267]
    (.letOp (n := 271) (.exec 0x10e66b (fun s => s.RIP = 0x10e66b) (mulR64Effect 0x10e66b 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[176, 267]
    (.letOp (n := 272) (.exec 0x10e66e (StorePre 0x10e66e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e66e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e66e 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[270, 65]
    (.letOp (n := 273) (.exec 0x10e673 (StorePre 0x10e673 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e673 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e673 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[269, 65]
    (.letOp (n := 274) (.out 0x10e678 (movR64M64Effect 0x10e678 0 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 275) (.exec 0x10e678 (LoadPre 0x10e678 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e678 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e678 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 276) (.out 0x10e67d (movR64M64Effect 0x10e67d 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[65]
    (.letOp (n := 277) (.exec 0x10e67d (LoadPre 0x10e67d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e67d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e67d 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 278) (.out 0x10e682 (mulR64Effect 0x10e682 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[276, 274]
    (.letOp (n := 279) (.out 0x10e682 (mulR64Effect 0x10e682 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[276, 274]
    (.letOp (n := 280) (.exec 0x10e682 (fun s => s.RIP = 0x10e682) (mulR64Effect 0x10e682 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[276, 274]
    (.letOp (n := 281) (.exec 0x10e685 (StorePre 0x10e685 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e685 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e685 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[279, 65]
    (.letOp (n := 282) (.out 0x10e68a (movR64R64Effect 0x10e68a 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[278]
    (.letOp (n := 283) (.exec 0x10e68a (fun s => s.RIP = 0x10e68a) (movR64R64Effect 0x10e68a 11 0) (Reg.operands [.gpr 0] [])) #v[278]
    (.letOp (n := 284) (.out 0x10e68d (movR64M64Effect 0x10e68d 14 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 285) (.exec 0x10e68d (LoadPre 0x10e68d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e68d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e68d 14 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 286) (.out 0x10e692 (movR64R64Effect 0x10e692 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[284]
    (.letOp (n := 287) (.exec 0x10e692 (fun s => s.RIP = 0x10e692) (movR64R64Effect 0x10e692 0 14) (Reg.operands [.gpr 14] [])) #v[284]
    (.letOp (n := 288) (.out 0x10e695 (mulR64Effect 0x10e695 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[192, 286]
    (.letOp (n := 289) (.out 0x10e695 (mulR64Effect 0x10e695 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[192, 286]
    (.letOp (n := 290) (.exec 0x10e695 (fun s => s.RIP = 0x10e695) (mulR64Effect 0x10e695 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[192, 286]
    (.letOp (n := 291) (.out 0x10e698 (movR64R64Effect 0x10e698 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[288]
    (.letOp (n := 292) (.exec 0x10e698 (fun s => s.RIP = 0x10e698) (movR64R64Effect 0x10e698 6 0) (Reg.operands [.gpr 0] [])) #v[288]
    (.letOp (n := 293) (.out 0x10e69b (movR64R64Effect 0x10e69b 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[289]
    (.letOp (n := 294) (.exec 0x10e69b (fun s => s.RIP = 0x10e69b) (movR64R64Effect 0x10e69b 15 2) (Reg.operands [.gpr 2] [])) #v[289]
    (b_l10e4c0_6))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_5 : List UInt8 :=
  [0x4C, 0x01, 0xC3, 0x48, 0x89, 0x5C, 0x24, 0x28, 0x49, 0x83, 0xD2, 0x00, 0x49, 0x0F, 0xA4, 0xDA,
    0x0C, 0x48, 0xC1, 0xEB, 0x30, 0x4C, 0x89, 0xFD, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE6, 0x48, 0x89,
    0x54, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x8B, 0x44, 0x24, 0x38, 0x4C, 0x8B, 0x44,
    0x24, 0x20, 0x49, 0xF7, 0xE0, 0x48, 0x89, 0x54, 0x24, 0x08, 0x49, 0x89, 0xC3, 0x4C, 0x8B, 0x74,
    0x24, 0x50, 0x4C, 0x89, 0xF0, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD7] ++ bytes_l10e4c0_6

theorem code_l10e4c0_5 : ∀ x ∈ codeRange 0x10e650 bytes_l10e4c0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe650 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_6

def b_l10e4c0_4 : Block Op Label signature Reg.count 208 :=
  .letOp (n := 208) (.out 0x10e5fe (movR64R64Effect 0x10e5fe 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[203]
    (.letOp (n := 209) (.exec 0x10e5fe (fun s => s.RIP = 0x10e5fe) (movR64R64Effect 0x10e5fe 11 0) (Reg.operands [.gpr 0] [])) #v[203]
    (.letOp (n := 210) (.out 0x10e601 (movR64M64Effect 0x10e601 15 (.sib 4 none 0 (.d32 0x80))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 211) (.exec 0x10e601 (LoadPre 0x10e601 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e601 + BitVec.ofNat 64 8)) 8) (movR64M64Effect 0x10e601 15 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 212) (.out 0x10e609 (movR64R64Effect 0x10e609 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[210]
    (.letOp (n := 213) (.exec 0x10e609 (fun s => s.RIP = 0x10e609) (movR64R64Effect 0x10e609 0 15) (Reg.operands [.gpr 15] [])) #v[210]
    (.letOp (n := 214) (.out 0x10e60c (movR64M64Effect 0x10e60c 1 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 215) (.exec 0x10e60c (LoadPre 0x10e60c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e60c + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e60c 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 216) (.out 0x10e611 (mulR64Effect 0x10e611 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[214, 212]
    (.letOp (n := 217) (.out 0x10e611 (mulR64Effect 0x10e611 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[214, 212]
    (.letOp (n := 218) (.exec 0x10e611 (fun s => s.RIP = 0x10e611) (mulR64Effect 0x10e611 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[214, 212]
    (.letOp (n := 219) (.out 0x10e614 (movR64R64Effect 0x10e614 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[217]
    (.letOp (n := 220) (.exec 0x10e614 (fun s => s.RIP = 0x10e614) (movR64R64Effect 0x10e614 10 2) (Reg.operands [.gpr 2] [])) #v[217]
    (.letOp (n := 221) (.out 0x10e617 (movR64R64Effect 0x10e617 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[216]
    (.letOp (n := 222) (.exec 0x10e617 (fun s => s.RIP = 0x10e617) (movR64R64Effect 0x10e617 3 0) (Reg.operands [.gpr 0] [])) #v[216]
    (.letOp (n := 223) (.out 0x10e61a (movR64R64Effect 0x10e61a 0 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[170]
    (.letOp (n := 224) (.exec 0x10e61a (fun s => s.RIP = 0x10e61a) (movR64R64Effect 0x10e61a 0 9) (Reg.operands [.gpr 9] [])) #v[170]
    (.letOp (n := 225) (.out 0x10e61d (movR64Imm64Effect 0x10e61d 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 226) (.exec 0x10e61d (fun s => s.RIP = 0x10e61d) (movR64Imm64Effect 0x10e61d 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 227) (.out 0x10e627 (mulR64Effect 0x10e627 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[225, 223]
    (.letOp (n := 228) (.out 0x10e627 (mulR64Effect 0x10e627 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[225, 223]
    (.letOp (n := 229) (.exec 0x10e627 (fun s => s.RIP = 0x10e627) (mulR64Effect 0x10e627 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[225, 223]
    (.letOp (n := 230) (.out 0x10e62a (addR64R64Effect 0x10e62a 3 11) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 11] []) (.reg (.gpr 3))) #v[221, 208]
    (.letOp (n := 231) (.out 0x10e62a (addR64R64Effect 0x10e62a 3 11) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 11] []) (.flag .CF)) #v[221, 208]
    (.letOp (n := 232) (.exec 0x10e62a (fun s => s.RIP = 0x10e62a) (addR64R64Effect 0x10e62a 3 11) (Reg.operands [.gpr 3, .gpr 11] [])) #v[221, 208]
    (.letOp (n := 233) (.out 0x10e62d (atFlags StatusFlags.CF (adcR64R64Effect 0x10e62d 10 5)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[219, 206, 231]
    (.letOp (n := 234) (.exec 0x10e62d (fun s => s.RIP = 0x10e62d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e62d 10 5)) (Reg.operands [.gpr 10, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[219, 206, 231]
    (.letOp (n := 235) (.out 0x10e630 (addR64R64Effect 0x10e630 3 13) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 13] []) (.reg (.gpr 3))) #v[230, 199]
    (.letOp (n := 236) (.out 0x10e630 (addR64R64Effect 0x10e630 3 13) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 13] []) (.flag .CF)) #v[230, 199]
    (.letOp (n := 237) (.exec 0x10e630 (fun s => s.RIP = 0x10e630) (addR64R64Effect 0x10e630 3 13) (Reg.operands [.gpr 3, .gpr 13] [])) #v[230, 199]
    (.letOp (n := 238) (.out 0x10e633 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e633 10 12)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[233, 197, 236]
    (.letOp (n := 239) (.exec 0x10e633 (fun s => s.RIP = 0x10e633) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e633 10 12)) (Reg.operands [.gpr 10, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 197, 236]
    (.letOp (n := 240) (.out 0x10e636 (addR64M64Effect 0x10e636 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[235, 65]
    (.letOp (n := 241) (.out 0x10e636 (addR64M64Effect 0x10e636 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[235, 65]
    (.letOp (n := 242) (.exec 0x10e636 (LoadPre 0x10e636 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e636 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e636 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[235, 65]
    (.letOp (n := 243) (.out 0x10e63b (atFlags StatusFlags.CF (adcR64M64Effect 0x10e63b 10 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[238, 65, 241]
    (.letOp (n := 244) (.exec 0x10e63b (LoadPre 0x10e63b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e63b + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e63b 10 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[238, 65, 241]
    (.letOp (n := 245) (.out 0x10e640 (addR64M64Effect 0x10e640 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[240, 65]
    (.letOp (n := 246) (.out 0x10e640 (addR64M64Effect 0x10e640 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 4] []) (.flag .CF)) #v[240, 65]
    (.letOp (n := 247) (.exec 0x10e640 (LoadPre 0x10e640 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e640 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e640 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 248) (.out 0x10e645 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e645 10 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 10))) #v[243, 65, 246]
    (.letOp (n := 249) (.exec 0x10e645 (LoadPre 0x10e645 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e645 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e645 10 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[243, 65, 246]
    (.letOp (n := 250) (.out 0x10e64a (addR64R64Effect 0x10e64a 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[245, 227]
    (.letOp (n := 251) (.out 0x10e64a (addR64R64Effect 0x10e64a 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[245, 227]
    (.letOp (n := 252) (.exec 0x10e64a (fun s => s.RIP = 0x10e64a) (addR64R64Effect 0x10e64a 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[245, 227]
    (.letOp (n := 253) (.out 0x10e64d (atFlags StatusFlags.CF (adcR64R64Effect 0x10e64d 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[248, 228, 251]
    (.letOp (n := 254) (.exec 0x10e64d (fun s => s.RIP = 0x10e64d) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e64d 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[248, 228, 251]
    (b_l10e4c0_5)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_4 : List UInt8 :=
  [0x49, 0x89, 0xC3, 0x4C, 0x8B, 0xBC, 0x24, 0x80, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF8, 0x48, 0x8B,
    0x4C, 0x24, 0x40, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD2, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xC8, 0x48,
    0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4C, 0x01, 0xDB, 0x49,
    0x11, 0xEA, 0x4C, 0x01, 0xEB, 0x4D, 0x11, 0xE2, 0x48, 0x03, 0x5C, 0x24, 0x08, 0x4C, 0x13, 0x54,
    0x24, 0x10, 0x48, 0x03, 0x5C, 0x24, 0x18, 0x4C, 0x13, 0x54, 0x24, 0x28, 0x48, 0x01, 0xC3, 0x49,
    0x11, 0xD2] ++ bytes_l10e4c0_5

theorem code_l10e4c0_4 : ∀ x ∈ codeRange 0x10e5fe bytes_l10e4c0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe5fe 82 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_5

def b_l10e4c0_3 : Block Op Label signature Reg.count 168 :=
  .letOp (n := 168) (.out 0x10e5af (atFlags StatusFlags.CF (adcR64R64Effect 0x10e5af 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[162, 147, 165]
    (.letOp (n := 169) (.exec 0x10e5af (fun s => s.RIP = 0x10e5af) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e5af 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[162, 147, 165]
    (.letOp (n := 170) (.out 0x10e5b2 (shldR64R64Effect 0x10e5b2 5 9 1 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[138, 136]
    (.letOp (n := 171) (.exec 0x10e5b2 (fun s => s.RIP = 0x10e5b2) (shldR64R64Effect 0x10e5b2 5 9 1 12) (Reg.operands [.gpr 9, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138, 136]
    (.letOp (n := 172) (.out 0x10e5b7 (shldR64R64Effect 0x10e5b7 5 8 10 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[168, 164]
    (.letOp (n := 173) (.exec 0x10e5b7 (fun s => s.RIP = 0x10e5b7) (shldR64R64Effect 0x10e5b7 5 8 10 12) (Reg.operands [.gpr 8, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[168, 164]
    (.letOp (n := 174) (.out 0x10e5bc (movR64R64Effect 0x10e5bc 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[125]
    (.letOp (n := 175) (.exec 0x10e5bc (fun s => s.RIP = 0x10e5bc) (movR64R64Effect 0x10e5bc 0 13) (Reg.operands [.gpr 13] [])) #v[125]
    (.letOp (n := 176) (.out 0x10e5bf (movR64M64Effect 0x10e5bf 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[65]
    (.letOp (n := 177) (.exec 0x10e5bf (LoadPre 0x10e5bf (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e5bf + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e5bf 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 178) (.out 0x10e5c3 (mulR64Effect 0x10e5c3 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14, .gpr 0] []) (.reg (.gpr 0))) #v[176, 174]
    (.letOp (n := 179) (.out 0x10e5c3 (mulR64Effect 0x10e5c3 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 14, .gpr 0] []) (.reg (.gpr 2))) #v[176, 174]
    (.letOp (n := 180) (.exec 0x10e5c3 (fun s => s.RIP = 0x10e5c3) (mulR64Effect 0x10e5c3 14) (Reg.operands [.gpr 14, .gpr 0] [])) #v[176, 174]
    (.letOp (n := 181) (.exec 0x10e5c6 (StorePre 0x10e5c6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e5c6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5c6 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[179, 65]
    (.letOp (n := 182) (.exec 0x10e5cb (StorePre 0x10e5cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e5cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5cb 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[178, 65]
    (.letOp (n := 183) (.out 0x10e5d0 (movR64M64Effect 0x10e5d0 0 (.sib 4 none 0 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 184) (.exec 0x10e5d0 (LoadPre 0x10e5d0 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e5d0 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5d0 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 185) (.out 0x10e5d5 (mulR64Effect 0x10e5d5 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[72, 183]
    (.letOp (n := 186) (.out 0x10e5d5 (mulR64Effect 0x10e5d5 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[72, 183]
    (.letOp (n := 187) (.exec 0x10e5d5 (fun s => s.RIP = 0x10e5d5) (mulR64Effect 0x10e5d5 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[72, 183]
    (.letOp (n := 188) (.exec 0x10e5d8 (StorePre 0x10e5d8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10e5d8 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5d8 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[186, 65]
    (.letOp (n := 189) (.exec 0x10e5dd (StorePre 0x10e5dd 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10e5dd + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5dd 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[185, 65]
    (.letOp (n := 190) (.out 0x10e5e2 (movR64R64Effect 0x10e5e2 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[82]
    (.letOp (n := 191) (.exec 0x10e5e2 (fun s => s.RIP = 0x10e5e2) (movR64R64Effect 0x10e5e2 0 11) (Reg.operands [.gpr 11] [])) #v[82]
    (.letOp (n := 192) (.out 0x10e5e5 (movR64M64Effect 0x10e5e5 6 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 193) (.exec 0x10e5e5 (LoadPre 0x10e5e5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e5e5 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5e5 6 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 194) (.out 0x10e5ea (mulR64Effect 0x10e5ea 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[192, 190]
    (.letOp (n := 195) (.out 0x10e5ea (mulR64Effect 0x10e5ea 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[192, 190]
    (.letOp (n := 196) (.exec 0x10e5ea (fun s => s.RIP = 0x10e5ea) (mulR64Effect 0x10e5ea 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[192, 190]
    (.letOp (n := 197) (.out 0x10e5ed (movR64R64Effect 0x10e5ed 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[195]
    (.letOp (n := 198) (.exec 0x10e5ed (fun s => s.RIP = 0x10e5ed) (movR64R64Effect 0x10e5ed 12 2) (Reg.operands [.gpr 2] [])) #v[195]
    (.letOp (n := 199) (.out 0x10e5f0 (movR64R64Effect 0x10e5f0 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[194]
    (.letOp (n := 200) (.exec 0x10e5f0 (fun s => s.RIP = 0x10e5f0) (movR64R64Effect 0x10e5f0 13 0) (Reg.operands [.gpr 0] [])) #v[194]
    (.letOp (n := 201) (.out 0x10e5f3 (movR64M64Effect 0x10e5f3 0 (.sib 4 none 0 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 202) (.exec 0x10e5f3 (LoadPre 0x10e5f3 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e5f3 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10e5f3 0 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 203) (.out 0x10e5f8 (mulR64Effect 0x10e5f8 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[112, 201]
    (.letOp (n := 204) (.out 0x10e5f8 (mulR64Effect 0x10e5f8 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[112, 201]
    (.letOp (n := 205) (.exec 0x10e5f8 (fun s => s.RIP = 0x10e5f8) (mulR64Effect 0x10e5f8 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[112, 201]
    (.letOp (n := 206) (.out 0x10e5fb (movR64R64Effect 0x10e5fb 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[204]
    (.letOp (n := 207) (.exec 0x10e5fb (fun s => s.RIP = 0x10e5fb) (movR64R64Effect 0x10e5fb 5 2) (Reg.operands [.gpr 2] [])) #v[204]
    (b_l10e4c0_4))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_3 : List UInt8 :=
  [0x49, 0x11, 0xD0, 0x49, 0x0F, 0xA4, 0xC9, 0x0C, 0x4D, 0x0F, 0xA4, 0xD0, 0x0C, 0x4C, 0x89, 0xE8,
    0x4C, 0x8B, 0x34, 0x24, 0x49, 0xF7, 0xE6, 0x48, 0x89, 0x54, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24,
    0x18, 0x48, 0x8B, 0x44, 0x24, 0x50, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89,
    0x44, 0x24, 0x08, 0x4C, 0x89, 0xD8, 0x48, 0x8B, 0x74, 0x24, 0x68, 0x48, 0xF7, 0xE6, 0x49, 0x89,
    0xD4, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x44, 0x24, 0x48, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0xD5] ++ bytes_l10e4c0_4

theorem code_l10e4c0_3 : ∀ x ∈ codeRange 0x10e5af bytes_l10e4c0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe5af 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_4

def b_l10e4c0_2 : Block Op Label signature Reg.count 125 :=
  .letOp (n := 125) (.out 0x10e557 (movR64M64Effect 0x10e557 13 (.base 1 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 1] []) (.reg (.gpr 13))) #v[67]
    (.letOp (n := 126) (.exec 0x10e557 (LoadPre 0x10e557 (fun s => AddrMode.addr (.base 1 (.d8 0x20)) s (0x10e557 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e557 13 (.base 1 (.d8 0x20))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 127) (.out 0x10e55b (movR64M64Effect 0x10e55b 1 (.base 9 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 128) (.exec 0x10e55b (LoadPre 0x10e55b (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x10e55b + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e55b 1 (.base 9 (.d8 0x20))) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 129) (.exec 0x10e55f (StorePre 0x10e55f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10e55f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e55f 1 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[127, 65]
    (.letOp (n := 130) (.out 0x10e564 (movR64R64Effect 0x10e564 0 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13] []) (.reg (.gpr 0))) #v[125]
    (.letOp (n := 131) (.exec 0x10e564 (fun s => s.RIP = 0x10e564) (movR64R64Effect 0x10e564 0 13) (Reg.operands [.gpr 13] [])) #v[125]
    (.letOp (n := 132) (.exec 0x10e567 (StorePre 0x10e567 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10e567 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e567 13 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[125, 65]
    (.letOp (n := 133) (.out 0x10e56c (mulR64Effect 0x10e56c 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[127, 130]
    (.letOp (n := 134) (.out 0x10e56c (mulR64Effect 0x10e56c 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[127, 130]
    (.letOp (n := 135) (.exec 0x10e56c (fun s => s.RIP = 0x10e56c) (mulR64Effect 0x10e56c 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[127, 130]
    (.letOp (n := 136) (.out 0x10e56f (movR64R64Effect 0x10e56f 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[133]
    (.letOp (n := 137) (.exec 0x10e56f (fun s => s.RIP = 0x10e56f) (movR64R64Effect 0x10e56f 1 0) (Reg.operands [.gpr 0] [])) #v[133]
    (.letOp (n := 138) (.out 0x10e572 (movR64R64Effect 0x10e572 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[134]
    (.letOp (n := 139) (.exec 0x10e572 (fun s => s.RIP = 0x10e572) (movR64R64Effect 0x10e572 9 2) (Reg.operands [.gpr 2] [])) #v[134]
    (.letOp (n := 140) (.out 0x10e575 (movR64Imm64Effect 0x10e575 2 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 141) (.exec 0x10e575 (fun s => s.RIP = 0x10e575) (movR64Imm64Effect 0x10e575 2 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 142) (.out 0x10e57f (andR64R64Effect 0x10e57f 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[133, 140]
    (.letOp (n := 143) (.exec 0x10e57f (fun s => s.RIP = 0x10e57f) (andR64R64Effect 0x10e57f 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[133, 140]
    (.letOp (n := 144) (.out 0x10e582 (movR64Imm64Effect 0x10e582 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 145) (.exec 0x10e582 (fun s => s.RIP = 0x10e582) (movR64Imm64Effect 0x10e582 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 146) (.out 0x10e58c (mulR64Effect 0x10e58c 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[144, 142]
    (.letOp (n := 147) (.out 0x10e58c (mulR64Effect 0x10e58c 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[144, 142]
    (.letOp (n := 148) (.exec 0x10e58c (fun s => s.RIP = 0x10e58c) (mulR64Effect 0x10e58c 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[144, 142]
    (.letOp (n := 149) (.out 0x10e58f (addR64R64Effect 0x10e58f 10 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 12] []) (.reg (.gpr 10))) #v[121, 107]
    (.letOp (n := 150) (.out 0x10e58f (addR64R64Effect 0x10e58f 10 12) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 12] []) (.flag .CF)) #v[121, 107]
    (.letOp (n := 151) (.exec 0x10e58f (fun s => s.RIP = 0x10e58f) (addR64R64Effect 0x10e58f 10 12) (Reg.operands [.gpr 10, .gpr 12] [])) #v[121, 107]
    (.letOp (n := 152) (.out 0x10e592 (atFlags StatusFlags.CF (adcR64R64Effect 0x10e592 8 15)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[123, 109, 150]
    (.letOp (n := 153) (.exec 0x10e592 (fun s => s.RIP = 0x10e592) (atFlags StatusFlags.CF (adcR64R64Effect 0x10e592 8 15)) (Reg.operands [.gpr 8, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[123, 109, 150]
    (.letOp (n := 154) (.out 0x10e595 (addR64R64Effect 0x10e595 10 14) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 14] []) (.reg (.gpr 10))) #v[149, 100]
    (.letOp (n := 155) (.out 0x10e595 (addR64R64Effect 0x10e595 10 14) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 14] []) (.flag .CF)) #v[149, 100]
    (.letOp (n := 156) (.exec 0x10e595 (fun s => s.RIP = 0x10e595) (addR64R64Effect 0x10e595 10 14) (Reg.operands [.gpr 10, .gpr 14] [])) #v[149, 100]
    (.letOp (n := 157) (.out 0x10e598 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e598 8 (.sib 4 none 0 (.d8 0x18)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[152, 65, 155]
    (.letOp (n := 158) (.exec 0x10e598 (LoadPre 0x10e598 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e598 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e598 8 (.sib 4 none 0 (.d8 0x18)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[152, 65, 155]
    (.letOp (n := 159) (.out 0x10e59d (addR64M64Effect 0x10e59d 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 4] []) (.reg (.gpr 10))) #v[154, 65]
    (.letOp (n := 160) (.out 0x10e59d (addR64M64Effect 0x10e59d 10 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 4] []) (.flag .CF)) #v[154, 65]
    (.letOp (n := 161) (.exec 0x10e59d (LoadPre 0x10e59d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e59d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x10e59d 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[154, 65]
    (.letOp (n := 162) (.out 0x10e5a2 (atFlags StatusFlags.CF (adcR64M64Effect 0x10e5a2 8 (.sib 4 none 0 (.d8 0x28)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[157, 65, 160]
    (.letOp (n := 163) (.exec 0x10e5a2 (LoadPre 0x10e5a2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e5a2 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x10e5a2 8 (.sib 4 none 0 (.d8 0x28)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[157, 65, 160]
    (.letOp (n := 164) (.out 0x10e5a7 (addR64R64Effect 0x10e5a7 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0] []) (.reg (.gpr 10))) #v[159, 146]
    (.letOp (n := 165) (.out 0x10e5a7 (addR64R64Effect 0x10e5a7 10 0) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 0] []) (.flag .CF)) #v[159, 146]
    (.letOp (n := 166) (.exec 0x10e5a7 (fun s => s.RIP = 0x10e5a7) (addR64R64Effect 0x10e5a7 10 0) (Reg.operands [.gpr 10, .gpr 0] [])) #v[159, 146]
    (.letOp (n := 167) (.exec 0x10e5aa (StorePre 0x10e5aa 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e5aa + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e5aa 10 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[164, 65]
    (b_l10e4c0_3)))))))))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_2 : List UInt8 :=
  [0x4C, 0x8B, 0x69, 0x20, 0x49, 0x8B, 0x49, 0x20, 0x48, 0x89, 0x4C, 0x24, 0x40, 0x4C, 0x89, 0xE8,
    0x4C, 0x89, 0x6C, 0x24, 0x38, 0x48, 0xF7, 0xE1, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD1, 0x48, 0xBA,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00,
    0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x4D, 0x01, 0xE2, 0x4D, 0x11, 0xF8, 0x4D, 0x01,
    0xF2, 0x4C, 0x13, 0x44, 0x24, 0x18, 0x4C, 0x03, 0x54, 0x24, 0x78, 0x4C, 0x13, 0x44, 0x24, 0x28,
    0x49, 0x01, 0xC2, 0x4C, 0x89, 0x54, 0x24, 0x78] ++ bytes_l10e4c0_3

theorem code_l10e4c0_2 : ∀ x ∈ codeRange 0x10e557 bytes_l10e4c0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe557 88 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_3

def b_l10e4c0_1 : Block Op Label signature Reg.count 90 :=
  .letOp (n := 90) (.exec 0x10e504 (StorePre 0x10e504 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10e504 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e504 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[88, 65]
    (.letOp (n := 91) (.exec 0x10e509 (StorePre 0x10e509 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10e509 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e509 0 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[87, 65]
    (.letOp (n := 92) (.out 0x10e50e (movR64R64Effect 0x10e50e 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[82]
    (.letOp (n := 93) (.exec 0x10e50e (fun s => s.RIP = 0x10e50e) (movR64R64Effect 0x10e50e 0 11) (Reg.operands [.gpr 11] [])) #v[82]
    (.letOp (n := 94) (.exec 0x10e511 (StorePre 0x10e511 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10e511 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e511 11 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 11, .gpr 4] [])) #v[82, 65]
    (.letOp (n := 95) (.out 0x10e516 (mulR64Effect 0x10e516 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[72, 92]
    (.letOp (n := 96) (.out 0x10e516 (mulR64Effect 0x10e516 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[72, 92]
    (.letOp (n := 97) (.exec 0x10e516 (fun s => s.RIP = 0x10e516) (mulR64Effect 0x10e516 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[72, 92]
    (.letOp (n := 98) (.exec 0x10e519 (StorePre 0x10e519 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10e519 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e519 5 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[72, 65]
    (.letOp (n := 99) (.exec 0x10e51e (StorePre 0x10e51e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10e51e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e51e 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[96, 65]
    (.letOp (n := 100) (.out 0x10e523 (movR64R64Effect 0x10e523 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[95]
    (.letOp (n := 101) (.exec 0x10e523 (fun s => s.RIP = 0x10e523) (movR64R64Effect 0x10e523 14 0) (Reg.operands [.gpr 0] [])) #v[95]
    (.letOp (n := 102) (.out 0x10e526 (movR64R64Effect 0x10e526 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 103) (.exec 0x10e526 (fun s => s.RIP = 0x10e526) (movR64R64Effect 0x10e526 0 6) (Reg.operands [.gpr 6] [])) #v[79]
    (.letOp (n := 104) (.out 0x10e529 (mulR64Effect 0x10e529 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[74, 102]
    (.letOp (n := 105) (.out 0x10e529 (mulR64Effect 0x10e529 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[74, 102]
    (.letOp (n := 106) (.exec 0x10e529 (fun s => s.RIP = 0x10e529) (mulR64Effect 0x10e529 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[74, 102]
    (.letOp (n := 107) (.out 0x10e52c (movR64R64Effect 0x10e52c 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[104]
    (.letOp (n := 108) (.exec 0x10e52c (fun s => s.RIP = 0x10e52c) (movR64R64Effect 0x10e52c 12 0) (Reg.operands [.gpr 0] [])) #v[104]
    (.letOp (n := 109) (.out 0x10e52f (movR64R64Effect 0x10e52f 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[105]
    (.letOp (n := 110) (.exec 0x10e52f (fun s => s.RIP = 0x10e52f) (movR64R64Effect 0x10e52f 15 2) (Reg.operands [.gpr 2] [])) #v[105]
    (.letOp (n := 111) (.exec 0x10e532 (StorePre 0x10e532 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10e532 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e532 9 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[77, 65]
    (.letOp (n := 112) (.out 0x10e53a (movR64M64Effect 0x10e53a 3 (.base 9 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[77]
    (.letOp (n := 113) (.exec 0x10e53a (LoadPre 0x10e53a (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x10e53a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e53a 3 (.base 9 (.d8 0x18))) (Reg.operands [.gpr 9] [])) #v[77]
    (.letOp (n := 114) (.out 0x10e53e (movR64M64Effect 0x10e53e 0 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 115) (.exec 0x10e53e (LoadPre 0x10e53e (fun s => AddrMode.addr (.base 1 .none) s (0x10e53e + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e53e 0 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 116) (.exec 0x10e541 (StorePre 0x10e541 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10e541 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10e541 0 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[114, 65]
    (.letOp (n := 117) (.out 0x10e549 (mulR64Effect 0x10e549 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[112, 114]
    (.letOp (n := 118) (.out 0x10e549 (mulR64Effect 0x10e549 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[112, 114]
    (.letOp (n := 119) (.exec 0x10e549 (fun s => s.RIP = 0x10e549) (mulR64Effect 0x10e549 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[112, 114]
    (.letOp (n := 120) (.exec 0x10e54c (StorePre 0x10e54c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10e54c + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e54c 3 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[112, 65]
    (.letOp (n := 121) (.out 0x10e551 (movR64R64Effect 0x10e551 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[117]
    (.letOp (n := 122) (.exec 0x10e551 (fun s => s.RIP = 0x10e551) (movR64R64Effect 0x10e551 10 0) (Reg.operands [.gpr 0] [])) #v[117]
    (.letOp (n := 123) (.out 0x10e554 (movR64R64Effect 0x10e554 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[118]
    (.letOp (n := 124) (.exec 0x10e554 (fun s => s.RIP = 0x10e554) (movR64R64Effect 0x10e554 8 2) (Reg.operands [.gpr 2] [])) #v[118]
    (b_l10e4c0_2)))))))))))))))))))))))))))))))))))

def bytes_l10e4c0_1 : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x78, 0x4C, 0x89, 0xD8, 0x4C, 0x89, 0x5C,
    0x24, 0x30, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0x6C, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x18, 0x49,
    0x89, 0xC6, 0x48, 0x89, 0xF0, 0x49, 0xF7, 0xE2, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD7, 0x4C, 0x89,
    0x8C, 0x24, 0x90, 0x00, 0x00, 0x00, 0x49, 0x8B, 0x59, 0x18, 0x48, 0x8B, 0x01, 0x48, 0x89, 0x84,
    0x24, 0x80, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE3, 0x48, 0x89, 0x5C, 0x24, 0x70, 0x49, 0x89, 0xC2,
    0x49, 0x89, 0xD0] ++ bytes_l10e4c0_2

theorem code_l10e4c0_1 : ∀ x ∈ codeRange 0x10e504 bytes_l10e4c0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe504 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_2

def b_l10e4c0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10e4c0 (pushR64Effect 0x10e4c0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10e4c0 (PushPre 0x10e4c0 1) (pushR64Effect 0x10e4c0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10e4c1 (pushR64Effect 0x10e4c1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10e4c1 (PushPre 0x10e4c1 2) (pushR64Effect 0x10e4c1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10e4c3 (pushR64Effect 0x10e4c3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10e4c3 (PushPre 0x10e4c3 2) (pushR64Effect 0x10e4c3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10e4c5 (pushR64Effect 0x10e4c5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10e4c5 (PushPre 0x10e4c5 2) (pushR64Effect 0x10e4c5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10e4c7 (pushR64Effect 0x10e4c7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10e4c7 (PushPre 0x10e4c7 2) (pushR64Effect 0x10e4c7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10e4c9 (pushR64Effect 0x10e4c9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10e4c9 (PushPre 0x10e4c9 1) (pushR64Effect 0x10e4c9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10e4ca (subR64Imm32Effect 0x10e4ca 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10e4ca (fun s => s.RIP = 0x10e4ca) (subR64Imm32Effect 0x10e4ca 4 0xe8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10e4d1 (movR64R64Effect 0x10e4d1 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[2]
    (.letOp (n := 68) (.exec 0x10e4d1 (fun s => s.RIP = 0x10e4d1) (movR64R64Effect 0x10e4d1 1 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x10e4d4 (movR64M64Effect 0x10e4d4 2 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 70) (.exec 0x10e4d4 (LoadPre 0x10e4d4 (fun s => AddrMode.addr (.base 6 .none) s (0x10e4d4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10e4d4 2 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.exec 0x10e4d7 (StorePre 0x10e4d7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10e4d7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10e4d7 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[69, 65]
    (.letOp (n := 72) (.out 0x10e4db (movR64M64Effect 0x10e4db 5 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 73) (.exec 0x10e4db (LoadPre 0x10e4db (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10e4db + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4db 5 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 74) (.out 0x10e4df (movR64M64Effect 0x10e4df 10 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 75) (.exec 0x10e4df (LoadPre 0x10e4df (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x10e4df + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4df 10 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.exec 0x10e4e3 (StorePre 0x10e4e3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10e4e3 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4e3 10 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 10, .gpr 4] [])) #v[74, 65]
    (.letOp (n := 77) (.out 0x10e4e8 (movR64R64Effect 0x10e4e8 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 78) (.exec 0x10e4e8 (fun s => s.RIP = 0x10e4e8) (movR64R64Effect 0x10e4e8 9 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.out 0x10e4eb (movR64M64Effect 0x10e4eb 6 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 80) (.exec 0x10e4eb (LoadPre 0x10e4eb (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x10e4eb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4eb 6 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 81) (.exec 0x10e4ef (StorePre 0x10e4ef 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10e4ef + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4ef 6 (.sib 4 none 0 (.d8 0x48))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[79, 65]
    (.letOp (n := 82) (.out 0x10e4f4 (movR64M64Effect 0x10e4f4 11 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 1] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 83) (.exec 0x10e4f4 (LoadPre 0x10e4f4 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x10e4f4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4f4 11 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 84) (.out 0x10e4f8 (movR64M64Effect 0x10e4f8 0 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 85) (.exec 0x10e4f8 (LoadPre 0x10e4f8 (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x10e4f8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10e4f8 0 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 86) (.exec 0x10e4fc (StorePre 0x10e4fc 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x50)) s (0x10e4fc + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10e4fc 0 (.sib 4 none 0 (.d8 0x50))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[84, 65]
    (.letOp (n := 87) (.out 0x10e501 (mulR64Effect 0x10e501 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[69, 84]
    (.letOp (n := 88) (.out 0x10e501 (mulR64Effect 0x10e501 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[69, 84]
    (.letOp (n := 89) (.exec 0x10e501 (fun s => s.RIP = 0x10e501) (mulR64Effect 0x10e501 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[69, 84]
    (b_l10e4c0_1)))))))))))))))))))))))))))))))))))))

def bytes_l10e4c0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xE8, 0x00, 0x00,
    0x00, 0x48, 0x89, 0xD1, 0x48, 0x8B, 0x16, 0x48, 0x89, 0x14, 0x24, 0x48, 0x8B, 0x6E, 0x08, 0x4C,
    0x8B, 0x56, 0x10, 0x4C, 0x89, 0x54, 0x24, 0x68, 0x49, 0x89, 0xF1, 0x48, 0x8B, 0x71, 0x08, 0x48,
    0x89, 0x74, 0x24, 0x48, 0x4C, 0x8B, 0x59, 0x10, 0x48, 0x8B, 0x41, 0x18, 0x48, 0x89, 0x44, 0x24,
    0x50, 0x48, 0xF7, 0xE2] ++ bytes_l10e4c0_1

theorem code_l10e4c0 : ∀ x ∈ codeRange 0x10e4c0 bytes_l10e4c0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xe4c0 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10e4c0_1

@[cfg_block] def b_l10ecb2 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ecb2 (leaR64Effect 0x10ecb2 7 (.base 3 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 54) (.exec 0x10ecb2 (fun s => s.RIP = 0x10ecb2) (leaR64Effect 0x10ecb2 7 (.base 3 (.d8 0x28))) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10ecb6 (leaR64Effect 0x10ecb6 6 (.sib 4 none 0 (.d32 0xc0))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 56) (.exec 0x10ecb6 (fun s => s.RIP = 0x10ecb6) (leaR64Effect 0x10ecb6 6 (.sib 4 none 0 (.d32 0xc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10ecbe (callEffect (fun _ => 0x114930) 0x10ecc3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x10ecbe (PushPre 0x10ecbe 5) (callEffect (fun _ => 0x114930) 0x10ecc3) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x10ecc3⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(3, 3), (4, 57), (5, 5), (6, 55), (7, 53), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l10ecc3, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l10ecb2 : List UInt8 :=
  [0x48, 0x8D, 0x7B, 0x28, 0x48, 0x8D, 0xB4, 0x24, 0xC0, 0x00, 0x00, 0x00, 0xE8, 0x6D, 0x5C, 0x00,
    0x00]

theorem code_l10ecb2 : ∀ x ∈ codeRange 0x10ecb2 bytes_l10ecb2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xecb2 17 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ecc3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10ecc3 (StorePre 0x10ecc3 4 (fun s => AddrMode.addr (.base 3 (.d8 0x50)) s (0x10ecc3 + BitVec.ofNat 64 4)) 1) (movM8Imm8Effect 0x10ecc3 (.base 3 (.d8 0x50)) 0x0) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 54) (.out 0x10ecc7 (addR64Imm32Effect 0x10ecc7 4 0xe8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 55) (.exec 0x10ecc7 (fun s => s.RIP = 0x10ecc7) (addR64Imm32Effect 0x10ecc7 4 0xe8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10ecce (popR64Effect 0x10ecce 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[54]
    (.letOp (n := 57) (.out 0x10ecce (popR64Effect 0x10ecce 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[54]
    (.letOp (n := 58) (.exec 0x10ecce (PopPre 0x10ecce) (popR64Effect 0x10ecce 1 3) (Reg.operands [.gpr 4] [])) #v[54]
    (.letOp (n := 59) (.out 0x10eccf (popR64Effect 0x10eccf 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[57]
    (.letOp (n := 60) (.out 0x10eccf (popR64Effect 0x10eccf 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[57]
    (.letOp (n := 61) (.exec 0x10eccf (PopPre 0x10eccf) (popR64Effect 0x10eccf 2 12) (Reg.operands [.gpr 4] [])) #v[57]
    (.letOp (n := 62) (.out 0x10ecd1 (popR64Effect 0x10ecd1 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[60]
    (.letOp (n := 63) (.out 0x10ecd1 (popR64Effect 0x10ecd1 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[60]
    (.letOp (n := 64) (.exec 0x10ecd1 (PopPre 0x10ecd1) (popR64Effect 0x10ecd1 2 13) (Reg.operands [.gpr 4] [])) #v[60]
    (.letOp (n := 65) (.out 0x10ecd3 (popR64Effect 0x10ecd3 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[63]
    (.letOp (n := 66) (.out 0x10ecd3 (popR64Effect 0x10ecd3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x10ecd3 (PopPre 0x10ecd3) (popR64Effect 0x10ecd3 2 14) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x10ecd5 (popR64Effect 0x10ecd5 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[66]
    (.letOp (n := 69) (.out 0x10ecd5 (popR64Effect 0x10ecd5 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[66]
    (.letOp (n := 70) (.exec 0x10ecd5 (PopPre 0x10ecd5) (popR64Effect 0x10ecd5 2 15) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 71) (.out 0x10ecd7 (popR64Effect 0x10ecd7 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[69]
    (.letOp (n := 72) (.out 0x10ecd7 (popR64Effect 0x10ecd7 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[69]
    (.letOp (n := 73) (.exec 0x10ecd7 (PopPre 0x10ecd7) (popR64Effect 0x10ecd7 1 5) (Reg.operands [.gpr 4] [])) #v[69]
    (.letOp (n := 74) (.out 0x10ecd8 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[72]
    (.letOp (n := 75) (.out 0x10ecd8 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[72]
    (.letOp (n := 76) (.exec 0x10ecd8 (RetPre 0x10ecd8) (retEffect) (Reg.operands [.gpr 4] [])) #v[72]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 1), (2, 2), (3, 56), (4, 75), (5, 71), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 59), (13, 62), (14, 65), (15, 68), (22, 22), (39, 39), (50, 50), (51, 51)] 77) (some ⟨74, by decide⟩))))))))))))))))))))))))))

def bytes_l10ecc3 : List UInt8 :=
  [0xC6, 0x43, 0x50, 0x00, 0x48, 0x81, 0xC4, 0xE8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10ecc3 : ∀ x ∈ codeRange 0x10ecc3 bytes_l10ecc3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xecc3 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ece0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ece0 (pushR64Effect 0x10ece0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10ece0 (PushPre 0x10ece0 1) (pushR64Effect 0x10ece0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10ece1 (pushR64Effect 0x10ece1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10ece1 (PushPre 0x10ece1 2) (pushR64Effect 0x10ece1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10ece3 (pushR64Effect 0x10ece3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10ece3 (PushPre 0x10ece3 2) (pushR64Effect 0x10ece3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10ece5 (pushR64Effect 0x10ece5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10ece5 (PushPre 0x10ece5 2) (pushR64Effect 0x10ece5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10ece7 (pushR64Effect 0x10ece7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10ece7 (PushPre 0x10ece7 2) (pushR64Effect 0x10ece7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10ece9 (pushR64Effect 0x10ece9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10ece9 (PushPre 0x10ece9 1) (pushR64Effect 0x10ece9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10ecea (subR64Imm32Effect 0x10ecea 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10ecea (fun s => s.RIP = 0x10ecea) (subR64Imm32Effect 0x10ecea 4 0xb8) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10ecf1 (movR64R64Effect 0x10ecf1 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 68) (.exec 0x10ecf1 (fun s => s.RIP = 0x10ecf1) (movR64R64Effect 0x10ecf1 14 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x10ecf4 (movR64R64Effect 0x10ecf4 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 70) (.exec 0x10ecf4 (fun s => s.RIP = 0x10ecf4) (movR64R64Effect 0x10ecf4 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 71) (.out 0x10ecf7 (addR64Imm8Effect 0x10ecf7 6 0x50) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 72) (.exec 0x10ecf7 (fun s => s.RIP = 0x10ecf7) (addR64Imm8Effect 0x10ecf7 6 0x50) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x10ecfb (leaR64Effect 0x10ecfb 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 74) (.exec 0x10ecfb (fun s => s.RIP = 0x10ecfb) (leaR64Effect 0x10ecfb 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 75) (.out 0x10ed00 (callEffect (fun _ => 0x114930) 0x10ed05) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 76) (.exec 0x10ed00 (PushPre 0x10ed00 5) (callEffect (fun _ => 0x114930) 0x10ed05) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 77) (.const ⟨64, 0x10ed05⟩) #v[]
    (.terminate (.call ⟨.l114930, RegMap.args [(3, 69), (4, 75), (5, 5), (6, 71), (7, 73), (10, 10), (11, 11), (12, 12), (13, 13), (14, 67), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l10ed05, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10ece0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0xB8, 0x00, 0x00,
    0x00, 0x49, 0x89, 0xF6, 0x48, 0x89, 0xFB, 0x48, 0x83, 0xC6, 0x50, 0x48, 0x8D, 0x7C, 0x24, 0x58,
    0xE8, 0x2B, 0x5C, 0x00, 0x00]

theorem code_l10ece0 : ∀ x ∈ codeRange 0x10ece0 bytes_l10ece0, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xece0 37 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ed05_1 : Block Op Label signature Reg.count 91 :=
  .letOp (n := 91) (.exec 0x10ed55 (StorePre 0x10ed55 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ed55 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed55 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 92) (.exec 0x10ed5a (StorePre 0x10ed5a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ed5a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed5a 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[87, 4]
    (.letOp (n := 93) (.out 0x10ed5f (leaR64Effect 0x10ed5f 7 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 94) (.exec 0x10ed5f (fun s => s.RIP = 0x10ed5f) (leaR64Effect 0x10ed5f 7 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 95) (.out 0x10ed64 (movR64R64Effect 0x10ed64 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[4]
    (.letOp (n := 96) (.exec 0x10ed64 (fun s => s.RIP = 0x10ed64) (movR64R64Effect 0x10ed64 6 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 97) (.out 0x10ed67 (movR64Imm64Effect 0x10ed67 1 0x27c7f6e22ddacacf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 98) (.exec 0x10ed67 (fun s => s.RIP = 0x10ed67) (movR64Imm64Effect 0x10ed67 1 0x27c7f6e22ddacacf) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x10ed71 (movR64Imm32Effect 0x10ed71 2 0x2021e0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 100) (.exec 0x10ed71 (fun s => s.RIP = 0x10ed71) (movR64Imm32Effect 0x10ed71 2 0x2021e0) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x10ed78 (movR64Imm32Effect 0x10ed78 8 0x202180) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 102) (.exec 0x10ed78 (fun s => s.RIP = 0x10ed78) (movR64Imm32Effect 0x10ed78 8 0x202180) (Reg.operands [] [])) #v[]
    (.letOp (n := 103) (.out 0x10ed7f (callEffect (fun _ => 0x108e30) 0x10ed84) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 104) (.exec 0x10ed7f (PushPre 0x10ed7f 5) (callEffect (fun _ => 0x108e30) 0x10ed84) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 105) (.const ⟨64, 0x10ed84⟩) #v[]
    (.terminate (.call ⟨.l108e30, RegMap.args [(0, 81), (1, 97), (2, 99), (3, 3), (4, 103), (5, 5), (6, 95), (7, 93), (8, 101), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 106⟩ { target := .l10ed84, kept := #v[], arity := rfl, guard := some (Fin.last 105) }))))))))))))))))

def bytes_l10ed05_1 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x10, 0x48, 0x89, 0x7C, 0x24, 0x18, 0x48, 0x8D, 0x7C, 0x24, 0x58, 0x48,
    0x89, 0xE6, 0x48, 0xB9, 0xCF, 0xCA, 0xDA, 0x2D, 0xE2, 0xF6, 0xC7, 0x27, 0x48, 0xC7, 0xC2, 0xE0,
    0x21, 0x20, 0x00, 0x49, 0xC7, 0xC0, 0x80, 0x21, 0x20, 0x00, 0xE8, 0xAC, 0xA0, 0xFF, 0xFF]

theorem code_l10ed05_1 : ∀ x ∈ codeRange 0x10ed55 bytes_l10ed05_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xed55 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ed05 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ed05 (movR64M64Effect 0x10ed05 0 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10ed05 (LoadPre 0x10ed05 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ed05 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed05 0 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10ed0a (movR64M64Effect 0x10ed0a 1 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 56) (.exec 0x10ed0a (LoadPre 0x10ed0a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ed0a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed0a 1 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10ed0f (movR64M64Effect 0x10ed0f 2 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 58) (.exec 0x10ed0f (LoadPre 0x10ed0f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ed0f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed0f 2 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10ed14 (movR64R64Effect 0x10ed14 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 60) (.exec 0x10ed14 (fun s => s.RIP = 0x10ed14) (movR64R64Effect 0x10ed14 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 61) (.out 0x10ed17 (shlR64Effect 0x10ed17 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[59]
    (.letOp (n := 62) (.exec 0x10ed17 (fun s => s.RIP = 0x10ed17) (shlR64Effect 0x10ed17 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 63) (.out 0x10ed1b (orR64M64Effect 0x10ed1b 6 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[61, 4]
    (.letOp (n := 64) (.exec 0x10ed1b (LoadPre 0x10ed1b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ed1b + BitVec.ofNat 64 5)) 8) (orR64M64Effect 0x10ed1b 6 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 65) (.out 0x10ed20 (movR64M64Effect 0x10ed20 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 66) (.exec 0x10ed20 (LoadPre 0x10ed20 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ed20 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed20 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x10ed25 (shrR64Effect 0x10ed25 4 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x10ed25 (fun s => s.RIP = 0x10ed25) (shrR64Effect 0x10ed25 4 0 12) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 69) (.out 0x10ed29 (movR64R64Effect 0x10ed29 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 70) (.exec 0x10ed29 (fun s => s.RIP = 0x10ed29) (movR64R64Effect 0x10ed29 8 1) (Reg.operands [.gpr 1] [])) #v[55]
    (.letOp (n := 71) (.out 0x10ed2c (shlR64Effect 0x10ed2c 4 8 40) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[69]
    (.letOp (n := 72) (.exec 0x10ed2c (fun s => s.RIP = 0x10ed2c) (shlR64Effect 0x10ed2c 4 8 40) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x10ed30 (orR64R64Effect 0x10ed30 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x10ed30 (fun s => s.RIP = 0x10ed30) (orR64R64Effect 0x10ed30 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x10ed33 (shrR64Effect 0x10ed33 4 1 24) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 76) (.exec 0x10ed33 (fun s => s.RIP = 0x10ed33) (shrR64Effect 0x10ed33 4 1 24) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 77) (.out 0x10ed37 (movR64R64Effect 0x10ed37 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2] []) (.reg (.gpr 0))) #v[57]
    (.letOp (n := 78) (.exec 0x10ed37 (fun s => s.RIP = 0x10ed37) (movR64R64Effect 0x10ed37 0 2) (Reg.operands [.gpr 2] [])) #v[57]
    (.letOp (n := 79) (.out 0x10ed3a (shlR64Effect 0x10ed3a 4 0 28) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[77]
    (.letOp (n := 80) (.exec 0x10ed3a (fun s => s.RIP = 0x10ed3a) (shlR64Effect 0x10ed3a 4 0 28) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x10ed3e (orR64R64Effect 0x10ed3e 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[79, 75]
    (.letOp (n := 82) (.exec 0x10ed3e (fun s => s.RIP = 0x10ed3e) (orR64R64Effect 0x10ed3e 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[79, 75]
    (.letOp (n := 83) (.out 0x10ed41 (shrR64Effect 0x10ed41 4 2 36) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[57]
    (.letOp (n := 84) (.exec 0x10ed41 (fun s => s.RIP = 0x10ed41) (shrR64Effect 0x10ed41 4 2 36) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 85) (.out 0x10ed45 (shlR64Effect 0x10ed45 4 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 86) (.exec 0x10ed45 (fun s => s.RIP = 0x10ed45) (shlR64Effect 0x10ed45 4 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 87) (.out 0x10ed49 (orR64R64Effect 0x10ed49 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[85, 83]
    (.letOp (n := 88) (.exec 0x10ed49 (fun s => s.RIP = 0x10ed49) (orR64R64Effect 0x10ed49 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[85, 83]
    (.letOp (n := 89) (.exec 0x10ed4c (StorePre 0x10ed4c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ed4c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10ed4c 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 90) (.exec 0x10ed50 (StorePre 0x10ed50 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ed50 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ed50 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[73, 4]
    (b_l10ed05_1))))))))))))))))))))))))))))))))))))))

def bytes_l10ed05 : List UInt8 :=
  [0x48, 0x8B, 0x44, 0x24, 0x60, 0x48, 0x8B, 0x4C, 0x24, 0x68, 0x48, 0x8B, 0x54, 0x24, 0x70, 0x48,
    0x89, 0xC6, 0x48, 0xC1, 0xE6, 0x34, 0x48, 0x0B, 0x74, 0x24, 0x58, 0x48, 0x8B, 0x7C, 0x24, 0x78,
    0x48, 0xC1, 0xE8, 0x0C, 0x49, 0x89, 0xC8, 0x49, 0xC1, 0xE0, 0x28, 0x49, 0x09, 0xC0, 0x48, 0xC1,
    0xE9, 0x18, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE0, 0x1C, 0x48, 0x09, 0xC8, 0x48, 0xC1, 0xEA, 0x24,
    0x48, 0xC1, 0xE7, 0x10, 0x48, 0x09, 0xD7, 0x48, 0x89, 0x34, 0x24, 0x4C, 0x89, 0x44, 0x24, 0x08] ++ bytes_l10ed05_1

theorem code_l10ed05 : ∀ x ∈ codeRange 0x10ed05 bytes_l10ed05, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xed05 80 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ed05_1

@[cfg_block] def b_l10ed84 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ed84 (movR64M64Effect 0x10ed84 15 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10ed84 (LoadPre 0x10ed84 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x58)) s (0x10ed84 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed84 15 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10ed89 (movR64M64Effect 0x10ed89 12 (.sib 4 none 0 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 56) (.exec 0x10ed89 (LoadPre 0x10ed89 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x60)) s (0x10ed89 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed89 12 (.sib 4 none 0 (.d8 0x60))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10ed8e (movR64M64Effect 0x10ed8e 13 (.sib 4 none 0 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[4]
    (.letOp (n := 58) (.exec 0x10ed8e (LoadPre 0x10ed8e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x68)) s (0x10ed8e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed8e 13 (.sib 4 none 0 (.d8 0x68))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x10ed93 (movR64M64Effect 0x10ed93 5 (.sib 4 none 0 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[4]
    (.letOp (n := 60) (.exec 0x10ed93 (LoadPre 0x10ed93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x70)) s (0x10ed93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10ed93 5 (.sib 4 none 0 (.d8 0x70))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x10ed98 (movR32M32LowEffect 0x10ed98 7 (.sib 4 none 0 (.d8 0x78))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 62) (.exec 0x10ed98 (LoadPre 0x10ed98 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x78)) s (0x10ed98 + BitVec.ofNat 64 4)) 4) (movR32M32LowEffect 0x10ed98 7 (.sib 4 none 0 (.d8 0x78))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10ed9c (callEffect (fun _ => 0x127d50) 0x10eda1) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 64) (.exec 0x10ed9c (PushPre 0x10ed9c 5) (callEffect (fun _ => 0x127d50) 0x10eda1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.const ⟨64, 0x10eda1⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 63), (5, 59), (6, 6), (7, 61), (8, 8), (9, 9), (10, 10), (11, 11), (12, 55), (13, 57), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 66⟩ { target := .l10eda1, kept := #v[], arity := rfl, guard := some (Fin.last 65) }))))))))))))))

def bytes_l10ed84 : List UInt8 :=
  [0x4C, 0x8B, 0x7C, 0x24, 0x58, 0x4C, 0x8B, 0x64, 0x24, 0x60, 0x4C, 0x8B, 0x6C, 0x24, 0x68, 0x48,
    0x8B, 0x6C, 0x24, 0x70, 0x8B, 0x7C, 0x24, 0x78, 0xE8, 0xAF, 0x8F, 0x01, 0x00]

theorem code_l10ed84 : ∀ x ∈ codeRange 0x10ed84 bytes_l10ed84, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xed84 29 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10eda1_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x10ede6 (movzxR32R8Effect 0x10ede6 4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[0]
    (.letOp (n := 93) (.exec 0x10ede6 (fun s => s.RIP = 0x10ede6) (movzxR32R8Effect 0x10ede6 4 15 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 94) (.out 0x10edea (movR64R64Effect 0x10edea 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[92]
    (.letOp (n := 95) (.exec 0x10edea (fun s => s.RIP = 0x10edea) (movR64R64Effect 0x10edea 0 15) (Reg.operands [.gpr 15] [])) #v[92]
    (.letOp (n := 96) (.out 0x10eded (negR64Effect 0x10eded 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[94]
    (.letOp (n := 97) (.exec 0x10eded (fun s => s.RIP = 0x10eded) (negR64Effect 0x10eded 0) (Reg.operands [.gpr 0] [])) #v[94]
    (.letOp (n := 98) (.out 0x10edf0 (movR64Imm64Effect 0x10edf0 9 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 99) (.exec 0x10edf0 (fun s => s.RIP = 0x10edf0) (movR64Imm64Effect 0x10edf0 9 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 100) (.out 0x10edfa (andR64R64Effect 0x10edfa 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[98, 96]
    (.letOp (n := 101) (.exec 0x10edfa (fun s => s.RIP = 0x10edfa) (andR64R64Effect 0x10edfa 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[98, 96]
    (.letOp (n := 102) (.out 0x10edfd (andR64R64Effect 0x10edfd 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[64, 100]
    (.letOp (n := 103) (.exec 0x10edfd (fun s => s.RIP = 0x10edfd) (andR64R64Effect 0x10edfd 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[64, 100]
    (.letOp (n := 104) (.out 0x10ee00 (andR64R64Effect 0x10ee00 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[88, 100]
    (.letOp (n := 105) (.exec 0x10ee00 (fun s => s.RIP = 0x10ee00) (andR64R64Effect 0x10ee00 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[88, 100]
    (.letOp (n := 106) (.out 0x10ee03 (andR64R64Effect 0x10ee03 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[86, 100]
    (.letOp (n := 107) (.exec 0x10ee03 (fun s => s.RIP = 0x10ee03) (andR64R64Effect 0x10ee03 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[86, 100]
    (.letOp (n := 108) (.out 0x10ee06 (andR64R64Effect 0x10ee06 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[100, 84]
    (.letOp (n := 109) (.exec 0x10ee06 (fun s => s.RIP = 0x10ee06) (andR64R64Effect 0x10ee06 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[100, 84]
    (.letOp (n := 110) (.out 0x10ee09 (andR64R64Effect 0x10ee09 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[96, 90]
    (.letOp (n := 111) (.exec 0x10ee09 (fun s => s.RIP = 0x10ee09) (andR64R64Effect 0x10ee09 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[96, 90]
    (.letOp (n := 112) (.exec 0x10ee0c (StorePre 0x10ee0c 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ee0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10ee0c 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 2, .gpr 4] [])) #v[102, 4]
    (.letOp (n := 113) (.exec 0x10ee10 (StorePre 0x10ee10 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10ee10 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee10 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[104, 4]
    (.letOp (n := 114) (.exec 0x10ee15 (StorePre 0x10ee15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10ee15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee15 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[106, 4]
    (.letOp (n := 115) (.exec 0x10ee1a (StorePre 0x10ee1a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10ee1a + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee1a 9 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 9, .gpr 4] [])) #v[108, 4]
    (.letOp (n := 116) (.exec 0x10ee1f (StorePre 0x10ee1f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10ee1f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10ee1f 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[110, 4]
    (.letOp (n := 117) (.out 0x10ee24 (leaR64Effect 0x10ee24 12 (.sib 4 none 0 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 118) (.exec 0x10ee24 (fun s => s.RIP = 0x10ee24) (leaR64Effect 0x10ee24 12 (.sib 4 none 0 (.d8 0x58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 119) (.out 0x10ee29 (movR64R64Effect 0x10ee29 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 120) (.exec 0x10ee29 (fun s => s.RIP = 0x10ee29) (movR64R64Effect 0x10ee29 2 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 121) (.out 0x10ee2c (movR64R64Effect 0x10ee2c 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[117]
    (.letOp (n := 122) (.exec 0x10ee2c (fun s => s.RIP = 0x10ee2c) (movR64R64Effect 0x10ee2c 7 12) (Reg.operands [.gpr 12] [])) #v[117]
    (.letOp (n := 123) (.out 0x10ee2f (movR64R64Effect 0x10ee2f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 124) (.exec 0x10ee2f (fun s => s.RIP = 0x10ee2f) (movR64R64Effect 0x10ee2f 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 125) (.out 0x10ee32 (callEffect (fun _ => 0x10e4c0) 0x10ee37) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 126) (.exec 0x10ee32 (PushPre 0x10ee32 5) (callEffect (fun _ => 0x10e4c0) 0x10ee37) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.const ⟨64, 0x10ee37⟩) #v[]
    (.terminate (.call ⟨.l10e4c0, RegMap.args [(0, 110), (1, 90), (2, 119), (3, 3), (4, 125), (5, 5), (6, 123), (7, 121), (8, 84), (9, 108), (12, 117), (13, 13), (14, 14), (15, 92), (22, 22), (39, 39), (50, 50), (51, 51)] 128⟩ { target := .l10ee37, kept := #v[], arity := rfl, guard := some (Fin.last 127) })))))))))))))))))))))))))))))))))))))

def bytes_l10eda1_1 : List UInt8 :=
  [0x44, 0x0F, 0xB6, 0xF8, 0x4C, 0x89, 0xF8, 0x48, 0xF7, 0xD8, 0x49, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x49, 0x21, 0xC1, 0x4C, 0x21, 0xCA, 0x4C, 0x21, 0xCE, 0x4C, 0x21, 0xCF,
    0x4D, 0x21, 0xC1, 0x48, 0x21, 0xC8, 0x48, 0x89, 0x14, 0x24, 0x48, 0x89, 0x74, 0x24, 0x08, 0x48,
    0x89, 0x7C, 0x24, 0x10, 0x4C, 0x89, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x4C, 0x8D,
    0x64, 0x24, 0x58, 0x48, 0x89, 0xE2, 0x4C, 0x89, 0xE7, 0x4C, 0x89, 0xF6, 0xE8, 0x89, 0xF6, 0xFF,
    0xFF]

theorem code_l10eda1_1 : ∀ x ∈ codeRange 0x10ede6 bytes_l10eda1_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xede6 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10eda1 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10eda1 (StorePre 0x10eda1 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eda1 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x10eda1 3 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x10eda4 (movR64R64Effect 0x10eda4 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 55) (.exec 0x10eda4 (fun s => s.RIP = 0x10eda4) (movR64R64Effect 0x10eda4 1 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10eda7 (movzxR32M8Effect 0x10eda7 5 8 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 57) (.exec 0x10eda7 (LoadPre 0x10eda7 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10eda7 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x10eda7 5 8 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.out 0x10edac (xorR32R32Effect 0x10edac 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[54, 54]
    (.letOp (n := 59) (.exec 0x10edac (fun s => s.RIP = 0x10edac) (xorR32R32Effect 0x10edac 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[54, 54]
    (.letOp (n := 60) (.out 0x10edae (xorR32R32Effect 0x10edae 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 61) (.exec 0x10edae (fun s => s.RIP = 0x10edae) (xorR32R32Effect 0x10edae 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 62) (.out 0x10edb0 (testR8R8Effect 0x10edb0 3 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 63) (.exec 0x10edb0 (fun s => s.RIP = 0x10edb0) (testR8R8Effect 0x10edb0 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[56, 56]
    (.letOp (n := 64) (.out 0x10edb3 (atFlags (condHolds 5) (cmovR64R64Effect 0x10edb3 4 2 15)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[60, 15, 62]
    (.letOp (n := 65) (.exec 0x10edb3 (fun s => s.RIP = 0x10edb3) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edb3 4 2 15)) (Reg.operands [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[60, 15, 62]
    (.letOp (n := 66) (.out 0x10edb7 (xorR32R32Effect 0x10edb7 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[6, 6]
    (.letOp (n := 67) (.exec 0x10edb7 (fun s => s.RIP = 0x10edb7) (xorR32R32Effect 0x10edb7 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[6, 6]
    (.letOp (n := 68) (.out 0x10edb9 (testR8R8Effect 0x10edb9 3 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 69) (.exec 0x10edb9 (fun s => s.RIP = 0x10edb9) (testR8R8Effect 0x10edb9 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[56, 56]
    (.letOp (n := 70) (.out 0x10edbc (atFlags (condHolds 5) (cmovR64R64Effect 0x10edbc 4 6 12)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 6))) #v[66, 12, 68]
    (.letOp (n := 71) (.exec 0x10edbc (fun s => s.RIP = 0x10edbc) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edbc 4 6 12)) (Reg.operands [.gpr 6, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[66, 12, 68]
    (.letOp (n := 72) (.out 0x10edc0 (xorR32R32Effect 0x10edc0 2 7 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 7] []) (.reg (.gpr 7))) #v[7, 7]
    (.letOp (n := 73) (.exec 0x10edc0 (fun s => s.RIP = 0x10edc0) (xorR32R32Effect 0x10edc0 2 7 7) (Reg.operands [.gpr 7, .gpr 7] [])) #v[7, 7]
    (.letOp (n := 74) (.out 0x10edc2 (testR8R8Effect 0x10edc2 3 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 75) (.exec 0x10edc2 (fun s => s.RIP = 0x10edc2) (testR8R8Effect 0x10edc2 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[56, 56]
    (.letOp (n := 76) (.out 0x10edc5 (atFlags (condHolds 5) (cmovR64R64Effect 0x10edc5 4 7 13)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 7))) #v[72, 13, 74]
    (.letOp (n := 77) (.exec 0x10edc5 (fun s => s.RIP = 0x10edc5) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edc5 4 7 13)) (Reg.operands [.gpr 7, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[72, 13, 74]
    (.letOp (n := 78) (.out 0x10edc9 (testR8R8Effect 0x10edc9 3 8 8) (EffectPart.reads (.flag .ZF) [.gpr 8, .gpr 8] []) (.flag .ZF)) #v[56, 56]
    (.letOp (n := 79) (.exec 0x10edc9 (fun s => s.RIP = 0x10edc9) (testR8R8Effect 0x10edc9 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[56, 56]
    (.letOp (n := 80) (.out 0x10edcc (atFlags (condHolds 5) (cmovR64R64Effect 0x10edcc 4 1 5)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[58, 5, 78]
    (.letOp (n := 81) (.exec 0x10edcc (fun s => s.RIP = 0x10edcc) (atFlags (condHolds 5) (cmovR64R64Effect 0x10edcc 4 1 5)) (Reg.operands [.gpr 1, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[58, 5, 78]
    (.letOp (n := 82) (.out 0x10edd0 (movR64R64Effect 0x10edd0 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 1] []) (.reg (.gpr 8))) #v[80]
    (.letOp (n := 83) (.exec 0x10edd0 (fun s => s.RIP = 0x10edd0) (movR64R64Effect 0x10edd0 8 1) (Reg.operands [.gpr 1] [])) #v[80]
    (.letOp (n := 84) (.out 0x10edd3 (shldR64R64Effect 0x10edd3 5 8 7 36) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[82, 76]
    (.letOp (n := 85) (.exec 0x10edd3 (fun s => s.RIP = 0x10edd3) (shldR64R64Effect 0x10edd3 5 8 7 36) (Reg.operands [.gpr 8, .gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[82, 76]
    (.letOp (n := 86) (.out 0x10edd8 (shldR64R64Effect 0x10edd8 5 7 6 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[76, 70]
    (.letOp (n := 87) (.exec 0x10edd8 (fun s => s.RIP = 0x10edd8) (shldR64R64Effect 0x10edd8 5 7 6 24) (Reg.operands [.gpr 7, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[76, 70]
    (.letOp (n := 88) (.out 0x10eddd (shldR64R64Effect 0x10eddd 5 6 2 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[70, 64]
    (.letOp (n := 89) (.exec 0x10eddd (fun s => s.RIP = 0x10eddd) (shldR64R64Effect 0x10eddd 5 6 2 12) (Reg.operands [.gpr 6, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[70, 64]
    (.letOp (n := 90) (.out 0x10ede2 (shrR64Effect 0x10ede2 4 1 16) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[80]
    (.letOp (n := 91) (.exec 0x10ede2 (fun s => s.RIP = 0x10ede2) (shrR64Effect 0x10ede2 4 1 16) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (b_l10eda1_1)))))))))))))))))))))))))))))))))))))))

def bytes_l10eda1 : List UInt8 :=
  [0x88, 0x04, 0x24, 0x48, 0x89, 0xE1, 0x44, 0x0F, 0xB6, 0x04, 0x24, 0x31, 0xC9, 0x31, 0xD2, 0x45,
    0x84, 0xC0, 0x49, 0x0F, 0x45, 0xD7, 0x31, 0xF6, 0x45, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xF4, 0x31,
    0xFF, 0x45, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xFD, 0x45, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xCD, 0x49,
    0x89, 0xC8, 0x49, 0x0F, 0xA4, 0xF8, 0x24, 0x48, 0x0F, 0xA4, 0xF7, 0x18, 0x48, 0x0F, 0xA4, 0xD6,
    0x0C, 0x48, 0xC1, 0xE9, 0x10] ++ bytes_l10eda1_1

theorem code_l10eda1 : ∀ x ∈ codeRange 0x10eda1 bytes_l10eda1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xeda1 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10eda1_1

@[cfg_block] def b_l10ee37 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10ee37 (StorePre 0x10ee37 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0xb0)) s (0x10ee37 + BitVec.ofNat 64 8)) 1) (movM8R8Effect 0x10ee37 8 15 (.sib 4 none 0 (.d32 0xb0))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[15, 4]
    (.letOp (n := 54) (.out 0x10ee3f (movR64R64Effect 0x10ee3f 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 55) (.exec 0x10ee3f (fun s => s.RIP = 0x10ee3f) (movR64R64Effect 0x10ee3f 0 4) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.out 0x10ee42 (movR32Imm32Effect 0x10ee42 5 1 0xb) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 57) (.exec 0x10ee42 (fun s => s.RIP = 0x10ee42) (movR32Imm32Effect 0x10ee42 5 1 0xb) (Reg.operands [] [])) #v[]
    (.letOp (n := 58) (.out 0x10ee47 (movR64R64Effect 0x10ee47 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[54]
    (.letOp (n := 59) (.exec 0x10ee47 (fun s => s.RIP = 0x10ee47) (movR64R64Effect 0x10ee47 7 0) (Reg.operands [.gpr 0] [])) #v[54]
    (.letOp (n := 60) (.out 0x10ee4a (movR64Imm32Effect 0x10ee4a 6 0x202b70) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 61) (.exec 0x10ee4a (fun s => s.RIP = 0x10ee4a) (movR64Imm32Effect 0x10ee4a 6 0x202b70) (Reg.operands [] [])) #v[]
    (.letOp (n := 62) (.exec 0x10ee51 (RepPre 0x10ee51 (RepMovsqPre 0x10ee51)) (repMovsqEffect 0x10ee51) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[60, 58, 56, 22]
    (.letOp (n := 63) (.out 0x10ee54 (movR64R64Effect 0x10ee54 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 64) (.exec 0x10ee54 (fun s => s.RIP = 0x10ee54) (movR64R64Effect 0x10ee54 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 65) (.out 0x10ee57 (movR64R64Effect 0x10ee57 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[54]
    (.letOp (n := 66) (.exec 0x10ee57 (fun s => s.RIP = 0x10ee57) (movR64R64Effect 0x10ee57 6 0) (Reg.operands [.gpr 0] [])) #v[54]
    (.letOp (n := 67) (.out 0x10ee5a (movR64R64Effect 0x10ee5a 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[12]
    (.letOp (n := 68) (.exec 0x10ee5a (fun s => s.RIP = 0x10ee5a) (movR64R64Effect 0x10ee5a 2 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 69) (.out 0x10ee5d (movR32R32Effect 0x10ee5d 3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 70) (.exec 0x10ee5d (fun s => s.RIP = 0x10ee5d) (movR32R32Effect 0x10ee5d 3 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 71) (.out 0x10ee60 (callEffect (fun _ => 0x120470) 0x10ee65) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 72) (.exec 0x10ee60 (PushPre 0x10ee60 5) (callEffect (fun _ => 0x120470) 0x10ee65) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 73) (.const ⟨64, 0x10ee65⟩) #v[]
    (.terminate (.call ⟨.l120470, RegMap.args [(0, 54), (1, 69), (2, 67), (3, 3), (4, 71), (5, 5), (6, 65), (7, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 74⟩ { target := .l10ee65, kept := #v[], arity := rfl, guard := some (Fin.last 73) }))))))))))))))))))))))

def bytes_l10ee37 : List UInt8 :=
  [0x44, 0x88, 0xBC, 0x24, 0xB0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xE0, 0xB9, 0x0B, 0x00, 0x00, 0x00,
    0x48, 0x89, 0xC7, 0x48, 0xC7, 0xC6, 0x70, 0x2B, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x89, 0xDF,
    0x48, 0x89, 0xC6, 0x4C, 0x89, 0xE2, 0x44, 0x89, 0xF9, 0xE8, 0x0B, 0x16, 0x01, 0x00]

theorem code_l10ee37 : ∀ x ∈ codeRange 0x10ee37 bytes_l10ee37, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xee37 46 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ee65 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ee65 (movR64R64Effect 0x10ee65 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10ee65 (fun s => s.RIP = 0x10ee65) (movR64R64Effect 0x10ee65 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10ee68 (addR64Imm32Effect 0x10ee68 4 0xb8) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10ee68 (fun s => s.RIP = 0x10ee68) (addR64Imm32Effect 0x10ee68 4 0xb8) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10ee6f (popR64Effect 0x10ee6f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x10ee6f (popR64Effect 0x10ee6f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x10ee6f (PopPre 0x10ee6f) (popR64Effect 0x10ee6f 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x10ee70 (popR64Effect 0x10ee70 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x10ee70 (popR64Effect 0x10ee70 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10ee70 (PopPre 0x10ee70) (popR64Effect 0x10ee70 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10ee72 (popR64Effect 0x10ee72 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10ee72 (popR64Effect 0x10ee72 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10ee72 (PopPre 0x10ee72) (popR64Effect 0x10ee72 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10ee74 (popR64Effect 0x10ee74 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10ee74 (popR64Effect 0x10ee74 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10ee74 (PopPre 0x10ee74) (popR64Effect 0x10ee74 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10ee76 (popR64Effect 0x10ee76 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10ee76 (popR64Effect 0x10ee76 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10ee76 (PopPre 0x10ee76) (popR64Effect 0x10ee76 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10ee78 (popR64Effect 0x10ee78 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[70]
    (.letOp (n := 73) (.out 0x10ee78 (popR64Effect 0x10ee78 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10ee78 (PopPre 0x10ee78) (popR64Effect 0x10ee78 1 5) (Reg.operands [.gpr 4] [])) #v[70]
    (.letOp (n := 75) (.out 0x10ee79 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[73]
    (.letOp (n := 76) (.out 0x10ee79 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[73]
    (.letOp (n := 77) (.exec 0x10ee79 (RetPre 0x10ee79) (retEffect) (Reg.operands [.gpr 4] [])) #v[73]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 76), (5, 72), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 78) (some ⟨75, by decide⟩)))))))))))))))))))))))))))

def bytes_l10ee65 : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0xB8, 0x00, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10ee65 : ∀ x ∈ codeRange 0x10ee65 bytes_l10ee65, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xee65 21 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ee80_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.out 0x10eed7 (movR64M64Effect 0x10eed7 0 (.base 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[68]
    (.letOp (n := 90) (.exec 0x10eed7 (LoadPre 0x10eed7 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x10eed7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eed7 0 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 91) (.exec 0x10eedb (StorePre 0x10eedb 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x88)) s (0x10eedb + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eedb 0 (.sib 4 none 0 (.d32 0x88))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[89, 66]
    (.letOp (n := 92) (.exec 0x10eee3 (StorePre 0x10eee3 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x80)) s (0x10eee3 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eee3 1 (.sib 4 none 0 (.d32 0x80))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 66]
    (.letOp (n := 93) (.out 0x10eeeb (leaR64Effect 0x10eeeb 14 (.sib 4 none 0 (.d32 0xf08))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[66]
    (.letOp (n := 94) (.exec 0x10eeeb (fun s => s.RIP = 0x10eeeb) (leaR64Effect 0x10eeeb 14 (.sib 4 none 0 (.d32 0xf08))) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 95) (.out 0x10eef3 (leaR64Effect 0x10eef3 13 (.rip 0x1b926)) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 96) (.exec 0x10eef3 (fun s => s.RIP = 0x10eef3) (leaR64Effect 0x10eef3 13 (.rip 0x1b926)) (Reg.operands [] [])) #v[]
    (.letOp (n := 97) (.out 0x10eefa (movR32Imm32Effect 0x10eefa 5 2 0x98) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 98) (.exec 0x10eefa (fun s => s.RIP = 0x10eefa) (movR32Imm32Effect 0x10eefa 5 2 0x98) (Reg.operands [] [])) #v[]
    (.letOp (n := 99) (.out 0x10eeff (movR64R64Effect 0x10eeff 7 14) (EffectPart.reads (.reg (.gpr 7)) [.gpr 14] []) (.reg (.gpr 7))) #v[93]
    (.letOp (n := 100) (.exec 0x10eeff (fun s => s.RIP = 0x10eeff) (movR64R64Effect 0x10eeff 7 14) (Reg.operands [.gpr 14] [])) #v[93]
    (.letOp (n := 101) (.out 0x10ef02 (movR64R64Effect 0x10ef02 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[72]
    (.letOp (n := 102) (.exec 0x10ef02 (fun s => s.RIP = 0x10ef02) (movR64R64Effect 0x10ef02 6 8) (Reg.operands [.gpr 8] [])) #v[72]
    (.letOp (n := 103) (.out 0x10ef05 (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10ef08) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[66, 95]
    (.letOp (n := 104) (.exec 0x10ef05 (GoesTo (CallPre 0x10ef05 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10ef08) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10ef08) (Reg.operands [.gpr 4, .gpr 13] [])) #v[66, 95]
    (.letOp (n := 105) (.const ⟨64, 0x10ef08⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 89), (1, 87), (2, 97), (3, 70), (4, 103), (5, 5), (6, 101), (7, 99), (8, 72), (9, 9), (10, 10), (11, 11), (12, 12), (13, 95), (14, 93), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 106⟩ { target := .l10ef08, kept := #v[], arity := rfl, guard := some (Fin.last 105) }))))))))))))))))))

def bytes_l10ee80_1 : List UInt8 :=
  [0x48, 0x8B, 0x40, 0x08, 0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8C, 0x24,
    0x80, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0xB4, 0x24, 0x08, 0x0F, 0x00, 0x00, 0x4C, 0x8D, 0x2D, 0x26,
    0xB9, 0x01, 0x00, 0xBA, 0x98, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xF7, 0x4C, 0x89, 0xC6, 0x41, 0xFF,
    0xD5]

theorem code_l10ee80_1 : ∀ x ∈ codeRange 0x10eed7 bytes_l10ee80_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xeed7 49 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ee80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ee80 (pushR64Effect 0x10ee80 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x10ee80 (PushPre 0x10ee80 2) (pushR64Effect 0x10ee80 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x10ee82 (pushR64Effect 0x10ee82 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x10ee82 (PushPre 0x10ee82 2) (pushR64Effect 0x10ee82 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x10ee84 (pushR64Effect 0x10ee84 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[55, 13]
    (.letOp (n := 58) (.exec 0x10ee84 (PushPre 0x10ee84 2) (pushR64Effect 0x10ee84 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 59) (.out 0x10ee86 (pushR64Effect 0x10ee86 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[57, 12]
    (.letOp (n := 60) (.exec 0x10ee86 (PushPre 0x10ee86 2) (pushR64Effect 0x10ee86 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[57, 12]
    (.letOp (n := 61) (.out 0x10ee88 (pushR64Effect 0x10ee88 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[59, 3]
    (.letOp (n := 62) (.exec 0x10ee88 (PushPre 0x10ee88 1) (pushR64Effect 0x10ee88 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[59, 3]
    (.letOp (n := 63) (.out 0x10ee89 (subR64Imm32Effect 0x10ee89 4 0x1000) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 64) (.exec 0x10ee89 (fun s => s.RIP = 0x10ee89) (subR64Imm32Effect 0x10ee89 4 0x1000) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 65) (.exec 0x10ee90 (StorePre 0x10ee90 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10ee90 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10ee90 (.sib 4 none 0 .none) 0x0) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 66) (.out 0x10ee98 (subR64Imm32Effect 0x10ee98 4 0x720) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 67) (.exec 0x10ee98 (fun s => s.RIP = 0x10ee98) (subR64Imm32Effect 0x10ee98 4 0x720) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 68) (.out 0x10ee9f (movR64R64Effect 0x10ee9f 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 69) (.exec 0x10ee9f (fun s => s.RIP = 0x10ee9f) (movR64R64Effect 0x10ee9f 0 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 70) (.out 0x10eea2 (movR64R64Effect 0x10eea2 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 7] []) (.reg (.gpr 3))) #v[7]
    (.letOp (n := 71) (.exec 0x10eea2 (fun s => s.RIP = 0x10eea2) (movR64R64Effect 0x10eea2 3 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 72) (.out 0x10eea5 (leaR64Effect 0x10eea5 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[66]
    (.letOp (n := 73) (.exec 0x10eea5 (fun s => s.RIP = 0x10eea5) (leaR64Effect 0x10eea5 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[66]
    (.letOp (n := 74) (.out 0x10eeaa (movR32Imm32Effect 0x10eeaa 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 75) (.exec 0x10eeaa (fun s => s.RIP = 0x10eeaa) (movR32Imm32Effect 0x10eeaa 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 76) (.out 0x10eeaf (movR64R64Effect 0x10eeaf 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[72]
    (.letOp (n := 77) (.exec 0x10eeaf (fun s => s.RIP = 0x10eeaf) (movR64R64Effect 0x10eeaf 7 8) (Reg.operands [.gpr 8] [])) #v[72]
    (.letOp (n := 78) (.out 0x10eeb2 (movR64Imm32Effect 0x10eeb2 6 0x202bc8) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 79) (.exec 0x10eeb2 (fun s => s.RIP = 0x10eeb2) (movR64Imm32Effect 0x10eeb2 6 0x202bc8) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.exec 0x10eeb9 (RepPre 0x10eeb9 (RepMovsqPre 0x10eeb9)) (repMovsqEffect 0x10eeb9) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[78, 76, 74, 22]
    (.letOp (n := 81) (.out 0x10eebc (movR64M64Effect 0x10eebc 1 (.base 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 82) (.exec 0x10eebc (LoadPre 0x10eebc (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x10eebc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eebc 1 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 83) (.exec 0x10eec0 (StorePre 0x10eec0 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x98)) s (0x10eec0 + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eec0 1 (.sib 4 none 0 (.d32 0x98))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 66]
    (.letOp (n := 84) (.out 0x10eec8 (movR64M64Effect 0x10eec8 1 (.base 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 85) (.exec 0x10eec8 (LoadPre 0x10eec8 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x10eec8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10eec8 1 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 86) (.exec 0x10eecc (StorePre 0x10eecc 8 (fun s => AddrMode.addr (.sib 4 none 0 (.d32 0x90)) s (0x10eecc + BitVec.ofNat 64 8)) 8) (movM64R64Effect 0x10eecc 1 (.sib 4 none 0 (.d32 0x90))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 66]
    (.letOp (n := 87) (.out 0x10eed4 (movR64M64Effect 0x10eed4 1 (.base 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 88) (.exec 0x10eed4 (LoadPre 0x10eed4 (fun s => AddrMode.addr (.base 0 .none) s (0x10eed4 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10eed4 1 (.base 0 .none)) (Reg.operands [.gpr 0] [])) #v[68]
    (b_l10ee80_1))))))))))))))))))))))))))))))))))))

def bytes_l10ee80 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xEC, 0x00, 0x10, 0x00, 0x00,
    0x48, 0xC7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0x81, 0xEC, 0x20, 0x07, 0x00, 0x00, 0x48,
    0x89, 0xF0, 0x48, 0x89, 0xFB, 0x4C, 0x8D, 0x44, 0x24, 0x08, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C,
    0x89, 0xC7, 0x48, 0xC7, 0xC6, 0xC8, 0x2B, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8B, 0x48, 0x18,
    0x48, 0x89, 0x8C, 0x24, 0x98, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x48, 0x10, 0x48, 0x89, 0x8C, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x48, 0x8B, 0x08] ++ bytes_l10ee80_1

theorem code_l10ee80 : ∀ x ∈ codeRange 0x10ee80 bytes_l10ee80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xee80 87 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ee80_1

@[cfg_block] def b_l10ef08_3 : Block Op Label signature Reg.count 159 :=
  .letOp (n := 159) (.out 0x10f05d (movR64Imm32Effect 0x10f05d 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 160) (.exec 0x10f05d (fun s => s.RIP = 0x10f05d) (movR64Imm32Effect 0x10f05d 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 161) (.exec 0x10f064 (RepPre 0x10f064 (RepMovsqPre 0x10f064)) (repMovsqEffect 0x10f064) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[159, 155, 157, 22]
    (.letOp (n := 162) (.out 0x10f067 (leaR64Effect 0x10f067 7 (.sib 4 none 0 (.d32 0xe90))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 163) (.exec 0x10f067 (fun s => s.RIP = 0x10f067) (leaR64Effect 0x10f067 7 (.sib 4 none 0 (.d32 0xe90))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 164) (.out 0x10f06f (movR32Imm32Effect 0x10f06f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 165) (.exec 0x10f06f (fun s => s.RIP = 0x10f06f) (movR32Imm32Effect 0x10f06f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 166) (.out 0x10f074 (movR64Imm32Effect 0x10f074 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 167) (.exec 0x10f074 (fun s => s.RIP = 0x10f074) (movR64Imm32Effect 0x10f074 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 168) (.exec 0x10f07b (RepPre 0x10f07b (RepMovsqPre 0x10f07b)) (repMovsqEffect 0x10f07b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[166, 162, 164, 22]
    (.letOp (n := 169) (.out 0x10f07e (leaR64Effect 0x10f07e 12 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[4]
    (.letOp (n := 170) (.exec 0x10f07e (fun s => s.RIP = 0x10f07e) (leaR64Effect 0x10f07e 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 171) (.out 0x10f083 (movR32Imm32Effect 0x10f083 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 172) (.exec 0x10f083 (fun s => s.RIP = 0x10f083) (movR32Imm32Effect 0x10f083 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 173) (.out 0x10f088 (movR64R64Effect 0x10f088 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 12] []) (.reg (.gpr 7))) #v[169]
    (.letOp (n := 174) (.exec 0x10f088 (fun s => s.RIP = 0x10f088) (movR64R64Effect 0x10f088 7 12) (Reg.operands [.gpr 12] [])) #v[169]
    (.letOp (n := 175) (.out 0x10f08b (movR64R64Effect 0x10f08b 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 176) (.exec 0x10f08b (fun s => s.RIP = 0x10f08b) (movR64R64Effect 0x10f08b 6 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 177) (.out 0x10f08e (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f091) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 178) (.exec 0x10f08e (GoesTo (CallPre 0x10f08e 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f091) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f091) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 179) (.const ⟨64, 0x10f091⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(0, 53), (2, 171), (3, 3), (4, 177), (5, 5), (6, 175), (7, 173), (9, 9), (10, 10), (11, 11), (12, 169), (13, 13), (14, 14), (15, 111), (22, 22), (39, 39), (50, 50), (51, 51)] 180⟩ { target := .l10f091, kept := #v[], arity := rfl, guard := some (Fin.last 179) }))))))))))))))))))))))

def bytes_l10ef08_3 : List UInt8 :=
  [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x90, 0x0E,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x4C, 0x8D, 0x64, 0x24, 0x08, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xE7, 0x48, 0x89,
    0xC6, 0x41, 0xFF, 0xD5]

theorem code_l10ef08_3 : ∀ x ∈ codeRange 0x10f05d bytes_l10ef08_3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf05d 52 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10ef08_2 : Block Op Label signature Reg.count 124 :=
  .letOp (n := 124) (.out 0x10efea (movR64Imm32Effect 0x10efea 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 125) (.exec 0x10efea (fun s => s.RIP = 0x10efea) (movR64Imm32Effect 0x10efea 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 126) (.exec 0x10eff1 (RepPre 0x10eff1 (RepMovsqPre 0x10eff1)) (repMovsqEffect 0x10eff1) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[124, 120, 122, 22]
    (.letOp (n := 127) (.out 0x10eff4 (leaR64Effect 0x10eff4 7 (.sib 4 none 0 (.d32 0xc38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 128) (.exec 0x10eff4 (fun s => s.RIP = 0x10eff4) (leaR64Effect 0x10eff4 7 (.sib 4 none 0 (.d32 0xc38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 129) (.out 0x10effc (movR32Imm32Effect 0x10effc 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 130) (.exec 0x10effc (fun s => s.RIP = 0x10effc) (movR32Imm32Effect 0x10effc 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 131) (.out 0x10f001 (movR64Imm32Effect 0x10f001 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 132) (.exec 0x10f001 (fun s => s.RIP = 0x10f001) (movR64Imm32Effect 0x10f001 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 133) (.exec 0x10f008 (RepPre 0x10f008 (RepMovsqPre 0x10f008)) (repMovsqEffect 0x10f008) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[131, 127, 129, 22]
    (.letOp (n := 134) (.out 0x10f00b (leaR64Effect 0x10f00b 7 (.sib 4 none 0 (.d32 0xcb0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 135) (.exec 0x10f00b (fun s => s.RIP = 0x10f00b) (leaR64Effect 0x10f00b 7 (.sib 4 none 0 (.d32 0xcb0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 136) (.out 0x10f013 (movR32Imm32Effect 0x10f013 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 137) (.exec 0x10f013 (fun s => s.RIP = 0x10f013) (movR32Imm32Effect 0x10f013 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 138) (.out 0x10f018 (movR64Imm32Effect 0x10f018 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 139) (.exec 0x10f018 (fun s => s.RIP = 0x10f018) (movR64Imm32Effect 0x10f018 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 140) (.exec 0x10f01f (RepPre 0x10f01f (RepMovsqPre 0x10f01f)) (repMovsqEffect 0x10f01f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[138, 134, 136, 22]
    (.letOp (n := 141) (.out 0x10f022 (leaR64Effect 0x10f022 7 (.sib 4 none 0 (.d32 0xd28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 142) (.exec 0x10f022 (fun s => s.RIP = 0x10f022) (leaR64Effect 0x10f022 7 (.sib 4 none 0 (.d32 0xd28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 143) (.out 0x10f02a (movR32Imm32Effect 0x10f02a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 144) (.exec 0x10f02a (fun s => s.RIP = 0x10f02a) (movR32Imm32Effect 0x10f02a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 145) (.out 0x10f02f (movR64Imm32Effect 0x10f02f 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 146) (.exec 0x10f02f (fun s => s.RIP = 0x10f02f) (movR64Imm32Effect 0x10f02f 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 147) (.exec 0x10f036 (RepPre 0x10f036 (RepMovsqPre 0x10f036)) (repMovsqEffect 0x10f036) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[145, 141, 143, 22]
    (.letOp (n := 148) (.out 0x10f039 (leaR64Effect 0x10f039 7 (.sib 4 none 0 (.d32 0xda0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 149) (.exec 0x10f039 (fun s => s.RIP = 0x10f039) (leaR64Effect 0x10f039 7 (.sib 4 none 0 (.d32 0xda0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 150) (.out 0x10f041 (movR32Imm32Effect 0x10f041 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 151) (.exec 0x10f041 (fun s => s.RIP = 0x10f041) (movR32Imm32Effect 0x10f041 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 152) (.out 0x10f046 (movR64Imm32Effect 0x10f046 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 153) (.exec 0x10f046 (fun s => s.RIP = 0x10f046) (movR64Imm32Effect 0x10f046 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 154) (.exec 0x10f04d (RepPre 0x10f04d (RepMovsqPre 0x10f04d)) (repMovsqEffect 0x10f04d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[152, 148, 150, 22]
    (.letOp (n := 155) (.out 0x10f050 (leaR64Effect 0x10f050 7 (.sib 4 none 0 (.d32 0xe18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 156) (.exec 0x10f050 (fun s => s.RIP = 0x10f050) (leaR64Effect 0x10f050 7 (.sib 4 none 0 (.d32 0xe18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 157) (.out 0x10f058 (movR32Imm32Effect 0x10f058 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 158) (.exec 0x10f058 (fun s => s.RIP = 0x10f058) (movR32Imm32Effect 0x10f058 5 1 0xf) (Reg.operands [] [])) #v[]
    (b_l10ef08_3)))))))))))))))))))))))))))))))))))

def bytes_l10ef08_2 : List UInt8 :=
  [0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x38, 0x0C,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xB0, 0x0C, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x28, 0x0D, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48,
    0x8D, 0xBC, 0x24, 0xA0, 0x0D, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40,
    0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x18, 0x0E, 0x00, 0x00, 0xB9, 0x0F,
    0x00, 0x00, 0x00] ++ bytes_l10ef08_3

theorem code_l10ef08_2 : ∀ x ∈ codeRange 0x10efea bytes_l10ef08_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xefea 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ef08_3

@[cfg_block] def b_l10ef08_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x10ef7b (RepPre 0x10ef7b (RepMovsqPre 0x10ef7b)) (repMovsqEffect 0x10ef7b) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[87, 83, 85, 22]
    (.letOp (n := 90) (.out 0x10ef7e (leaR64Effect 0x10ef7e 7 (.sib 4 none 0 (.d32 0x9e0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 91) (.exec 0x10ef7e (fun s => s.RIP = 0x10ef7e) (leaR64Effect 0x10ef7e 7 (.sib 4 none 0 (.d32 0x9e0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 92) (.out 0x10ef86 (movR32Imm32Effect 0x10ef86 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 93) (.exec 0x10ef86 (fun s => s.RIP = 0x10ef86) (movR32Imm32Effect 0x10ef86 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 94) (.out 0x10ef8b (movR64Imm32Effect 0x10ef8b 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 95) (.exec 0x10ef8b (fun s => s.RIP = 0x10ef8b) (movR64Imm32Effect 0x10ef8b 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 96) (.exec 0x10ef92 (RepPre 0x10ef92 (RepMovsqPre 0x10ef92)) (repMovsqEffect 0x10ef92) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[94, 90, 92, 22]
    (.letOp (n := 97) (.out 0x10ef95 (leaR64Effect 0x10ef95 7 (.sib 4 none 0 (.d32 0xa58))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 98) (.exec 0x10ef95 (fun s => s.RIP = 0x10ef95) (leaR64Effect 0x10ef95 7 (.sib 4 none 0 (.d32 0xa58))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 99) (.out 0x10ef9d (movR32Imm32Effect 0x10ef9d 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 100) (.exec 0x10ef9d (fun s => s.RIP = 0x10ef9d) (movR32Imm32Effect 0x10ef9d 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 101) (.out 0x10efa2 (movR64Imm32Effect 0x10efa2 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 102) (.exec 0x10efa2 (fun s => s.RIP = 0x10efa2) (movR64Imm32Effect 0x10efa2 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 103) (.exec 0x10efa9 (RepPre 0x10efa9 (RepMovsqPre 0x10efa9)) (repMovsqEffect 0x10efa9) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[101, 97, 99, 22]
    (.letOp (n := 104) (.out 0x10efac (leaR64Effect 0x10efac 7 (.sib 4 none 0 (.d32 0xad0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 105) (.exec 0x10efac (fun s => s.RIP = 0x10efac) (leaR64Effect 0x10efac 7 (.sib 4 none 0 (.d32 0xad0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 106) (.out 0x10efb4 (movR32Imm32Effect 0x10efb4 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 107) (.exec 0x10efb4 (fun s => s.RIP = 0x10efb4) (movR32Imm32Effect 0x10efb4 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 108) (.out 0x10efb9 (movR64Imm32Effect 0x10efb9 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 109) (.exec 0x10efb9 (fun s => s.RIP = 0x10efb9) (movR64Imm32Effect 0x10efb9 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 110) (.exec 0x10efc0 (RepPre 0x10efc0 (RepMovsqPre 0x10efc0)) (repMovsqEffect 0x10efc0) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[108, 104, 106, 22]
    (.letOp (n := 111) (.out 0x10efc3 (leaR64Effect 0x10efc3 15 (.sib 4 none 0 (.d32 0xb48))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 112) (.exec 0x10efc3 (fun s => s.RIP = 0x10efc3) (leaR64Effect 0x10efc3 15 (.sib 4 none 0 (.d32 0xb48))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 113) (.out 0x10efcb (movR32Imm32Effect 0x10efcb 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 114) (.exec 0x10efcb (fun s => s.RIP = 0x10efcb) (movR32Imm32Effect 0x10efcb 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 115) (.out 0x10efd0 (movR64R64Effect 0x10efd0 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[111]
    (.letOp (n := 116) (.exec 0x10efd0 (fun s => s.RIP = 0x10efd0) (movR64R64Effect 0x10efd0 7 15) (Reg.operands [.gpr 15] [])) #v[111]
    (.letOp (n := 117) (.out 0x10efd3 (movR64Imm32Effect 0x10efd3 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 118) (.exec 0x10efd3 (fun s => s.RIP = 0x10efd3) (movR64Imm32Effect 0x10efd3 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 119) (.exec 0x10efda (RepPre 0x10efda (RepMovsqPre 0x10efda)) (repMovsqEffect 0x10efda) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[117, 115, 113, 22]
    (.letOp (n := 120) (.out 0x10efdd (leaR64Effect 0x10efdd 7 (.sib 4 none 0 (.d32 0xbc0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 121) (.exec 0x10efdd (fun s => s.RIP = 0x10efdd) (leaR64Effect 0x10efdd 7 (.sib 4 none 0 (.d32 0xbc0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 122) (.out 0x10efe5 (movR32Imm32Effect 0x10efe5 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 123) (.exec 0x10efe5 (fun s => s.RIP = 0x10efe5) (movR32Imm32Effect 0x10efe5 5 1 0xf) (Reg.operands [] [])) #v[]
    (b_l10ef08_2)))))))))))))))))))))))))))))))))))

def bytes_l10ef08_1 : List UInt8 :=
  [0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xE0, 0x09, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x58, 0x0A,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xD0, 0x0A, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x4C, 0x8D, 0xBC, 0x24, 0x48, 0x0B, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x4C, 0x89, 0xFF, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3,
    0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xC0, 0x0B, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00] ++ bytes_l10ef08_2

theorem code_l10ef08_1 : ∀ x ∈ codeRange 0x10ef7b bytes_l10ef08_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xef7b 111 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ef08_2

@[cfg_block] def b_l10ef08 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10ef08 (leaR64Effect 0x10ef08 0 (.sib 4 none 0 (.d32 0x788))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 54) (.exec 0x10ef08 (fun s => s.RIP = 0x10ef08) (leaR64Effect 0x10ef08 0 (.sib 4 none 0 (.d32 0x788))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10ef10 (movR32Imm32Effect 0x10ef10 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 56) (.exec 0x10ef10 (fun s => s.RIP = 0x10ef10) (movR32Imm32Effect 0x10ef10 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10ef15 (movR64R64Effect 0x10ef15 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10ef15 (fun s => s.RIP = 0x10ef15) (movR64R64Effect 0x10ef15 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 59) (.out 0x10ef18 (movR64Imm32Effect 0x10ef18 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 60) (.exec 0x10ef18 (fun s => s.RIP = 0x10ef18) (movR64Imm32Effect 0x10ef18 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 61) (.exec 0x10ef1f (RepPre 0x10ef1f (RepMovsqPre 0x10ef1f)) (repMovsqEffect 0x10ef1f) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[59, 57, 55, 22]
    (.letOp (n := 62) (.out 0x10ef22 (leaR64Effect 0x10ef22 7 (.sib 4 none 0 (.d32 0x800))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 63) (.exec 0x10ef22 (fun s => s.RIP = 0x10ef22) (leaR64Effect 0x10ef22 7 (.sib 4 none 0 (.d32 0x800))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x10ef2a (movR32Imm32Effect 0x10ef2a 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 65) (.exec 0x10ef2a (fun s => s.RIP = 0x10ef2a) (movR32Imm32Effect 0x10ef2a 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 66) (.out 0x10ef2f (movR64Imm32Effect 0x10ef2f 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 67) (.exec 0x10ef2f (fun s => s.RIP = 0x10ef2f) (movR64Imm32Effect 0x10ef2f 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 68) (.exec 0x10ef36 (RepPre 0x10ef36 (RepMovsqPre 0x10ef36)) (repMovsqEffect 0x10ef36) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[66, 62, 64, 22]
    (.letOp (n := 69) (.out 0x10ef39 (leaR64Effect 0x10ef39 7 (.sib 4 none 0 (.d32 0x878))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 70) (.exec 0x10ef39 (fun s => s.RIP = 0x10ef39) (leaR64Effect 0x10ef39 7 (.sib 4 none 0 (.d32 0x878))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x10ef41 (movR32Imm32Effect 0x10ef41 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 72) (.exec 0x10ef41 (fun s => s.RIP = 0x10ef41) (movR32Imm32Effect 0x10ef41 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 73) (.out 0x10ef46 (movR64Imm32Effect 0x10ef46 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 74) (.exec 0x10ef46 (fun s => s.RIP = 0x10ef46) (movR64Imm32Effect 0x10ef46 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.exec 0x10ef4d (RepPre 0x10ef4d (RepMovsqPre 0x10ef4d)) (repMovsqEffect 0x10ef4d) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[73, 69, 71, 22]
    (.letOp (n := 76) (.out 0x10ef50 (leaR64Effect 0x10ef50 7 (.sib 4 none 0 (.d32 0x8f0))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 77) (.exec 0x10ef50 (fun s => s.RIP = 0x10ef50) (leaR64Effect 0x10ef50 7 (.sib 4 none 0 (.d32 0x8f0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 78) (.out 0x10ef58 (movR32Imm32Effect 0x10ef58 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 79) (.exec 0x10ef58 (fun s => s.RIP = 0x10ef58) (movR32Imm32Effect 0x10ef58 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 80) (.out 0x10ef5d (movR64Imm32Effect 0x10ef5d 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 81) (.exec 0x10ef5d (fun s => s.RIP = 0x10ef5d) (movR64Imm32Effect 0x10ef5d 6 0x202c40) (Reg.operands [] [])) #v[]
    (.letOp (n := 82) (.exec 0x10ef64 (RepPre 0x10ef64 (RepMovsqPre 0x10ef64)) (repMovsqEffect 0x10ef64) (Reg.operands [.gpr 6, .gpr 7, .gpr 1, .df] [])) #v[80, 76, 78, 22]
    (.letOp (n := 83) (.out 0x10ef67 (leaR64Effect 0x10ef67 7 (.sib 4 none 0 (.d32 0x968))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 84) (.exec 0x10ef67 (fun s => s.RIP = 0x10ef67) (leaR64Effect 0x10ef67 7 (.sib 4 none 0 (.d32 0x968))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 85) (.out 0x10ef6f (movR32Imm32Effect 0x10ef6f 5 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 86) (.exec 0x10ef6f (fun s => s.RIP = 0x10ef6f) (movR32Imm32Effect 0x10ef6f 5 1 0xf) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x10ef74 (movR64Imm32Effect 0x10ef74 6 0x202c40) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 88) (.exec 0x10ef74 (fun s => s.RIP = 0x10ef74) (movR64Imm32Effect 0x10ef74 6 0x202c40) (Reg.operands [] [])) #v[]
    (b_l10ef08_1))))))))))))))))))))))))))))))))))))

def bytes_l10ef08 : List UInt8 :=
  [0x48, 0x8D, 0x84, 0x24, 0x88, 0x07, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0x89, 0xC7,
    0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x00, 0x08,
    0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48,
    0xA5, 0x48, 0x8D, 0xBC, 0x24, 0x78, 0x08, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7,
    0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48, 0x8D, 0xBC, 0x24, 0xF0, 0x08, 0x00, 0x00,
    0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40, 0x2C, 0x20, 0x00, 0xF3, 0x48, 0xA5, 0x48,
    0x8D, 0xBC, 0x24, 0x68, 0x09, 0x00, 0x00, 0xB9, 0x0F, 0x00, 0x00, 0x00, 0x48, 0xC7, 0xC6, 0x40,
    0x2C, 0x20, 0x00] ++ bytes_l10ef08_1

theorem code_l10ef08 : ∀ x ∈ codeRange 0x10ef08 bytes_l10ef08, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xef08 115 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10ef08_1

@[cfg_block] def b_l10f091 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f091 (leaR64Effect 0x10f091 7 (.sib 4 none 0 (.d32 0x3c8))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 54) (.exec 0x10f091 (fun s => s.RIP = 0x10f091) (leaR64Effect 0x10f091 7 (.sib 4 none 0 (.d32 0x3c8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f099 (movR32Imm32Effect 0x10f099 5 2 0x3c0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10f099 (fun s => s.RIP = 0x10f099) (movR32Imm32Effect 0x10f099 5 2 0x3c0) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f09e (movR64R64Effect 0x10f09e 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 15] []) (.reg (.gpr 6))) #v[15]
    (.letOp (n := 58) (.exec 0x10f09e (fun s => s.RIP = 0x10f09e) (movR64R64Effect 0x10f09e 6 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 59) (.out 0x10f0a1 (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0a4) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 60) (.exec 0x10f0a1 (GoesTo (CallPre 0x10f0a1 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0a4) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0a4) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 61) (.const ⟨64, 0x10f0a4⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 59), (5, 5), (6, 57), (7, 53), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l10f0a4, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l10f091 : List UInt8 :=
  [0x48, 0x8D, 0xBC, 0x24, 0xC8, 0x03, 0x00, 0x00, 0xBA, 0xC0, 0x03, 0x00, 0x00, 0x4C, 0x89, 0xFE,
    0x41, 0xFF, 0xD5]

theorem code_l10f091 : ∀ x ∈ codeRange 0x10f091 bytes_l10f091, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf091 19 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f0a4 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f0a4 (leaR64Effect 0x10f0a4 15 (.sib 4 none 0 (.d32 0xfa0))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[4]
    (.letOp (n := 54) (.exec 0x10f0a4 (fun s => s.RIP = 0x10f0a4) (leaR64Effect 0x10f0a4 15 (.sib 4 none 0 (.d32 0xfa0))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x10f0ac (movR32Imm32Effect 0x10f0ac 5 2 0x780) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 56) (.exec 0x10f0ac (fun s => s.RIP = 0x10f0ac) (movR32Imm32Effect 0x10f0ac 5 2 0x780) (Reg.operands [] [])) #v[]
    (.letOp (n := 57) (.out 0x10f0b1 (movR64R64Effect 0x10f0b1 7 15) (EffectPart.reads (.reg (.gpr 7)) [.gpr 15] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 58) (.exec 0x10f0b1 (fun s => s.RIP = 0x10f0b1) (movR64R64Effect 0x10f0b1 7 15) (Reg.operands [.gpr 15] [])) #v[53]
    (.letOp (n := 59) (.out 0x10f0b4 (movR64R64Effect 0x10f0b4 6 12) (EffectPart.reads (.reg (.gpr 6)) [.gpr 12] []) (.reg (.gpr 6))) #v[12]
    (.letOp (n := 60) (.exec 0x10f0b4 (fun s => s.RIP = 0x10f0b4) (movR64R64Effect 0x10f0b4 6 12) (Reg.operands [.gpr 12] [])) #v[12]
    (.letOp (n := 61) (.out 0x10f0b7 (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0ba) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[4, 13]
    (.letOp (n := 62) (.exec 0x10f0b7 (GoesTo (CallPre 0x10f0b7 3 (fun s => (Operand.reg 13 : Operand 64).read s)) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0ba) 0x12a820) (callEffect (fun s => (Operand.reg 13 : Operand 64).read s) 0x10f0ba) (Reg.operands [.gpr 4, .gpr 13] [])) #v[4, 13]
    (.letOp (n := 63) (.const ⟨64, 0x10f0ba⟩) #v[]
    (.terminate (.call ⟨.l12a820, RegMap.args [(2, 55), (3, 3), (4, 61), (5, 5), (6, 59), (7, 57), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 53), (22, 22), (39, 39), (50, 50), (51, 51)] 64⟩ { target := .l10f0ba, kept := #v[], arity := rfl, guard := some (Fin.last 63) }))))))))))))

def bytes_l10f0a4 : List UInt8 :=
  [0x4C, 0x8D, 0xBC, 0x24, 0xA0, 0x0F, 0x00, 0x00, 0xBA, 0x80, 0x07, 0x00, 0x00, 0x4C, 0x89, 0xFF,
    0x4C, 0x89, 0xE6, 0x41, 0xFF, 0xD5]

theorem code_l10f0a4 : ∀ x ∈ codeRange 0x10f0a4 bytes_l10f0a4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf0a4 22 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f0ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x10f0ba (StorePre 0x10f0ba 7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x48)) s (0x10f0ba + BitVec.ofNat 64 7)) 2) (movM16Imm16Effect 0x10f0ba (.sib 4 none 0 (.d8 0x48)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x10f0c1 (StorePre 0x10f0c1 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x10f0c1 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0c1 (.sib 4 none 0 (.d8 0x40)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x10f0ca (StorePre 0x10f0ca 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x10f0ca + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0ca (.sib 4 none 0 (.d8 0x38)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 56) (.exec 0x10f0d3 (StorePre 0x10f0d3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x10f0d3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0d3 (.sib 4 none 0 (.d8 0x30)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.exec 0x10f0dc (StorePre 0x10f0dc 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x10f0dc + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0dc (.sib 4 none 0 (.d8 0x28)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x10f0e5 (StorePre 0x10f0e5 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x10f0e5 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0e5 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.exec 0x10f0ee (StorePre 0x10f0ee 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10f0ee + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0ee (.sib 4 none 0 (.d8 0x18)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.exec 0x10f0f7 (StorePre 0x10f0f7 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10f0f7 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f0f7 (.sib 4 none 0 (.d8 0x10)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x10f100 (StorePre 0x10f100 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10f100 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x10f100 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 62) (.exec 0x10f109 (StorePre 0x10f109 8 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10f109 + BitVec.ofNat 64 8)) 8) (movM64Imm32Effect 0x10f109 (.sib 4 none 0 .none) 0x1) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x10f111 (leaR64Effect 0x10f111 9 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[4]
    (.letOp (n := 64) (.exec 0x10f111 (fun s => s.RIP = 0x10f111) (leaR64Effect 0x10f111 9 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x10f116 (movR32Imm32Effect 0x10f116 5 2 0x1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 66) (.exec 0x10f116 (fun s => s.RIP = 0x10f116) (movR32Imm32Effect 0x10f116 5 2 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 67) (.out 0x10f11b (movR32Imm32Effect 0x10f11b 6 8 0x1) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 68) (.exec 0x10f11b (fun s => s.RIP = 0x10f11b) (movR32Imm32Effect 0x10f11b 6 8 0x1) (Reg.operands [] [])) #v[]
    (.letOp (n := 69) (.out 0x10f121 (movR64R64Effect 0x10f121 7 3) (EffectPart.reads (.reg (.gpr 7)) [.gpr 3] []) (.reg (.gpr 7))) #v[3]
    (.letOp (n := 70) (.exec 0x10f121 (fun s => s.RIP = 0x10f121) (movR64R64Effect 0x10f121 7 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 71) (.out 0x10f124 (movR64R64Effect 0x10f124 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 14] []) (.reg (.gpr 6))) #v[14]
    (.letOp (n := 72) (.exec 0x10f124 (fun s => s.RIP = 0x10f124) (movR64R64Effect 0x10f124 6 14) (Reg.operands [.gpr 14] [])) #v[14]
    (.letOp (n := 73) (.out 0x10f127 (movR64R64Effect 0x10f127 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 15] []) (.reg (.gpr 1))) #v[15]
    (.letOp (n := 74) (.exec 0x10f127 (fun s => s.RIP = 0x10f127) (movR64R64Effect 0x10f127 1 15) (Reg.operands [.gpr 15] [])) #v[15]
    (.letOp (n := 75) (.out 0x10f12a (callEffect (fun _ => 0x11c880) 0x10f12f) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 76) (.exec 0x10f12a (PushPre 0x10f12a 5) (callEffect (fun _ => 0x11c880) 0x10f12f) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.const ⟨64, 0x10f12f⟩) #v[]
    (.terminate (.call ⟨.l11c880, RegMap.args [(1, 73), (2, 65), (3, 3), (4, 75), (5, 5), (6, 71), (7, 69), (8, 67), (9, 63), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 78⟩ { target := .l10f12f, kept := #v[], arity := rfl, guard := some (Fin.last 77) }))))))))))))))))))))))))))

def bytes_l10f0ba : List UInt8 :=
  [0x66, 0xC7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x40, 0x00, 0x00, 0x00, 0x00,
    0x48, 0xC7, 0x44, 0x24, 0x38, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x30, 0x00, 0x00,
    0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x20,
    0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44,
    0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48,
    0xC7, 0x04, 0x24, 0x01, 0x00, 0x00, 0x00, 0x4C, 0x8D, 0x4C, 0x24, 0x08, 0xBA, 0x01, 0x00, 0x00,
    0x00, 0x41, 0xB8, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xDF, 0x4C, 0x89, 0xF6, 0x4C, 0x89, 0xF9,
    0xE8, 0x51, 0xD7, 0x00, 0x00]

theorem code_l10f0ba : ∀ x ∈ codeRange 0x10f0ba bytes_l10f0ba, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf0ba 117 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10f12f : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10f12f (movR64R64Effect 0x10f12f 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[3]
    (.letOp (n := 54) (.exec 0x10f12f (fun s => s.RIP = 0x10f12f) (movR64R64Effect 0x10f12f 0 3) (Reg.operands [.gpr 3] [])) #v[3]
    (.letOp (n := 55) (.out 0x10f132 (addR64Imm32Effect 0x10f132 4 0x1720) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 56) (.exec 0x10f132 (fun s => s.RIP = 0x10f132) (addR64Imm32Effect 0x10f132 4 0x1720) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x10f139 (popR64Effect 0x10f139 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[55]
    (.letOp (n := 58) (.out 0x10f139 (popR64Effect 0x10f139 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[55]
    (.letOp (n := 59) (.exec 0x10f139 (PopPre 0x10f139) (popR64Effect 0x10f139 1 3) (Reg.operands [.gpr 4] [])) #v[55]
    (.letOp (n := 60) (.out 0x10f13a (popR64Effect 0x10f13a 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[58]
    (.letOp (n := 61) (.out 0x10f13a (popR64Effect 0x10f13a 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[58]
    (.letOp (n := 62) (.exec 0x10f13a (PopPre 0x10f13a) (popR64Effect 0x10f13a 2 12) (Reg.operands [.gpr 4] [])) #v[58]
    (.letOp (n := 63) (.out 0x10f13c (popR64Effect 0x10f13c 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[61]
    (.letOp (n := 64) (.out 0x10f13c (popR64Effect 0x10f13c 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 65) (.exec 0x10f13c (PopPre 0x10f13c) (popR64Effect 0x10f13c 2 13) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 66) (.out 0x10f13e (popR64Effect 0x10f13e 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[64]
    (.letOp (n := 67) (.out 0x10f13e (popR64Effect 0x10f13e 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[64]
    (.letOp (n := 68) (.exec 0x10f13e (PopPre 0x10f13e) (popR64Effect 0x10f13e 2 14) (Reg.operands [.gpr 4] [])) #v[64]
    (.letOp (n := 69) (.out 0x10f140 (popR64Effect 0x10f140 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 70) (.out 0x10f140 (popR64Effect 0x10f140 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[67]
    (.letOp (n := 71) (.exec 0x10f140 (PopPre 0x10f140) (popR64Effect 0x10f140 2 15) (Reg.operands [.gpr 4] [])) #v[67]
    (.letOp (n := 72) (.out 0x10f142 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[70]
    (.letOp (n := 73) (.out 0x10f142 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[70]
    (.letOp (n := 74) (.exec 0x10f142 (RetPre 0x10f142) (retEffect) (Reg.operands [.gpr 4] [])) #v[70]
    (.terminate (.ret (RegMap.args [(0, 53), (1, 1), (2, 2), (3, 57), (4, 73), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 60), (13, 63), (14, 66), (15, 69), (22, 22), (39, 39), (50, 50), (51, 51)] 75) (some ⟨72, by decide⟩))))))))))))))))))))))))

def bytes_l10f12f : List UInt8 :=
  [0x48, 0x89, 0xD8, 0x48, 0x81, 0xC4, 0x20, 0x17, 0x00, 0x00, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41,
    0x5E, 0x41, 0x5F, 0xC3]

theorem code_l10f12f : ∀ x ∈ codeRange 0x10f12f bytes_l10f12f, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xf12f 20 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fcc0_5 : Block Op Label signature Reg.count 243 :=
  .letOp (n := 243) (.exec 0x10fe14 (StorePre 0x10fe14 4 (fun s => AddrMode.addr (.base 7 (.d8 0x30)) s (0x10fe14 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe14 14 (.base 7 (.d8 0x30))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[147, 7]
    (.letOp (n := 244) (.exec 0x10fe18 (StorePre 0x10fe18 4 (fun s => AddrMode.addr (.base 7 (.d8 0x38)) s (0x10fe18 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe18 15 (.base 7 (.d8 0x38))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[157, 7]
    (.letOp (n := 245) (.exec 0x10fe1c (StorePre 0x10fe1c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x40)) s (0x10fe1c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe1c 12 (.base 7 (.d8 0x40))) (Reg.operands [.gpr 12, .gpr 7] [])) #v[167, 7]
    (.letOp (n := 246) (.exec 0x10fe20 (StorePre 0x10fe20 4 (fun s => AddrMode.addr (.base 7 (.d8 0x48)) s (0x10fe20 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe20 13 (.base 7 (.d8 0x48))) (Reg.operands [.gpr 13, .gpr 7] [])) #v[177, 7]
    (.letOp (n := 247) (.exec 0x10fe24 (StorePre 0x10fe24 4 (fun s => AddrMode.addr (.base 7 (.d8 0x50)) s (0x10fe24 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe24 5 (.base 7 (.d8 0x50))) (Reg.operands [.gpr 5, .gpr 7] [])) #v[187, 7]
    (.letOp (n := 248) (.exec 0x10fe28 (StorePre 0x10fe28 4 (fun s => AddrMode.addr (.base 7 (.d8 0x58)) s (0x10fe28 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe28 6 (.base 7 (.d8 0x58))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[197, 7]
    (.letOp (n := 249) (.exec 0x10fe2c (StorePre 0x10fe2c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x60)) s (0x10fe2c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe2c 1 (.base 7 (.d8 0x60))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[207, 7]
    (.letOp (n := 250) (.exec 0x10fe30 (StorePre 0x10fe30 4 (fun s => AddrMode.addr (.base 7 (.d8 0x68)) s (0x10fe30 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe30 0 (.base 7 (.d8 0x68))) (Reg.operands [.gpr 0, .gpr 7] [])) #v[217, 7]
    (.letOp (n := 251) (.exec 0x10fe34 (StorePre 0x10fe34 4 (fun s => AddrMode.addr (.base 7 (.d8 0x70)) s (0x10fe34 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe34 9 (.base 7 (.d8 0x70))) (Reg.operands [.gpr 9, .gpr 7] [])) #v[227, 7]
    (.letOp (n := 252) (.out 0x10fe38 (movR64R64Effect 0x10fe38 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 253) (.exec 0x10fe38 (fun s => s.RIP = 0x10fe38) (movR64R64Effect 0x10fe38 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 254) (.out 0x10fe3b (addR64Imm8Effect 0x10fe3b 4 0x20) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 255) (.exec 0x10fe3b (fun s => s.RIP = 0x10fe3b) (addR64Imm8Effect 0x10fe3b 4 0x20) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 256) (.out 0x10fe3f (popR64Effect 0x10fe3f 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[254]
    (.letOp (n := 257) (.out 0x10fe3f (popR64Effect 0x10fe3f 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[254]
    (.letOp (n := 258) (.exec 0x10fe3f (PopPre 0x10fe3f) (popR64Effect 0x10fe3f 1 3) (Reg.operands [.gpr 4] [])) #v[254]
    (.letOp (n := 259) (.out 0x10fe40 (popR64Effect 0x10fe40 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[257]
    (.letOp (n := 260) (.out 0x10fe40 (popR64Effect 0x10fe40 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[257]
    (.letOp (n := 261) (.exec 0x10fe40 (PopPre 0x10fe40) (popR64Effect 0x10fe40 2 12) (Reg.operands [.gpr 4] [])) #v[257]
    (.letOp (n := 262) (.out 0x10fe42 (popR64Effect 0x10fe42 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[260]
    (.letOp (n := 263) (.out 0x10fe42 (popR64Effect 0x10fe42 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[260]
    (.letOp (n := 264) (.exec 0x10fe42 (PopPre 0x10fe42) (popR64Effect 0x10fe42 2 13) (Reg.operands [.gpr 4] [])) #v[260]
    (.letOp (n := 265) (.out 0x10fe44 (popR64Effect 0x10fe44 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[263]
    (.letOp (n := 266) (.out 0x10fe44 (popR64Effect 0x10fe44 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[263]
    (.letOp (n := 267) (.exec 0x10fe44 (PopPre 0x10fe44) (popR64Effect 0x10fe44 2 14) (Reg.operands [.gpr 4] [])) #v[263]
    (.letOp (n := 268) (.out 0x10fe46 (popR64Effect 0x10fe46 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[266]
    (.letOp (n := 269) (.out 0x10fe46 (popR64Effect 0x10fe46 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[266]
    (.letOp (n := 270) (.exec 0x10fe46 (PopPre 0x10fe46) (popR64Effect 0x10fe46 2 15) (Reg.operands [.gpr 4] [])) #v[266]
    (.letOp (n := 271) (.out 0x10fe48 (popR64Effect 0x10fe48 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[269]
    (.letOp (n := 272) (.out 0x10fe48 (popR64Effect 0x10fe48 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[269]
    (.letOp (n := 273) (.exec 0x10fe48 (PopPre 0x10fe48) (popR64Effect 0x10fe48 1 5) (Reg.operands [.gpr 4] [])) #v[269]
    (.letOp (n := 274) (.out 0x10fe49 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[272]
    (.letOp (n := 275) (.out 0x10fe49 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[272]
    (.letOp (n := 276) (.exec 0x10fe49 (RetPre 0x10fe49) (retEffect) (Reg.operands [.gpr 4] [])) #v[272]
    (.terminate (.ret (RegMap.args [(0, 252), (1, 207), (2, 238), (3, 256), (4, 275), (5, 271), (6, 197), (7, 7), (8, 219), (9, 227), (10, 209), (11, 127), (12, 259), (13, 262), (14, 265), (15, 268), (22, 22), (39, 39), (50, 50), (51, 51)] 277) (some ⟨274, by decide⟩))))))))))))))))))))))))))))))))))))

def bytes_l10fcc0_5 : List UInt8 :=
  [0x4C, 0x89, 0x77, 0x30, 0x4C, 0x89, 0x7F, 0x38, 0x4C, 0x89, 0x67, 0x40, 0x4C, 0x89, 0x6F, 0x48,
    0x48, 0x89, 0x6F, 0x50, 0x48, 0x89, 0x77, 0x58, 0x48, 0x89, 0x4F, 0x60, 0x48, 0x89, 0x47, 0x68,
    0x4C, 0x89, 0x4F, 0x70, 0x48, 0x89, 0xF8, 0x48, 0x83, 0xC4, 0x20, 0x5B, 0x41, 0x5C, 0x41, 0x5D,
    0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l10fcc0_5 : ∀ x ∈ codeRange 0x10fe14 bytes_l10fcc0_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfe14 54 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l10fcc0_4 : Block Op Label signature Reg.count 209 :=
  .letOp (n := 209) (.out 0x10fdc8 (movR64M64Effect 0x10fdc8 10 (.base 8 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 8] []) (.reg (.gpr 10))) #v[69]
    (.letOp (n := 210) (.exec 0x10fdc8 (LoadPre 0x10fdc8 (fun s => AddrMode.addr (.base 8 (.d8 0x68)) s (0x10fdc8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdc8 10 (.base 8 (.d8 0x68))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 211) (.out 0x10fdcc (movR64M64Effect 0x10fdcc 0 (.base 9 (.d8 0x68))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 212) (.exec 0x10fdcc (LoadPre 0x10fdcc (fun s => AddrMode.addr (.base 9 (.d8 0x68)) s (0x10fdcc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdcc 0 (.base 9 (.d8 0x68))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 213) (.out 0x10fdd0 (xorR64R64Effect 0x10fdd0 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[211, 209]
    (.letOp (n := 214) (.exec 0x10fdd0 (fun s => s.RIP = 0x10fdd0) (xorR64R64Effect 0x10fdd0 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[211, 209]
    (.letOp (n := 215) (.out 0x10fdd3 (andR64R64Effect 0x10fdd3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[213, 73]
    (.letOp (n := 216) (.exec 0x10fdd3 (fun s => s.RIP = 0x10fdd3) (andR64R64Effect 0x10fdd3 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[213, 73]
    (.letOp (n := 217) (.out 0x10fdd6 (xorR64R64Effect 0x10fdd6 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[215, 209]
    (.letOp (n := 218) (.exec 0x10fdd6 (fun s => s.RIP = 0x10fdd6) (xorR64R64Effect 0x10fdd6 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[215, 209]
    (.letOp (n := 219) (.out 0x10fdd9 (movR64M64Effect 0x10fdd9 8 (.base 8 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[69]
    (.letOp (n := 220) (.exec 0x10fdd9 (LoadPre 0x10fdd9 (fun s => AddrMode.addr (.base 8 (.d8 0x70)) s (0x10fdd9 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdd9 8 (.base 8 (.d8 0x70))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 221) (.out 0x10fddd (movR64M64Effect 0x10fddd 9 (.base 9 (.d8 0x70))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9] []) (.reg (.gpr 9))) #v[67]
    (.letOp (n := 222) (.exec 0x10fddd (LoadPre 0x10fddd (fun s => AddrMode.addr (.base 9 (.d8 0x70)) s (0x10fddd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fddd 9 (.base 9 (.d8 0x70))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 223) (.out 0x10fde1 (xorR64R64Effect 0x10fde1 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[221, 219]
    (.letOp (n := 224) (.exec 0x10fde1 (fun s => s.RIP = 0x10fde1) (xorR64R64Effect 0x10fde1 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[221, 219]
    (.letOp (n := 225) (.out 0x10fde4 (andR64R64Effect 0x10fde4 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 2] []) (.reg (.gpr 9))) #v[223, 73]
    (.letOp (n := 226) (.exec 0x10fde4 (fun s => s.RIP = 0x10fde4) (andR64R64Effect 0x10fde4 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[223, 73]
    (.letOp (n := 227) (.out 0x10fde7 (xorR64R64Effect 0x10fde7 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[225, 219]
    (.letOp (n := 228) (.exec 0x10fde7 (fun s => s.RIP = 0x10fde7) (xorR64R64Effect 0x10fde7 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[225, 219]
    (.letOp (n := 229) (.out 0x10fdea (movR64M64Effect 0x10fdea 2 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 230) (.exec 0x10fdea (LoadPre 0x10fdea (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fdea + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdea 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 231) (.exec 0x10fdef (StorePre 0x10fdef 3 (fun s => AddrMode.addr (.base 7 .none) s (0x10fdef + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x10fdef 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[229, 7]
    (.letOp (n := 232) (.out 0x10fdf2 (movR64M64Effect 0x10fdf2 2 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 233) (.exec 0x10fdf2 (LoadPre 0x10fdf2 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fdf2 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdf2 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 234) (.exec 0x10fdf7 (StorePre 0x10fdf7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x10fdf7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fdf7 2 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[232, 7]
    (.letOp (n := 235) (.out 0x10fdfb (movR64M64Effect 0x10fdfb 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 236) (.exec 0x10fdfb (LoadPre 0x10fdfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fdfb + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x10fdfb 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 237) (.exec 0x10fe00 (StorePre 0x10fe00 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x10fe00 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe00 2 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[235, 7]
    (.letOp (n := 238) (.out 0x10fe04 (movR64M64Effect 0x10fe04 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 239) (.exec 0x10fe04 (LoadPre 0x10fe04 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fe04 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fe04 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 240) (.exec 0x10fe08 (StorePre 0x10fe08 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x10fe08 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe08 2 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 7] [])) #v[238, 7]
    (.letOp (n := 241) (.exec 0x10fe0c (StorePre 0x10fe0c 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x10fe0c + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe0c 11 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[127, 7]
    (.letOp (n := 242) (.exec 0x10fe10 (StorePre 0x10fe10 4 (fun s => AddrMode.addr (.base 7 (.d8 0x28)) s (0x10fe10 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fe10 3 (.base 7 (.d8 0x28))) (Reg.operands [.gpr 3, .gpr 7] [])) #v[137, 7]
    (b_l10fcc0_5))))))))))))))))))))))))))))))))))

def bytes_l10fcc0_4 : List UInt8 :=
  [0x4D, 0x8B, 0x50, 0x68, 0x49, 0x8B, 0x41, 0x68, 0x4C, 0x31, 0xD0, 0x48, 0x21, 0xD0, 0x4C, 0x31,
    0xD0, 0x4D, 0x8B, 0x40, 0x70, 0x4D, 0x8B, 0x49, 0x70, 0x4D, 0x31, 0xC1, 0x49, 0x21, 0xD1, 0x4D,
    0x31, 0xC1, 0x48, 0x8B, 0x54, 0x24, 0x18, 0x48, 0x89, 0x17, 0x48, 0x8B, 0x54, 0x24, 0x10, 0x48,
    0x89, 0x57, 0x08, 0x48, 0x8B, 0x54, 0x24, 0x08, 0x48, 0x89, 0x57, 0x10, 0x48, 0x8B, 0x14, 0x24,
    0x48, 0x89, 0x57, 0x18, 0x4C, 0x89, 0x5F, 0x20, 0x48, 0x89, 0x5F, 0x28] ++ bytes_l10fcc0_5

theorem code_l10fcc0_4 : ∀ x ∈ codeRange 0x10fdc8 bytes_l10fcc0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfdc8 76 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fcc0_5

@[cfg_block] def b_l10fcc0_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x10fd84 (movR64M64Effect 0x10fd84 0 (.base 8 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 170) (.exec 0x10fd84 (LoadPre 0x10fd84 (fun s => AddrMode.addr (.base 8 (.d8 0x48)) s (0x10fd84 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd84 0 (.base 8 (.d8 0x48))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 171) (.out 0x10fd88 (movR64M64Effect 0x10fd88 13 (.base 9 (.d8 0x48))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[67]
    (.letOp (n := 172) (.exec 0x10fd88 (LoadPre 0x10fd88 (fun s => AddrMode.addr (.base 9 (.d8 0x48)) s (0x10fd88 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd88 13 (.base 9 (.d8 0x48))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 173) (.out 0x10fd8c (xorR64R64Effect 0x10fd8c 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[171, 169]
    (.letOp (n := 174) (.exec 0x10fd8c (fun s => s.RIP = 0x10fd8c) (xorR64R64Effect 0x10fd8c 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[171, 169]
    (.letOp (n := 175) (.out 0x10fd8f (andR64R64Effect 0x10fd8f 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 2] []) (.reg (.gpr 13))) #v[173, 73]
    (.letOp (n := 176) (.exec 0x10fd8f (fun s => s.RIP = 0x10fd8f) (andR64R64Effect 0x10fd8f 13 2) (Reg.operands [.gpr 13, .gpr 2] [])) #v[173, 73]
    (.letOp (n := 177) (.out 0x10fd92 (xorR64R64Effect 0x10fd92 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0] []) (.reg (.gpr 13))) #v[175, 169]
    (.letOp (n := 178) (.exec 0x10fd92 (fun s => s.RIP = 0x10fd92) (xorR64R64Effect 0x10fd92 13 0) (Reg.operands [.gpr 13, .gpr 0] [])) #v[175, 169]
    (.letOp (n := 179) (.out 0x10fd95 (movR64M64Effect 0x10fd95 0 (.base 8 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 180) (.exec 0x10fd95 (LoadPre 0x10fd95 (fun s => AddrMode.addr (.base 8 (.d8 0x50)) s (0x10fd95 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd95 0 (.base 8 (.d8 0x50))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 181) (.out 0x10fd99 (movR64M64Effect 0x10fd99 5 (.base 9 (.d8 0x50))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 9] []) (.reg (.gpr 5))) #v[67]
    (.letOp (n := 182) (.exec 0x10fd99 (LoadPre 0x10fd99 (fun s => AddrMode.addr (.base 9 (.d8 0x50)) s (0x10fd99 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd99 5 (.base 9 (.d8 0x50))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 183) (.out 0x10fd9d (xorR64R64Effect 0x10fd9d 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[181, 179]
    (.letOp (n := 184) (.exec 0x10fd9d (fun s => s.RIP = 0x10fd9d) (xorR64R64Effect 0x10fd9d 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[181, 179]
    (.letOp (n := 185) (.out 0x10fda0 (andR64R64Effect 0x10fda0 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[183, 73]
    (.letOp (n := 186) (.exec 0x10fda0 (fun s => s.RIP = 0x10fda0) (andR64R64Effect 0x10fda0 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[183, 73]
    (.letOp (n := 187) (.out 0x10fda3 (xorR64R64Effect 0x10fda3 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 0] []) (.reg (.gpr 5))) #v[185, 179]
    (.letOp (n := 188) (.exec 0x10fda3 (fun s => s.RIP = 0x10fda3) (xorR64R64Effect 0x10fda3 5 0) (Reg.operands [.gpr 5, .gpr 0] [])) #v[185, 179]
    (.letOp (n := 189) (.out 0x10fda6 (movR64M64Effect 0x10fda6 0 (.base 8 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 190) (.exec 0x10fda6 (LoadPre 0x10fda6 (fun s => AddrMode.addr (.base 8 (.d8 0x58)) s (0x10fda6 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fda6 0 (.base 8 (.d8 0x58))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 191) (.out 0x10fdaa (movR64M64Effect 0x10fdaa 6 (.base 9 (.d8 0x58))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 192) (.exec 0x10fdaa (LoadPre 0x10fdaa (fun s => AddrMode.addr (.base 9 (.d8 0x58)) s (0x10fdaa + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdaa 6 (.base 9 (.d8 0x58))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 193) (.out 0x10fdae (xorR64R64Effect 0x10fdae 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[191, 189]
    (.letOp (n := 194) (.exec 0x10fdae (fun s => s.RIP = 0x10fdae) (xorR64R64Effect 0x10fdae 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[191, 189]
    (.letOp (n := 195) (.out 0x10fdb1 (andR64R64Effect 0x10fdb1 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[193, 73]
    (.letOp (n := 196) (.exec 0x10fdb1 (fun s => s.RIP = 0x10fdb1) (andR64R64Effect 0x10fdb1 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[193, 73]
    (.letOp (n := 197) (.out 0x10fdb4 (xorR64R64Effect 0x10fdb4 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[195, 189]
    (.letOp (n := 198) (.exec 0x10fdb4 (fun s => s.RIP = 0x10fdb4) (xorR64R64Effect 0x10fdb4 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[195, 189]
    (.letOp (n := 199) (.out 0x10fdb7 (movR64M64Effect 0x10fdb7 0 (.base 8 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 200) (.exec 0x10fdb7 (LoadPre 0x10fdb7 (fun s => AddrMode.addr (.base 8 (.d8 0x60)) s (0x10fdb7 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdb7 0 (.base 8 (.d8 0x60))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 201) (.out 0x10fdbb (movR64M64Effect 0x10fdbb 1 (.base 9 (.d8 0x60))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 202) (.exec 0x10fdbb (LoadPre 0x10fdbb (fun s => AddrMode.addr (.base 9 (.d8 0x60)) s (0x10fdbb + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fdbb 1 (.base 9 (.d8 0x60))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 203) (.out 0x10fdbf (xorR64R64Effect 0x10fdbf 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[201, 199]
    (.letOp (n := 204) (.exec 0x10fdbf (fun s => s.RIP = 0x10fdbf) (xorR64R64Effect 0x10fdbf 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[201, 199]
    (.letOp (n := 205) (.out 0x10fdc2 (andR64R64Effect 0x10fdc2 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[203, 73]
    (.letOp (n := 206) (.exec 0x10fdc2 (fun s => s.RIP = 0x10fdc2) (andR64R64Effect 0x10fdc2 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[203, 73]
    (.letOp (n := 207) (.out 0x10fdc5 (xorR64R64Effect 0x10fdc5 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[205, 199]
    (.letOp (n := 208) (.exec 0x10fdc5 (fun s => s.RIP = 0x10fdc5) (xorR64R64Effect 0x10fdc5 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[205, 199]
    (b_l10fcc0_4))))))))))))))))))))))))))))))))))))))))

def bytes_l10fcc0_3 : List UInt8 :=
  [0x49, 0x8B, 0x40, 0x48, 0x4D, 0x8B, 0x69, 0x48, 0x49, 0x31, 0xC5, 0x49, 0x21, 0xD5, 0x49, 0x31,
    0xC5, 0x49, 0x8B, 0x40, 0x50, 0x49, 0x8B, 0x69, 0x50, 0x48, 0x31, 0xC5, 0x48, 0x21, 0xD5, 0x48,
    0x31, 0xC5, 0x49, 0x8B, 0x40, 0x58, 0x49, 0x8B, 0x71, 0x58, 0x48, 0x31, 0xC6, 0x48, 0x21, 0xD6,
    0x48, 0x31, 0xC6, 0x49, 0x8B, 0x40, 0x60, 0x49, 0x8B, 0x49, 0x60, 0x48, 0x31, 0xC1, 0x48, 0x21,
    0xD1, 0x48, 0x31, 0xC1] ++ bytes_l10fcc0_4

theorem code_l10fcc0_3 : ∀ x ∈ codeRange 0x10fd84 bytes_l10fcc0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfd84 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fcc0_4

@[cfg_block] def b_l10fcc0_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x10fd40 (movR64M64Effect 0x10fd40 0 (.base 8 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 130) (.exec 0x10fd40 (LoadPre 0x10fd40 (fun s => AddrMode.addr (.base 8 (.d8 0x28)) s (0x10fd40 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd40 0 (.base 8 (.d8 0x28))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 131) (.out 0x10fd44 (movR64M64Effect 0x10fd44 3 (.base 9 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 9] []) (.reg (.gpr 3))) #v[67]
    (.letOp (n := 132) (.exec 0x10fd44 (LoadPre 0x10fd44 (fun s => AddrMode.addr (.base 9 (.d8 0x28)) s (0x10fd44 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd44 3 (.base 9 (.d8 0x28))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 133) (.out 0x10fd48 (xorR64R64Effect 0x10fd48 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[131, 129]
    (.letOp (n := 134) (.exec 0x10fd48 (fun s => s.RIP = 0x10fd48) (xorR64R64Effect 0x10fd48 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[131, 129]
    (.letOp (n := 135) (.out 0x10fd4b (andR64R64Effect 0x10fd4b 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 2] []) (.reg (.gpr 3))) #v[133, 73]
    (.letOp (n := 136) (.exec 0x10fd4b (fun s => s.RIP = 0x10fd4b) (andR64R64Effect 0x10fd4b 3 2) (Reg.operands [.gpr 3, .gpr 2] [])) #v[133, 73]
    (.letOp (n := 137) (.out 0x10fd4e (xorR64R64Effect 0x10fd4e 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[135, 129]
    (.letOp (n := 138) (.exec 0x10fd4e (fun s => s.RIP = 0x10fd4e) (xorR64R64Effect 0x10fd4e 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[135, 129]
    (.letOp (n := 139) (.out 0x10fd51 (movR64M64Effect 0x10fd51 0 (.base 8 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 140) (.exec 0x10fd51 (LoadPre 0x10fd51 (fun s => AddrMode.addr (.base 8 (.d8 0x30)) s (0x10fd51 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd51 0 (.base 8 (.d8 0x30))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 141) (.out 0x10fd55 (movR64M64Effect 0x10fd55 14 (.base 9 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 9] []) (.reg (.gpr 14))) #v[67]
    (.letOp (n := 142) (.exec 0x10fd55 (LoadPre 0x10fd55 (fun s => AddrMode.addr (.base 9 (.d8 0x30)) s (0x10fd55 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd55 14 (.base 9 (.d8 0x30))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 143) (.out 0x10fd59 (xorR64R64Effect 0x10fd59 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[141, 139]
    (.letOp (n := 144) (.exec 0x10fd59 (fun s => s.RIP = 0x10fd59) (xorR64R64Effect 0x10fd59 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[141, 139]
    (.letOp (n := 145) (.out 0x10fd5c (andR64R64Effect 0x10fd5c 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[143, 73]
    (.letOp (n := 146) (.exec 0x10fd5c (fun s => s.RIP = 0x10fd5c) (andR64R64Effect 0x10fd5c 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[143, 73]
    (.letOp (n := 147) (.out 0x10fd5f (xorR64R64Effect 0x10fd5f 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 0] []) (.reg (.gpr 14))) #v[145, 139]
    (.letOp (n := 148) (.exec 0x10fd5f (fun s => s.RIP = 0x10fd5f) (xorR64R64Effect 0x10fd5f 14 0) (Reg.operands [.gpr 14, .gpr 0] [])) #v[145, 139]
    (.letOp (n := 149) (.out 0x10fd62 (movR64M64Effect 0x10fd62 0 (.base 8 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 150) (.exec 0x10fd62 (LoadPre 0x10fd62 (fun s => AddrMode.addr (.base 8 (.d8 0x38)) s (0x10fd62 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd62 0 (.base 8 (.d8 0x38))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 151) (.out 0x10fd66 (movR64M64Effect 0x10fd66 15 (.base 9 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[67]
    (.letOp (n := 152) (.exec 0x10fd66 (LoadPre 0x10fd66 (fun s => AddrMode.addr (.base 9 (.d8 0x38)) s (0x10fd66 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd66 15 (.base 9 (.d8 0x38))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 153) (.out 0x10fd6a (xorR64R64Effect 0x10fd6a 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[151, 149]
    (.letOp (n := 154) (.exec 0x10fd6a (fun s => s.RIP = 0x10fd6a) (xorR64R64Effect 0x10fd6a 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[151, 149]
    (.letOp (n := 155) (.out 0x10fd6d (andR64R64Effect 0x10fd6d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[153, 73]
    (.letOp (n := 156) (.exec 0x10fd6d (fun s => s.RIP = 0x10fd6d) (andR64R64Effect 0x10fd6d 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[153, 73]
    (.letOp (n := 157) (.out 0x10fd70 (xorR64R64Effect 0x10fd70 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[155, 149]
    (.letOp (n := 158) (.exec 0x10fd70 (fun s => s.RIP = 0x10fd70) (xorR64R64Effect 0x10fd70 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[155, 149]
    (.letOp (n := 159) (.out 0x10fd73 (movR64M64Effect 0x10fd73 0 (.base 8 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 160) (.exec 0x10fd73 (LoadPre 0x10fd73 (fun s => AddrMode.addr (.base 8 (.d8 0x40)) s (0x10fd73 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd73 0 (.base 8 (.d8 0x40))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 161) (.out 0x10fd77 (movR64M64Effect 0x10fd77 12 (.base 9 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 162) (.exec 0x10fd77 (LoadPre 0x10fd77 (fun s => AddrMode.addr (.base 9 (.d8 0x40)) s (0x10fd77 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd77 12 (.base 9 (.d8 0x40))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 163) (.out 0x10fd7b (xorR64R64Effect 0x10fd7b 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[161, 159]
    (.letOp (n := 164) (.exec 0x10fd7b (fun s => s.RIP = 0x10fd7b) (xorR64R64Effect 0x10fd7b 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[161, 159]
    (.letOp (n := 165) (.out 0x10fd7e (andR64R64Effect 0x10fd7e 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[163, 73]
    (.letOp (n := 166) (.exec 0x10fd7e (fun s => s.RIP = 0x10fd7e) (andR64R64Effect 0x10fd7e 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[163, 73]
    (.letOp (n := 167) (.out 0x10fd81 (xorR64R64Effect 0x10fd81 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[165, 159]
    (.letOp (n := 168) (.exec 0x10fd81 (fun s => s.RIP = 0x10fd81) (xorR64R64Effect 0x10fd81 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[165, 159]
    (b_l10fcc0_3))))))))))))))))))))))))))))))))))))))))

def bytes_l10fcc0_2 : List UInt8 :=
  [0x49, 0x8B, 0x40, 0x28, 0x49, 0x8B, 0x59, 0x28, 0x48, 0x31, 0xC3, 0x48, 0x21, 0xD3, 0x48, 0x31,
    0xC3, 0x49, 0x8B, 0x40, 0x30, 0x4D, 0x8B, 0x71, 0x30, 0x49, 0x31, 0xC6, 0x49, 0x21, 0xD6, 0x49,
    0x31, 0xC6, 0x49, 0x8B, 0x40, 0x38, 0x4D, 0x8B, 0x79, 0x38, 0x49, 0x31, 0xC7, 0x49, 0x21, 0xD7,
    0x49, 0x31, 0xC7, 0x49, 0x8B, 0x40, 0x40, 0x4D, 0x8B, 0x61, 0x40, 0x49, 0x31, 0xC4, 0x49, 0x21,
    0xD4, 0x49, 0x31, 0xC4] ++ bytes_l10fcc0_3

theorem code_l10fcc0_2 : ∀ x ∈ codeRange 0x10fd40 bytes_l10fcc0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfd40 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fcc0_3

@[cfg_block] def b_l10fcc0_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x10fcf9 (andR64R64Effect 0x10fcf9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[90, 73]
    (.letOp (n := 93) (.exec 0x10fcf9 (fun s => s.RIP = 0x10fcf9) (andR64R64Effect 0x10fcf9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[90, 73]
    (.letOp (n := 94) (.out 0x10fcfc (xorR64R64Effect 0x10fcfc 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[92, 77]
    (.letOp (n := 95) (.exec 0x10fcfc (fun s => s.RIP = 0x10fcfc) (xorR64R64Effect 0x10fcfc 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[92, 77]
    (.letOp (n := 96) (.exec 0x10fcff (StorePre 0x10fcff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x10fcff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fcff 0 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[94, 65]
    (.letOp (n := 97) (.out 0x10fd04 (movR64M64Effect 0x10fd04 0 (.base 8 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 98) (.exec 0x10fd04 (LoadPre 0x10fd04 (fun s => AddrMode.addr (.base 8 (.d8 0x10)) s (0x10fd04 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd04 0 (.base 8 (.d8 0x10))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 99) (.out 0x10fd08 (movR64M64Effect 0x10fd08 1 (.base 9 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 100) (.exec 0x10fd08 (LoadPre 0x10fd08 (fun s => AddrMode.addr (.base 9 (.d8 0x10)) s (0x10fd08 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd08 1 (.base 9 (.d8 0x10))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 101) (.out 0x10fd0c (xorR64R64Effect 0x10fd0c 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[99, 97]
    (.letOp (n := 102) (.exec 0x10fd0c (fun s => s.RIP = 0x10fd0c) (xorR64R64Effect 0x10fd0c 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[99, 97]
    (.letOp (n := 103) (.out 0x10fd0f (andR64R64Effect 0x10fd0f 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[101, 73]
    (.letOp (n := 104) (.exec 0x10fd0f (fun s => s.RIP = 0x10fd0f) (andR64R64Effect 0x10fd0f 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[101, 73]
    (.letOp (n := 105) (.out 0x10fd12 (xorR64R64Effect 0x10fd12 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[103, 97]
    (.letOp (n := 106) (.exec 0x10fd12 (fun s => s.RIP = 0x10fd12) (xorR64R64Effect 0x10fd12 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[103, 97]
    (.letOp (n := 107) (.exec 0x10fd15 (StorePre 0x10fd15 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x10fd15 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fd15 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[105, 65]
    (.letOp (n := 108) (.out 0x10fd1a (movR64M64Effect 0x10fd1a 0 (.base 8 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 109) (.exec 0x10fd1a (LoadPre 0x10fd1a (fun s => AddrMode.addr (.base 8 (.d8 0x18)) s (0x10fd1a + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd1a 0 (.base 8 (.d8 0x18))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 110) (.out 0x10fd1e (movR64M64Effect 0x10fd1e 1 (.base 9 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 9] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 111) (.exec 0x10fd1e (LoadPre 0x10fd1e (fun s => AddrMode.addr (.base 9 (.d8 0x18)) s (0x10fd1e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd1e 1 (.base 9 (.d8 0x18))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 112) (.out 0x10fd22 (xorR64R64Effect 0x10fd22 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[110, 108]
    (.letOp (n := 113) (.exec 0x10fd22 (fun s => s.RIP = 0x10fd22) (xorR64R64Effect 0x10fd22 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[110, 108]
    (.letOp (n := 114) (.out 0x10fd25 (andR64R64Effect 0x10fd25 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[112, 73]
    (.letOp (n := 115) (.exec 0x10fd25 (fun s => s.RIP = 0x10fd25) (andR64R64Effect 0x10fd25 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[112, 73]
    (.letOp (n := 116) (.out 0x10fd28 (xorR64R64Effect 0x10fd28 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[114, 108]
    (.letOp (n := 117) (.exec 0x10fd28 (fun s => s.RIP = 0x10fd28) (xorR64R64Effect 0x10fd28 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[114, 108]
    (.letOp (n := 118) (.exec 0x10fd2b (StorePre 0x10fd2b 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x10fd2b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x10fd2b 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[116, 65]
    (.letOp (n := 119) (.out 0x10fd2f (movR64M64Effect 0x10fd2f 0 (.base 8 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 120) (.exec 0x10fd2f (LoadPre 0x10fd2f (fun s => AddrMode.addr (.base 8 (.d8 0x20)) s (0x10fd2f + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd2f 0 (.base 8 (.d8 0x20))) (Reg.operands [.gpr 8] [])) #v[69]
    (.letOp (n := 121) (.out 0x10fd33 (movR64M64Effect 0x10fd33 11 (.base 9 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 9] []) (.reg (.gpr 11))) #v[67]
    (.letOp (n := 122) (.exec 0x10fd33 (LoadPre 0x10fd33 (fun s => AddrMode.addr (.base 9 (.d8 0x20)) s (0x10fd33 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fd33 11 (.base 9 (.d8 0x20))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 123) (.out 0x10fd37 (xorR64R64Effect 0x10fd37 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[121, 119]
    (.letOp (n := 124) (.exec 0x10fd37 (fun s => s.RIP = 0x10fd37) (xorR64R64Effect 0x10fd37 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[121, 119]
    (.letOp (n := 125) (.out 0x10fd3a (andR64R64Effect 0x10fd3a 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[123, 73]
    (.letOp (n := 126) (.exec 0x10fd3a (fun s => s.RIP = 0x10fd3a) (andR64R64Effect 0x10fd3a 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[123, 73]
    (.letOp (n := 127) (.out 0x10fd3d (xorR64R64Effect 0x10fd3d 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[125, 119]
    (.letOp (n := 128) (.exec 0x10fd3d (fun s => s.RIP = 0x10fd3d) (xorR64R64Effect 0x10fd3d 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[125, 119]
    (b_l10fcc0_2)))))))))))))))))))))))))))))))))))))

def bytes_l10fcc0_1 : List UInt8 :=
  [0x48, 0x21, 0xD0, 0x48, 0x31, 0xC8, 0x48, 0x89, 0x44, 0x24, 0x10, 0x49, 0x8B, 0x40, 0x10, 0x49,
    0x8B, 0x49, 0x10, 0x48, 0x31, 0xC1, 0x48, 0x21, 0xD1, 0x48, 0x31, 0xC1, 0x48, 0x89, 0x4C, 0x24,
    0x08, 0x49, 0x8B, 0x40, 0x18, 0x49, 0x8B, 0x49, 0x18, 0x48, 0x31, 0xC1, 0x48, 0x21, 0xD1, 0x48,
    0x31, 0xC1, 0x48, 0x89, 0x0C, 0x24, 0x49, 0x8B, 0x40, 0x20, 0x4D, 0x8B, 0x59, 0x20, 0x49, 0x31,
    0xC3, 0x49, 0x21, 0xD3, 0x49, 0x31, 0xC3] ++ bytes_l10fcc0_2

theorem code_l10fcc0_1 : ∀ x ∈ codeRange 0x10fcf9 bytes_l10fcc0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfcf9 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fcc0_2

@[cfg_block] def b_l10fcc0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x10fcc0 (pushR64Effect 0x10fcc0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x10fcc0 (PushPre 0x10fcc0 1) (pushR64Effect 0x10fcc0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x10fcc1 (pushR64Effect 0x10fcc1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x10fcc1 (PushPre 0x10fcc1 2) (pushR64Effect 0x10fcc1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x10fcc3 (pushR64Effect 0x10fcc3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x10fcc3 (PushPre 0x10fcc3 2) (pushR64Effect 0x10fcc3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x10fcc5 (pushR64Effect 0x10fcc5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x10fcc5 (PushPre 0x10fcc5 2) (pushR64Effect 0x10fcc5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x10fcc7 (pushR64Effect 0x10fcc7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x10fcc7 (PushPre 0x10fcc7 2) (pushR64Effect 0x10fcc7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x10fcc9 (pushR64Effect 0x10fcc9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x10fcc9 (PushPre 0x10fcc9 1) (pushR64Effect 0x10fcc9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x10fcca (subR64Imm8Effect 0x10fcca 4 0x20) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x10fcca (fun s => s.RIP = 0x10fcca) (subR64Imm8Effect 0x10fcca 4 0x20) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x10fcce (movR64R64Effect 0x10fcce 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 68) (.exec 0x10fcce (fun s => s.RIP = 0x10fcce) (movR64R64Effect 0x10fcce 9 2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x10fcd1 (movR64R64Effect 0x10fcd1 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 70) (.exec 0x10fcd1 (fun s => s.RIP = 0x10fcd1) (movR64R64Effect 0x10fcd1 8 6) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x10fcd4 (movzxR32R8Effect 0x10fcd4 3 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[1]
    (.letOp (n := 72) (.exec 0x10fcd4 (fun s => s.RIP = 0x10fcd4) (movzxR32R8Effect 0x10fcd4 3 2 1) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 73) (.out 0x10fcd7 (negR64Effect 0x10fcd7 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 74) (.exec 0x10fcd7 (fun s => s.RIP = 0x10fcd7) (negR64Effect 0x10fcd7 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x10fcda (movR64M64Effect 0x10fcda 0 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 76) (.exec 0x10fcda (LoadPre 0x10fcda (fun s => AddrMode.addr (.base 6 .none) s (0x10fcda + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fcda 0 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 77) (.out 0x10fcdd (movR64M64Effect 0x10fcdd 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 78) (.exec 0x10fcdd (LoadPre 0x10fcdd (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x10fcdd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fcdd 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 79) (.out 0x10fce1 (movR64M64Effect 0x10fce1 6 (.base 9 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 9] []) (.reg (.gpr 6))) #v[67]
    (.letOp (n := 80) (.exec 0x10fce1 (LoadPre 0x10fce1 (fun s => AddrMode.addr (.base 9 .none) s (0x10fce1 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x10fce1 6 (.base 9 .none)) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 81) (.out 0x10fce4 (xorR64R64Effect 0x10fce4 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[79, 75]
    (.letOp (n := 82) (.exec 0x10fce4 (fun s => s.RIP = 0x10fce4) (xorR64R64Effect 0x10fce4 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[79, 75]
    (.letOp (n := 83) (.out 0x10fce7 (andR64R64Effect 0x10fce7 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[81, 73]
    (.letOp (n := 84) (.exec 0x10fce7 (fun s => s.RIP = 0x10fce7) (andR64R64Effect 0x10fce7 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[81, 73]
    (.letOp (n := 85) (.out 0x10fcea (xorR64R64Effect 0x10fcea 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[83, 75]
    (.letOp (n := 86) (.exec 0x10fcea (fun s => s.RIP = 0x10fcea) (xorR64R64Effect 0x10fcea 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[83, 75]
    (.letOp (n := 87) (.exec 0x10fced (StorePre 0x10fced 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x10fced + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x10fced 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[85, 65]
    (.letOp (n := 88) (.out 0x10fcf2 (movR64M64Effect 0x10fcf2 0 (.base 9 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 89) (.exec 0x10fcf2 (LoadPre 0x10fcf2 (fun s => AddrMode.addr (.base 9 (.d8 0x8)) s (0x10fcf2 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x10fcf2 0 (.base 9 (.d8 0x8))) (Reg.operands [.gpr 9] [])) #v[67]
    (.letOp (n := 90) (.out 0x10fcf6 (xorR64R64Effect 0x10fcf6 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1] []) (.reg (.gpr 0))) #v[88, 77]
    (.letOp (n := 91) (.exec 0x10fcf6 (fun s => s.RIP = 0x10fcf6) (xorR64R64Effect 0x10fcf6 0 1) (Reg.operands [.gpr 0, .gpr 1] [])) #v[88, 77]
    (b_l10fcc0_1)))))))))))))))))))))))))))))))))))))))

def bytes_l10fcc0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x20, 0x49, 0x89,
    0xD1, 0x49, 0x89, 0xF0, 0x0F, 0xB6, 0xD1, 0x48, 0xF7, 0xDA, 0x48, 0x8B, 0x06, 0x48, 0x8B, 0x4E,
    0x08, 0x49, 0x8B, 0x31, 0x48, 0x31, 0xC6, 0x48, 0x21, 0xD6, 0x48, 0x31, 0xC6, 0x48, 0x89, 0x74,
    0x24, 0x18, 0x49, 0x8B, 0x41, 0x08, 0x48, 0x31, 0xC8] ++ bytes_l10fcc0_1

theorem code_l10fcc0 : ∀ x ∈ codeRange 0x10fcc0 bytes_l10fcc0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0xfcc0 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l10fcc0_1

@[cfg_block] def b_l10fe50 : Block Op Label signature Reg.count 53 :=
  .terminate (.br ⟨.l10ece0, RegMap.args (entryMap (live .l10fe50)) 53⟩)

def bytes_l10fe50 : List UInt8 :=
  [0xE9, 0x8B, 0xEE, 0xFF, 0xFF]

theorem code_l10fe50 : ∀ x ∈ codeRange 0x10fe50 bytes_l10fe50, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0xfe50 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109b0_7 : Block Op Label signature Reg.count 326 :=
  .letOp (n := 326) (.out 0x110b70 (popR64Effect 0x110b70 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[324]
    (.letOp (n := 327) (.out 0x110b70 (popR64Effect 0x110b70 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[324]
    (.letOp (n := 328) (.exec 0x110b70 (PopPre 0x110b70) (popR64Effect 0x110b70 1 5) (Reg.operands [.gpr 4] [])) #v[324]
    (.letOp (n := 329) (.out 0x110b71 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[327]
    (.letOp (n := 330) (.out 0x110b71 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[327]
    (.letOp (n := 331) (.exec 0x110b71 (RetPre 0x110b71) (retEffect) (Reg.operands [.gpr 4] [])) #v[327]
    (.terminate (.ret (RegMap.args [(0, 234), (1, 303), (2, 281), (3, 311), (4, 330), (5, 326), (6, 292), (7, 270), (8, 297), (9, 286), (10, 275), (11, 264), (12, 314), (13, 317), (14, 320), (15, 323), (22, 22), (39, 39), (50, 50), (51, 51)] 332) (some ⟨329, by decide⟩))))))))

def bytes_l1109b0_7 : List UInt8 :=
  [0x5D, 0xC3]

theorem code_l1109b0_7 : ∀ x ∈ codeRange 0x110b70 bytes_l1109b0_7, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10b70 2 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1109b0_6 : Block Op Label signature Reg.count 286 :=
  .letOp (n := 286) (.out 0x110b35 (xorR64R64Effect 0x110b35 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[102, 180]
    (.letOp (n := 287) (.exec 0x110b35 (fun s => s.RIP = 0x110b35) (xorR64R64Effect 0x110b35 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[102, 180]
    (.letOp (n := 288) (.out 0x110b38 (negR64Effect 0x110b38 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[284]
    (.letOp (n := 289) (.exec 0x110b38 (fun s => s.RIP = 0x110b38) (negR64Effect 0x110b38 6) (Reg.operands [.gpr 6] [])) #v[284]
    (.letOp (n := 290) (.out 0x110b3b (andR64R64Effect 0x110b3b 6 9) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9] []) (.reg (.gpr 6))) #v[288, 286]
    (.letOp (n := 291) (.exec 0x110b3b (fun s => s.RIP = 0x110b3b) (andR64R64Effect 0x110b3b 6 9) (Reg.operands [.gpr 6, .gpr 9] [])) #v[288, 286]
    (.letOp (n := 292) (.out 0x110b3e (xorR64R64Effect 0x110b3e 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[290, 180]
    (.letOp (n := 293) (.exec 0x110b3e (fun s => s.RIP = 0x110b3e) (xorR64R64Effect 0x110b3e 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[290, 180]
    (.letOp (n := 294) (.exec 0x110b41 (StorePre 0x110b41 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b41 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b41 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 295) (.out 0x110b44 (movzxR32M8Effect 0x110b44 4 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 296) (.exec 0x110b44 (LoadPre 0x110b44 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b44 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b44 4 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 297) (.out 0x110b48 (xorR64R64Effect 0x110b48 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[105, 211]
    (.letOp (n := 298) (.exec 0x110b48 (fun s => s.RIP = 0x110b48) (xorR64R64Effect 0x110b48 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[105, 211]
    (.letOp (n := 299) (.out 0x110b4b (negR64Effect 0x110b4b 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[295]
    (.letOp (n := 300) (.exec 0x110b4b (fun s => s.RIP = 0x110b4b) (negR64Effect 0x110b4b 1) (Reg.operands [.gpr 1] [])) #v[295]
    (.letOp (n := 301) (.out 0x110b4e (andR64R64Effect 0x110b4e 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[299, 297]
    (.letOp (n := 302) (.exec 0x110b4e (fun s => s.RIP = 0x110b4e) (andR64R64Effect 0x110b4e 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[299, 297]
    (.letOp (n := 303) (.out 0x110b51 (xorR64R64Effect 0x110b51 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[301, 211]
    (.letOp (n := 304) (.exec 0x110b51 (fun s => s.RIP = 0x110b51) (xorR64R64Effect 0x110b51 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[301, 211]
    (.letOp (n := 305) (.exec 0x110b54 (StorePre 0x110b54 3 (fun s => AddrMode.addr (.base 0 .none) s (0x110b54 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110b54 7 (.base 0 .none)) (Reg.operands [.gpr 7, .gpr 0] [])) #v[270, 234]
    (.letOp (n := 306) (.exec 0x110b57 (StorePre 0x110b57 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x110b57 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b57 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[281, 234]
    (.letOp (n := 307) (.exec 0x110b5b (StorePre 0x110b5b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x110b5b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5b 6 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[292, 234]
    (.letOp (n := 308) (.exec 0x110b5f (StorePre 0x110b5f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x110b5f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110b5f 1 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[303, 234]
    (.letOp (n := 309) (.out 0x110b63 (addR64Imm8Effect 0x110b63 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 310) (.exec 0x110b63 (fun s => s.RIP = 0x110b63) (addR64Imm8Effect 0x110b63 4 0x10) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 311) (.out 0x110b67 (popR64Effect 0x110b67 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[309]
    (.letOp (n := 312) (.out 0x110b67 (popR64Effect 0x110b67 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[309]
    (.letOp (n := 313) (.exec 0x110b67 (PopPre 0x110b67) (popR64Effect 0x110b67 1 3) (Reg.operands [.gpr 4] [])) #v[309]
    (.letOp (n := 314) (.out 0x110b68 (popR64Effect 0x110b68 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[312]
    (.letOp (n := 315) (.out 0x110b68 (popR64Effect 0x110b68 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[312]
    (.letOp (n := 316) (.exec 0x110b68 (PopPre 0x110b68) (popR64Effect 0x110b68 2 12) (Reg.operands [.gpr 4] [])) #v[312]
    (.letOp (n := 317) (.out 0x110b6a (popR64Effect 0x110b6a 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[315]
    (.letOp (n := 318) (.out 0x110b6a (popR64Effect 0x110b6a 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[315]
    (.letOp (n := 319) (.exec 0x110b6a (PopPre 0x110b6a) (popR64Effect 0x110b6a 2 13) (Reg.operands [.gpr 4] [])) #v[315]
    (.letOp (n := 320) (.out 0x110b6c (popR64Effect 0x110b6c 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[318]
    (.letOp (n := 321) (.out 0x110b6c (popR64Effect 0x110b6c 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[318]
    (.letOp (n := 322) (.exec 0x110b6c (PopPre 0x110b6c) (popR64Effect 0x110b6c 2 14) (Reg.operands [.gpr 4] [])) #v[318]
    (.letOp (n := 323) (.out 0x110b6e (popR64Effect 0x110b6e 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[321]
    (.letOp (n := 324) (.out 0x110b6e (popR64Effect 0x110b6e 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[321]
    (.letOp (n := 325) (.exec 0x110b6e (PopPre 0x110b6e) (popR64Effect 0x110b6e 2 15) (Reg.operands [.gpr 4] [])) #v[321]
    (b_l1109b0_7))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_6 : List UInt8 :=
  [0x4D, 0x31, 0xF1, 0x48, 0xF7, 0xDE, 0x4C, 0x21, 0xCE, 0x4C, 0x31, 0xF6, 0x88, 0x0C, 0x24, 0x0F,
    0xB6, 0x0C, 0x24, 0x4D, 0x31, 0xF8, 0x48, 0xF7, 0xD9, 0x4C, 0x21, 0xC1, 0x4C, 0x31, 0xF9, 0x48,
    0x89, 0x38, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x70, 0x10, 0x48, 0x89, 0x48, 0x18, 0x48, 0x83,
    0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F] ++ bytes_l1109b0_7

theorem code_l1109b0_6 : ∀ x ∈ codeRange 0x110b35 bytes_l1109b0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10b35 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_7

@[cfg_block] def b_l1109b0_5 : Block Op Label signature Reg.count 252 :=
  .letOp (n := 252) (.out 0x110af2 (addM8Imm8Effect 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff) (EffectPart.reads (.flag .CF) [.gpr 4] []) (.flag .CF)) #v[65]
    (.letOp (n := 253) (.exec 0x110af2 (StorePre 0x110af2 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x110af2 + BitVec.ofNat 64 5)) 1) (addM8Imm8Effect 0x110af2 5 (.sib 4 none 0 (.d8 0xf)) 0xff) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 254) (.out 0x110af7 (atFlags StatusFlags.CF (adcR64R64Effect 0x110af7 7 3)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 7))) #v[250, 97, 252]
    (.letOp (n := 255) (.exec 0x110af7 (fun s => s.RIP = 0x110af7) (atFlags StatusFlags.CF (adcR64R64Effect 0x110af7 7 3)) (Reg.operands [.gpr 7, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[250, 97, 252]
    (.letOp (n := 256) (.out 0x110afa (shrR64Effect 0x110afa 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[254]
    (.letOp (n := 257) (.exec 0x110afa (fun s => s.RIP = 0x110afa) (shrR64Effect 0x110afa 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[254]
    (.letOp (n := 258) (.exec 0x110afe (StorePre 0x110afe 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110afe + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110afe 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 7, .gpr 4] [])) #v[256, 65]
    (.letOp (n := 259) (.exec 0x110b02 (fun s => s.RIP = 0x110b02) (movR64R64Effect 0x110b02 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 260) (.exec 0x110b05 (StorePre 0x110b05 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b05 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b05 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 261) (.exec 0x110b08 (fun s => s.RIP = 0x110b08) (movR64R64Effect 0x110b08 3 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 262) (.out 0x110b0b (movzxR32M8Effect 0x110b0b 4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 263) (.exec 0x110b0b (LoadPre 0x110b0b (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b0b + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b0b 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 264) (.out 0x110b0f (xorR64R64Effect 0x110b0f 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 2] []) (.reg (.gpr 11))) #v[71, 117]
    (.letOp (n := 265) (.exec 0x110b0f (fun s => s.RIP = 0x110b0f) (xorR64R64Effect 0x110b0f 11 2) (Reg.operands [.gpr 11, .gpr 2] [])) #v[71, 117]
    (.letOp (n := 266) (.out 0x110b12 (negR64Effect 0x110b12 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[262]
    (.letOp (n := 267) (.exec 0x110b12 (fun s => s.RIP = 0x110b12) (negR64Effect 0x110b12 7) (Reg.operands [.gpr 7] [])) #v[262]
    (.letOp (n := 268) (.out 0x110b15 (andR64R64Effect 0x110b15 7 11) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 11] []) (.reg (.gpr 7))) #v[266, 264]
    (.letOp (n := 269) (.exec 0x110b15 (fun s => s.RIP = 0x110b15) (andR64R64Effect 0x110b15 7 11) (Reg.operands [.gpr 7, .gpr 11] [])) #v[266, 264]
    (.letOp (n := 270) (.out 0x110b18 (xorR64R64Effect 0x110b18 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[268, 117]
    (.letOp (n := 271) (.exec 0x110b18 (fun s => s.RIP = 0x110b18) (xorR64R64Effect 0x110b18 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[268, 117]
    (.letOp (n := 272) (.exec 0x110b1b (StorePre 0x110b1b 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1b + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b1b 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 273) (.out 0x110b1e (movzxR32M8Effect 0x110b1e 4 2 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 274) (.exec 0x110b1e (LoadPre 0x110b1e (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b1e + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b1e 4 2 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 275) (.out 0x110b22 (xorR64R64Effect 0x110b22 10 6) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[99, 149]
    (.letOp (n := 276) (.exec 0x110b22 (fun s => s.RIP = 0x110b22) (xorR64R64Effect 0x110b22 10 6) (Reg.operands [.gpr 10, .gpr 6] [])) #v[99, 149]
    (.letOp (n := 277) (.out 0x110b25 (negR64Effect 0x110b25 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[273]
    (.letOp (n := 278) (.exec 0x110b25 (fun s => s.RIP = 0x110b25) (negR64Effect 0x110b25 2) (Reg.operands [.gpr 2] [])) #v[273]
    (.letOp (n := 279) (.out 0x110b28 (andR64R64Effect 0x110b28 2 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 10] []) (.reg (.gpr 2))) #v[277, 275]
    (.letOp (n := 280) (.exec 0x110b28 (fun s => s.RIP = 0x110b28) (andR64R64Effect 0x110b28 2 10) (Reg.operands [.gpr 2, .gpr 10] [])) #v[277, 275]
    (.letOp (n := 281) (.out 0x110b2b (xorR64R64Effect 0x110b2b 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[279, 149]
    (.letOp (n := 282) (.exec 0x110b2b (fun s => s.RIP = 0x110b2b) (xorR64R64Effect 0x110b2b 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[279, 149]
    (.letOp (n := 283) (.exec 0x110b2e (StorePre 0x110b2e 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b2e + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110b2e 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 284) (.out 0x110b31 (movzxR32M8Effect 0x110b31 4 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 4] []) (.reg (.gpr 6))) #v[65]
    (.letOp (n := 285) (.exec 0x110b31 (LoadPre 0x110b31 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110b31 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110b31 4 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1109b0_6))))))))))))))))))))))))))))))))))

def bytes_l1109b0_5 : List UInt8 :=
  [0x80, 0x44, 0x24, 0x0F, 0xFF, 0x48, 0x11, 0xDF, 0x48, 0xC1, 0xEF, 0x3F, 0x48, 0x89, 0x3C, 0x24,
    0x48, 0x89, 0xE7, 0x88, 0x0C, 0x24, 0x48, 0x89, 0xE3, 0x0F, 0xB6, 0x3C, 0x24, 0x49, 0x31, 0xD3,
    0x48, 0xF7, 0xDF, 0x4C, 0x21, 0xDF, 0x48, 0x31, 0xD7, 0x88, 0x0C, 0x24, 0x0F, 0xB6, 0x14, 0x24,
    0x49, 0x31, 0xF2, 0x48, 0xF7, 0xDA, 0x4C, 0x21, 0xD2, 0x48, 0x31, 0xF2, 0x88, 0x0C, 0x24, 0x0F,
    0xB6, 0x34, 0x24] ++ bytes_l1109b0_6

theorem code_l1109b0_5 : ∀ x ∈ codeRange 0x110af2 bytes_l1109b0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10af2 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_6

@[cfg_block] def b_l1109b0_4 : Block Op Label signature Reg.count 215 :=
  .letOp (n := 215) (.out 0x110ab1 (notR64Effect 0x110ab1 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[213]
    (.letOp (n := 216) (.exec 0x110ab1 (fun s => s.RIP = 0x110ab1) (notR64Effect 0x110ab1 13) (Reg.operands [.gpr 13] [])) #v[213]
    (.letOp (n := 217) (.out 0x110ab4 (movR64R64Effect 0x110ab4 5 1) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[203]
    (.letOp (n := 218) (.exec 0x110ab4 (fun s => s.RIP = 0x110ab4) (movR64R64Effect 0x110ab4 5 1) (Reg.operands [.gpr 1] [])) #v[203]
    (.letOp (n := 219) (.out 0x110ab7 (andR64R64Effect 0x110ab7 5 13) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 13] []) (.reg (.gpr 5))) #v[217, 215]
    (.letOp (n := 220) (.exec 0x110ab7 (fun s => s.RIP = 0x110ab7) (andR64R64Effect 0x110ab7 5 13) (Reg.operands [.gpr 5, .gpr 13] [])) #v[217, 215]
    (.letOp (n := 221) (.out 0x110aba (orR64R64Effect 0x110aba 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[215, 203]
    (.letOp (n := 222) (.exec 0x110aba (fun s => s.RIP = 0x110aba) (orR64R64Effect 0x110aba 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[215, 203]
    (.letOp (n := 223) (.out 0x110abd (andR64R64Effect 0x110abd 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[221, 211]
    (.letOp (n := 224) (.exec 0x110abd (fun s => s.RIP = 0x110abd) (andR64R64Effect 0x110abd 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[221, 211]
    (.letOp (n := 225) (.out 0x110ac0 (orR64R64Effect 0x110ac0 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[223, 219]
    (.letOp (n := 226) (.exec 0x110ac0 (fun s => s.RIP = 0x110ac0) (orR64R64Effect 0x110ac0 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[223, 219]
    (.letOp (n := 227) (.out 0x110ac3 (shrR64Effect 0x110ac3 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[225]
    (.letOp (n := 228) (.exec 0x110ac3 (fun s => s.RIP = 0x110ac3) (shrR64Effect 0x110ac3 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[225]
    (.letOp (n := 229) (.exec 0x110ac7 (StorePre 0x110ac7 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ac7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110ac7 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[227, 65]
    (.letOp (n := 230) (.out 0x110acb (xorR32R32Effect 0x110acb 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[227, 227]
    (.letOp (n := 231) (.exec 0x110acb (fun s => s.RIP = 0x110acb) (xorR32R32Effect 0x110acb 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[227, 227]
    (.letOp (n := 232) (.out 0x110ace (subR64M64Effect 0x110ace 13 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[230, 65]
    (.letOp (n := 233) (.exec 0x110ace (LoadPre 0x110ace (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ace + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110ace 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[230, 65]
    (.letOp (n := 234) (.out 0x110ad2 (movR64R64Effect 0x110ad2 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 235) (.exec 0x110ad2 (fun s => s.RIP = 0x110ad2) (movR64R64Effect 0x110ad2 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 236) (.out 0x110ad5 (testR64R64Effect 0x110ad5 12 12) (EffectPart.reads (.flag .ZF) [.gpr 12, .gpr 12] []) (.flag .ZF)) #v[111, 111]
    (.letOp (n := 237) (.exec 0x110ad5 (fun s => s.RIP = 0x110ad5) (testR64R64Effect 0x110ad5 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[111, 111]
    (.letOp (n := 238) (.out 0x110ad8 (atFlags (condHolds 4) (setccR8Effect 0x110ad8 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[203, 236]
    (.letOp (n := 239) (.exec 0x110ad8 (fun s => s.RIP = 0x110ad8) (atFlags (condHolds 4) (setccR8Effect 0x110ad8 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[203, 236]
    (.letOp (n := 240) (.out 0x110adb (andR8R8Effect 0x110adb 3 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 13] []) (.reg (.gpr 1))) #v[238, 232]
    (.letOp (n := 241) (.exec 0x110adb (fun s => s.RIP = 0x110adb) (andR8R8Effect 0x110adb 3 1 13) (Reg.operands [.gpr 1, .gpr 13] [])) #v[238, 232]
    (.letOp (n := 242) (.exec 0x110ade (StorePre 0x110ade 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ade + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x110ade 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[240, 65]
    (.letOp (n := 243) (.exec 0x110ae1 (fun s => s.RIP = 0x110ae1) (movR64R64Effect 0x110ae1 7 4) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 244) (.out 0x110ae4 (movzxR32M8Effect 0x110ae4 4 7 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[65]
    (.letOp (n := 245) (.exec 0x110ae4 (LoadPre 0x110ae4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110ae4 + BitVec.ofNat 64 4)) 1) (movzxR32M8Effect 0x110ae4 4 7 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 246) (.out 0x110ae8 (decR64Effect 0x110ae8 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[244]
    (.letOp (n := 247) (.exec 0x110ae8 (fun s => s.RIP = 0x110ae8) (decR64Effect 0x110ae8 7) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[244]
    (.letOp (n := 248) (.out 0x110aeb (andR64R64Effect 0x110aeb 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 13] []) (.reg (.gpr 7))) #v[246, 232]
    (.letOp (n := 249) (.exec 0x110aeb (fun s => s.RIP = 0x110aeb) (andR64R64Effect 0x110aeb 7 13) (Reg.operands [.gpr 7, .gpr 13] [])) #v[246, 232]
    (.letOp (n := 250) (.out 0x110aee (sarR64Effect 0x110aee 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[248]
    (.letOp (n := 251) (.exec 0x110aee (fun s => s.RIP = 0x110aee) (sarR64Effect 0x110aee 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[248]
    (b_l1109b0_5)))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_4 : List UInt8 :=
  [0x49, 0xF7, 0xD5, 0x48, 0x89, 0xCD, 0x4C, 0x21, 0xED, 0x49, 0x09, 0xCD, 0x4D, 0x21, 0xFD, 0x49,
    0x09, 0xED, 0x49, 0xC1, 0xED, 0x3F, 0x4C, 0x89, 0x2C, 0x24, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x2C,
    0x24, 0x48, 0x89, 0xF8, 0x4D, 0x85, 0xE4, 0x0F, 0x94, 0xC1, 0x44, 0x20, 0xE9, 0x88, 0x0C, 0x24,
    0x48, 0x89, 0xE7, 0x0F, 0xB6, 0x3C, 0x24, 0x48, 0xFF, 0xCF, 0x4C, 0x21, 0xEF, 0x48, 0xC1, 0xFF,
    0x3F] ++ bytes_l1109b0_5

theorem code_l1109b0_4 : ∀ x ∈ codeRange 0x110ab1 bytes_l1109b0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10ab1 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_5

@[cfg_block] def b_l1109b0_3 : Block Op Label signature Reg.count 176 :=
  .letOp (n := 176) (.out 0x110a6f (subR64R64Effect 0x110a6f 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[174, 172]
    (.letOp (n := 177) (.exec 0x110a6f (fun s => s.RIP = 0x110a6f) (subR64R64Effect 0x110a6f 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[174, 172]
    (.letOp (n := 178) (.out 0x110a72 (sarR64Effect 0x110a72 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[170]
    (.letOp (n := 179) (.exec 0x110a72 (fun s => s.RIP = 0x110a72) (sarR64Effect 0x110a72 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 180) (.out 0x110a76 (addR64R64Effect 0x110a76 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[178, 176]
    (.letOp (n := 181) (.exec 0x110a76 (fun s => s.RIP = 0x110a76) (addR64R64Effect 0x110a76 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[178, 176]
    (.letOp (n := 182) (.out 0x110a79 (movR64R64Effect 0x110a79 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[102]
    (.letOp (n := 183) (.exec 0x110a79 (fun s => s.RIP = 0x110a79) (movR64R64Effect 0x110a79 13 9) (Reg.operands [.gpr 9] [])) #v[102]
    (.letOp (n := 184) (.out 0x110a7c (notR64Effect 0x110a7c 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13] []) (.reg (.gpr 13))) #v[182]
    (.letOp (n := 185) (.exec 0x110a7c (fun s => s.RIP = 0x110a7c) (notR64Effect 0x110a7c 13) (Reg.operands [.gpr 13] [])) #v[182]
    (.letOp (n := 186) (.out 0x110a7f (movR64R64Effect 0x110a7f 15 5) (EffectPart.reads (.reg (.gpr 15)) [.gpr 5] []) (.reg (.gpr 15))) #v[172]
    (.letOp (n := 187) (.exec 0x110a7f (fun s => s.RIP = 0x110a7f) (movR64R64Effect 0x110a7f 15 5) (Reg.operands [.gpr 5] [])) #v[172]
    (.letOp (n := 188) (.out 0x110a82 (andR64R64Effect 0x110a82 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[186, 184]
    (.letOp (n := 189) (.exec 0x110a82 (fun s => s.RIP = 0x110a82) (andR64R64Effect 0x110a82 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[186, 184]
    (.letOp (n := 190) (.out 0x110a85 (orR64R64Effect 0x110a85 13 5) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 5] []) (.reg (.gpr 13))) #v[184, 172]
    (.letOp (n := 191) (.exec 0x110a85 (fun s => s.RIP = 0x110a85) (orR64R64Effect 0x110a85 13 5) (Reg.operands [.gpr 13, .gpr 5] [])) #v[184, 172]
    (.letOp (n := 192) (.out 0x110a88 (andR64R64Effect 0x110a88 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[190, 180]
    (.letOp (n := 193) (.exec 0x110a88 (fun s => s.RIP = 0x110a88) (andR64R64Effect 0x110a88 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[190, 180]
    (.letOp (n := 194) (.out 0x110a8b (orR64R64Effect 0x110a8b 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[192, 188]
    (.letOp (n := 195) (.exec 0x110a8b (fun s => s.RIP = 0x110a8b) (orR64R64Effect 0x110a8b 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[192, 188]
    (.letOp (n := 196) (.out 0x110a8e (shrR64Effect 0x110a8e 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[194]
    (.letOp (n := 197) (.exec 0x110a8e (fun s => s.RIP = 0x110a8e) (shrR64Effect 0x110a8e 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.exec 0x110a92 (StorePre 0x110a92 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a92 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a92 13 (.sib 4 none 0 .none)) (Reg.operands [.gpr 13, .gpr 4] [])) #v[196, 65]
    (.letOp (n := 199) (.out 0x110a96 (xorR32R32Effect 0x110a96 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[188, 188]
    (.letOp (n := 200) (.exec 0x110a96 (fun s => s.RIP = 0x110a96) (xorR32R32Effect 0x110a96 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[188, 188]
    (.letOp (n := 201) (.out 0x110a99 (subR64M64Effect 0x110a99 15 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 4] []) (.reg (.gpr 15))) #v[199, 65]
    (.letOp (n := 202) (.exec 0x110a99 (LoadPre 0x110a99 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a99 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a99 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[199, 65]
    (.letOp (n := 203) (.out 0x110a9d (movR64M64Effect 0x110a9d 1 (.base 1 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[1]
    (.letOp (n := 204) (.exec 0x110a9d (LoadPre 0x110a9d (fun s => AddrMode.addr (.base 1 (.d8 0x18)) s (0x110a9d + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a9d 1 (.base 1 (.d8 0x18))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 205) (.out 0x110aa1 (movR64R64Effect 0x110aa1 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 206) (.exec 0x110aa1 (fun s => s.RIP = 0x110aa1) (movR64R64Effect 0x110aa1 13 8) (Reg.operands [.gpr 8] [])) #v[105]
    (.letOp (n := 207) (.out 0x110aa4 (subR64R64Effect 0x110aa4 13 1) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 1] []) (.reg (.gpr 13))) #v[205, 203]
    (.letOp (n := 208) (.exec 0x110aa4 (fun s => s.RIP = 0x110aa4) (subR64R64Effect 0x110aa4 13 1) (Reg.operands [.gpr 13, .gpr 1] [])) #v[205, 203]
    (.letOp (n := 209) (.out 0x110aa7 (sarR64Effect 0x110aa7 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[201]
    (.letOp (n := 210) (.exec 0x110aa7 (fun s => s.RIP = 0x110aa7) (sarR64Effect 0x110aa7 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[201]
    (.letOp (n := 211) (.out 0x110aab (addR64R64Effect 0x110aab 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[209, 207]
    (.letOp (n := 212) (.exec 0x110aab (fun s => s.RIP = 0x110aab) (addR64R64Effect 0x110aab 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[209, 207]
    (.letOp (n := 213) (.out 0x110aae (movR64R64Effect 0x110aae 13 8) (EffectPart.reads (.reg (.gpr 13)) [.gpr 8] []) (.reg (.gpr 13))) #v[105]
    (.letOp (n := 214) (.exec 0x110aae (fun s => s.RIP = 0x110aae) (movR64R64Effect 0x110aae 13 8) (Reg.operands [.gpr 8] [])) #v[105]
    (b_l1109b0_4)))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_3 : List UInt8 :=
  [0x49, 0x29, 0xED, 0x49, 0xC1, 0xFE, 0x3F, 0x4D, 0x01, 0xEE, 0x4D, 0x89, 0xCD, 0x49, 0xF7, 0xD5,
    0x49, 0x89, 0xEF, 0x4D, 0x21, 0xEF, 0x49, 0x09, 0xED, 0x4D, 0x21, 0xF5, 0x4D, 0x09, 0xFD, 0x49,
    0xC1, 0xED, 0x3F, 0x4C, 0x89, 0x2C, 0x24, 0x45, 0x31, 0xFF, 0x4C, 0x2B, 0x3C, 0x24, 0x48, 0x8B,
    0x49, 0x18, 0x4D, 0x89, 0xC5, 0x49, 0x29, 0xCD, 0x49, 0xC1, 0xFF, 0x3F, 0x4D, 0x01, 0xEF, 0x4D,
    0x89, 0xC5] ++ bytes_l1109b0_4

theorem code_l1109b0_3 : ∀ x ∈ codeRange 0x110a6f bytes_l1109b0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10a6f 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_4

@[cfg_block] def b_l1109b0_2 : Block Op Label signature Reg.count 137 :=
  .letOp (n := 137) (.out 0x110a2d (xorR32R32Effect 0x110a2d 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[133, 133]
    (.letOp (n := 138) (.exec 0x110a2d (fun s => s.RIP = 0x110a2d) (xorR32R32Effect 0x110a2d 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[133, 133]
    (.letOp (n := 139) (.out 0x110a2f (subR64M64Effect 0x110a2f 6 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[137, 65]
    (.letOp (n := 140) (.exec 0x110a2f (LoadPre 0x110a2f (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a2f + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a2f 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[137, 65]
    (.letOp (n := 141) (.out 0x110a33 (movR64M64Effect 0x110a33 14 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 1] []) (.reg (.gpr 14))) #v[1]
    (.letOp (n := 142) (.exec 0x110a33 (LoadPre 0x110a33 (fun s => AddrMode.addr (.base 1 (.d8 0x8)) s (0x110a33 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a33 14 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 143) (.out 0x110a37 (movR64R64Effect 0x110a37 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 144) (.exec 0x110a37 (fun s => s.RIP = 0x110a37) (movR64R64Effect 0x110a37 15 10) (Reg.operands [.gpr 10] [])) #v[99]
    (.letOp (n := 145) (.out 0x110a3a (subR64R64Effect 0x110a3a 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[143, 141]
    (.letOp (n := 146) (.exec 0x110a3a (fun s => s.RIP = 0x110a3a) (subR64R64Effect 0x110a3a 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[143, 141]
    (.letOp (n := 147) (.out 0x110a3d (sarR64Effect 0x110a3d 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[139]
    (.letOp (n := 148) (.exec 0x110a3d (fun s => s.RIP = 0x110a3d) (sarR64Effect 0x110a3d 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[139]
    (.letOp (n := 149) (.out 0x110a41 (addR64R64Effect 0x110a41 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[147, 145]
    (.letOp (n := 150) (.exec 0x110a41 (fun s => s.RIP = 0x110a41) (addR64R64Effect 0x110a41 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[147, 145]
    (.letOp (n := 151) (.out 0x110a44 (movR64R64Effect 0x110a44 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 10] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 152) (.exec 0x110a44 (fun s => s.RIP = 0x110a44) (movR64R64Effect 0x110a44 15 10) (Reg.operands [.gpr 10] [])) #v[99]
    (.letOp (n := 153) (.out 0x110a47 (notR64Effect 0x110a47 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[151]
    (.letOp (n := 154) (.exec 0x110a47 (fun s => s.RIP = 0x110a47) (notR64Effect 0x110a47 15) (Reg.operands [.gpr 15] [])) #v[151]
    (.letOp (n := 155) (.out 0x110a4a (movR64R64Effect 0x110a4a 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 14] []) (.reg (.gpr 13))) #v[141]
    (.letOp (n := 156) (.exec 0x110a4a (fun s => s.RIP = 0x110a4a) (movR64R64Effect 0x110a4a 13 14) (Reg.operands [.gpr 14] [])) #v[141]
    (.letOp (n := 157) (.out 0x110a4d (andR64R64Effect 0x110a4d 13 15) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 15] []) (.reg (.gpr 13))) #v[155, 153]
    (.letOp (n := 158) (.exec 0x110a4d (fun s => s.RIP = 0x110a4d) (andR64R64Effect 0x110a4d 13 15) (Reg.operands [.gpr 13, .gpr 15] [])) #v[155, 153]
    (.letOp (n := 159) (.out 0x110a50 (orR64R64Effect 0x110a50 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[153, 141]
    (.letOp (n := 160) (.exec 0x110a50 (fun s => s.RIP = 0x110a50) (orR64R64Effect 0x110a50 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[153, 141]
    (.letOp (n := 161) (.out 0x110a53 (andR64R64Effect 0x110a53 15 6) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 6] []) (.reg (.gpr 15))) #v[159, 149]
    (.letOp (n := 162) (.exec 0x110a53 (fun s => s.RIP = 0x110a53) (andR64R64Effect 0x110a53 15 6) (Reg.operands [.gpr 15, .gpr 6] [])) #v[159, 149]
    (.letOp (n := 163) (.out 0x110a56 (orR64R64Effect 0x110a56 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[161, 157]
    (.letOp (n := 164) (.exec 0x110a56 (fun s => s.RIP = 0x110a56) (orR64R64Effect 0x110a56 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[161, 157]
    (.letOp (n := 165) (.out 0x110a59 (shrR64Effect 0x110a59 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[163]
    (.letOp (n := 166) (.exec 0x110a59 (fun s => s.RIP = 0x110a59) (shrR64Effect 0x110a59 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[163]
    (.letOp (n := 167) (.exec 0x110a5d (StorePre 0x110a5d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a5d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a5d 15 (.sib 4 none 0 .none)) (Reg.operands [.gpr 15, .gpr 4] [])) #v[165, 65]
    (.letOp (n := 168) (.out 0x110a61 (xorR32R32Effect 0x110a61 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[141, 141]
    (.letOp (n := 169) (.exec 0x110a61 (fun s => s.RIP = 0x110a61) (xorR32R32Effect 0x110a61 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[141, 141]
    (.letOp (n := 170) (.out 0x110a64 (subR64M64Effect 0x110a64 14 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[168, 65]
    (.letOp (n := 171) (.exec 0x110a64 (LoadPre 0x110a64 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a64 + BitVec.ofNat 64 4)) 8) (subR64M64Effect 0x110a64 14 (.sib 4 none 0 .none)) (Reg.operands [.gpr 14, .gpr 4] [])) #v[168, 65]
    (.letOp (n := 172) (.out 0x110a68 (movR64M64Effect 0x110a68 5 (.base 1 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 1] []) (.reg (.gpr 5))) #v[1]
    (.letOp (n := 173) (.exec 0x110a68 (LoadPre 0x110a68 (fun s => AddrMode.addr (.base 1 (.d8 0x10)) s (0x110a68 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110a68 5 (.base 1 (.d8 0x10))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 174) (.out 0x110a6c (movR64R64Effect 0x110a6c 13 9) (EffectPart.reads (.reg (.gpr 13)) [.gpr 9] []) (.reg (.gpr 13))) #v[102]
    (.letOp (n := 175) (.exec 0x110a6c (fun s => s.RIP = 0x110a6c) (movR64R64Effect 0x110a6c 13 9) (Reg.operands [.gpr 9] [])) #v[102]
    (b_l1109b0_3)))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_2 : List UInt8 :=
  [0x31, 0xF6, 0x48, 0x2B, 0x34, 0x24, 0x4C, 0x8B, 0x71, 0x08, 0x4D, 0x89, 0xD7, 0x4D, 0x29, 0xF7,
    0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x4D, 0x89, 0xD7, 0x49, 0xF7, 0xD7, 0x4D, 0x89, 0xF5,
    0x4D, 0x21, 0xFD, 0x4D, 0x09, 0xF7, 0x49, 0x21, 0xF7, 0x4D, 0x09, 0xEF, 0x49, 0xC1, 0xEF, 0x3F,
    0x4C, 0x89, 0x3C, 0x24, 0x45, 0x31, 0xF6, 0x4C, 0x2B, 0x34, 0x24, 0x48, 0x8B, 0x69, 0x10, 0x4D,
    0x89, 0xCD] ++ bytes_l1109b0_3

theorem code_l1109b0_2 : ∀ x ∈ codeRange 0x110a2d bytes_l1109b0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10a2d 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_3

@[cfg_block] def b_l1109b0_1 : Block Op Label signature Reg.count 97 :=
  .letOp (n := 97) (.out 0x1109eb (atFlags (condHolds 2) (setccR8Effect 0x1109eb 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[90, 93]
    (.letOp (n := 98) (.exec 0x1109eb (fun s => s.RIP = 0x1109eb) (atFlags (condHolds 2) (setccR8Effect 0x1109eb 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[90, 93]
    (.letOp (n := 99) (.out 0x1109ee (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2] []) (.reg (.gpr 10))) #v[76, 2]
    (.letOp (n := 100) (.out 0x1109ee (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 2] []) (.flag .CF)) #v[76, 2]
    (.letOp (n := 101) (.exec 0x1109ee (LoadPre 0x1109ee (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x1109ee + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109ee 10 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 2] [])) #v[76, 2]
    (.letOp (n := 102) (.out 0x1109f2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[83, 95, 100]
    (.letOp (n := 103) (.out 0x1109f2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[83, 95, 100]
    (.letOp (n := 104) (.exec 0x1109f2 (fun s => s.RIP = 0x1109f2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f2 9 0)) (Reg.operands [.gpr 9, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[83, 95, 100]
    (.letOp (n := 105) (.out 0x1109f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[86, 92, 103]
    (.letOp (n := 106) (.out 0x1109f5 (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[86, 92, 103]
    (.letOp (n := 107) (.exec 0x1109f5 (fun s => s.RIP = 0x1109f5) (atFlags StatusFlags.CF (adcR64R64Effect 0x1109f5 8 14)) (Reg.operands [.gpr 8, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[86, 92, 103]
    (.letOp (n := 108) (.exec 0x1109f8 (StorePre 0x1109f8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x1109f8 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 2) (setccM8Effect 0x1109f8 5 (.sib 4 none 0 (.d8 0xf)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[65, 106]
    (.letOp (n := 109) (.out 0x1109fd (movR64R64Effect 0x1109fd 12 3) (EffectPart.reads (.reg (.gpr 12)) [.gpr 3] []) (.reg (.gpr 12))) #v[97]
    (.letOp (n := 110) (.exec 0x1109fd (fun s => s.RIP = 0x1109fd) (movR64R64Effect 0x1109fd 12 3) (Reg.operands [.gpr 3] [])) #v[97]
    (.letOp (n := 111) (.out 0x110a00 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110a00 12 0x0)) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 12))) #v[109, 106]
    (.letOp (n := 112) (.exec 0x110a00 (fun s => s.RIP = 0x110a00) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x110a00 12 0x0)) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[109, 106]
    (.letOp (n := 113) (.out 0x110a04 (movR64M64Effect 0x110a04 0 (.base 1 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[1]
    (.letOp (n := 114) (.exec 0x110a04 (LoadPre 0x110a04 (fun s => AddrMode.addr (.base 1 .none) s (0x110a04 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110a04 0 (.base 1 .none)) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 115) (.out 0x110a07 (movR64R64Effect 0x110a07 2 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 116) (.exec 0x110a07 (fun s => s.RIP = 0x110a07) (movR64R64Effect 0x110a07 2 11) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 117) (.out 0x110a0a (subR64R64Effect 0x110a0a 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[115, 113]
    (.letOp (n := 118) (.exec 0x110a0a (fun s => s.RIP = 0x110a0a) (subR64R64Effect 0x110a0a 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[115, 113]
    (.letOp (n := 119) (.out 0x110a0d (movR64R64Effect 0x110a0d 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 11] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 120) (.exec 0x110a0d (fun s => s.RIP = 0x110a0d) (movR64R64Effect 0x110a0d 6 11) (Reg.operands [.gpr 11] [])) #v[71]
    (.letOp (n := 121) (.out 0x110a10 (notR64Effect 0x110a10 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[119]
    (.letOp (n := 122) (.exec 0x110a10 (fun s => s.RIP = 0x110a10) (notR64Effect 0x110a10 6) (Reg.operands [.gpr 6] [])) #v[119]
    (.letOp (n := 123) (.out 0x110a13 (movR64R64Effect 0x110a13 14 0) (EffectPart.reads (.reg (.gpr 14)) [.gpr 0] []) (.reg (.gpr 14))) #v[113]
    (.letOp (n := 124) (.exec 0x110a13 (fun s => s.RIP = 0x110a13) (movR64R64Effect 0x110a13 14 0) (Reg.operands [.gpr 0] [])) #v[113]
    (.letOp (n := 125) (.out 0x110a16 (andR64R64Effect 0x110a16 14 6) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[123, 121]
    (.letOp (n := 126) (.exec 0x110a16 (fun s => s.RIP = 0x110a16) (andR64R64Effect 0x110a16 14 6) (Reg.operands [.gpr 14, .gpr 6] [])) #v[123, 121]
    (.letOp (n := 127) (.out 0x110a19 (orR64R64Effect 0x110a19 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[121, 113]
    (.letOp (n := 128) (.exec 0x110a19 (fun s => s.RIP = 0x110a19) (orR64R64Effect 0x110a19 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[121, 113]
    (.letOp (n := 129) (.out 0x110a1c (andR64R64Effect 0x110a1c 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[127, 117]
    (.letOp (n := 130) (.exec 0x110a1c (fun s => s.RIP = 0x110a1c) (andR64R64Effect 0x110a1c 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[127, 117]
    (.letOp (n := 131) (.out 0x110a1f (orR64R64Effect 0x110a1f 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[129, 125]
    (.letOp (n := 132) (.exec 0x110a1f (fun s => s.RIP = 0x110a1f) (orR64R64Effect 0x110a1f 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[129, 125]
    (.letOp (n := 133) (.out 0x110a22 (shrR64Effect 0x110a22 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[131]
    (.letOp (n := 134) (.exec 0x110a22 (fun s => s.RIP = 0x110a22) (shrR64Effect 0x110a22 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[131]
    (.letOp (n := 135) (.exec 0x110a26 (StorePre 0x110a26 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x110a26 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110a26 6 (.sib 4 none 0 .none)) (Reg.operands [.gpr 6, .gpr 4] [])) #v[133, 65]
    (.letOp (n := 136) (.exec 0x110a2a (fun s => s.RIP = 0x110a2a) (movR64R64Effect 0x110a2a 0 4) (Reg.operands [.gpr 4] [])) #v[65]
    (b_l1109b0_2))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0_1 : List UInt8 :=
  [0x0F, 0x92, 0xC3, 0x4C, 0x03, 0x52, 0x08, 0x49, 0x11, 0xC1, 0x4D, 0x11, 0xF0, 0x0F, 0x92, 0x44,
    0x24, 0x0F, 0x49, 0x89, 0xDC, 0x49, 0x83, 0xD4, 0x00, 0x48, 0x8B, 0x01, 0x4C, 0x89, 0xDA, 0x48,
    0x29, 0xC2, 0x4C, 0x89, 0xDE, 0x48, 0xF7, 0xD6, 0x49, 0x89, 0xC6, 0x49, 0x21, 0xF6, 0x48, 0x09,
    0xC6, 0x48, 0x21, 0xD6, 0x4C, 0x09, 0xF6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x34, 0x24, 0x48,
    0x89, 0xE0] ++ bytes_l1109b0_2

theorem code_l1109b0_1 : ∀ x ∈ codeRange 0x1109eb bytes_l1109b0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x109eb 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_2

@[cfg_block] def b_l1109b0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1109b0 (pushR64Effect 0x1109b0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1109b0 (PushPre 0x1109b0 1) (pushR64Effect 0x1109b0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1109b1 (pushR64Effect 0x1109b1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1109b1 (PushPre 0x1109b1 2) (pushR64Effect 0x1109b1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1109b3 (pushR64Effect 0x1109b3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1109b3 (PushPre 0x1109b3 2) (pushR64Effect 0x1109b3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1109b5 (pushR64Effect 0x1109b5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1109b5 (PushPre 0x1109b5 2) (pushR64Effect 0x1109b5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1109b7 (pushR64Effect 0x1109b7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1109b7 (PushPre 0x1109b7 2) (pushR64Effect 0x1109b7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1109b9 (pushR64Effect 0x1109b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1109b9 (PushPre 0x1109b9 1) (pushR64Effect 0x1109b9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1109ba (subR64Imm8Effect 0x1109ba 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1109ba (fun s => s.RIP = 0x1109ba) (subR64Imm8Effect 0x1109ba 4 0x10) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1109be (movR64M64Effect 0x1109be 11 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[2]
    (.letOp (n := 68) (.exec 0x1109be (LoadPre 0x1109be (fun s => AddrMode.addr (.base 2 .none) s (0x1109be + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1109be 11 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 69) (.out 0x1109c1 (movR64M64Effect 0x1109c1 9 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[2]
    (.letOp (n := 70) (.exec 0x1109c1 (LoadPre 0x1109c1 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x1109c1 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c1 9 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 71) (.out 0x1109c5 (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 6] []) (.reg (.gpr 11))) #v[67, 6]
    (.letOp (n := 72) (.out 0x1109c5 (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 6] []) (.flag .CF)) #v[67, 6]
    (.letOp (n := 73) (.exec 0x1109c5 (LoadPre 0x1109c5 (fun s => AddrMode.addr (.base 6 .none) s (0x1109c5 + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x1109c5 11 (.base 6 .none)) (Reg.operands [.gpr 11, .gpr 6] [])) #v[67, 6]
    (.letOp (n := 74) (.out 0x1109c8 (movR64M64Effect 0x1109c8 10 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 75) (.exec 0x1109c8 (LoadPre 0x1109c8 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1109c8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109c8 10 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 76) (.out 0x1109cc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[74, 72]
    (.letOp (n := 77) (.out 0x1109cc (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[74, 72]
    (.letOp (n := 78) (.exec 0x1109cc (fun s => s.RIP = 0x1109cc) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1109cc 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[74, 72]
    (.letOp (n := 79) (.out 0x1109d0 (atFlags (condHolds 2) (setccR8Effect 0x1109d0 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[0, 77]
    (.letOp (n := 80) (.exec 0x1109d0 (fun s => s.RIP = 0x1109d0) (atFlags (condHolds 2) (setccR8Effect 0x1109d0 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[0, 77]
    (.letOp (n := 81) (.out 0x1109d3 (xorR32R32Effect 0x1109d3 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[8, 8]
    (.letOp (n := 82) (.exec 0x1109d3 (fun s => s.RIP = 0x1109d3) (xorR32R32Effect 0x1109d3 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[8, 8]
    (.letOp (n := 83) (.out 0x1109d6 (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[69, 6]
    (.letOp (n := 84) (.out 0x1109d6 (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[69, 6]
    (.letOp (n := 85) (.exec 0x1109d6 (LoadPre 0x1109d6 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1109d6 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109d6 9 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 9, .gpr 6] [])) #v[69, 6]
    (.letOp (n := 86) (.out 0x1109da (atFlags (condHolds 2) (setccR8Effect 0x1109da 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[81, 84]
    (.letOp (n := 87) (.exec 0x1109da (fun s => s.RIP = 0x1109da) (atFlags (condHolds 2) (setccR8Effect 0x1109da 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[81, 84]
    (.letOp (n := 88) (.out 0x1109de (movR64M64Effect 0x1109de 14 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[2]
    (.letOp (n := 89) (.exec 0x1109de (LoadPre 0x1109de (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x1109de + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1109de 14 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 90) (.out 0x1109e2 (xorR32R32Effect 0x1109e2 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[3, 3]
    (.letOp (n := 91) (.exec 0x1109e2 (fun s => s.RIP = 0x1109e2) (xorR32R32Effect 0x1109e2 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[3, 3]
    (.letOp (n := 92) (.out 0x1109e4 (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6] []) (.reg (.gpr 14))) #v[88, 6]
    (.letOp (n := 93) (.out 0x1109e4 (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 6] []) (.flag .CF)) #v[88, 6]
    (.letOp (n := 94) (.exec 0x1109e4 (LoadPre 0x1109e4 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1109e4 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1109e4 14 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 6] [])) #v[88, 6]
    (.letOp (n := 95) (.out 0x1109e8 (movzxR32R8Effect 0x1109e8 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[79]
    (.letOp (n := 96) (.exec 0x1109e8 (fun s => s.RIP = 0x1109e8) (movzxR32R8Effect 0x1109e8 3 0 0) (Reg.operands [.gpr 0] [])) #v[79]
    (b_l1109b0_1))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1109b0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B,
    0x1A, 0x4C, 0x8B, 0x4A, 0x10, 0x4C, 0x03, 0x1E, 0x4C, 0x8B, 0x56, 0x08, 0x49, 0x83, 0xD2, 0x00,
    0x0F, 0x92, 0xC0, 0x45, 0x31, 0xC0, 0x4C, 0x03, 0x4E, 0x10, 0x41, 0x0F, 0x92, 0xC0, 0x4C, 0x8B,
    0x72, 0x18, 0x31, 0xDB, 0x4C, 0x03, 0x76, 0x18, 0x0F, 0xB6, 0xC0] ++ bytes_l1109b0_1

theorem code_l1109b0 : ∀ x ∈ codeRange 0x1109b0 bytes_l1109b0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x109b0 59 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1109b0_1

@[cfg_block] def b_l110b80_4 : Block Op Label signature Reg.count 204 :=
  .letOp (n := 204) (.out 0x110c99 (decR64Effect 0x110c99 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[192]
    (.letOp (n := 205) (.exec 0x110c99 (fun s => s.RIP = 0x110c99) (decR64Effect 0x110c99 10) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[192]
    (.letOp (n := 206) (.out 0x110c9c (andR64R64Effect 0x110c9c 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[204, 107]
    (.letOp (n := 207) (.exec 0x110c9c (fun s => s.RIP = 0x110c9c) (andR64R64Effect 0x110c9c 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[204, 107]
    (.letOp (n := 208) (.out 0x110c9f (decR64Effect 0x110c9f 11) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 11))) #v[195]
    (.letOp (n := 209) (.exec 0x110c9f (fun s => s.RIP = 0x110c9f) (decR64Effect 0x110c9f 11) (Reg.operands [.gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[195]
    (.letOp (n := 210) (.out 0x110ca2 (andR64R64Effect 0x110ca2 11 3) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3] []) (.reg (.gpr 11))) #v[208, 136]
    (.letOp (n := 211) (.exec 0x110ca2 (fun s => s.RIP = 0x110ca2) (andR64R64Effect 0x110ca2 11 3) (Reg.operands [.gpr 11, .gpr 3] [])) #v[208, 136]
    (.letOp (n := 212) (.out 0x110ca5 (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 213) (.exec 0x110ca5 (LoadPre 0x110ca5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110ca5 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110ca5 5 1 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 214) (.out 0x110caa (decR64Effect 0x110caa 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[212]
    (.letOp (n := 215) (.exec 0x110caa (fun s => s.RIP = 0x110caa) (decR64Effect 0x110caa 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[212]
    (.letOp (n := 216) (.out 0x110cad (andR64R64Effect 0x110cad 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[214, 163]
    (.letOp (n := 217) (.exec 0x110cad (fun s => s.RIP = 0x110cad) (andR64R64Effect 0x110cad 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[214, 163]
    (.letOp (n := 218) (.exec 0x110cb0 (StorePre 0x110cb0 3 (fun s => AddrMode.addr (.base 7 .none) s (0x110cb0 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x110cb0 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[202, 7]
    (.letOp (n := 219) (.exec 0x110cb3 (StorePre 0x110cb3 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x110cb3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb3 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[206, 7]
    (.letOp (n := 220) (.exec 0x110cb7 (StorePre 0x110cb7 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x110cb7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cb7 11 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 11, .gpr 7] [])) #v[210, 7]
    (.letOp (n := 221) (.exec 0x110cbb (StorePre 0x110cbb 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x110cbb + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x110cbb 1 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[216, 7]
    (.letOp (n := 222) (.out 0x110cbf (addR64Imm8Effect 0x110cbf 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[61]
    (.letOp (n := 223) (.exec 0x110cbf (fun s => s.RIP = 0x110cbf) (addR64Imm8Effect 0x110cbf 4 0x10) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 224) (.out 0x110cc3 (popR64Effect 0x110cc3 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[222]
    (.letOp (n := 225) (.out 0x110cc3 (popR64Effect 0x110cc3 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[222]
    (.letOp (n := 226) (.exec 0x110cc3 (PopPre 0x110cc3) (popR64Effect 0x110cc3 1 3) (Reg.operands [.gpr 4] [])) #v[222]
    (.letOp (n := 227) (.out 0x110cc4 (popR64Effect 0x110cc4 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[225]
    (.letOp (n := 228) (.out 0x110cc4 (popR64Effect 0x110cc4 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[225]
    (.letOp (n := 229) (.exec 0x110cc4 (PopPre 0x110cc4) (popR64Effect 0x110cc4 2 12) (Reg.operands [.gpr 4] [])) #v[225]
    (.letOp (n := 230) (.out 0x110cc6 (popR64Effect 0x110cc6 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[228]
    (.letOp (n := 231) (.out 0x110cc6 (popR64Effect 0x110cc6 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[228]
    (.letOp (n := 232) (.exec 0x110cc6 (PopPre 0x110cc6) (popR64Effect 0x110cc6 2 14) (Reg.operands [.gpr 4] [])) #v[228]
    (.letOp (n := 233) (.out 0x110cc8 (popR64Effect 0x110cc8 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[231]
    (.letOp (n := 234) (.out 0x110cc8 (popR64Effect 0x110cc8 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[231]
    (.letOp (n := 235) (.exec 0x110cc8 (PopPre 0x110cc8) (popR64Effect 0x110cc8 2 15) (Reg.operands [.gpr 4] [])) #v[231]
    (.letOp (n := 236) (.out 0x110cca (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[234]
    (.letOp (n := 237) (.out 0x110cca (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[234]
    (.letOp (n := 238) (.exec 0x110cca (RetPre 0x110cca) (retEffect) (Reg.operands [.gpr 4] [])) #v[234]
    (.terminate (.ret (RegMap.args [(0, 198), (1, 216), (2, 202), (3, 224), (4, 237), (5, 5), (6, 163), (7, 7), (8, 107), (9, 187), (10, 206), (11, 210), (12, 227), (13, 13), (14, 230), (15, 233), (22, 22), (39, 39), (50, 50), (51, 51)] 239) (some ⟨236, by decide⟩)))))))))))))))))))))))))))))))))))))

def bytes_l110b80_4 : List UInt8 :=
  [0x49, 0xFF, 0xCA, 0x4D, 0x21, 0xC2, 0x49, 0xFF, 0xCB, 0x49, 0x21, 0xDB, 0x0F, 0xB6, 0x4C, 0x24,
    0x07, 0x48, 0xFF, 0xC9, 0x48, 0x21, 0xF1, 0x48, 0x89, 0x17, 0x4C, 0x89, 0x57, 0x08, 0x4C, 0x89,
    0x5F, 0x10, 0x48, 0x89, 0x4F, 0x18, 0x48, 0x83, 0xC4, 0x10, 0x5B, 0x41, 0x5C, 0x41, 0x5E, 0x41,
    0x5F, 0xC3]

theorem code_l110b80_4 : ∀ x ∈ codeRange 0x110c99 bytes_l110b80_4, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x10c99 50 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l110b80_3 : Block Op Label signature Reg.count 169 :=
  .letOp (n := 169) (.out 0x110c48 (andR64R64Effect 0x110c48 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2] []) (.reg (.gpr 15))) #v[167, 165]
    (.letOp (n := 170) (.exec 0x110c48 (fun s => s.RIP = 0x110c48) (andR64R64Effect 0x110c48 15 2) (Reg.operands [.gpr 15, .gpr 2] [])) #v[167, 165]
    (.letOp (n := 171) (.out 0x110c4b (orR64R64Effect 0x110c4b 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[165, 69]
    (.letOp (n := 172) (.exec 0x110c4b (fun s => s.RIP = 0x110c4b) (orR64R64Effect 0x110c4b 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[165, 69]
    (.letOp (n := 173) (.out 0x110c4e (andR64R64Effect 0x110c4e 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[171, 163]
    (.letOp (n := 174) (.exec 0x110c4e (fun s => s.RIP = 0x110c4e) (andR64R64Effect 0x110c4e 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[171, 163]
    (.letOp (n := 175) (.out 0x110c51 (orR64R64Effect 0x110c51 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[173, 169]
    (.letOp (n := 176) (.exec 0x110c51 (fun s => s.RIP = 0x110c51) (orR64R64Effect 0x110c51 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[173, 169]
    (.letOp (n := 177) (.out 0x110c54 (shrR64Effect 0x110c54 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[175]
    (.letOp (n := 178) (.exec 0x110c54 (fun s => s.RIP = 0x110c54) (shrR64Effect 0x110c54 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[175]
    (.letOp (n := 179) (.exec 0x110c58 (StorePre 0x110c58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c58 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c58 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[177, 61]
    (.letOp (n := 180) (.out 0x110c5d (orR64R64Effect 0x110c5d 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[65, 63]
    (.letOp (n := 181) (.exec 0x110c5d (fun s => s.RIP = 0x110c5d) (orR64R64Effect 0x110c5d 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[65, 63]
    (.letOp (n := 182) (.out 0x110c60 (orR64R64Effect 0x110c60 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[180, 67]
    (.letOp (n := 183) (.exec 0x110c60 (fun s => s.RIP = 0x110c60) (orR64R64Effect 0x110c60 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[180, 67]
    (.letOp (n := 184) (.out 0x110c63 (orR64R64Effect 0x110c63 0 9) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 9] []) (.flag .ZF)) #v[182, 69]
    (.letOp (n := 185) (.exec 0x110c63 (fun s => s.RIP = 0x110c63) (orR64R64Effect 0x110c63 0 9) (Reg.operands [.gpr 0, .gpr 9] [])) #v[182, 69]
    (.letOp (n := 186) (.exec 0x110c66 (StorePre 0x110c66 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c66 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c66 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 187) (.out 0x110c6b (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 4] []) (.reg (.gpr 9))) #v[61]
    (.letOp (n := 188) (.exec 0x110c6b (fun s => s.RIP = 0x110c6b) (leaR64Effect 0x110c6b 9 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 189) (.out 0x110c70 (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[61]
    (.letOp (n := 190) (.exec 0x110c70 (LoadPre 0x110c70 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c70 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x110c70 5 2 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 191) (.exec 0x110c75 (StorePre 0x110c75 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c75 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c75 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 192) (.out 0x110c7a (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[61]
    (.letOp (n := 193) (.exec 0x110c7a (LoadPre 0x110c7a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c7a + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c7a 6 10 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 194) (.exec 0x110c80 (StorePre 0x110c80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c80 + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c80 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 195) (.out 0x110c85 (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[61]
    (.letOp (n := 196) (.exec 0x110c85 (LoadPre 0x110c85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c85 + BitVec.ofNat 64 6)) 1) (movzxR32M8Effect 0x110c85 6 11 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 197) (.exec 0x110c8b (StorePre 0x110c8b 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x110c8b + BitVec.ofNat 64 5)) 1) (atFlags (condHolds 4) (setccM8Effect 0x110c8b 5 (.sib 4 none 0 (.d8 0x7)))) (Reg.operands [.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.ZF])) #v[61, 184]
    (.letOp (n := 198) (.out 0x110c90 (movR64R64Effect 0x110c90 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 199) (.exec 0x110c90 (fun s => s.RIP = 0x110c90) (movR64R64Effect 0x110c90 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 200) (.out 0x110c93 (decR64Effect 0x110c93 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[189]
    (.letOp (n := 201) (.exec 0x110c93 (fun s => s.RIP = 0x110c93) (decR64Effect 0x110c93 2) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[189]
    (.letOp (n := 202) (.out 0x110c96 (andR64R64Effect 0x110c96 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[200, 75]
    (.letOp (n := 203) (.exec 0x110c96 (fun s => s.RIP = 0x110c96) (andR64R64Effect 0x110c96 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[200, 75]
    (b_l110b80_4)))))))))))))))))))))))))))))))))))

def bytes_l110b80_3 : List UInt8 :=
  [0x49, 0x21, 0xD7, 0x4C, 0x09, 0xCA, 0x48, 0x21, 0xF2, 0x4C, 0x09, 0xFA, 0x48, 0xC1, 0xEA, 0x3F,
    0x48, 0x89, 0x54, 0x24, 0x08, 0x4C, 0x09, 0xD0, 0x4C, 0x09, 0xD8, 0x4C, 0x09, 0xC8, 0x0F, 0x94,
    0x44, 0x24, 0x07, 0x4C, 0x8D, 0x4C, 0x24, 0x07, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x0F, 0x94, 0x44,
    0x24, 0x07, 0x44, 0x0F, 0xB6, 0x54, 0x24, 0x07, 0x0F, 0x94, 0x44, 0x24, 0x07, 0x44, 0x0F, 0xB6,
    0x5C, 0x24, 0x07, 0x0F, 0x94, 0x44, 0x24, 0x07, 0x48, 0x89, 0xF8, 0x48, 0xFF, 0xCA, 0x48, 0x21,
    0xCA] ++ bytes_l110b80_4

theorem code_l110b80_3 : ∀ x ∈ codeRange 0x110c48 bytes_l110b80_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10c48 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_4

@[cfg_block] def b_l110b80_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.out 0x110c04 (movR64R64Effect 0x110c04 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 15] []) (.reg (.gpr 12))) #v[128]
    (.letOp (n := 131) (.exec 0x110c04 (fun s => s.RIP = 0x110c04) (movR64R64Effect 0x110c04 12 15) (Reg.operands [.gpr 15] [])) #v[128]
    (.letOp (n := 132) (.out 0x110c07 (subR64R64Effect 0x110c07 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 11] []) (.reg (.gpr 12))) #v[130, 67]
    (.letOp (n := 133) (.exec 0x110c07 (fun s => s.RIP = 0x110c07) (subR64R64Effect 0x110c07 12 11) (Reg.operands [.gpr 12, .gpr 11] [])) #v[130, 67]
    (.letOp (n := 134) (.out 0x110c0a (sarR64Effect 0x110c0a 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[126]
    (.letOp (n := 135) (.exec 0x110c0a (fun s => s.RIP = 0x110c0a) (sarR64Effect 0x110c0a 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 136) (.out 0x110c0e (addR64R64Effect 0x110c0e 3 12) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 12] []) (.reg (.gpr 3))) #v[134, 132]
    (.letOp (n := 137) (.exec 0x110c0e (fun s => s.RIP = 0x110c0e) (addR64R64Effect 0x110c0e 3 12) (Reg.operands [.gpr 3, .gpr 12] [])) #v[134, 132]
    (.letOp (n := 138) (.out 0x110c11 (notR64Effect 0x110c11 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15] []) (.reg (.gpr 15))) #v[128]
    (.letOp (n := 139) (.exec 0x110c11 (fun s => s.RIP = 0x110c11) (notR64Effect 0x110c11 15) (Reg.operands [.gpr 15] [])) #v[128]
    (.letOp (n := 140) (.out 0x110c14 (movR64R64Effect 0x110c14 12 11) (EffectPart.reads (.reg (.gpr 12)) [.gpr 11] []) (.reg (.gpr 12))) #v[67]
    (.letOp (n := 141) (.exec 0x110c14 (fun s => s.RIP = 0x110c14) (movR64R64Effect 0x110c14 12 11) (Reg.operands [.gpr 11] [])) #v[67]
    (.letOp (n := 142) (.out 0x110c17 (andR64R64Effect 0x110c17 12 15) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 15] []) (.reg (.gpr 12))) #v[140, 138]
    (.letOp (n := 143) (.exec 0x110c17 (fun s => s.RIP = 0x110c17) (andR64R64Effect 0x110c17 12 15) (Reg.operands [.gpr 12, .gpr 15] [])) #v[140, 138]
    (.letOp (n := 144) (.out 0x110c1a (orR64R64Effect 0x110c1a 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[138, 67]
    (.letOp (n := 145) (.exec 0x110c1a (fun s => s.RIP = 0x110c1a) (orR64R64Effect 0x110c1a 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[138, 67]
    (.letOp (n := 146) (.out 0x110c1d (andR64R64Effect 0x110c1d 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[144, 136]
    (.letOp (n := 147) (.exec 0x110c1d (fun s => s.RIP = 0x110c1d) (andR64R64Effect 0x110c1d 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[144, 136]
    (.letOp (n := 148) (.out 0x110c20 (orR64R64Effect 0x110c20 15 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 12] []) (.reg (.gpr 15))) #v[146, 142]
    (.letOp (n := 149) (.exec 0x110c20 (fun s => s.RIP = 0x110c20) (orR64R64Effect 0x110c20 15 12) (Reg.operands [.gpr 15, .gpr 12] [])) #v[146, 142]
    (.letOp (n := 150) (.out 0x110c23 (shrR64Effect 0x110c23 4 15 63) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[148]
    (.letOp (n := 151) (.exec 0x110c23 (fun s => s.RIP = 0x110c23) (shrR64Effect 0x110c23 4 15 63) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[148]
    (.letOp (n := 152) (.exec 0x110c27 (StorePre 0x110c27 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c27 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110c27 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[150, 61]
    (.letOp (n := 153) (.out 0x110c2c (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[93, 61]
    (.letOp (n := 154) (.exec 0x110c2c (LoadPre 0x110c2c (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110c2c + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110c2c 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[93, 61]
    (.letOp (n := 155) (.out 0x110c31 (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 156) (.exec 0x110c31 (LoadPre 0x110c31 (fun s => AddrMode.addr (.base 2 (.d8 0x18)) s (0x110c31 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c31 2 (.base 2 (.d8 0x18))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 157) (.out 0x110c35 (movR64R64Effect 0x110c35 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[155]
    (.letOp (n := 158) (.exec 0x110c35 (fun s => s.RIP = 0x110c35) (movR64R64Effect 0x110c35 15 2) (Reg.operands [.gpr 2] [])) #v[155]
    (.letOp (n := 159) (.out 0x110c38 (subR64R64Effect 0x110c38 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 9] []) (.reg (.gpr 15))) #v[157, 69]
    (.letOp (n := 160) (.exec 0x110c38 (fun s => s.RIP = 0x110c38) (subR64R64Effect 0x110c38 15 9) (Reg.operands [.gpr 15, .gpr 9] [])) #v[157, 69]
    (.letOp (n := 161) (.out 0x110c3b (sarR64Effect 0x110c3b 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[153]
    (.letOp (n := 162) (.exec 0x110c3b (fun s => s.RIP = 0x110c3b) (sarR64Effect 0x110c3b 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[153]
    (.letOp (n := 163) (.out 0x110c3f (addR64R64Effect 0x110c3f 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[161, 159]
    (.letOp (n := 164) (.exec 0x110c3f (fun s => s.RIP = 0x110c3f) (addR64R64Effect 0x110c3f 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[161, 159]
    (.letOp (n := 165) (.out 0x110c42 (notR64Effect 0x110c42 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[155]
    (.letOp (n := 166) (.exec 0x110c42 (fun s => s.RIP = 0x110c42) (notR64Effect 0x110c42 2) (Reg.operands [.gpr 2] [])) #v[155]
    (.letOp (n := 167) (.out 0x110c45 (movR64R64Effect 0x110c45 15 9) (EffectPart.reads (.reg (.gpr 15)) [.gpr 9] []) (.reg (.gpr 15))) #v[69]
    (.letOp (n := 168) (.exec 0x110c45 (fun s => s.RIP = 0x110c45) (movR64R64Effect 0x110c45 15 9) (Reg.operands [.gpr 9] [])) #v[69]
    (b_l110b80_3)))))))))))))))))))))))))))))))))))))))

def bytes_l110b80_2 : List UInt8 :=
  [0x4D, 0x89, 0xFC, 0x4D, 0x29, 0xDC, 0x48, 0xC1, 0xFB, 0x3F, 0x4C, 0x01, 0xE3, 0x49, 0xF7, 0xD7,
    0x4D, 0x89, 0xDC, 0x4D, 0x21, 0xFC, 0x4D, 0x09, 0xDF, 0x49, 0x21, 0xDF, 0x4D, 0x09, 0xE7, 0x49,
    0xC1, 0xEF, 0x3F, 0x4C, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x2B, 0x74, 0x24, 0x08, 0x48, 0x8B, 0x52,
    0x18, 0x49, 0x89, 0xD7, 0x4D, 0x29, 0xCF, 0x48, 0xC1, 0xFE, 0x3F, 0x4C, 0x01, 0xFE, 0x48, 0xF7,
    0xD2, 0x4D, 0x89, 0xCF] ++ bytes_l110b80_3

theorem code_l110b80_2 : ∀ x ∈ codeRange 0x110c04 bytes_l110b80_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10c04 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_3

@[cfg_block] def b_l110b80_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.exec 0x110bbe (fun s => s.RIP = 0x110bbe) (leaR64Effect 0x110bbe 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[61]
    (.letOp (n := 93) (.out 0x110bc3 (xorR32R32Effect 0x110bc3 2 6 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 6] []) (.reg (.gpr 6))) #v[89, 89]
    (.letOp (n := 94) (.exec 0x110bc3 (fun s => s.RIP = 0x110bc3) (xorR32R32Effect 0x110bc3 2 6 6) (Reg.operands [.gpr 6, .gpr 6] [])) #v[89, 89]
    (.letOp (n := 95) (.out 0x110bc5 (xorR32R32Effect 0x110bc5 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[81, 81]
    (.letOp (n := 96) (.exec 0x110bc5 (fun s => s.RIP = 0x110bc5) (xorR32R32Effect 0x110bc5 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[81, 81]
    (.letOp (n := 97) (.out 0x110bc8 (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 4] []) (.reg (.gpr 8))) #v[95, 61]
    (.letOp (n := 98) (.exec 0x110bc8 (LoadPre 0x110bc8 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bc8 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bc8 8 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[95, 61]
    (.letOp (n := 99) (.out 0x110bcd (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[2]
    (.letOp (n := 100) (.exec 0x110bcd (LoadPre 0x110bcd (fun s => AddrMode.addr (.base 2 (.d8 0x8)) s (0x110bcd + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110bcd 3 (.base 2 (.d8 0x8))) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 101) (.out 0x110bd1 (movR64R64Effect 0x110bd1 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 3] []) (.reg (.gpr 15))) #v[99]
    (.letOp (n := 102) (.exec 0x110bd1 (fun s => s.RIP = 0x110bd1) (movR64R64Effect 0x110bd1 15 3) (Reg.operands [.gpr 3] [])) #v[99]
    (.letOp (n := 103) (.out 0x110bd4 (subR64R64Effect 0x110bd4 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[101, 65]
    (.letOp (n := 104) (.exec 0x110bd4 (fun s => s.RIP = 0x110bd4) (subR64R64Effect 0x110bd4 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[101, 65]
    (.letOp (n := 105) (.out 0x110bd7 (sarR64Effect 0x110bd7 4 8 63) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[97]
    (.letOp (n := 106) (.exec 0x110bd7 (fun s => s.RIP = 0x110bd7) (sarR64Effect 0x110bd7 4 8 63) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[97]
    (.letOp (n := 107) (.out 0x110bdb (addR64R64Effect 0x110bdb 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[105, 103]
    (.letOp (n := 108) (.exec 0x110bdb (fun s => s.RIP = 0x110bdb) (addR64R64Effect 0x110bdb 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[105, 103]
    (.letOp (n := 109) (.out 0x110bde (notR64Effect 0x110bde 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3] []) (.reg (.gpr 3))) #v[99]
    (.letOp (n := 110) (.exec 0x110bde (fun s => s.RIP = 0x110bde) (notR64Effect 0x110bde 3) (Reg.operands [.gpr 3] [])) #v[99]
    (.letOp (n := 111) (.out 0x110be1 (movR64R64Effect 0x110be1 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[65]
    (.letOp (n := 112) (.exec 0x110be1 (fun s => s.RIP = 0x110be1) (movR64R64Effect 0x110be1 15 0) (Reg.operands [.gpr 0] [])) #v[65]
    (.letOp (n := 113) (.out 0x110be4 (andR64R64Effect 0x110be4 15 3) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 3] []) (.reg (.gpr 15))) #v[111, 109]
    (.letOp (n := 114) (.exec 0x110be4 (fun s => s.RIP = 0x110be4) (andR64R64Effect 0x110be4 15 3) (Reg.operands [.gpr 15, .gpr 3] [])) #v[111, 109]
    (.letOp (n := 115) (.out 0x110be7 (orR64R64Effect 0x110be7 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[109, 65]
    (.letOp (n := 116) (.exec 0x110be7 (fun s => s.RIP = 0x110be7) (orR64R64Effect 0x110be7 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[109, 65]
    (.letOp (n := 117) (.out 0x110bea (andR64R64Effect 0x110bea 3 8) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 8] []) (.reg (.gpr 3))) #v[115, 107]
    (.letOp (n := 118) (.exec 0x110bea (fun s => s.RIP = 0x110bea) (andR64R64Effect 0x110bea 3 8) (Reg.operands [.gpr 3, .gpr 8] [])) #v[115, 107]
    (.letOp (n := 119) (.out 0x110bed (orR64R64Effect 0x110bed 3 15) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 15] []) (.reg (.gpr 3))) #v[117, 113]
    (.letOp (n := 120) (.exec 0x110bed (fun s => s.RIP = 0x110bed) (orR64R64Effect 0x110bed 3 15) (Reg.operands [.gpr 3, .gpr 15] [])) #v[117, 113]
    (.letOp (n := 121) (.out 0x110bf0 (shrR64Effect 0x110bf0 4 3 63) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[119]
    (.letOp (n := 122) (.exec 0x110bf0 (fun s => s.RIP = 0x110bf0) (shrR64Effect 0x110bf0 4 3 63) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[119]
    (.letOp (n := 123) (.exec 0x110bf4 (StorePre 0x110bf4 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bf4 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bf4 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[121, 61]
    (.letOp (n := 124) (.out 0x110bf9 (xorR32R32Effect 0x110bf9 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[121, 121]
    (.letOp (n := 125) (.exec 0x110bf9 (fun s => s.RIP = 0x110bf9) (xorR32R32Effect 0x110bf9 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[121, 121]
    (.letOp (n := 126) (.out 0x110bfb (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 4] []) (.reg (.gpr 3))) #v[124, 61]
    (.letOp (n := 127) (.exec 0x110bfb (LoadPre 0x110bfb (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bfb + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x110bfb 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 3, .gpr 4] [])) #v[124, 61]
    (.letOp (n := 128) (.out 0x110c00 (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[2]
    (.letOp (n := 129) (.exec 0x110c00 (LoadPre 0x110c00 (fun s => AddrMode.addr (.base 2 (.d8 0x10)) s (0x110c00 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110c00 15 (.base 2 (.d8 0x10))) (Reg.operands [.gpr 2] [])) #v[2]
    (b_l110b80_2))))))))))))))))))))))))))))))))))))))

def bytes_l110b80_1 : List UInt8 :=
  [0x4C, 0x8D, 0x74, 0x24, 0x08, 0x31, 0xF6, 0x45, 0x31, 0xC0, 0x4C, 0x2B, 0x44, 0x24, 0x08, 0x48,
    0x8B, 0x5A, 0x08, 0x49, 0x89, 0xDF, 0x49, 0x29, 0xC7, 0x49, 0xC1, 0xF8, 0x3F, 0x4D, 0x01, 0xF8,
    0x48, 0xF7, 0xD3, 0x49, 0x89, 0xC7, 0x49, 0x21, 0xDF, 0x48, 0x09, 0xC3, 0x4C, 0x21, 0xC3, 0x4C,
    0x09, 0xFB, 0x48, 0xC1, 0xEB, 0x3F, 0x48, 0x89, 0x5C, 0x24, 0x08, 0x31, 0xDB, 0x48, 0x2B, 0x5C,
    0x24, 0x08, 0x4C, 0x8B, 0x7A, 0x10] ++ bytes_l110b80_2

theorem code_l110b80_1 : ∀ x ∈ codeRange 0x110bbe bytes_l110b80_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10bbe 70 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_2

@[cfg_block] def b_l110b80 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x110b80 (pushR64Effect 0x110b80 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[4, 15]
    (.letOp (n := 54) (.exec 0x110b80 (PushPre 0x110b80 2) (pushR64Effect 0x110b80 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[4, 15]
    (.letOp (n := 55) (.out 0x110b82 (pushR64Effect 0x110b82 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[53, 14]
    (.letOp (n := 56) (.exec 0x110b82 (PushPre 0x110b82 2) (pushR64Effect 0x110b82 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[53, 14]
    (.letOp (n := 57) (.out 0x110b84 (pushR64Effect 0x110b84 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[55, 12]
    (.letOp (n := 58) (.exec 0x110b84 (PushPre 0x110b84 2) (pushR64Effect 0x110b84 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[55, 12]
    (.letOp (n := 59) (.out 0x110b86 (pushR64Effect 0x110b86 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[57, 3]
    (.letOp (n := 60) (.exec 0x110b86 (PushPre 0x110b86 1) (pushR64Effect 0x110b86 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[57, 3]
    (.letOp (n := 61) (.out 0x110b87 (subR64Imm8Effect 0x110b87 4 0x10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[59]
    (.letOp (n := 62) (.exec 0x110b87 (fun s => s.RIP = 0x110b87) (subR64Imm8Effect 0x110b87 4 0x10) (Reg.operands [.gpr 4] [])) #v[59]
    (.letOp (n := 63) (.out 0x110b8b (movR64M64Effect 0x110b8b 10 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 6] []) (.reg (.gpr 10))) #v[6]
    (.letOp (n := 64) (.exec 0x110b8b (LoadPre 0x110b8b (fun s => AddrMode.addr (.base 6 .none) s (0x110b8b + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b8b 10 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 65) (.out 0x110b8e (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 66) (.exec 0x110b8e (LoadPre 0x110b8e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x110b8e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b8e 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 67) (.out 0x110b92 (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 68) (.exec 0x110b92 (LoadPre 0x110b92 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x110b92 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b92 11 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x110b96 (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 70) (.exec 0x110b96 (LoadPre 0x110b96 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x110b96 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x110b96 9 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x110b9a (movR64M64Effect 0x110b9a 6 (.base 2 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[2]
    (.letOp (n := 72) (.exec 0x110b9a (LoadPre 0x110b9a (fun s => AddrMode.addr (.base 2 .none) s (0x110b9a + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x110b9a 6 (.base 2 .none)) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 73) (.out 0x110b9d (movR64R64Effect 0x110b9d 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[71]
    (.letOp (n := 74) (.exec 0x110b9d (fun s => s.RIP = 0x110b9d) (movR64R64Effect 0x110b9d 1 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 75) (.out 0x110ba0 (subR64R64Effect 0x110ba0 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[73, 63]
    (.letOp (n := 76) (.exec 0x110ba0 (fun s => s.RIP = 0x110ba0) (subR64R64Effect 0x110ba0 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[73, 63]
    (.letOp (n := 77) (.out 0x110ba3 (notR64Effect 0x110ba3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 78) (.exec 0x110ba3 (fun s => s.RIP = 0x110ba3) (notR64Effect 0x110ba3 6) (Reg.operands [.gpr 6] [])) #v[71]
    (.letOp (n := 79) (.out 0x110ba6 (movR64R64Effect 0x110ba6 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 10] []) (.reg (.gpr 8))) #v[63]
    (.letOp (n := 80) (.exec 0x110ba6 (fun s => s.RIP = 0x110ba6) (movR64R64Effect 0x110ba6 8 10) (Reg.operands [.gpr 10] [])) #v[63]
    (.letOp (n := 81) (.out 0x110ba9 (andR64R64Effect 0x110ba9 8 6) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6] []) (.reg (.gpr 8))) #v[79, 77]
    (.letOp (n := 82) (.exec 0x110ba9 (fun s => s.RIP = 0x110ba9) (andR64R64Effect 0x110ba9 8 6) (Reg.operands [.gpr 8, .gpr 6] [])) #v[79, 77]
    (.letOp (n := 83) (.out 0x110bac (orR64R64Effect 0x110bac 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[77, 63]
    (.letOp (n := 84) (.exec 0x110bac (fun s => s.RIP = 0x110bac) (orR64R64Effect 0x110bac 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[77, 63]
    (.letOp (n := 85) (.out 0x110baf (andR64R64Effect 0x110baf 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[83, 75]
    (.letOp (n := 86) (.exec 0x110baf (fun s => s.RIP = 0x110baf) (andR64R64Effect 0x110baf 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[83, 75]
    (.letOp (n := 87) (.out 0x110bb2 (orR64R64Effect 0x110bb2 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[85, 81]
    (.letOp (n := 88) (.exec 0x110bb2 (fun s => s.RIP = 0x110bb2) (orR64R64Effect 0x110bb2 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[85, 81]
    (.letOp (n := 89) (.out 0x110bb5 (shrR64Effect 0x110bb5 4 6 63) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[87]
    (.letOp (n := 90) (.exec 0x110bb5 (fun s => s.RIP = 0x110bb5) (shrR64Effect 0x110bb5 4 6 63) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[87]
    (.letOp (n := 91) (.exec 0x110bb9 (StorePre 0x110bb9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x110bb9 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x110bb9 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[89, 61]
    (b_l110b80_1)))))))))))))))))))))))))))))))))))))))

def bytes_l110b80 : List UInt8 :=
  [0x41, 0x57, 0x41, 0x56, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x10, 0x4C, 0x8B, 0x16, 0x48, 0x8B,
    0x46, 0x08, 0x4C, 0x8B, 0x5E, 0x10, 0x4C, 0x8B, 0x4E, 0x18, 0x48, 0x8B, 0x32, 0x48, 0x89, 0xF1,
    0x4C, 0x29, 0xD1, 0x48, 0xF7, 0xD6, 0x4D, 0x89, 0xD0, 0x49, 0x21, 0xF0, 0x4C, 0x09, 0xD6, 0x48,
    0x21, 0xCE, 0x4C, 0x09, 0xC6, 0x48, 0xC1, 0xEE, 0x3F, 0x48, 0x89, 0x74, 0x24, 0x08] ++ bytes_l110b80_1

theorem code_l110b80 : ∀ x ∈ codeRange 0x110b80 bytes_l110b80, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x10b80 62 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l110b80_1

@[cfg_block] def b_l1145f0_9 : Block Op Label signature Reg.count 446 :=
  .letOp (n := 446) (.out 0x114888 (shldR64R64Effect 0x114888 5 2 1 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[442, 439]
    (.letOp (n := 447) (.exec 0x114888 (fun s => s.RIP = 0x114888) (shldR64R64Effect 0x114888 5 2 1 12) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[442, 439]
    (.letOp (n := 448) (.out 0x11488d (movR64Imm64Effect 0x11488d 1 0xffffffffffff) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 449) (.exec 0x11488d (fun s => s.RIP = 0x11488d) (movR64Imm64Effect 0x11488d 1 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 450) (.out 0x114897 (andR64R64Effect 0x114897 1 9) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 9] []) (.reg (.gpr 1))) #v[448, 190]
    (.letOp (n := 451) (.exec 0x114897 (fun s => s.RIP = 0x114897) (andR64R64Effect 0x114897 1 9) (Reg.operands [.gpr 1, .gpr 9] [])) #v[448, 190]
    (.letOp (n := 452) (.out 0x11489a (addR64R64Effect 0x11489a 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[450, 446]
    (.letOp (n := 453) (.exec 0x11489a (fun s => s.RIP = 0x11489a) (addR64R64Effect 0x11489a 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[450, 446]
    (.letOp (n := 454) (.out 0x11489d (movR64M64Effect 0x11489d 2 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 455) (.exec 0x11489d (LoadPre 0x11489d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11489d + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11489d 2 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 456) (.exec 0x1148a2 (StorePre 0x1148a2 3 (fun s => AddrMode.addr (.base 7 .none) s (0x1148a2 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x1148a2 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[454, 7]
    (.letOp (n := 457) (.exec 0x1148a5 (StorePre 0x1148a5 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x1148a5 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148a5 15 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 7] [])) #v[346, 7]
    (.letOp (n := 458) (.exec 0x1148a9 (StorePre 0x1148a9 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x1148a9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148a9 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[423, 7]
    (.letOp (n := 459) (.exec 0x1148ad (StorePre 0x1148ad 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x1148ad + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148ad 14 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 14, .gpr 7] [])) #v[444, 7]
    (.letOp (n := 460) (.exec 0x1148b1 (StorePre 0x1148b1 4 (fun s => AddrMode.addr (.base 7 (.d8 0x20)) s (0x1148b1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x1148b1 1 (.base 7 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[452, 7]
    (.letOp (n := 461) (.out 0x1148b5 (addR64Imm8Effect 0x1148b5 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 462) (.exec 0x1148b5 (fun s => s.RIP = 0x1148b5) (addR64Imm8Effect 0x1148b5 4 0x38) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 463) (.out 0x1148b9 (popR64Effect 0x1148b9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[461]
    (.letOp (n := 464) (.out 0x1148b9 (popR64Effect 0x1148b9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[461]
    (.letOp (n := 465) (.exec 0x1148b9 (PopPre 0x1148b9) (popR64Effect 0x1148b9 1 3) (Reg.operands [.gpr 4] [])) #v[461]
    (.letOp (n := 466) (.out 0x1148ba (popR64Effect 0x1148ba 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[464]
    (.letOp (n := 467) (.out 0x1148ba (popR64Effect 0x1148ba 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[464]
    (.letOp (n := 468) (.exec 0x1148ba (PopPre 0x1148ba) (popR64Effect 0x1148ba 2 12) (Reg.operands [.gpr 4] [])) #v[464]
    (.letOp (n := 469) (.out 0x1148bc (popR64Effect 0x1148bc 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[467]
    (.letOp (n := 470) (.out 0x1148bc (popR64Effect 0x1148bc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[467]
    (.letOp (n := 471) (.exec 0x1148bc (PopPre 0x1148bc) (popR64Effect 0x1148bc 2 13) (Reg.operands [.gpr 4] [])) #v[467]
    (.letOp (n := 472) (.out 0x1148be (popR64Effect 0x1148be 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[470]
    (.letOp (n := 473) (.out 0x1148be (popR64Effect 0x1148be 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[470]
    (.letOp (n := 474) (.exec 0x1148be (PopPre 0x1148be) (popR64Effect 0x1148be 2 14) (Reg.operands [.gpr 4] [])) #v[470]
    (.letOp (n := 475) (.out 0x1148c0 (popR64Effect 0x1148c0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[473]
    (.letOp (n := 476) (.out 0x1148c0 (popR64Effect 0x1148c0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[473]
    (.letOp (n := 477) (.exec 0x1148c0 (PopPre 0x1148c0) (popR64Effect 0x1148c0 2 15) (Reg.operands [.gpr 4] [])) #v[473]
    (.letOp (n := 478) (.out 0x1148c2 (popR64Effect 0x1148c2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[476]
    (.letOp (n := 479) (.out 0x1148c2 (popR64Effect 0x1148c2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[476]
    (.letOp (n := 480) (.exec 0x1148c2 (PopPre 0x1148c2) (popR64Effect 0x1148c2 1 5) (Reg.operands [.gpr 4] [])) #v[476]
    (.letOp (n := 481) (.out 0x1148c3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[479]
    (.letOp (n := 482) (.out 0x1148c3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[479]
    (.letOp (n := 483) (.exec 0x1148c3 (RetPre 0x1148c3) (retEffect) (Reg.operands [.gpr 4] [])) #v[479]
    (.terminate (.ret (RegMap.args [(0, 437), (1, 452), (2, 454), (3, 463), (4, 482), (5, 478), (6, 423), (7, 7), (8, 421), (9, 190), (10, 415), (11, 369), (12, 466), (13, 469), (14, 472), (15, 475), (22, 22), (39, 39), (50, 50), (51, 51)] 484) (some ⟨481, by decide⟩))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_9 : List UInt8 :=
  [0x48, 0x0F, 0xA4, 0xCA, 0x0C, 0x48, 0xB9, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C,
    0x21, 0xC9, 0x48, 0x01, 0xD1, 0x48, 0x8B, 0x54, 0x24, 0x28, 0x48, 0x89, 0x17, 0x4C, 0x89, 0x7F,
    0x08, 0x48, 0x89, 0x77, 0x10, 0x4C, 0x89, 0x77, 0x18, 0x48, 0x89, 0x4F, 0x20, 0x48, 0x83, 0xC4,
    0x38, 0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l1145f0_9 : ∀ x ∈ codeRange 0x114888 bytes_l1145f0_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14888 60 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1145f0_8 : Block Op Label signature Reg.count 400 :=
  .letOp (n := 400) (.out 0x114833 (addR64R64Effect 0x114833 6 13) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 13] []) (.reg (.gpr 6))) #v[394, 354]
    (.letOp (n := 401) (.out 0x114833 (addR64R64Effect 0x114833 6 13) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 13] []) (.flag .CF)) #v[394, 354]
    (.letOp (n := 402) (.exec 0x114833 (fun s => s.RIP = 0x114833) (addR64R64Effect 0x114833 6 13) (Reg.operands [.gpr 6, .gpr 13] [])) #v[394, 354]
    (.letOp (n := 403) (.out 0x114836 (atFlags StatusFlags.CF (adcR64M64Effect 0x114836 8 (.sib 4 none 0 (.d8 0x10)))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF]) (.reg (.gpr 8))) #v[398, 65, 401]
    (.letOp (n := 404) (.exec 0x114836 (LoadPre 0x114836 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114836 + BitVec.ofNat 64 5)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x114836 8 (.sib 4 none 0 (.d8 0x10)))) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 4] [.CF])) #v[398, 65, 401]
    (.letOp (n := 405) (.out 0x11483b (addR64R64Effect 0x11483b 6 3) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 3] []) (.reg (.gpr 6))) #v[400, 381]
    (.letOp (n := 406) (.out 0x11483b (addR64R64Effect 0x11483b 6 3) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 3] []) (.flag .CF)) #v[400, 381]
    (.letOp (n := 407) (.exec 0x11483b (fun s => s.RIP = 0x11483b) (addR64R64Effect 0x11483b 6 3) (Reg.operands [.gpr 6, .gpr 3] [])) #v[400, 381]
    (.letOp (n := 408) (.out 0x11483e (atFlags StatusFlags.CF (adcR64R64Effect 0x11483e 8 12)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[403, 383, 406]
    (.letOp (n := 409) (.exec 0x11483e (fun s => s.RIP = 0x11483e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11483e 8 12)) (Reg.operands [.gpr 8, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[403, 383, 406]
    (.letOp (n := 410) (.out 0x114841 (addR64R64Effect 0x114841 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[405, 344]
    (.letOp (n := 411) (.out 0x114841 (addR64R64Effect 0x114841 6 5) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 5] []) (.flag .CF)) #v[405, 344]
    (.letOp (n := 412) (.exec 0x114841 (fun s => s.RIP = 0x114841) (addR64R64Effect 0x114841 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[405, 344]
    (.letOp (n := 413) (.out 0x114844 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114844 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[408, 411]
    (.letOp (n := 414) (.exec 0x114844 (fun s => s.RIP = 0x114844) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114844 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[408, 411]
    (.letOp (n := 415) (.out 0x114848 (shldR64R64Effect 0x114848 5 10 11 12) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[372, 369]
    (.letOp (n := 416) (.exec 0x114848 (fun s => s.RIP = 0x114848) (shldR64R64Effect 0x114848 5 10 11 12) (Reg.operands [.gpr 10, .gpr 11, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[372, 369]
    (.letOp (n := 417) (.out 0x11484d (movR64Imm64Effect 0x11484d 1 0xffffffffffffe) (EffectPart.reads (.reg (.gpr 1)) [] []) (.reg (.gpr 1))) #v[]
    (.letOp (n := 418) (.exec 0x11484d (fun s => s.RIP = 0x11484d) (movR64Imm64Effect 0x11484d 1 0xffffffffffffe) (Reg.operands [] [])) #v[]
    (.letOp (n := 419) (.out 0x114857 (andR64M64Effect 0x114857 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[417, 65]
    (.letOp (n := 420) (.exec 0x114857 (LoadPre 0x114857 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114857 + BitVec.ofNat 64 5)) 8) (andR64M64Effect 0x114857 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[417, 65]
    (.letOp (n := 421) (.out 0x11485c (shldR64R64Effect 0x11485c 5 8 6 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[413, 410]
    (.letOp (n := 422) (.exec 0x11485c (fun s => s.RIP = 0x11485c) (shldR64R64Effect 0x11485c 5 8 6 12) (Reg.operands [.gpr 8, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[413, 410]
    (.letOp (n := 423) (.out 0x114861 (andR64R64Effect 0x114861 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[410, 286]
    (.letOp (n := 424) (.exec 0x114861 (fun s => s.RIP = 0x114861) (andR64R64Effect 0x114861 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[410, 286]
    (.letOp (n := 425) (.out 0x114864 (movR64R64Effect 0x114864 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10] []) (.reg (.gpr 0))) #v[415]
    (.letOp (n := 426) (.exec 0x114864 (fun s => s.RIP = 0x114864) (movR64R64Effect 0x114864 0 10) (Reg.operands [.gpr 10] [])) #v[415]
    (.letOp (n := 427) (.out 0x114867 (movR64Imm64Effect 0x114867 2 0x1000003d10) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 428) (.exec 0x114867 (fun s => s.RIP = 0x114867) (movR64Imm64Effect 0x114867 2 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 429) (.out 0x114871 (mulR64Effect 0x114871 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[427, 425]
    (.letOp (n := 430) (.out 0x114871 (mulR64Effect 0x114871 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[427, 425]
    (.letOp (n := 431) (.exec 0x114871 (fun s => s.RIP = 0x114871) (mulR64Effect 0x114871 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[427, 425]
    (.letOp (n := 432) (.out 0x114874 (addR64R64Effect 0x114874 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 0] []) (.reg (.gpr 1))) #v[419, 429]
    (.letOp (n := 433) (.out 0x114874 (addR64R64Effect 0x114874 1 0) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 0] []) (.flag .CF)) #v[419, 429]
    (.letOp (n := 434) (.exec 0x114874 (fun s => s.RIP = 0x114874) (addR64R64Effect 0x114874 1 0) (Reg.operands [.gpr 1, .gpr 0] [])) #v[419, 429]
    (.letOp (n := 435) (.out 0x114877 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114877 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[430, 433]
    (.letOp (n := 436) (.exec 0x114877 (fun s => s.RIP = 0x114877) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114877 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[430, 433]
    (.letOp (n := 437) (.out 0x11487b (movR64R64Effect 0x11487b 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 438) (.exec 0x11487b (fun s => s.RIP = 0x11487b) (movR64R64Effect 0x11487b 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 439) (.out 0x11487e (addR64R64Effect 0x11487e 1 8) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 8] []) (.reg (.gpr 1))) #v[432, 421]
    (.letOp (n := 440) (.out 0x11487e (addR64R64Effect 0x11487e 1 8) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 8] []) (.flag .CF)) #v[432, 421]
    (.letOp (n := 441) (.exec 0x11487e (fun s => s.RIP = 0x11487e) (addR64R64Effect 0x11487e 1 8) (Reg.operands [.gpr 1, .gpr 8] [])) #v[432, 421]
    (.letOp (n := 442) (.out 0x114881 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114881 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[435, 440]
    (.letOp (n := 443) (.exec 0x114881 (fun s => s.RIP = 0x114881) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114881 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[435, 440]
    (.letOp (n := 444) (.out 0x114885 (andR64R64Effect 0x114885 14 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 1] []) (.reg (.gpr 14))) #v[286, 439]
    (.letOp (n := 445) (.exec 0x114885 (fun s => s.RIP = 0x114885) (andR64R64Effect 0x114885 14 1) (Reg.operands [.gpr 14, .gpr 1] [])) #v[286, 439]
    (b_l1145f0_9))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_8 : List UInt8 :=
  [0x4C, 0x01, 0xEE, 0x4C, 0x13, 0x44, 0x24, 0x10, 0x48, 0x01, 0xDE, 0x4D, 0x11, 0xE0, 0x48, 0x01,
    0xEE, 0x49, 0x83, 0xD0, 0x00, 0x4D, 0x0F, 0xA4, 0xDA, 0x0C, 0x48, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x23, 0x4C, 0x24, 0x30, 0x49, 0x0F, 0xA4, 0xF0, 0x0C, 0x4C, 0x21,
    0xF6, 0x4C, 0x89, 0xD0, 0x48, 0xBA, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48, 0xF7,
    0xE2, 0x48, 0x01, 0xC1, 0x48, 0x83, 0xD2, 0x00, 0x48, 0x89, 0xF8, 0x4C, 0x01, 0xC1, 0x48, 0x83,
    0xD2, 0x00, 0x49, 0x21, 0xCE] ++ bytes_l1145f0_9

theorem code_l1145f0_8 : ∀ x ∈ codeRange 0x114833 bytes_l1145f0_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14833 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_9

@[cfg_block] def b_l1145f0_7 : Block Op Label signature Reg.count 356 :=
  .letOp (n := 356) (.out 0x1147ee (movR64M64Effect 0x1147ee 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 357) (.exec 0x1147ee (LoadPre 0x1147ee (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1147ee + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1147ee 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 358) (.out 0x1147f2 (mulR64Effect 0x1147f2 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[302, 356]
    (.letOp (n := 359) (.out 0x1147f2 (mulR64Effect 0x1147f2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[302, 356]
    (.letOp (n := 360) (.exec 0x1147f2 (fun s => s.RIP = 0x1147f2) (mulR64Effect 0x1147f2 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[302, 356]
    (.letOp (n := 361) (.out 0x1147f5 (movR64R64Effect 0x1147f5 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[359]
    (.letOp (n := 362) (.exec 0x1147f5 (fun s => s.RIP = 0x1147f5) (movR64R64Effect 0x1147f5 10 2) (Reg.operands [.gpr 2] [])) #v[359]
    (.letOp (n := 363) (.out 0x1147f8 (movR64R64Effect 0x1147f8 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 0] []) (.reg (.gpr 11))) #v[358]
    (.letOp (n := 364) (.exec 0x1147f8 (fun s => s.RIP = 0x1147f8) (movR64R64Effect 0x1147f8 11 0) (Reg.operands [.gpr 0] [])) #v[358]
    (.letOp (n := 365) (.out 0x1147fb (shldR64R64Effect 0x1147fb 5 10 0 1) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[361, 358]
    (.letOp (n := 366) (.exec 0x1147fb (fun s => s.RIP = 0x1147fb) (shldR64R64Effect 0x1147fb 5 10 0 1) (Reg.operands [.gpr 10, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[361, 358]
    (.letOp (n := 367) (.out 0x114800 (addR64R64Effect 0x114800 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[363, 358]
    (.letOp (n := 368) (.exec 0x114800 (fun s => s.RIP = 0x114800) (addR64R64Effect 0x114800 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[363, 358]
    (.letOp (n := 369) (.out 0x114803 (addR64R64Effect 0x114803 11 8) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 8] []) (.reg (.gpr 11))) #v[367, 321]
    (.letOp (n := 370) (.out 0x114803 (addR64R64Effect 0x114803 11 8) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 8] []) (.flag .CF)) #v[367, 321]
    (.letOp (n := 371) (.exec 0x114803 (fun s => s.RIP = 0x114803) (addR64R64Effect 0x114803 11 8) (Reg.operands [.gpr 11, .gpr 8] [])) #v[367, 321]
    (.letOp (n := 372) (.out 0x114806 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114806 10 0x0)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[365, 370]
    (.letOp (n := 373) (.exec 0x114806 (fun s => s.RIP = 0x114806) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114806 10 0x0)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[365, 370]
    (.letOp (n := 374) (.out 0x11480a (movR64R64Effect 0x11480a 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[369]
    (.letOp (n := 375) (.exec 0x11480a (fun s => s.RIP = 0x11480a) (movR64R64Effect 0x11480a 0 11) (Reg.operands [.gpr 11] [])) #v[369]
    (.letOp (n := 376) (.out 0x11480d (andR64R64Effect 0x11480d 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[374, 286]
    (.letOp (n := 377) (.exec 0x11480d (fun s => s.RIP = 0x11480d) (andR64R64Effect 0x11480d 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[374, 286]
    (.letOp (n := 378) (.out 0x114810 (mulR64Effect 0x114810 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[325, 376]
    (.letOp (n := 379) (.out 0x114810 (mulR64Effect 0x114810 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[325, 376]
    (.letOp (n := 380) (.exec 0x114810 (fun s => s.RIP = 0x114810) (mulR64Effect 0x114810 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[325, 376]
    (.letOp (n := 381) (.out 0x114813 (movR64R64Effect 0x114813 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[378]
    (.letOp (n := 382) (.exec 0x114813 (fun s => s.RIP = 0x114813) (movR64R64Effect 0x114813 3 0) (Reg.operands [.gpr 0] [])) #v[378]
    (.letOp (n := 383) (.out 0x114816 (movR64R64Effect 0x114816 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[379]
    (.letOp (n := 384) (.exec 0x114816 (fun s => s.RIP = 0x114816) (movR64R64Effect 0x114816 12 2) (Reg.operands [.gpr 2] [])) #v[379]
    (.letOp (n := 385) (.out 0x114819 (movR64M64Effect 0x114819 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 386) (.exec 0x114819 (LoadPre 0x114819 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114819 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114819 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 387) (.out 0x11481e (imulR64R64Effect 0x11481e 4 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2] []) (.reg (.gpr 1))) #v[271, 385]
    (.letOp (n := 388) (.exec 0x11481e (fun s => s.RIP = 0x11481e) (imulR64R64Effect 0x11481e 4 1 2) (Reg.operands [.gpr 1, .gpr 2] [])) #v[271, 385]
    (.letOp (n := 389) (.out 0x114822 (movR64M64Effect 0x114822 0 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 390) (.exec 0x114822 (LoadPre 0x114822 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114822 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114822 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 391) (.out 0x114827 (mulR64Effect 0x114827 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[385, 389]
    (.letOp (n := 392) (.out 0x114827 (mulR64Effect 0x114827 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[385, 389]
    (.letOp (n := 393) (.exec 0x114827 (fun s => s.RIP = 0x114827) (mulR64Effect 0x114827 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[385, 389]
    (.letOp (n := 394) (.out 0x11482a (movR64R64Effect 0x11482a 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[391]
    (.letOp (n := 395) (.exec 0x11482a (fun s => s.RIP = 0x11482a) (movR64R64Effect 0x11482a 6 0) (Reg.operands [.gpr 0] [])) #v[391]
    (.letOp (n := 396) (.out 0x11482d (movR64R64Effect 0x11482d 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[392]
    (.letOp (n := 397) (.exec 0x11482d (fun s => s.RIP = 0x11482d) (movR64R64Effect 0x11482d 8 2) (Reg.operands [.gpr 2] [])) #v[392]
    (.letOp (n := 398) (.out 0x114830 (addR64R64Effect 0x114830 8 1) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 1] []) (.reg (.gpr 8))) #v[396, 387]
    (.letOp (n := 399) (.exec 0x114830 (fun s => s.RIP = 0x114830) (addR64R64Effect 0x114830 8 1) (Reg.operands [.gpr 8, .gpr 1] [])) #v[396, 387]
    (b_l1145f0_8))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_7 : List UInt8 :=
  [0x48, 0x8B, 0x04, 0x24, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC3, 0x49, 0x0F, 0xA4,
    0xC2, 0x01, 0x49, 0x01, 0xC3, 0x4D, 0x01, 0xC3, 0x49, 0x83, 0xD2, 0x00, 0x4C, 0x89, 0xD8, 0x4C,
    0x21, 0xF0, 0x48, 0xF7, 0xE6, 0x48, 0x89, 0xC3, 0x49, 0x89, 0xD4, 0x48, 0x8B, 0x54, 0x24, 0x08,
    0x48, 0x0F, 0xAF, 0xCA, 0x48, 0x8B, 0x44, 0x24, 0x20, 0x48, 0xF7, 0xE2, 0x48, 0x89, 0xC6, 0x49,
    0x89, 0xD0, 0x49, 0x01, 0xC8] ++ bytes_l1145f0_8

theorem code_l1145f0_7 : ∀ x ∈ codeRange 0x1147ee bytes_l1145f0_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x147ee 69 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_8

@[cfg_block] def b_l1145f0_6 : Block Op Label signature Reg.count 311 :=
  .letOp (n := 311) (.out 0x1147a3 (addR64R64Effect 0x1147a3 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[309, 298]
    (.letOp (n := 312) (.out 0x1147a3 (addR64R64Effect 0x1147a3 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[309, 298]
    (.letOp (n := 313) (.exec 0x1147a3 (fun s => s.RIP = 0x1147a3) (addR64R64Effect 0x1147a3 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[309, 298]
    (.letOp (n := 314) (.out 0x1147a6 (atFlags StatusFlags.CF (adcR64R64Effect 0x1147a6 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[296, 307, 312]
    (.letOp (n := 315) (.exec 0x1147a6 (fun s => s.RIP = 0x1147a6) (atFlags StatusFlags.CF (adcR64R64Effect 0x1147a6 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[296, 307, 312]
    (.letOp (n := 316) (.out 0x1147a9 (addR64R64Effect 0x1147a9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[311, 242]
    (.letOp (n := 317) (.out 0x1147a9 (addR64R64Effect 0x1147a9 0 15) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 15] []) (.flag .CF)) #v[311, 242]
    (.letOp (n := 318) (.exec 0x1147a9 (fun s => s.RIP = 0x1147a9) (addR64R64Effect 0x1147a9 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[311, 242]
    (.letOp (n := 319) (.out 0x1147ac (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147ac 8 0x0)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[314, 317]
    (.letOp (n := 320) (.exec 0x1147ac (fun s => s.RIP = 0x1147ac) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147ac 8 0x0)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[314, 317]
    (.letOp (n := 321) (.out 0x1147b0 (shldR64R64Effect 0x1147b0 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[319, 316]
    (.letOp (n := 322) (.exec 0x1147b0 (fun s => s.RIP = 0x1147b0) (shldR64R64Effect 0x1147b0 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[319, 316]
    (.letOp (n := 323) (.out 0x1147b5 (andR64R64Effect 0x1147b5 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[316, 286]
    (.letOp (n := 324) (.exec 0x1147b5 (fun s => s.RIP = 0x1147b5) (andR64R64Effect 0x1147b5 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[316, 286]
    (.letOp (n := 325) (.out 0x1147b8 (movR64Imm64Effect 0x1147b8 6 0x1000003d10) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 326) (.exec 0x1147b8 (fun s => s.RIP = 0x1147b8) (movR64Imm64Effect 0x1147b8 6 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 327) (.out 0x1147c2 (mulR64Effect 0x1147c2 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6, .gpr 0] []) (.reg (.gpr 0))) #v[325, 323]
    (.letOp (n := 328) (.out 0x1147c2 (mulR64Effect 0x1147c2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6, .gpr 0] []) (.reg (.gpr 2))) #v[325, 323]
    (.letOp (n := 329) (.exec 0x1147c2 (fun s => s.RIP = 0x1147c2) (mulR64Effect 0x1147c2 6) (Reg.operands [.gpr 6, .gpr 0] [])) #v[325, 323]
    (.letOp (n := 330) (.out 0x1147c5 (movR64R64Effect 0x1147c5 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 2] []) (.reg (.gpr 5))) #v[328]
    (.letOp (n := 331) (.exec 0x1147c5 (fun s => s.RIP = 0x1147c5) (movR64R64Effect 0x1147c5 5 2) (Reg.operands [.gpr 2] [])) #v[328]
    (.letOp (n := 332) (.out 0x1147c8 (movR64R64Effect 0x1147c8 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[327]
    (.letOp (n := 333) (.exec 0x1147c8 (fun s => s.RIP = 0x1147c8) (movR64R64Effect 0x1147c8 15 0) (Reg.operands [.gpr 0] [])) #v[327]
    (.letOp (n := 334) (.out 0x1147cb (addR64R64Effect 0x1147cb 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[332, 280]
    (.letOp (n := 335) (.out 0x1147cb (addR64R64Effect 0x1147cb 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[332, 280]
    (.letOp (n := 336) (.exec 0x1147cb (fun s => s.RIP = 0x1147cb) (addR64R64Effect 0x1147cb 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[332, 280]
    (.letOp (n := 337) (.out 0x1147ce (atFlags StatusFlags.CF (adcR64R64Effect 0x1147ce 5 12)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[330, 284, 335]
    (.letOp (n := 338) (.exec 0x1147ce (fun s => s.RIP = 0x1147ce) (atFlags StatusFlags.CF (adcR64R64Effect 0x1147ce 5 12)) (Reg.operands [.gpr 5, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[330, 284, 335]
    (.letOp (n := 339) (.out 0x1147d1 (addR64R64Effect 0x1147d1 15 13) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 13] []) (.reg (.gpr 15))) #v[334, 264]
    (.letOp (n := 340) (.out 0x1147d1 (addR64R64Effect 0x1147d1 15 13) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 13] []) (.flag .CF)) #v[334, 264]
    (.letOp (n := 341) (.exec 0x1147d1 (fun s => s.RIP = 0x1147d1) (addR64R64Effect 0x1147d1 15 13) (Reg.operands [.gpr 15, .gpr 13] [])) #v[334, 264]
    (.letOp (n := 342) (.out 0x1147d4 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147d4 5 0x0)) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 5))) #v[337, 340]
    (.letOp (n := 343) (.exec 0x1147d4 (fun s => s.RIP = 0x1147d4) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1147d4 5 0x0)) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[337, 340]
    (.letOp (n := 344) (.out 0x1147d8 (shldR64R64Effect 0x1147d8 5 5 15 12) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[342, 339]
    (.letOp (n := 345) (.exec 0x1147d8 (fun s => s.RIP = 0x1147d8) (shldR64R64Effect 0x1147d8 5 5 15 12) (Reg.operands [.gpr 5, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[342, 339]
    (.letOp (n := 346) (.out 0x1147dd (andR64R64Effect 0x1147dd 15 14) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14] []) (.reg (.gpr 15))) #v[339, 286]
    (.letOp (n := 347) (.exec 0x1147dd (fun s => s.RIP = 0x1147dd) (andR64R64Effect 0x1147dd 15 14) (Reg.operands [.gpr 15, .gpr 14] [])) #v[339, 286]
    (.letOp (n := 348) (.out 0x1147e0 (movR64R64Effect 0x1147e0 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[69]
    (.letOp (n := 349) (.exec 0x1147e0 (fun s => s.RIP = 0x1147e0) (movR64R64Effect 0x1147e0 0 11) (Reg.operands [.gpr 11] [])) #v[69]
    (.letOp (n := 350) (.out 0x1147e3 (mulR64Effect 0x1147e3 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[69, 348]
    (.letOp (n := 351) (.out 0x1147e3 (mulR64Effect 0x1147e3 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[69, 348]
    (.letOp (n := 352) (.exec 0x1147e3 (fun s => s.RIP = 0x1147e3) (mulR64Effect 0x1147e3 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[69, 348]
    (.letOp (n := 353) (.exec 0x1147e6 (StorePre 0x1147e6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x1147e6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1147e6 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[351, 65]
    (.letOp (n := 354) (.out 0x1147eb (movR64R64Effect 0x1147eb 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[350]
    (.letOp (n := 355) (.exec 0x1147eb (fun s => s.RIP = 0x1147eb) (movR64R64Effect 0x1147eb 13 0) (Reg.operands [.gpr 0] [])) #v[350]
    (b_l1145f0_7)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_6 : List UInt8 :=
  [0x48, 0x01, 0xF0, 0x49, 0x11, 0xD0, 0x4C, 0x01, 0xF8, 0x49, 0x83, 0xD0, 0x00, 0x49, 0x0F, 0xA4,
    0xC0, 0x0C, 0x4C, 0x21, 0xF0, 0x48, 0xBE, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x48,
    0xF7, 0xE6, 0x48, 0x89, 0xD5, 0x49, 0x89, 0xC7, 0x4D, 0x01, 0xD7, 0x4C, 0x11, 0xE5, 0x4D, 0x01,
    0xEF, 0x48, 0x83, 0xD5, 0x00, 0x4C, 0x0F, 0xA4, 0xFD, 0x0C, 0x4D, 0x21, 0xF7, 0x4C, 0x89, 0xD8,
    0x49, 0xF7, 0xE3, 0x48, 0x89, 0x54, 0x24, 0x10, 0x49, 0x89, 0xC5] ++ bytes_l1145f0_7

theorem code_l1145f0_6 : ∀ x ∈ codeRange 0x1147a3 bytes_l1145f0_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x147a3 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_7

@[cfg_block] def b_l1145f0_5 : Block Op Label signature Reg.count 270 :=
  .letOp (n := 270) (.exec 0x114755 (StorePre 0x114755 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114755 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114755 0 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[268, 65]
    (.letOp (n := 271) (.out 0x11475a (shrR64Effect 0x11475a 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[67]
    (.letOp (n := 272) (.exec 0x11475a (fun s => s.RIP = 0x11475a) (shrR64Effect 0x11475a 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 273) (.out 0x11475e (movR64R64Effect 0x11475e 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[271]
    (.letOp (n := 274) (.exec 0x11475e (fun s => s.RIP = 0x11475e) (movR64R64Effect 0x11475e 6 1) (Reg.operands [.gpr 1] [])) #v[271]
    (.letOp (n := 275) (.out 0x114761 (imulR64R64Effect 0x114761 4 6 11) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 11] []) (.reg (.gpr 6))) #v[273, 69]
    (.letOp (n := 276) (.exec 0x114761 (fun s => s.RIP = 0x114761) (imulR64R64Effect 0x114761 4 6 11) (Reg.operands [.gpr 6, .gpr 11] [])) #v[273, 69]
    (.letOp (n := 277) (.out 0x114765 (mulR64Effect 0x114765 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[69, 268]
    (.letOp (n := 278) (.out 0x114765 (mulR64Effect 0x114765 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[69, 268]
    (.letOp (n := 279) (.exec 0x114765 (fun s => s.RIP = 0x114765) (mulR64Effect 0x114765 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[69, 268]
    (.letOp (n := 280) (.out 0x114768 (movR64R64Effect 0x114768 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[277]
    (.letOp (n := 281) (.exec 0x114768 (fun s => s.RIP = 0x114768) (movR64R64Effect 0x114768 10 0) (Reg.operands [.gpr 0] [])) #v[277]
    (.letOp (n := 282) (.out 0x11476b (movR64R64Effect 0x11476b 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 2] []) (.reg (.gpr 12))) #v[278]
    (.letOp (n := 283) (.exec 0x11476b (fun s => s.RIP = 0x11476b) (movR64R64Effect 0x11476b 12 2) (Reg.operands [.gpr 2] [])) #v[278]
    (.letOp (n := 284) (.out 0x11476e (addR64R64Effect 0x11476e 12 6) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 6] []) (.reg (.gpr 12))) #v[282, 275]
    (.letOp (n := 285) (.exec 0x11476e (fun s => s.RIP = 0x11476e) (addR64R64Effect 0x11476e 12 6) (Reg.operands [.gpr 12, .gpr 6] [])) #v[282, 275]
    (.letOp (n := 286) (.out 0x114771 (movR64Imm64Effect 0x114771 14 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 287) (.exec 0x114771 (fun s => s.RIP = 0x114771) (movR64Imm64Effect 0x114771 14 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 288) (.out 0x11477b (andR64R64Effect 0x11477b 8 14) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 14] []) (.reg (.gpr 8))) #v[266, 286]
    (.letOp (n := 289) (.exec 0x11477b (fun s => s.RIP = 0x11477b) (andR64R64Effect 0x11477b 8 14) (Reg.operands [.gpr 8, .gpr 14] [])) #v[266, 286]
    (.letOp (n := 290) (.exec 0x11477e (StorePre 0x11477e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11477e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11477e 8 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[288, 65]
    (.letOp (n := 291) (.out 0x114783 (movR64M64Effect 0x114783 0 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[65]
    (.letOp (n := 292) (.exec 0x114783 (LoadPre 0x114783 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x114783 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114783 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 293) (.out 0x114787 (mulR64Effect 0x114787 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[291, 291]
    (.letOp (n := 294) (.out 0x114787 (mulR64Effect 0x114787 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0, .gpr 0] []) (.reg (.gpr 2))) #v[291, 291]
    (.letOp (n := 295) (.exec 0x114787 (fun s => s.RIP = 0x114787) (mulR64Effect 0x114787 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[291, 291]
    (.letOp (n := 296) (.out 0x11478a (movR64R64Effect 0x11478a 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[294]
    (.letOp (n := 297) (.exec 0x11478a (fun s => s.RIP = 0x11478a) (movR64R64Effect 0x11478a 8 2) (Reg.operands [.gpr 2] [])) #v[294]
    (.letOp (n := 298) (.out 0x11478d (movR64R64Effect 0x11478d 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[293]
    (.letOp (n := 299) (.exec 0x11478d (fun s => s.RIP = 0x11478d) (movR64R64Effect 0x11478d 6 0) (Reg.operands [.gpr 0] [])) #v[293]
    (.letOp (n := 300) (.out 0x114790 (movR64R64Effect 0x114790 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[214]
    (.letOp (n := 301) (.exec 0x114790 (fun s => s.RIP = 0x114790) (movR64R64Effect 0x114790 0 3) (Reg.operands [.gpr 3] [])) #v[214]
    (.letOp (n := 302) (.out 0x114793 (movR64M64Effect 0x114793 3 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 303) (.exec 0x114793 (LoadPre 0x114793 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114793 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114793 3 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 304) (.out 0x114798 (mulR64Effect 0x114798 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[302, 300]
    (.letOp (n := 305) (.out 0x114798 (mulR64Effect 0x114798 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[302, 300]
    (.letOp (n := 306) (.exec 0x114798 (fun s => s.RIP = 0x114798) (mulR64Effect 0x114798 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[302, 300]
    (.letOp (n := 307) (.out 0x11479b (shldR64R64Effect 0x11479b 5 2 0 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[305, 304]
    (.letOp (n := 308) (.exec 0x11479b (fun s => s.RIP = 0x11479b) (shldR64R64Effect 0x11479b 5 2 0 1) (Reg.operands [.gpr 2, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[305, 304]
    (.letOp (n := 309) (.out 0x1147a0 (addR64R64Effect 0x1147a0 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[304, 304]
    (.letOp (n := 310) (.exec 0x1147a0 (fun s => s.RIP = 0x1147a0) (addR64R64Effect 0x1147a0 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[304, 304]
    (b_l1145f0_6)))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_5 : List UInt8 :=
  [0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0xC1, 0xE9, 0x3F, 0x48, 0x89, 0xCE, 0x49, 0x0F, 0xAF, 0xF3,
    0x49, 0xF7, 0xE3, 0x49, 0x89, 0xC2, 0x49, 0x89, 0xD4, 0x49, 0x01, 0xF4, 0x49, 0xBE, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x4D, 0x21, 0xF0, 0x4C, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8B,
    0x04, 0x24, 0x48, 0xF7, 0xE0, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xD8, 0x48, 0x8B,
    0x5C, 0x24, 0x18, 0x48, 0xF7, 0xE3, 0x48, 0x0F, 0xA4, 0xC2, 0x01, 0x48, 0x01, 0xC0] ++ bytes_l1145f0_6

theorem code_l1145f0_5 : ∀ x ∈ codeRange 0x114755 bytes_l1145f0_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14755 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_6

@[cfg_block] def b_l1145f0_4 : Block Op Label signature Reg.count 225 :=
  .letOp (n := 225) (.out 0x114702 (mulR64Effect 0x114702 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[69, 223]
    (.letOp (n := 226) (.out 0x114702 (mulR64Effect 0x114702 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[69, 223]
    (.letOp (n := 227) (.exec 0x114702 (fun s => s.RIP = 0x114702) (mulR64Effect 0x114702 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[69, 223]
    (.letOp (n := 228) (.out 0x114705 (addR64R64Effect 0x114705 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[225, 221]
    (.letOp (n := 229) (.out 0x114705 (addR64R64Effect 0x114705 0 6) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 6] []) (.flag .CF)) #v[225, 221]
    (.letOp (n := 230) (.exec 0x114705 (fun s => s.RIP = 0x114705) (addR64R64Effect 0x114705 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[225, 221]
    (.letOp (n := 231) (.out 0x114708 (atFlags StatusFlags.CF (adcR64R64Effect 0x114708 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[219, 226, 229]
    (.letOp (n := 232) (.exec 0x114708 (fun s => s.RIP = 0x114708) (atFlags StatusFlags.CF (adcR64R64Effect 0x114708 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[219, 226, 229]
    (.letOp (n := 233) (.out 0x11470b (shldR64R64Effect 0x11470b 5 15 0 1) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[231, 228]
    (.letOp (n := 234) (.exec 0x11470b (fun s => s.RIP = 0x11470b) (shldR64R64Effect 0x11470b 5 15 0 1) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[231, 228]
    (.letOp (n := 235) (.out 0x114710 (addR64R64Effect 0x114710 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[228, 228]
    (.letOp (n := 236) (.exec 0x114710 (fun s => s.RIP = 0x114710) (addR64R64Effect 0x114710 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[228, 228]
    (.letOp (n := 237) (.out 0x114713 (addR64R64Effect 0x114713 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 14] []) (.reg (.gpr 0))) #v[235, 195]
    (.letOp (n := 238) (.out 0x114713 (addR64R64Effect 0x114713 0 14) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 14] []) (.flag .CF)) #v[235, 195]
    (.letOp (n := 239) (.exec 0x114713 (fun s => s.RIP = 0x114713) (addR64R64Effect 0x114713 0 14) (Reg.operands [.gpr 0, .gpr 14] [])) #v[235, 195]
    (.letOp (n := 240) (.out 0x114716 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114716 15 0x0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[233, 238]
    (.letOp (n := 241) (.exec 0x114716 (fun s => s.RIP = 0x114716) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x114716 15 0x0)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[233, 238]
    (.letOp (n := 242) (.out 0x11471a (shldR64R64Effect 0x11471a 5 15 0 12) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 15))) #v[240, 237]
    (.letOp (n := 243) (.exec 0x11471a (fun s => s.RIP = 0x11471a) (shldR64R64Effect 0x11471a 5 15 0 12) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[240, 237]
    (.letOp (n := 244) (.out 0x11471f (shlR64Effect 0x11471f 4 0 4) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[237]
    (.letOp (n := 245) (.exec 0x11471f (fun s => s.RIP = 0x11471f) (shlR64Effect 0x11471f 4 0 4) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[237]
    (.letOp (n := 246) (.out 0x114723 (movR64Imm64Effect 0x114723 2 0xfffffffffffff0) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 247) (.exec 0x114723 (fun s => s.RIP = 0x114723) (movR64Imm64Effect 0x114723 2 0xfffffffffffff0) (Reg.operands [] [])) #v[]
    (.letOp (n := 248) (.out 0x11472d (andR64R64Effect 0x11472d 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[244, 246]
    (.letOp (n := 249) (.exec 0x11472d (fun s => s.RIP = 0x11472d) (andR64R64Effect 0x11472d 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[244, 246]
    (.letOp (n := 250) (.out 0x114730 (orR64R64Effect 0x114730 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[248, 210]
    (.letOp (n := 251) (.exec 0x114730 (fun s => s.RIP = 0x114730) (orR64R64Effect 0x114730 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[248, 210]
    (.letOp (n := 252) (.out 0x114733 (movR64Imm64Effect 0x114733 2 0x1000003d1) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 253) (.exec 0x114733 (fun s => s.RIP = 0x114733) (movR64Imm64Effect 0x114733 2 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 254) (.out 0x11473d (mulR64Effect 0x11473d 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[252, 250]
    (.letOp (n := 255) (.out 0x11473d (mulR64Effect 0x11473d 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[252, 250]
    (.letOp (n := 256) (.exec 0x11473d (fun s => s.RIP = 0x11473d) (mulR64Effect 0x11473d 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[252, 250]
    (.letOp (n := 257) (.out 0x114740 (movR64R64Effect 0x114740 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[255]
    (.letOp (n := 258) (.exec 0x114740 (fun s => s.RIP = 0x114740) (movR64R64Effect 0x114740 13 2) (Reg.operands [.gpr 2] [])) #v[255]
    (.letOp (n := 259) (.out 0x114743 (addR64R64Effect 0x114743 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 12] []) (.reg (.gpr 0))) #v[254, 206]
    (.letOp (n := 260) (.out 0x114743 (addR64R64Effect 0x114743 0 12) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 12] []) (.flag .CF)) #v[254, 206]
    (.letOp (n := 261) (.exec 0x114743 (fun s => s.RIP = 0x114743) (addR64R64Effect 0x114743 0 12) (Reg.operands [.gpr 0, .gpr 12] [])) #v[254, 206]
    (.letOp (n := 262) (.out 0x114746 (atFlags StatusFlags.CF (adcR64R64Effect 0x114746 13 8)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 13))) #v[257, 208, 260]
    (.letOp (n := 263) (.exec 0x114746 (fun s => s.RIP = 0x114746) (atFlags StatusFlags.CF (adcR64R64Effect 0x114746 13 8)) (Reg.operands [.gpr 13, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[257, 208, 260]
    (.letOp (n := 264) (.out 0x114749 (shldR64R64Effect 0x114749 5 13 0 12) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[262, 259]
    (.letOp (n := 265) (.exec 0x114749 (fun s => s.RIP = 0x114749) (shldR64R64Effect 0x114749 5 13 0 12) (Reg.operands [.gpr 13, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[262, 259]
    (.letOp (n := 266) (.out 0x11474e (movR64R64Effect 0x11474e 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 0] []) (.reg (.gpr 8))) #v[259]
    (.letOp (n := 267) (.exec 0x11474e (fun s => s.RIP = 0x11474e) (movR64R64Effect 0x11474e 8 0) (Reg.operands [.gpr 0] [])) #v[259]
    (.letOp (n := 268) (.out 0x114751 (leaR64Effect 0x114751 0 (.sib 1 (some 1) 0 .none)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 1] []) (.reg (.gpr 0))) #v[67, 67]
    (.letOp (n := 269) (.exec 0x114751 (fun s => s.RIP = 0x114751) (leaR64Effect 0x114751 0 (.sib 1 (some 1) 0 .none)) (Reg.operands [.gpr 1, .gpr 1] [])) #v[67, 67]
    (b_l1145f0_5)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_4 : List UInt8 :=
  [0x49, 0xF7, 0xE3, 0x48, 0x01, 0xF0, 0x49, 0x11, 0xD7, 0x49, 0x0F, 0xA4, 0xC7, 0x01, 0x48, 0x01,
    0xC0, 0x4C, 0x01, 0xF0, 0x49, 0x83, 0xD7, 0x00, 0x49, 0x0F, 0xA4, 0xC7, 0x0C, 0x48, 0xC1, 0xE0,
    0x04, 0x48, 0xBA, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x48, 0x21, 0xD0, 0x4C, 0x09,
    0xD0, 0x48, 0xBA, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0xF7, 0xE2, 0x49, 0x89,
    0xD5, 0x4C, 0x01, 0xE0, 0x4D, 0x11, 0xC5, 0x49, 0x0F, 0xA4, 0xC5, 0x0C, 0x49, 0x89, 0xC0, 0x48,
    0x8D, 0x04, 0x09] ++ bytes_l1145f0_5

theorem code_l1145f0_4 : ∀ x ∈ codeRange 0x114702 bytes_l1145f0_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14702 83 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_5

@[cfg_block] def b_l1145f0_3 : Block Op Label signature Reg.count 180 :=
  .letOp (n := 180) (.out 0x1146bf (addR64R64Effect 0x1146bf 9 12) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 12] []) (.reg (.gpr 9))) #v[178, 141]
    (.letOp (n := 181) (.out 0x1146bf (addR64R64Effect 0x1146bf 9 12) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 12] []) (.flag .CF)) #v[178, 141]
    (.letOp (n := 182) (.exec 0x1146bf (fun s => s.RIP = 0x1146bf) (addR64R64Effect 0x1146bf 9 12) (Reg.operands [.gpr 9, .gpr 12] [])) #v[178, 141]
    (.letOp (n := 183) (.out 0x1146c2 (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c2 14 10)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[176, 139, 181]
    (.letOp (n := 184) (.exec 0x1146c2 (fun s => s.RIP = 0x1146c2) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c2 14 10)) (Reg.operands [.gpr 14, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[176, 139, 181]
    (.letOp (n := 185) (.out 0x1146c5 (addR64R64Effect 0x1146c5 9 6) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 6] []) (.reg (.gpr 9))) #v[180, 150]
    (.letOp (n := 186) (.out 0x1146c5 (addR64R64Effect 0x1146c5 9 6) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 6] []) (.flag .CF)) #v[180, 150]
    (.letOp (n := 187) (.exec 0x1146c5 (fun s => s.RIP = 0x1146c5) (addR64R64Effect 0x1146c5 9 6) (Reg.operands [.gpr 9, .gpr 6] [])) #v[180, 150]
    (.letOp (n := 188) (.out 0x1146c8 (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c8 14 15)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[183, 148, 186]
    (.letOp (n := 189) (.exec 0x1146c8 (fun s => s.RIP = 0x1146c8) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146c8 14 15)) (Reg.operands [.gpr 14, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[183, 148, 186]
    (.letOp (n := 190) (.out 0x1146cb (addR64R64Effect 0x1146cb 9 8) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8] []) (.reg (.gpr 9))) #v[185, 131]
    (.letOp (n := 191) (.out 0x1146cb (addR64R64Effect 0x1146cb 9 8) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 8] []) (.flag .CF)) #v[185, 131]
    (.letOp (n := 192) (.exec 0x1146cb (fun s => s.RIP = 0x1146cb) (addR64R64Effect 0x1146cb 9 8) (Reg.operands [.gpr 9, .gpr 8] [])) #v[185, 131]
    (.letOp (n := 193) (.out 0x1146ce (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1146ce 14 0x0)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[188, 191]
    (.letOp (n := 194) (.exec 0x1146ce (fun s => s.RIP = 0x1146ce) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x1146ce 14 0x0)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[188, 191]
    (.letOp (n := 195) (.out 0x1146d2 (shldR64R64Effect 0x1146d2 5 14 9 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[193, 190]
    (.letOp (n := 196) (.exec 0x1146d2 (fun s => s.RIP = 0x1146d2) (shldR64R64Effect 0x1146d2 5 14 9 12) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[193, 190]
    (.letOp (n := 197) (.out 0x1146d7 (movR64R64Effect 0x1146d7 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[190]
    (.letOp (n := 198) (.exec 0x1146d7 (fun s => s.RIP = 0x1146d7) (movR64R64Effect 0x1146d7 10 9) (Reg.operands [.gpr 9] [])) #v[190]
    (.letOp (n := 199) (.out 0x1146da (shrR64Effect 0x1146da 4 10 48) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[197]
    (.letOp (n := 200) (.exec 0x1146da (fun s => s.RIP = 0x1146da) (shrR64Effect 0x1146da 4 10 48) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[197]
    (.letOp (n := 201) (.out 0x1146de (movR64R64Effect 0x1146de 0 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1] []) (.reg (.gpr 0))) #v[67]
    (.letOp (n := 202) (.exec 0x1146de (fun s => s.RIP = 0x1146de) (movR64R64Effect 0x1146de 0 1) (Reg.operands [.gpr 1] [])) #v[67]
    (.letOp (n := 203) (.out 0x1146e1 (mulR64Effect 0x1146e1 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[67, 201]
    (.letOp (n := 204) (.out 0x1146e1 (mulR64Effect 0x1146e1 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[67, 201]
    (.letOp (n := 205) (.exec 0x1146e1 (fun s => s.RIP = 0x1146e1) (mulR64Effect 0x1146e1 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 201]
    (.letOp (n := 206) (.out 0x1146e4 (movR64R64Effect 0x1146e4 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[203]
    (.letOp (n := 207) (.exec 0x1146e4 (fun s => s.RIP = 0x1146e4) (movR64R64Effect 0x1146e4 12 0) (Reg.operands [.gpr 0] [])) #v[203]
    (.letOp (n := 208) (.out 0x1146e7 (movR64R64Effect 0x1146e7 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[204]
    (.letOp (n := 209) (.exec 0x1146e7 (fun s => s.RIP = 0x1146e7) (movR64R64Effect 0x1146e7 8 2) (Reg.operands [.gpr 2] [])) #v[204]
    (.letOp (n := 210) (.out 0x1146ea (andR32Imm8Effect 0x1146ea 4 10 0xf) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[199]
    (.letOp (n := 211) (.exec 0x1146ea (fun s => s.RIP = 0x1146ea) (andR32Imm8Effect 0x1146ea 4 10 0xf) (Reg.operands [.gpr 10] [])) #v[199]
    (.letOp (n := 212) (.out 0x1146ee (movR64R64Effect 0x1146ee 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[162]
    (.letOp (n := 213) (.exec 0x1146ee (fun s => s.RIP = 0x1146ee) (movR64R64Effect 0x1146ee 0 3) (Reg.operands [.gpr 3] [])) #v[162]
    (.letOp (n := 214) (.out 0x1146f1 (movR64M64Effect 0x1146f1 3 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 215) (.exec 0x1146f1 (LoadPre 0x1146f1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1146f1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x1146f1 3 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 216) (.out 0x1146f6 (mulR64Effect 0x1146f6 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3, .gpr 0] []) (.reg (.gpr 0))) #v[214, 212]
    (.letOp (n := 217) (.out 0x1146f6 (mulR64Effect 0x1146f6 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3, .gpr 0] []) (.reg (.gpr 2))) #v[214, 212]
    (.letOp (n := 218) (.exec 0x1146f6 (fun s => s.RIP = 0x1146f6) (mulR64Effect 0x1146f6 3) (Reg.operands [.gpr 3, .gpr 0] [])) #v[214, 212]
    (.letOp (n := 219) (.out 0x1146f9 (movR64R64Effect 0x1146f9 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[217]
    (.letOp (n := 220) (.exec 0x1146f9 (fun s => s.RIP = 0x1146f9) (movR64R64Effect 0x1146f9 15 2) (Reg.operands [.gpr 2] [])) #v[217]
    (.letOp (n := 221) (.out 0x1146fc (movR64R64Effect 0x1146fc 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[216]
    (.letOp (n := 222) (.exec 0x1146fc (fun s => s.RIP = 0x1146fc) (movR64R64Effect 0x1146fc 6 0) (Reg.operands [.gpr 0] [])) #v[216]
    (.letOp (n := 223) (.out 0x1146ff (movR64R64Effect 0x1146ff 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 224) (.exec 0x1146ff (fun s => s.RIP = 0x1146ff) (movR64R64Effect 0x1146ff 0 5) (Reg.operands [.gpr 5] [])) #v[97]
    (b_l1145f0_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_3 : List UInt8 :=
  [0x4D, 0x01, 0xE1, 0x4D, 0x11, 0xD6, 0x49, 0x01, 0xF1, 0x4D, 0x11, 0xFE, 0x4D, 0x01, 0xC1, 0x49,
    0x83, 0xD6, 0x00, 0x4D, 0x0F, 0xA4, 0xCE, 0x0C, 0x4D, 0x89, 0xCA, 0x49, 0xC1, 0xEA, 0x30, 0x48,
    0x89, 0xC8, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xC4, 0x49, 0x89, 0xD0, 0x41, 0x83, 0xE2, 0x0F, 0x48,
    0x89, 0xD8, 0x48, 0x8B, 0x5C, 0x24, 0x08, 0x48, 0xF7, 0xE3, 0x49, 0x89, 0xD7, 0x48, 0x89, 0xC6,
    0x48, 0x89, 0xE8] ++ bytes_l1145f0_4

theorem code_l1145f0_3 : ∀ x ∈ codeRange 0x1146bf bytes_l1145f0_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x146bf 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_4

@[cfg_block] def b_l1145f0_2 : Block Op Label signature Reg.count 136 :=
  .letOp (n := 136) (.out 0x11467e (mulR64Effect 0x11467e 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15, .gpr 0] []) (.reg (.gpr 0))) #v[71, 134]
    (.letOp (n := 137) (.out 0x11467e (mulR64Effect 0x11467e 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15, .gpr 0] []) (.reg (.gpr 2))) #v[71, 134]
    (.letOp (n := 138) (.exec 0x11467e (fun s => s.RIP = 0x11467e) (mulR64Effect 0x11467e 15) (Reg.operands [.gpr 15, .gpr 0] [])) #v[71, 134]
    (.letOp (n := 139) (.out 0x114681 (movR64R64Effect 0x114681 10 2) (EffectPart.reads (.reg (.gpr 10)) [.gpr 2] []) (.reg (.gpr 10))) #v[137]
    (.letOp (n := 140) (.exec 0x114681 (fun s => s.RIP = 0x114681) (movR64R64Effect 0x114681 10 2) (Reg.operands [.gpr 2] [])) #v[137]
    (.letOp (n := 141) (.out 0x114684 (movR64R64Effect 0x114684 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 0] []) (.reg (.gpr 12))) #v[136]
    (.letOp (n := 142) (.exec 0x114684 (fun s => s.RIP = 0x114684) (movR64R64Effect 0x114684 12 0) (Reg.operands [.gpr 0] [])) #v[136]
    (.letOp (n := 143) (.out 0x114687 (movR64R64Effect 0x114687 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[129]
    (.letOp (n := 144) (.exec 0x114687 (fun s => s.RIP = 0x114687) (movR64R64Effect 0x114687 0 14) (Reg.operands [.gpr 14] [])) #v[129]
    (.letOp (n := 145) (.out 0x11468a (mulR64Effect 0x11468a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[116, 143]
    (.letOp (n := 146) (.out 0x11468a (mulR64Effect 0x11468a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[116, 143]
    (.letOp (n := 147) (.exec 0x11468a (fun s => s.RIP = 0x11468a) (mulR64Effect 0x11468a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[116, 143]
    (.letOp (n := 148) (.out 0x11468d (movR64R64Effect 0x11468d 15 2) (EffectPart.reads (.reg (.gpr 15)) [.gpr 2] []) (.reg (.gpr 15))) #v[146]
    (.letOp (n := 149) (.exec 0x11468d (fun s => s.RIP = 0x11468d) (movR64R64Effect 0x11468d 15 2) (Reg.operands [.gpr 2] [])) #v[146]
    (.letOp (n := 150) (.out 0x114690 (movR64R64Effect 0x114690 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[145]
    (.letOp (n := 151) (.exec 0x114690 (fun s => s.RIP = 0x114690) (movR64R64Effect 0x114690 6 0) (Reg.operands [.gpr 0] [])) #v[145]
    (.letOp (n := 152) (.out 0x114693 (movR64R64Effect 0x114693 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 153) (.exec 0x114693 (fun s => s.RIP = 0x114693) (movR64R64Effect 0x114693 0 5) (Reg.operands [.gpr 5] [])) #v[97]
    (.letOp (n := 154) (.exec 0x114696 (StorePre 0x114696 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114696 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114696 5 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[97, 65]
    (.letOp (n := 155) (.out 0x11469b (mulR64Effect 0x11469b 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[67, 152]
    (.letOp (n := 156) (.out 0x11469b (mulR64Effect 0x11469b 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[67, 152]
    (.letOp (n := 157) (.exec 0x11469b (fun s => s.RIP = 0x11469b) (mulR64Effect 0x11469b 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 152]
    (.letOp (n := 158) (.out 0x11469e (movR64R64Effect 0x11469e 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[156]
    (.letOp (n := 159) (.exec 0x11469e (fun s => s.RIP = 0x11469e) (movR64R64Effect 0x11469e 14 2) (Reg.operands [.gpr 2] [])) #v[156]
    (.letOp (n := 160) (.out 0x1146a1 (movR64R64Effect 0x1146a1 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[155]
    (.letOp (n := 161) (.exec 0x1146a1 (fun s => s.RIP = 0x1146a1) (movR64R64Effect 0x1146a1 13 0) (Reg.operands [.gpr 0] [])) #v[155]
    (.letOp (n := 162) (.out 0x1146a4 (movR64M64Effect 0x1146a4 3 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[65]
    (.letOp (n := 163) (.exec 0x1146a4 (LoadPre 0x1146a4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x1146a4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1146a4 3 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 164) (.out 0x1146a8 (movR64R64Effect 0x1146a8 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[162]
    (.letOp (n := 165) (.exec 0x1146a8 (fun s => s.RIP = 0x1146a8) (movR64R64Effect 0x1146a8 0 3) (Reg.operands [.gpr 3] [])) #v[162]
    (.letOp (n := 166) (.out 0x1146ab (mulR64Effect 0x1146ab 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[69, 164]
    (.letOp (n := 167) (.out 0x1146ab (mulR64Effect 0x1146ab 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[69, 164]
    (.letOp (n := 168) (.exec 0x1146ab (fun s => s.RIP = 0x1146ab) (mulR64Effect 0x1146ab 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[69, 164]
    (.letOp (n := 169) (.out 0x1146ae (movR64R64Effect 0x1146ae 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[166]
    (.letOp (n := 170) (.exec 0x1146ae (fun s => s.RIP = 0x1146ae) (movR64R64Effect 0x1146ae 9 0) (Reg.operands [.gpr 0] [])) #v[166]
    (.letOp (n := 171) (.out 0x1146b1 (addR64R64Effect 0x1146b1 9 13) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 13] []) (.reg (.gpr 9))) #v[169, 160]
    (.letOp (n := 172) (.out 0x1146b1 (addR64R64Effect 0x1146b1 9 13) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 13] []) (.flag .CF)) #v[169, 160]
    (.letOp (n := 173) (.exec 0x1146b1 (fun s => s.RIP = 0x1146b1) (addR64R64Effect 0x1146b1 9 13) (Reg.operands [.gpr 9, .gpr 13] [])) #v[169, 160]
    (.letOp (n := 174) (.out 0x1146b4 (atFlags StatusFlags.CF (adcR64R64Effect 0x1146b4 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[158, 167, 172]
    (.letOp (n := 175) (.exec 0x1146b4 (fun s => s.RIP = 0x1146b4) (atFlags StatusFlags.CF (adcR64R64Effect 0x1146b4 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[158, 167, 172]
    (.letOp (n := 176) (.out 0x1146b7 (shldR64R64Effect 0x1146b7 5 14 9 1) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[174, 171]
    (.letOp (n := 177) (.exec 0x1146b7 (fun s => s.RIP = 0x1146b7) (shldR64R64Effect 0x1146b7 5 14 9 1) (Reg.operands [.gpr 14, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[174, 171]
    (.letOp (n := 178) (.out 0x1146bc (addR64R64Effect 0x1146bc 9 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 9] []) (.reg (.gpr 9))) #v[171, 171]
    (.letOp (n := 179) (.exec 0x1146bc (fun s => s.RIP = 0x1146bc) (addR64R64Effect 0x1146bc 9 9) (Reg.operands [.gpr 9, .gpr 9] [])) #v[171, 171]
    (b_l1145f0_3))))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_2 : List UInt8 :=
  [0x49, 0xF7, 0xE7, 0x49, 0x89, 0xD2, 0x49, 0x89, 0xC4, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE5, 0x49,
    0x89, 0xD7, 0x48, 0x89, 0xC6, 0x48, 0x89, 0xE8, 0x48, 0x89, 0x6C, 0x24, 0x18, 0x48, 0xF7, 0xE1,
    0x49, 0x89, 0xD6, 0x49, 0x89, 0xC5, 0x48, 0x8B, 0x1C, 0x24, 0x48, 0x89, 0xD8, 0x49, 0xF7, 0xE3,
    0x49, 0x89, 0xC1, 0x4D, 0x01, 0xE9, 0x49, 0x11, 0xD6, 0x4D, 0x0F, 0xA4, 0xCE, 0x01, 0x4D, 0x01,
    0xC9] ++ bytes_l1145f0_3

theorem code_l1145f0_2 : ∀ x ∈ codeRange 0x11467e bytes_l1145f0_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1467e 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_3

@[cfg_block] def b_l1145f0_1 : Block Op Label signature Reg.count 95 :=
  .letOp (n := 95) (.out 0x114629 (atFlags StatusFlags.CF (adcR64R64Effect 0x114629 9 8)) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 9))) #v[88, 79, 93]
    (.letOp (n := 96) (.exec 0x114629 (fun s => s.RIP = 0x114629) (atFlags StatusFlags.CF (adcR64R64Effect 0x114629 9 8)) (Reg.operands [.gpr 9, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[88, 79, 93]
    (.letOp (n := 97) (.out 0x11462c (movR64M64Effect 0x11462c 5 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 6] []) (.reg (.gpr 5))) #v[6]
    (.letOp (n := 98) (.exec 0x11462c (LoadPre 0x11462c (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11462c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11462c 5 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 99) (.out 0x114630 (shldR64R64Effect 0x114630 5 9 10 1) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[95, 92]
    (.letOp (n := 100) (.exec 0x114630 (fun s => s.RIP = 0x114630) (shldR64R64Effect 0x114630 5 9 10 1) (Reg.operands [.gpr 9, .gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[95, 92]
    (.letOp (n := 101) (.out 0x114635 (addR64R64Effect 0x114635 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[92, 92]
    (.letOp (n := 102) (.exec 0x114635 (fun s => s.RIP = 0x114635) (addR64R64Effect 0x114635 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[92, 92]
    (.letOp (n := 103) (.out 0x114638 (movR64R64Effect 0x114638 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[97]
    (.letOp (n := 104) (.exec 0x114638 (fun s => s.RIP = 0x114638) (movR64R64Effect 0x114638 0 5) (Reg.operands [.gpr 5] [])) #v[97]
    (.letOp (n := 105) (.out 0x11463b (mulR64Effect 0x11463b 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5, .gpr 0] []) (.reg (.gpr 0))) #v[97, 103]
    (.letOp (n := 106) (.out 0x11463b (mulR64Effect 0x11463b 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 5, .gpr 0] []) (.reg (.gpr 2))) #v[97, 103]
    (.letOp (n := 107) (.exec 0x11463b (fun s => s.RIP = 0x11463b) (mulR64Effect 0x11463b 5) (Reg.operands [.gpr 5, .gpr 0] [])) #v[97, 103]
    (.letOp (n := 108) (.out 0x11463e (movR64R64Effect 0x11463e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[105]
    (.letOp (n := 109) (.exec 0x11463e (fun s => s.RIP = 0x11463e) (movR64R64Effect 0x11463e 6 0) (Reg.operands [.gpr 0] [])) #v[105]
    (.letOp (n := 110) (.out 0x114641 (movR64R64Effect 0x114641 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[106]
    (.letOp (n := 111) (.exec 0x114641 (fun s => s.RIP = 0x114641) (movR64R64Effect 0x114641 14 2) (Reg.operands [.gpr 2] [])) #v[106]
    (.letOp (n := 112) (.out 0x114644 (movR64Imm64Effect 0x114644 0 0xffffffffffffd) (EffectPart.reads (.reg (.gpr 0)) [] []) (.reg (.gpr 0))) #v[]
    (.letOp (n := 113) (.exec 0x114644 (fun s => s.RIP = 0x114644) (movR64Imm64Effect 0x114644 0 0xffffffffffffd) (Reg.operands [] [])) #v[]
    (.letOp (n := 114) (.out 0x11464e (andR64R64Effect 0x11464e 0 6) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 6] []) (.reg (.gpr 0))) #v[112, 108]
    (.letOp (n := 115) (.exec 0x11464e (fun s => s.RIP = 0x11464e) (andR64R64Effect 0x11464e 0 6) (Reg.operands [.gpr 0, .gpr 6] [])) #v[112, 108]
    (.letOp (n := 116) (.out 0x114651 (movR64Imm64Effect 0x114651 13 0x1000003d10) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 117) (.exec 0x114651 (fun s => s.RIP = 0x114651) (movR64Imm64Effect 0x114651 13 0x1000003d10) (Reg.operands [] [])) #v[]
    (.letOp (n := 118) (.out 0x11465b (mulR64Effect 0x11465b 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[116, 114]
    (.letOp (n := 119) (.out 0x11465b (mulR64Effect 0x11465b 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[116, 114]
    (.letOp (n := 120) (.exec 0x11465b (fun s => s.RIP = 0x11465b) (mulR64Effect 0x11465b 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[116, 114]
    (.letOp (n := 121) (.out 0x11465e (movR64R64Effect 0x11465e 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[119]
    (.letOp (n := 122) (.exec 0x11465e (fun s => s.RIP = 0x11465e) (movR64R64Effect 0x11465e 8 2) (Reg.operands [.gpr 2] [])) #v[119]
    (.letOp (n := 123) (.out 0x114661 (addR64R64Effect 0x114661 0 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 10] []) (.reg (.gpr 0))) #v[118, 101]
    (.letOp (n := 124) (.out 0x114661 (addR64R64Effect 0x114661 0 10) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 10] []) (.flag .CF)) #v[118, 101]
    (.letOp (n := 125) (.exec 0x114661 (fun s => s.RIP = 0x114661) (addR64R64Effect 0x114661 0 10) (Reg.operands [.gpr 0, .gpr 10] [])) #v[118, 101]
    (.letOp (n := 126) (.exec 0x114664 (StorePre 0x114664 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114664 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114664 0 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[123, 65]
    (.letOp (n := 127) (.out 0x114669 (atFlags StatusFlags.CF (adcR64R64Effect 0x114669 8 9)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[121, 99, 124]
    (.letOp (n := 128) (.exec 0x114669 (fun s => s.RIP = 0x114669) (atFlags StatusFlags.CF (adcR64R64Effect 0x114669 8 9)) (Reg.operands [.gpr 8, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[121, 99, 124]
    (.letOp (n := 129) (.out 0x11466c (shldR64R64Effect 0x11466c 5 14 6 12) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[110, 108]
    (.letOp (n := 130) (.exec 0x11466c (fun s => s.RIP = 0x11466c) (shldR64R64Effect 0x11466c 5 14 6 12) (Reg.operands [.gpr 14, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110, 108]
    (.letOp (n := 131) (.out 0x114671 (shldR64R64Effect 0x114671 5 8 0 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[127, 123]
    (.letOp (n := 132) (.exec 0x114671 (fun s => s.RIP = 0x114671) (shldR64R64Effect 0x114671 5 8 0 12) (Reg.operands [.gpr 8, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[127, 123]
    (.letOp (n := 133) (.exec 0x114676 (StorePre 0x114676 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114676 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114676 15 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 15, .gpr 4] [])) #v[71, 65]
    (.letOp (n := 134) (.out 0x11467b (movR64R64Effect 0x11467b 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 135) (.exec 0x11467b (fun s => s.RIP = 0x11467b) (movR64R64Effect 0x11467b 0 15) (Reg.operands [.gpr 15] [])) #v[71]
    (b_l1145f0_2)))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0_1 : List UInt8 :=
  [0x4D, 0x11, 0xC1, 0x48, 0x8B, 0x6E, 0x20, 0x4D, 0x0F, 0xA4, 0xD1, 0x01, 0x4D, 0x01, 0xD2, 0x48,
    0x89, 0xE8, 0x48, 0xF7, 0xE5, 0x48, 0x89, 0xC6, 0x49, 0x89, 0xD6, 0x48, 0xB8, 0xFD, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0x0F, 0x00, 0x48, 0x21, 0xF0, 0x49, 0xBD, 0x10, 0x3D, 0x00, 0x00, 0x10, 0x00,
    0x00, 0x00, 0x49, 0xF7, 0xE5, 0x49, 0x89, 0xD0, 0x4C, 0x01, 0xD0, 0x48, 0x89, 0x44, 0x24, 0x30,
    0x4D, 0x11, 0xC8, 0x49, 0x0F, 0xA4, 0xF6, 0x0C, 0x49, 0x0F, 0xA4, 0xC0, 0x0C, 0x4C, 0x89, 0x7C,
    0x24, 0x08, 0x4C, 0x89, 0xF8] ++ bytes_l1145f0_2

theorem code_l1145f0_1 : ∀ x ∈ codeRange 0x114629 bytes_l1145f0_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14629 85 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_2

@[cfg_block] def b_l1145f0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1145f0 (pushR64Effect 0x1145f0 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x1145f0 (PushPre 0x1145f0 1) (pushR64Effect 0x1145f0 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x1145f1 (pushR64Effect 0x1145f1 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x1145f1 (PushPre 0x1145f1 2) (pushR64Effect 0x1145f1 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x1145f3 (pushR64Effect 0x1145f3 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x1145f3 (PushPre 0x1145f3 2) (pushR64Effect 0x1145f3 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x1145f5 (pushR64Effect 0x1145f5 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x1145f5 (PushPre 0x1145f5 2) (pushR64Effect 0x1145f5 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x1145f7 (pushR64Effect 0x1145f7 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x1145f7 (PushPre 0x1145f7 2) (pushR64Effect 0x1145f7 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x1145f9 (pushR64Effect 0x1145f9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x1145f9 (PushPre 0x1145f9 1) (pushR64Effect 0x1145f9 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x1145fa (subR64Imm8Effect 0x1145fa 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x1145fa (fun s => s.RIP = 0x1145fa) (subR64Imm8Effect 0x1145fa 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x1145fe (movR64M64Effect 0x1145fe 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[6]
    (.letOp (n := 68) (.exec 0x1145fe (LoadPre 0x1145fe (fun s => AddrMode.addr (.base 6 .none) s (0x1145fe + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x1145fe 1 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x114601 (movR64M64Effect 0x114601 11 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 70) (.exec 0x114601 (LoadPre 0x114601 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x114601 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114601 11 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 71) (.out 0x114605 (movR64M64Effect 0x114605 15 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 15)) [.gpr 6] []) (.reg (.gpr 15))) #v[6]
    (.letOp (n := 72) (.exec 0x114605 (LoadPre 0x114605 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x114605 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114605 15 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 73) (.out 0x114609 (movR64M64Effect 0x114609 0 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 74) (.exec 0x114609 (LoadPre 0x114609 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x114609 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x114609 0 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 75) (.exec 0x11460d (StorePre 0x11460d 4 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11460d + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11460d 0 (.sib 4 none 0 .none)) (Reg.operands [.gpr 0, .gpr 4] [])) #v[73, 65]
    (.letOp (n := 76) (.out 0x114611 (mulR64Effect 0x114611 1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 1, .gpr 0] []) (.reg (.gpr 0))) #v[67, 73]
    (.letOp (n := 77) (.out 0x114611 (mulR64Effect 0x114611 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1, .gpr 0] []) (.reg (.gpr 2))) #v[67, 73]
    (.letOp (n := 78) (.exec 0x114611 (fun s => s.RIP = 0x114611) (mulR64Effect 0x114611 1) (Reg.operands [.gpr 1, .gpr 0] [])) #v[67, 73]
    (.letOp (n := 79) (.out 0x114614 (movR64R64Effect 0x114614 8 2) (EffectPart.reads (.reg (.gpr 8)) [.gpr 2] []) (.reg (.gpr 8))) #v[77]
    (.letOp (n := 80) (.exec 0x114614 (fun s => s.RIP = 0x114614) (movR64R64Effect 0x114614 8 2) (Reg.operands [.gpr 2] [])) #v[77]
    (.letOp (n := 81) (.out 0x114617 (movR64R64Effect 0x114617 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 0] []) (.reg (.gpr 3))) #v[76]
    (.letOp (n := 82) (.exec 0x114617 (fun s => s.RIP = 0x114617) (movR64R64Effect 0x114617 3 0) (Reg.operands [.gpr 0] [])) #v[76]
    (.letOp (n := 83) (.out 0x11461a (movR64R64Effect 0x11461a 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[71]
    (.letOp (n := 84) (.exec 0x11461a (fun s => s.RIP = 0x11461a) (movR64R64Effect 0x11461a 0 15) (Reg.operands [.gpr 15] [])) #v[71]
    (.letOp (n := 85) (.out 0x11461d (mulR64Effect 0x11461d 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11, .gpr 0] []) (.reg (.gpr 0))) #v[69, 83]
    (.letOp (n := 86) (.out 0x11461d (mulR64Effect 0x11461d 11) (EffectPart.reads (.reg (.gpr 2)) [.gpr 11, .gpr 0] []) (.reg (.gpr 2))) #v[69, 83]
    (.letOp (n := 87) (.exec 0x11461d (fun s => s.RIP = 0x11461d) (mulR64Effect 0x11461d 11) (Reg.operands [.gpr 11, .gpr 0] [])) #v[69, 83]
    (.letOp (n := 88) (.out 0x114620 (movR64R64Effect 0x114620 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[86]
    (.letOp (n := 89) (.exec 0x114620 (fun s => s.RIP = 0x114620) (movR64R64Effect 0x114620 9 2) (Reg.operands [.gpr 2] [])) #v[86]
    (.letOp (n := 90) (.out 0x114623 (movR64R64Effect 0x114623 10 0) (EffectPart.reads (.reg (.gpr 10)) [.gpr 0] []) (.reg (.gpr 10))) #v[85]
    (.letOp (n := 91) (.exec 0x114623 (fun s => s.RIP = 0x114623) (movR64R64Effect 0x114623 10 0) (Reg.operands [.gpr 0] [])) #v[85]
    (.letOp (n := 92) (.out 0x114626 (addR64R64Effect 0x114626 10 3) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 3] []) (.reg (.gpr 10))) #v[90, 81]
    (.letOp (n := 93) (.out 0x114626 (addR64R64Effect 0x114626 10 3) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 3] []) (.flag .CF)) #v[90, 81]
    (.letOp (n := 94) (.exec 0x114626 (fun s => s.RIP = 0x114626) (addR64R64Effect 0x114626 10 3) (Reg.operands [.gpr 10, .gpr 3] [])) #v[90, 81]
    (b_l1145f0_1))))))))))))))))))))))))))))))))))))))))))

def bytes_l1145f0 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x8B,
    0x0E, 0x4C, 0x8B, 0x5E, 0x08, 0x4C, 0x8B, 0x7E, 0x10, 0x48, 0x8B, 0x46, 0x18, 0x48, 0x89, 0x04,
    0x24, 0x48, 0xF7, 0xE1, 0x49, 0x89, 0xD0, 0x48, 0x89, 0xC3, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE3,
    0x49, 0x89, 0xD1, 0x49, 0x89, 0xC2, 0x49, 0x01, 0xDA] ++ bytes_l1145f0_1

theorem code_l1145f0 : ∀ x ∈ codeRange 0x1145f0 bytes_l1145f0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x145f0 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1145f0_1

@[cfg_block] def b_l1148d0_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x114917 (bswapR64Effect 0x114917 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 94) (.exec 0x114917 (fun s => s.RIP = 0x114917) (bswapR64Effect 0x114917 3 6) (Reg.operands [.gpr 6] [])) #v[73]
    (.letOp (n := 95) (.out 0x11491a (movR64R64Effect 0x11491a 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 96) (.exec 0x11491a (fun s => s.RIP = 0x11491a) (movR64R64Effect 0x11491a 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 97) (.out 0x11491d (bswapR64Effect 0x11491d 3 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[65]
    (.letOp (n := 98) (.exec 0x11491d (fun s => s.RIP = 0x11491d) (bswapR64Effect 0x11491d 3 1) (Reg.operands [.gpr 1] [])) #v[65]
    (.letOp (n := 99) (.exec 0x114920 (StorePre 0x114920 3 (fun s => AddrMode.addr (.base 7 .none) s (0x114920 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114920 2 (.base 7 .none)) (Reg.operands [.gpr 2, .gpr 7] [])) #v[89, 7]
    (.letOp (n := 100) (.exec 0x114923 (StorePre 0x114923 4 (fun s => AddrMode.addr (.base 7 (.d8 0x8)) s (0x114923 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114923 10 (.base 7 (.d8 0x8))) (Reg.operands [.gpr 10, .gpr 7] [])) #v[91, 7]
    (.letOp (n := 101) (.exec 0x114927 (StorePre 0x114927 4 (fun s => AddrMode.addr (.base 7 (.d8 0x10)) s (0x114927 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114927 6 (.base 7 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 7] [])) #v[93, 7]
    (.letOp (n := 102) (.exec 0x11492b (StorePre 0x11492b 4 (fun s => AddrMode.addr (.base 7 (.d8 0x18)) s (0x11492b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11492b 1 (.base 7 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 7] [])) #v[97, 7]
    (.letOp (n := 103) (.out 0x11492f (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[4]
    (.letOp (n := 104) (.out 0x11492f (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 105) (.exec 0x11492f (RetPre 0x11492f) (retEffect) (Reg.operands [.gpr 4] [])) #v[4]
    (.terminate (.ret (RegMap.args [(0, 95), (1, 97), (2, 89), (3, 3), (4, 104), (5, 5), (6, 93), (7, 7), (8, 75), (9, 83), (10, 91), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 106) (some ⟨103, by decide⟩)))))))))))))))

def bytes_l1148d0_1 : List UInt8 :=
  [0x48, 0x0F, 0xCE, 0x48, 0x89, 0xF8, 0x48, 0x0F, 0xC9, 0x48, 0x89, 0x17, 0x4C, 0x89, 0x57, 0x08,
    0x48, 0x89, 0x77, 0x10, 0x48, 0x89, 0x4F, 0x18, 0xC3]

theorem code_l1148d0_1 : ∀ x ∈ codeRange 0x114917 bytes_l1148d0_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14917 25 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l1148d0 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x1148d0 (movR64M64Effect 0x1148d0 0 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 54) (.exec 0x1148d0 (LoadPre 0x1148d0 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x1148d0 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d0 0 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x1148d4 (movR64M64Effect 0x1148d4 8 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 56) (.exec 0x1148d4 (LoadPre 0x1148d4 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x1148d4 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d4 8 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x1148d8 (movR64M64Effect 0x1148d8 9 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 9)) [.gpr 6] []) (.reg (.gpr 9))) #v[6]
    (.letOp (n := 58) (.exec 0x1148d8 (LoadPre 0x1148d8 (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1148d8 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148d8 9 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 59) (.out 0x1148dc (movR64M64Effect 0x1148dc 2 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 60) (.exec 0x1148dc (LoadPre 0x1148dc (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x1148dc + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x1148dc 2 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 61) (.out 0x1148e0 (movR64R64Effect 0x1148e0 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[53]
    (.letOp (n := 62) (.exec 0x1148e0 (fun s => s.RIP = 0x1148e0) (movR64R64Effect 0x1148e0 1 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 63) (.out 0x1148e3 (shlR64Effect 0x1148e3 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[61]
    (.letOp (n := 64) (.exec 0x1148e3 (fun s => s.RIP = 0x1148e3) (shlR64Effect 0x1148e3 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[61]
    (.letOp (n := 65) (.out 0x1148e7 (orR64M64Effect 0x1148e7 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[63, 6]
    (.letOp (n := 66) (.exec 0x1148e7 (LoadPre 0x1148e7 (fun s => AddrMode.addr (.base 6 .none) s (0x1148e7 + BitVec.ofNat 64 3)) 8) (orR64M64Effect 0x1148e7 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[63, 6]
    (.letOp (n := 67) (.out 0x1148ea (shrR64Effect 0x1148ea 4 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 68) (.exec 0x1148ea (fun s => s.RIP = 0x1148ea) (shrR64Effect 0x1148ea 4 0 12) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 69) (.out 0x1148ee (movR64R64Effect 0x1148ee 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 8] []) (.reg (.gpr 6))) #v[55]
    (.letOp (n := 70) (.exec 0x1148ee (fun s => s.RIP = 0x1148ee) (movR64R64Effect 0x1148ee 6 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 71) (.out 0x1148f1 (shlR64Effect 0x1148f1 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[69]
    (.letOp (n := 72) (.exec 0x1148f1 (fun s => s.RIP = 0x1148f1) (shlR64Effect 0x1148f1 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x1148f5 (orR64R64Effect 0x1148f5 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[71, 67]
    (.letOp (n := 74) (.exec 0x1148f5 (fun s => s.RIP = 0x1148f5) (orR64R64Effect 0x1148f5 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[71, 67]
    (.letOp (n := 75) (.out 0x1148f8 (shrR64Effect 0x1148f8 4 8 24) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 8))) #v[55]
    (.letOp (n := 76) (.exec 0x1148f8 (fun s => s.RIP = 0x1148f8) (shrR64Effect 0x1148f8 4 8 24) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[55]
    (.letOp (n := 77) (.out 0x1148fc (movR64R64Effect 0x1148fc 10 9) (EffectPart.reads (.reg (.gpr 10)) [.gpr 9] []) (.reg (.gpr 10))) #v[57]
    (.letOp (n := 78) (.exec 0x1148fc (fun s => s.RIP = 0x1148fc) (movR64R64Effect 0x1148fc 10 9) (Reg.operands [.gpr 9] [])) #v[57]
    (.letOp (n := 79) (.out 0x1148ff (shlR64Effect 0x1148ff 4 10 28) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 10))) #v[77]
    (.letOp (n := 80) (.exec 0x1148ff (fun s => s.RIP = 0x1148ff) (shlR64Effect 0x1148ff 4 10 28) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x114903 (orR64R64Effect 0x114903 10 8) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8] []) (.reg (.gpr 10))) #v[79, 75]
    (.letOp (n := 82) (.exec 0x114903 (fun s => s.RIP = 0x114903) (orR64R64Effect 0x114903 10 8) (Reg.operands [.gpr 10, .gpr 8] [])) #v[79, 75]
    (.letOp (n := 83) (.out 0x114906 (shrR64Effect 0x114906 4 9 36) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[57]
    (.letOp (n := 84) (.exec 0x114906 (fun s => s.RIP = 0x114906) (shrR64Effect 0x114906 4 9 36) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 85) (.out 0x11490a (shlR64Effect 0x11490a 4 2 16) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[59]
    (.letOp (n := 86) (.exec 0x11490a (fun s => s.RIP = 0x11490a) (shlR64Effect 0x11490a 4 2 16) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[59]
    (.letOp (n := 87) (.out 0x11490e (orR64R64Effect 0x11490e 2 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9] []) (.reg (.gpr 2))) #v[85, 83]
    (.letOp (n := 88) (.exec 0x11490e (fun s => s.RIP = 0x11490e) (orR64R64Effect 0x11490e 2 9) (Reg.operands [.gpr 2, .gpr 9] [])) #v[85, 83]
    (.letOp (n := 89) (.out 0x114911 (bswapR64Effect 0x114911 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[87]
    (.letOp (n := 90) (.exec 0x114911 (fun s => s.RIP = 0x114911) (bswapR64Effect 0x114911 3 2) (Reg.operands [.gpr 2] [])) #v[87]
    (.letOp (n := 91) (.out 0x114914 (bswapR64Effect 0x114914 3 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10] []) (.reg (.gpr 10))) #v[81]
    (.letOp (n := 92) (.exec 0x114914 (fun s => s.RIP = 0x114914) (bswapR64Effect 0x114914 3 10) (Reg.operands [.gpr 10] [])) #v[81]
    (b_l1148d0_1))))))))))))))))))))))))))))))))))))))))

def bytes_l1148d0 : List UInt8 :=
  [0x48, 0x8B, 0x46, 0x08, 0x4C, 0x8B, 0x46, 0x10, 0x4C, 0x8B, 0x4E, 0x18, 0x48, 0x8B, 0x56, 0x20,
    0x48, 0x89, 0xC1, 0x48, 0xC1, 0xE1, 0x34, 0x48, 0x0B, 0x0E, 0x48, 0xC1, 0xE8, 0x0C, 0x4C, 0x89,
    0xC6, 0x48, 0xC1, 0xE6, 0x28, 0x48, 0x09, 0xC6, 0x49, 0xC1, 0xE8, 0x18, 0x4D, 0x89, 0xCA, 0x49,
    0xC1, 0xE2, 0x1C, 0x4D, 0x09, 0xC2, 0x49, 0xC1, 0xE9, 0x24, 0x48, 0xC1, 0xE2, 0x10, 0x4C, 0x09,
    0xCA, 0x48, 0x0F, 0xCA, 0x49, 0x0F, 0xCA] ++ bytes_l1148d0_1

theorem code_l1148d0 : ∀ x ∈ codeRange 0x1148d0 bytes_l1148d0, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x148d0 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l1148d0_1

@[cfg_block] def b_l114930_2 : Block Op Label signature Reg.count 129 :=
  .letOp (n := 129) (.out 0x1149c8 (andR64R64Effect 0x1149c8 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[127, 90]
    (.letOp (n := 130) (.exec 0x1149c8 (fun s => s.RIP = 0x1149c8) (andR64R64Effect 0x1149c8 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[127, 90]
    (.letOp (n := 131) (.exec 0x1149cb (StorePre 0x1149cb 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x1149cb + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149cb 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[129, 65]
    (.letOp (n := 132) (.out 0x1149d0 (movR64R64Effect 0x1149d0 0 3) (EffectPart.reads (.reg (.gpr 0)) [.gpr 3] []) (.reg (.gpr 0))) #v[98]
    (.letOp (n := 133) (.exec 0x1149d0 (fun s => s.RIP = 0x1149d0) (movR64R64Effect 0x1149d0 0 3) (Reg.operands [.gpr 3] [])) #v[98]
    (.letOp (n := 134) (.out 0x1149d3 (andR64R64Effect 0x1149d3 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[132, 107]
    (.letOp (n := 135) (.exec 0x1149d3 (fun s => s.RIP = 0x1149d3) (andR64R64Effect 0x1149d3 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[132, 107]
    (.letOp (n := 136) (.out 0x1149d6 (andR64R64Effect 0x1149d6 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 5] []) (.reg (.gpr 0))) #v[134, 114]
    (.letOp (n := 137) (.exec 0x1149d6 (fun s => s.RIP = 0x1149d6) (andR64R64Effect 0x1149d6 0 5) (Reg.operands [.gpr 0, .gpr 5] [])) #v[134, 114]
    (.letOp (n := 138) (.out 0x1149d9 (movR64R64Effect 0x1149d9 1 12) (EffectPart.reads (.reg (.gpr 1)) [.gpr 12] []) (.reg (.gpr 1))) #v[125]
    (.letOp (n := 139) (.exec 0x1149d9 (fun s => s.RIP = 0x1149d9) (movR64R64Effect 0x1149d9 1 12) (Reg.operands [.gpr 12] [])) #v[125]
    (.letOp (n := 140) (.out 0x1149dc (shrR64Effect 0x1149dc 4 1 48) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[138]
    (.letOp (n := 141) (.exec 0x1149dc (fun s => s.RIP = 0x1149dc) (shrR64Effect 0x1149dc 4 1 48) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.out 0x1149e0 (movR64R64Effect 0x1149e0 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12] []) (.reg (.gpr 2))) #v[125]
    (.letOp (n := 143) (.exec 0x1149e0 (fun s => s.RIP = 0x1149e0) (movR64R64Effect 0x1149e0 2 12) (Reg.operands [.gpr 12] [])) #v[125]
    (.letOp (n := 144) (.out 0x1149e3 (xorR64R64Effect 0x1149e3 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[142, 73]
    (.letOp (n := 145) (.exec 0x1149e3 (fun s => s.RIP = 0x1149e3) (xorR64R64Effect 0x1149e3 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[142, 73]
    (.letOp (n := 146) (.out 0x1149e6 (xorR64R64Effect 0x1149e6 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 15] []) (.reg (.gpr 0))) #v[136, 90]
    (.letOp (n := 147) (.exec 0x1149e6 (fun s => s.RIP = 0x1149e6) (xorR64R64Effect 0x1149e6 0 15) (Reg.operands [.gpr 0, .gpr 15] [])) #v[136, 90]
    (.letOp (n := 148) (.out 0x1149e9 (orR64R64Effect 0x1149e9 0 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 2] []) (.reg (.gpr 0))) #v[146, 144]
    (.letOp (n := 149) (.out 0x1149e9 (orR64R64Effect 0x1149e9 0 2) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 2] []) (.flag .ZF)) #v[146, 144]
    (.letOp (n := 150) (.exec 0x1149e9 (fun s => s.RIP = 0x1149e9) (orR64R64Effect 0x1149e9 0 2) (Reg.operands [.gpr 0, .gpr 2] [])) #v[146, 144]
    (.letOp (n := 151) (.out 0x1149ec (atFlags (condHolds 4) (setccR8Effect 0x1149ec 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 0))) #v[148, 149]
    (.letOp (n := 152) (.exec 0x1149ec (fun s => s.RIP = 0x1149ec) (atFlags (condHolds 4) (setccR8Effect 0x1149ec 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[148, 149]
    (.letOp (n := 153) (.out 0x1149ef (movR64Imm64Effect 0x1149ef 2 0xffffefffffc2e) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 154) (.exec 0x1149ef (fun s => s.RIP = 0x1149ef) (movR64Imm64Effect 0x1149ef 2 0xffffefffffc2e) (Reg.operands [] [])) #v[]
    (.letOp (n := 155) (.out 0x1149f9 (cmpR64R64Effect 0x1149f9 9 2) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 2] []) (.flag .CF)) #v[102, 153]
    (.letOp (n := 156) (.out 0x1149f9 (cmpR64R64Effect 0x1149f9 9 2) (EffectPart.reads (.flag .ZF) [.gpr 9, .gpr 2] []) (.flag .ZF)) #v[102, 153]
    (.letOp (n := 157) (.exec 0x1149f9 (fun s => s.RIP = 0x1149f9) (cmpR64R64Effect 0x1149f9 9 2) (Reg.operands [.gpr 9, .gpr 2] [])) #v[102, 153]
    (.letOp (n := 158) (.out 0x1149fc (atFlags (condHolds 7) (setccR8Effect 0x1149fc 3 2)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF]) (.reg (.gpr 2))) #v[153, 155, 156]
    (.letOp (n := 159) (.exec 0x1149fc (fun s => s.RIP = 0x1149fc) (atFlags (condHolds 7) (setccR8Effect 0x1149fc 3 2)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF, .ZF])) #v[153, 155, 156]
    (.letOp (n := 160) (.exec 0x1149ff (StorePre 0x1149ff 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x1149ff + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149ff 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 161) (.out 0x114a04 (andR8R8Effect 0x114a04 2 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[158, 151]
    (.letOp (n := 162) (.exec 0x114a04 (fun s => s.RIP = 0x114a04) (andR8R8Effect 0x114a04 2 2 0) (Reg.operands [.gpr 2, .gpr 0] [])) #v[158, 151]
    (.letOp (n := 163) (.out 0x114a06 (orR8R8Effect 0x114a06 2 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1] []) (.reg (.gpr 2))) #v[161, 140]
    (.letOp (n := 164) (.exec 0x114a06 (fun s => s.RIP = 0x114a06) (orR8R8Effect 0x114a06 2 2 1) (Reg.operands [.gpr 2, .gpr 1] [])) #v[161, 140]
    (.letOp (n := 165) (.out 0x114a08 (movzxR32R8Effect 0x114a08 3 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[163]
    (.letOp (n := 166) (.exec 0x114a08 (fun s => s.RIP = 0x114a08) (movzxR32R8Effect 0x114a08 3 7 2) (Reg.operands [.gpr 2] [])) #v[163]
    (.letOp (n := 167) (.out 0x114a0b (callEffect (fun _ => 0x127d50) 0x114a10) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[65]
    (.letOp (n := 168) (.exec 0x114a0b (PushPre 0x114a0b 5) (callEffect (fun _ => 0x127d50) 0x114a10) (Reg.operands [.gpr 4] [])) #v[65]
    (.letOp (n := 169) (.const ⟨64, 0x114a10⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 151), (1, 140), (2, 163), (3, 98), (4, 167), (5, 114), (6, 6), (7, 165), (8, 73), (9, 102), (10, 10), (11, 11), (12, 125), (13, 81), (14, 77), (15, 90), (22, 22), (39, 39), (50, 50), (51, 51)] 170⟩ { target := .l114a10, kept := #v[], arity := rfl, guard := some (Fin.last 169) }))))))))))))))))))))))))))))))))))))))))))

def bytes_l114930_2 : List UInt8 :=
  [0x4C, 0x21, 0xF8, 0x48, 0x89, 0x44, 0x24, 0x08, 0x48, 0x89, 0xD8, 0x48, 0x21, 0xD0, 0x48, 0x21,
    0xE8, 0x4C, 0x89, 0xE1, 0x48, 0xC1, 0xE9, 0x30, 0x4C, 0x89, 0xE2, 0x4C, 0x31, 0xC2, 0x4C, 0x31,
    0xF8, 0x48, 0x09, 0xD0, 0x0F, 0x94, 0xC0, 0x48, 0xBA, 0x2E, 0xFC, 0xFF, 0xFF, 0xFE, 0xFF, 0x0F,
    0x00, 0x49, 0x39, 0xD1, 0x0F, 0x97, 0xC2, 0x48, 0x89, 0x7C, 0x24, 0x28, 0x20, 0xC2, 0x08, 0xCA,
    0x0F, 0xB6, 0xFA, 0xE8, 0x40, 0x33, 0x01, 0x00]

theorem code_l114930_2 : ∀ x ∈ codeRange 0x1149c8 bytes_l114930_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x149c8 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114930_1 : Block Op Label signature Reg.count 92 :=
  .letOp (n := 92) (.out 0x114981 (movR64R64Effect 0x114981 2 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13] []) (.reg (.gpr 2))) #v[81]
    (.letOp (n := 93) (.exec 0x114981 (fun s => s.RIP = 0x114981) (movR64R64Effect 0x114981 2 13) (Reg.operands [.gpr 13] [])) #v[81]
    (.letOp (n := 94) (.out 0x114984 (movR64R64Effect 0x114984 3 1) (EffectPart.reads (.reg (.gpr 3)) [.gpr 1] []) (.reg (.gpr 3))) #v[87]
    (.letOp (n := 95) (.exec 0x114984 (fun s => s.RIP = 0x114984) (movR64R64Effect 0x114984 3 1) (Reg.operands [.gpr 1] [])) #v[87]
    (.letOp (n := 96) (.out 0x114987 (shrR64Effect 0x114987 4 3 52) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 3))) #v[94]
    (.letOp (n := 97) (.exec 0x114987 (fun s => s.RIP = 0x114987) (shrR64Effect 0x114987 4 3 52) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[94]
    (.letOp (n := 98) (.out 0x11498b (addR64M64Effect 0x11498b 3 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6] []) (.reg (.gpr 3))) #v[96, 6]
    (.letOp (n := 99) (.exec 0x11498b (LoadPre 0x11498b (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11498b + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11498b 3 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 3, .gpr 6] [])) #v[96, 6]
    (.letOp (n := 100) (.out 0x11498f (andR64R64Effect 0x11498f 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[92, 90]
    (.letOp (n := 101) (.exec 0x11498f (fun s => s.RIP = 0x11498f) (andR64R64Effect 0x11498f 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[92, 90]
    (.letOp (n := 102) (.out 0x114992 (movR64R64Effect 0x114992 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[100]
    (.letOp (n := 103) (.exec 0x114992 (fun s => s.RIP = 0x114992) (movR64R64Effect 0x114992 9 2) (Reg.operands [.gpr 2] [])) #v[100]
    (.letOp (n := 104) (.exec 0x114995 (StorePre 0x114995 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114995 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114995 2 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[100, 65]
    (.letOp (n := 105) (.out 0x11499a (movR64R64Effect 0x11499a 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[87]
    (.letOp (n := 106) (.exec 0x11499a (fun s => s.RIP = 0x11499a) (movR64R64Effect 0x11499a 2 1) (Reg.operands [.gpr 1] [])) #v[87]
    (.letOp (n := 107) (.out 0x11499d (andR64R64Effect 0x11499d 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[105, 90]
    (.letOp (n := 108) (.exec 0x11499d (fun s => s.RIP = 0x11499d) (andR64R64Effect 0x11499d 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[105, 90]
    (.letOp (n := 109) (.exec 0x1149a0 (StorePre 0x1149a0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x1149a0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149a0 2 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[107, 65]
    (.letOp (n := 110) (.out 0x1149a5 (movR64R64Effect 0x1149a5 5 3) (EffectPart.reads (.reg (.gpr 5)) [.gpr 3] []) (.reg (.gpr 5))) #v[98]
    (.letOp (n := 111) (.exec 0x1149a5 (fun s => s.RIP = 0x1149a5) (movR64R64Effect 0x1149a5 5 3) (Reg.operands [.gpr 3] [])) #v[98]
    (.letOp (n := 112) (.out 0x1149a8 (shrR64Effect 0x1149a8 4 5 52) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[110]
    (.letOp (n := 113) (.exec 0x1149a8 (fun s => s.RIP = 0x1149a8) (shrR64Effect 0x1149a8 4 5 52) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[110]
    (.letOp (n := 114) (.out 0x1149ac (addR64M64Effect 0x1149ac 5 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 6] []) (.reg (.gpr 5))) #v[112, 6]
    (.letOp (n := 115) (.exec 0x1149ac (LoadPre 0x1149ac (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x1149ac + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x1149ac 5 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 5, .gpr 6] [])) #v[112, 6]
    (.letOp (n := 116) (.out 0x1149b0 (movR64R64Effect 0x1149b0 1 3) (EffectPart.reads (.reg (.gpr 1)) [.gpr 3] []) (.reg (.gpr 1))) #v[98]
    (.letOp (n := 117) (.exec 0x1149b0 (fun s => s.RIP = 0x1149b0) (movR64R64Effect 0x1149b0 1 3) (Reg.operands [.gpr 3] [])) #v[98]
    (.letOp (n := 118) (.out 0x1149b3 (andR64R64Effect 0x1149b3 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[116, 90]
    (.letOp (n := 119) (.exec 0x1149b3 (fun s => s.RIP = 0x1149b3) (andR64R64Effect 0x1149b3 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[116, 90]
    (.letOp (n := 120) (.exec 0x1149b6 (StorePre 0x1149b6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x1149b6 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x1149b6 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[118, 65]
    (.letOp (n := 121) (.out 0x1149bb (movR64R64Effect 0x1149bb 12 5) (EffectPart.reads (.reg (.gpr 12)) [.gpr 5] []) (.reg (.gpr 12))) #v[114]
    (.letOp (n := 122) (.exec 0x1149bb (fun s => s.RIP = 0x1149bb) (movR64R64Effect 0x1149bb 12 5) (Reg.operands [.gpr 5] [])) #v[114]
    (.letOp (n := 123) (.out 0x1149be (shrR64Effect 0x1149be 4 12 52) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[121]
    (.letOp (n := 124) (.exec 0x1149be (fun s => s.RIP = 0x1149be) (shrR64Effect 0x1149be 4 12 52) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.out 0x1149c2 (addR64R64Effect 0x1149c2 12 0) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 0] []) (.reg (.gpr 12))) #v[123, 75]
    (.letOp (n := 126) (.exec 0x1149c2 (fun s => s.RIP = 0x1149c2) (addR64R64Effect 0x1149c2 12 0) (Reg.operands [.gpr 12, .gpr 0] [])) #v[123, 75]
    (.letOp (n := 127) (.out 0x1149c5 (movR64R64Effect 0x1149c5 0 5) (EffectPart.reads (.reg (.gpr 0)) [.gpr 5] []) (.reg (.gpr 0))) #v[114]
    (.letOp (n := 128) (.exec 0x1149c5 (fun s => s.RIP = 0x1149c5) (movR64R64Effect 0x1149c5 0 5) (Reg.operands [.gpr 5] [])) #v[114]
    (b_l114930_2)))))))))))))))))))))))))))))))))))))

def bytes_l114930_1 : List UInt8 :=
  [0x4C, 0x89, 0xEA, 0x48, 0x89, 0xCB, 0x48, 0xC1, 0xEB, 0x34, 0x48, 0x03, 0x5E, 0x10, 0x4C, 0x21,
    0xFA, 0x49, 0x89, 0xD1, 0x48, 0x89, 0x54, 0x24, 0x10, 0x48, 0x89, 0xCA, 0x4C, 0x21, 0xFA, 0x48,
    0x89, 0x54, 0x24, 0x18, 0x48, 0x89, 0xDD, 0x48, 0xC1, 0xED, 0x34, 0x48, 0x03, 0x6E, 0x18, 0x48,
    0x89, 0xD9, 0x4C, 0x21, 0xF9, 0x48, 0x89, 0x4C, 0x24, 0x20, 0x49, 0x89, 0xEC, 0x49, 0xC1, 0xEC,
    0x34, 0x49, 0x01, 0xC4, 0x48, 0x89, 0xE8] ++ bytes_l114930_2

theorem code_l114930_1 : ∀ x ∈ codeRange 0x114981 bytes_l114930_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14981 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l114930_2

@[cfg_block] def b_l114930 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x114930 (pushR64Effect 0x114930 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x114930 (PushPre 0x114930 1) (pushR64Effect 0x114930 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x114931 (pushR64Effect 0x114931 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x114931 (PushPre 0x114931 2) (pushR64Effect 0x114931 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x114933 (pushR64Effect 0x114933 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x114933 (PushPre 0x114933 2) (pushR64Effect 0x114933 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x114935 (pushR64Effect 0x114935 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x114935 (PushPre 0x114935 2) (pushR64Effect 0x114935 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x114937 (pushR64Effect 0x114937 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x114937 (PushPre 0x114937 2) (pushR64Effect 0x114937 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x114939 (pushR64Effect 0x114939 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x114939 (PushPre 0x114939 1) (pushR64Effect 0x114939 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11493a (subR64Imm8Effect 0x11493a 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11493a (fun s => s.RIP = 0x11493a) (subR64Imm8Effect 0x11493a 4 0x38) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.out 0x11493e (movR64M64Effect 0x11493e 0 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 6] []) (.reg (.gpr 0))) #v[6]
    (.letOp (n := 68) (.exec 0x11493e (LoadPre 0x11493e (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11493e + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11493e 0 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 69) (.out 0x114942 (movR64R64Effect 0x114942 13 0) (EffectPart.reads (.reg (.gpr 13)) [.gpr 0] []) (.reg (.gpr 13))) #v[67]
    (.letOp (n := 70) (.exec 0x114942 (fun s => s.RIP = 0x114942) (movR64R64Effect 0x114942 13 0) (Reg.operands [.gpr 0] [])) #v[67]
    (.letOp (n := 71) (.out 0x114945 (shrR64Effect 0x114945 4 13 48) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[69]
    (.letOp (n := 72) (.exec 0x114945 (fun s => s.RIP = 0x114945) (shrR64Effect 0x114945 4 13 48) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[69]
    (.letOp (n := 73) (.out 0x114949 (movR64Imm64Effect 0x114949 8 0xffffffffffff) (EffectPart.reads (.reg (.gpr 8)) [] []) (.reg (.gpr 8))) #v[]
    (.letOp (n := 74) (.exec 0x114949 (fun s => s.RIP = 0x114949) (movR64Imm64Effect 0x114949 8 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 75) (.out 0x114953 (andR64R64Effect 0x114953 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 8] []) (.reg (.gpr 0))) #v[67, 73]
    (.letOp (n := 76) (.exec 0x114953 (fun s => s.RIP = 0x114953) (andR64R64Effect 0x114953 0 8) (Reg.operands [.gpr 0, .gpr 8] [])) #v[67, 73]
    (.letOp (n := 77) (.out 0x114956 (movR64Imm64Effect 0x114956 14 0x1000003d1) (EffectPart.reads (.reg (.gpr 14)) [] []) (.reg (.gpr 14))) #v[]
    (.letOp (n := 78) (.exec 0x114956 (fun s => s.RIP = 0x114956) (movR64Imm64Effect 0x114956 14 0x1000003d1) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x114960 (imulR64R64Effect 0x114960 4 13 14) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 14] []) (.reg (.gpr 13))) #v[71, 77]
    (.letOp (n := 80) (.exec 0x114960 (fun s => s.RIP = 0x114960) (imulR64R64Effect 0x114960 4 13 14) (Reg.operands [.gpr 13, .gpr 14] [])) #v[71, 77]
    (.letOp (n := 81) (.out 0x114964 (addR64M64Effect 0x114964 13 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 6] []) (.reg (.gpr 13))) #v[79, 6]
    (.letOp (n := 82) (.exec 0x114964 (LoadPre 0x114964 (fun s => AddrMode.addr (.base 6 .none) s (0x114964 + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x114964 13 (.base 6 .none)) (Reg.operands [.gpr 13, .gpr 6] [])) #v[79, 6]
    (.letOp (n := 83) (.out 0x114967 (movR64R64Effect 0x114967 1 13) (EffectPart.reads (.reg (.gpr 1)) [.gpr 13] []) (.reg (.gpr 1))) #v[81]
    (.letOp (n := 84) (.exec 0x114967 (fun s => s.RIP = 0x114967) (movR64R64Effect 0x114967 1 13) (Reg.operands [.gpr 13] [])) #v[81]
    (.letOp (n := 85) (.out 0x11496a (shrR64Effect 0x11496a 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[83]
    (.letOp (n := 86) (.exec 0x11496a (fun s => s.RIP = 0x11496a) (shrR64Effect 0x11496a 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[83]
    (.letOp (n := 87) (.out 0x11496e (addR64M64Effect 0x11496e 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[85, 6]
    (.letOp (n := 88) (.exec 0x11496e (LoadPre 0x11496e (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11496e + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11496e 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 6] [])) #v[85, 6]
    (.letOp (n := 89) (.exec 0x114972 (StorePre 0x114972 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114972 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x114972 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[87, 65]
    (.letOp (n := 90) (.out 0x114977 (movR64Imm64Effect 0x114977 15 0xfffffffffffff) (EffectPart.reads (.reg (.gpr 15)) [] []) (.reg (.gpr 15))) #v[]
    (.letOp (n := 91) (.exec 0x114977 (fun s => s.RIP = 0x114977) (movR64Imm64Effect 0x114977 15 0xfffffffffffff) (Reg.operands [] [])) #v[]
    (b_l114930_1)))))))))))))))))))))))))))))))))))))))

def bytes_l114930 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x38, 0x48, 0x8B,
    0x46, 0x20, 0x49, 0x89, 0xC5, 0x49, 0xC1, 0xED, 0x30, 0x49, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0x00, 0x00, 0x4C, 0x21, 0xC0, 0x49, 0xBE, 0xD1, 0x03, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    0x4D, 0x0F, 0xAF, 0xEE, 0x4C, 0x03, 0x2E, 0x4C, 0x89, 0xE9, 0x48, 0xC1, 0xE9, 0x34, 0x48, 0x03,
    0x4E, 0x08, 0x48, 0x89, 0x4C, 0x24, 0x30, 0x49, 0xBF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00] ++ bytes_l114930_1

theorem code_l114930 : ∀ x ∈ codeRange 0x114930 bytes_l114930, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14930 81 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l114930_1

@[cfg_block] def b_l114a10_2 : Block Op Label signature Reg.count 130 :=
  .letOp (n := 130) (.exec 0x114aa3 (StorePre 0x114aa3 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x114aa3 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114aa3 6 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 0] [])) #v[117, 125]
    (.letOp (n := 131) (.exec 0x114aa7 (StorePre 0x114aa7 4 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x114aa7 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114aa7 7 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 7, .gpr 0] [])) #v[123, 125]
    (.letOp (n := 132) (.out 0x114aab (addR64Imm8Effect 0x114aab 4 0x38) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 133) (.exec 0x114aab (fun s => s.RIP = 0x114aab) (addR64Imm8Effect 0x114aab 4 0x38) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 134) (.out 0x114aaf (popR64Effect 0x114aaf 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[132]
    (.letOp (n := 135) (.out 0x114aaf (popR64Effect 0x114aaf 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[132]
    (.letOp (n := 136) (.exec 0x114aaf (PopPre 0x114aaf) (popR64Effect 0x114aaf 1 3) (Reg.operands [.gpr 4] [])) #v[132]
    (.letOp (n := 137) (.out 0x114ab0 (popR64Effect 0x114ab0 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[135]
    (.letOp (n := 138) (.out 0x114ab0 (popR64Effect 0x114ab0 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[135]
    (.letOp (n := 139) (.exec 0x114ab0 (PopPre 0x114ab0) (popR64Effect 0x114ab0 2 12) (Reg.operands [.gpr 4] [])) #v[135]
    (.letOp (n := 140) (.out 0x114ab2 (popR64Effect 0x114ab2 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[138]
    (.letOp (n := 141) (.out 0x114ab2 (popR64Effect 0x114ab2 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[138]
    (.letOp (n := 142) (.exec 0x114ab2 (PopPre 0x114ab2) (popR64Effect 0x114ab2 2 13) (Reg.operands [.gpr 4] [])) #v[138]
    (.letOp (n := 143) (.out 0x114ab4 (popR64Effect 0x114ab4 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[141]
    (.letOp (n := 144) (.out 0x114ab4 (popR64Effect 0x114ab4 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[141]
    (.letOp (n := 145) (.exec 0x114ab4 (PopPre 0x114ab4) (popR64Effect 0x114ab4 2 14) (Reg.operands [.gpr 4] [])) #v[141]
    (.letOp (n := 146) (.out 0x114ab6 (popR64Effect 0x114ab6 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[144]
    (.letOp (n := 147) (.out 0x114ab6 (popR64Effect 0x114ab6 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[144]
    (.letOp (n := 148) (.exec 0x114ab6 (PopPre 0x114ab6) (popR64Effect 0x114ab6 2 15) (Reg.operands [.gpr 4] [])) #v[144]
    (.letOp (n := 149) (.out 0x114ab8 (popR64Effect 0x114ab8 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[147]
    (.letOp (n := 150) (.out 0x114ab8 (popR64Effect 0x114ab8 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[147]
    (.letOp (n := 151) (.exec 0x114ab8 (PopPre 0x114ab8) (popR64Effect 0x114ab8 1 5) (Reg.operands [.gpr 4] [])) #v[147]
    (.letOp (n := 152) (.out 0x114ab9 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[150]
    (.letOp (n := 153) (.out 0x114ab9 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[150]
    (.letOp (n := 154) (.exec 0x114ab9 (RetPre 0x114ab9) (retEffect) (Reg.operands [.gpr 4] [])) #v[150]
    (.terminate (.ret (RegMap.args [(0, 125), (1, 105), (2, 111), (3, 134), (4, 153), (5, 149), (6, 117), (7, 123), (8, 69), (9, 85), (10, 61), (11, 53), (12, 137), (13, 140), (14, 143), (15, 146), (22, 22), (39, 39), (50, 50), (51, 51)] 155) (some ⟨152, by decide⟩)))))))))))))))))))))))))))

def bytes_l114a10_2 : List UInt8 :=
  [0x48, 0x89, 0x70, 0x18, 0x48, 0x89, 0x78, 0x20, 0x48, 0x83, 0xC4, 0x38, 0x5B, 0x41, 0x5C, 0x41,
    0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l114a10_2 : ∀ x ∈ codeRange 0x114aa3 bytes_l114a10_2, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x14aa3 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l114a10_1 : Block Op Label signature Reg.count 93 :=
  .letOp (n := 93) (.out 0x114a5f (negR64Effect 0x114a5f 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[91]
    (.letOp (n := 94) (.exec 0x114a5f (fun s => s.RIP = 0x114a5f) (negR64Effect 0x114a5f 0) (Reg.operands [.gpr 0] [])) #v[91]
    (.letOp (n := 95) (.out 0x114a62 (andR64R64Effect 0x114a62 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0] []) (.reg (.gpr 15))) #v[15, 93]
    (.letOp (n := 96) (.exec 0x114a62 (fun s => s.RIP = 0x114a62) (andR64R64Effect 0x114a62 15 0) (Reg.operands [.gpr 15, .gpr 0] [])) #v[15, 93]
    (.letOp (n := 97) (.out 0x114a65 (andR64R64Effect 0x114a65 14 15) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 15] []) (.reg (.gpr 14))) #v[89, 95]
    (.letOp (n := 98) (.exec 0x114a65 (fun s => s.RIP = 0x114a65) (andR64R64Effect 0x114a65 14 15) (Reg.operands [.gpr 14, .gpr 15] [])) #v[89, 95]
    (.letOp (n := 99) (.out 0x114a68 (xorR64R64Effect 0x114a68 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[97, 53]
    (.letOp (n := 100) (.exec 0x114a68 (fun s => s.RIP = 0x114a68) (xorR64R64Effect 0x114a68 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[97, 53]
    (.letOp (n := 101) (.out 0x114a6b (xorR64M64Effect 0x114a6b 1 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[63, 4]
    (.letOp (n := 102) (.exec 0x114a6b (LoadPre 0x114a6b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x114a6b + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x114a6b 1 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[63, 4]
    (.letOp (n := 103) (.out 0x114a70 (andR64R64Effect 0x114a70 1 15) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 15] []) (.reg (.gpr 1))) #v[101, 95]
    (.letOp (n := 104) (.exec 0x114a70 (fun s => s.RIP = 0x114a70) (andR64R64Effect 0x114a70 1 15) (Reg.operands [.gpr 1, .gpr 15] [])) #v[101, 95]
    (.letOp (n := 105) (.out 0x114a73 (xorR64R64Effect 0x114a73 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[103, 61]
    (.letOp (n := 106) (.exec 0x114a73 (fun s => s.RIP = 0x114a73) (xorR64R64Effect 0x114a73 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[103, 61]
    (.letOp (n := 107) (.out 0x114a76 (xorR64R64Effect 0x114a76 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 3] []) (.reg (.gpr 2))) #v[71, 3]
    (.letOp (n := 108) (.exec 0x114a76 (fun s => s.RIP = 0x114a76) (xorR64R64Effect 0x114a76 2 3) (Reg.operands [.gpr 2, .gpr 3] [])) #v[71, 3]
    (.letOp (n := 109) (.out 0x114a79 (andR64R64Effect 0x114a79 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15] []) (.reg (.gpr 2))) #v[107, 95]
    (.letOp (n := 110) (.exec 0x114a79 (fun s => s.RIP = 0x114a79) (andR64R64Effect 0x114a79 2 15) (Reg.operands [.gpr 2, .gpr 15] [])) #v[107, 95]
    (.letOp (n := 111) (.out 0x114a7c (xorR64R64Effect 0x114a7c 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[109, 69]
    (.letOp (n := 112) (.exec 0x114a7c (fun s => s.RIP = 0x114a7c) (xorR64R64Effect 0x114a7c 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[109, 69]
    (.letOp (n := 113) (.out 0x114a7f (xorR64R64Effect 0x114a7f 6 5) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 5] []) (.reg (.gpr 6))) #v[77, 5]
    (.letOp (n := 114) (.exec 0x114a7f (fun s => s.RIP = 0x114a7f) (xorR64R64Effect 0x114a7f 6 5) (Reg.operands [.gpr 6, .gpr 5] [])) #v[77, 5]
    (.letOp (n := 115) (.out 0x114a82 (andR64R64Effect 0x114a82 6 15) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 15] []) (.reg (.gpr 6))) #v[113, 95]
    (.letOp (n := 116) (.exec 0x114a82 (fun s => s.RIP = 0x114a82) (andR64R64Effect 0x114a82 6 15) (Reg.operands [.gpr 6, .gpr 15] [])) #v[113, 95]
    (.letOp (n := 117) (.out 0x114a85 (xorR64M64Effect 0x114a85 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[115, 4]
    (.letOp (n := 118) (.exec 0x114a85 (LoadPre 0x114a85 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114a85 + BitVec.ofNat 64 5)) 8) (xorR64M64Effect 0x114a85 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[115, 4]
    (.letOp (n := 119) (.out 0x114a8a (xorR64R64Effect 0x114a8a 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[87, 12]
    (.letOp (n := 120) (.exec 0x114a8a (fun s => s.RIP = 0x114a8a) (xorR64R64Effect 0x114a8a 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[87, 12]
    (.letOp (n := 121) (.out 0x114a8d (andR64R64Effect 0x114a8d 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 0] []) (.reg (.gpr 7))) #v[119, 93]
    (.letOp (n := 122) (.exec 0x114a8d (fun s => s.RIP = 0x114a8d) (andR64R64Effect 0x114a8d 7 0) (Reg.operands [.gpr 7, .gpr 0] [])) #v[119, 93]
    (.letOp (n := 123) (.out 0x114a90 (xorR64R64Effect 0x114a90 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[121, 12]
    (.letOp (n := 124) (.exec 0x114a90 (fun s => s.RIP = 0x114a90) (xorR64R64Effect 0x114a90 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[121, 12]
    (.letOp (n := 125) (.out 0x114a93 (movR64M64Effect 0x114a93 0 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 126) (.exec 0x114a93 (LoadPre 0x114a93 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x114a93 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a93 0 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 127) (.exec 0x114a98 (StorePre 0x114a98 3 (fun s => AddrMode.addr (.base 0 .none) s (0x114a98 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x114a98 14 (.base 0 .none)) (Reg.operands [.gpr 14, .gpr 0] [])) #v[99, 125]
    (.letOp (n := 128) (.exec 0x114a9b (StorePre 0x114a9b 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x114a9b + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114a9b 1 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[105, 125]
    (.letOp (n := 129) (.exec 0x114a9f (StorePre 0x114a9f 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x114a9f + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x114a9f 2 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[111, 125]
    (b_l114a10_2)))))))))))))))))))))))))))))))))))))

def bytes_l114a10_1 : List UInt8 :=
  [0x48, 0xF7, 0xD8, 0x49, 0x21, 0xC7, 0x4D, 0x21, 0xFE, 0x4D, 0x31, 0xDE, 0x48, 0x33, 0x4C, 0x24,
    0x30, 0x4C, 0x21, 0xF9, 0x4C, 0x31, 0xD1, 0x48, 0x31, 0xDA, 0x4C, 0x21, 0xFA, 0x4C, 0x31, 0xC2,
    0x48, 0x31, 0xEE, 0x4C, 0x21, 0xFE, 0x48, 0x33, 0x74, 0x24, 0x08, 0x4C, 0x31, 0xE7, 0x48, 0x21,
    0xC7, 0x4C, 0x31, 0xE7, 0x48, 0x8B, 0x44, 0x24, 0x28, 0x4C, 0x89, 0x30, 0x48, 0x89, 0x48, 0x08,
    0x48, 0x89, 0x50, 0x10] ++ bytes_l114a10_2

theorem code_l114a10_1 : ∀ x ∈ codeRange 0x114a5f bytes_l114a10_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14a5f 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l114a10_2

@[cfg_block] def b_l114a10 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x114a10 (movR64M64Effect 0x114a10 11 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 4] []) (.reg (.gpr 11))) #v[4]
    (.letOp (n := 54) (.exec 0x114a10 (LoadPre 0x114a10 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x114a10 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a10 11 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x114a15 (addR64R64Effect 0x114a15 14 11) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 11] []) (.reg (.gpr 14))) #v[14, 53]
    (.letOp (n := 56) (.exec 0x114a15 (fun s => s.RIP = 0x114a15) (addR64R64Effect 0x114a15 14 11) (Reg.operands [.gpr 14, .gpr 11] [])) #v[14, 53]
    (.letOp (n := 57) (.out 0x114a18 (movR64R64Effect 0x114a18 1 14) (EffectPart.reads (.reg (.gpr 1)) [.gpr 14] []) (.reg (.gpr 1))) #v[55]
    (.letOp (n := 58) (.exec 0x114a18 (fun s => s.RIP = 0x114a18) (movR64R64Effect 0x114a18 1 14) (Reg.operands [.gpr 14] [])) #v[55]
    (.letOp (n := 59) (.out 0x114a1b (shrR64Effect 0x114a1b 4 1 52) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x114a1b (fun s => s.RIP = 0x114a1b) (shrR64Effect 0x114a1b 4 1 52) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x114a1f (movR64M64Effect 0x114a1f 10 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 62) (.exec 0x114a1f (LoadPre 0x114a1f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x114a1f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a1f 10 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 63) (.out 0x114a24 (addR64R64Effect 0x114a24 1 10) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 10] []) (.reg (.gpr 1))) #v[59, 61]
    (.letOp (n := 64) (.exec 0x114a24 (fun s => s.RIP = 0x114a24) (addR64R64Effect 0x114a24 1 10) (Reg.operands [.gpr 1, .gpr 10] [])) #v[59, 61]
    (.letOp (n := 65) (.out 0x114a27 (movR64R64Effect 0x114a27 2 1) (EffectPart.reads (.reg (.gpr 2)) [.gpr 1] []) (.reg (.gpr 2))) #v[63]
    (.letOp (n := 66) (.exec 0x114a27 (fun s => s.RIP = 0x114a27) (movR64R64Effect 0x114a27 2 1) (Reg.operands [.gpr 1] [])) #v[63]
    (.letOp (n := 67) (.out 0x114a2a (shrR64Effect 0x114a2a 4 2 52) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[65]
    (.letOp (n := 68) (.exec 0x114a2a (fun s => s.RIP = 0x114a2a) (shrR64Effect 0x114a2a 4 2 52) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[65]
    (.letOp (n := 69) (.out 0x114a2e (movR64M64Effect 0x114a2e 8 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 4] []) (.reg (.gpr 8))) #v[4]
    (.letOp (n := 70) (.exec 0x114a2e (LoadPre 0x114a2e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x114a2e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x114a2e 8 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 71) (.out 0x114a33 (addR64R64Effect 0x114a33 2 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 8] []) (.reg (.gpr 2))) #v[67, 69]
    (.letOp (n := 72) (.exec 0x114a33 (fun s => s.RIP = 0x114a33) (addR64R64Effect 0x114a33 2 8) (Reg.operands [.gpr 2, .gpr 8] [])) #v[67, 69]
    (.letOp (n := 73) (.out 0x114a36 (movR64R64Effect 0x114a36 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[71]
    (.letOp (n := 74) (.exec 0x114a36 (fun s => s.RIP = 0x114a36) (movR64R64Effect 0x114a36 6 2) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.out 0x114a39 (shrR64Effect 0x114a39 4 6 52) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[73]
    (.letOp (n := 76) (.exec 0x114a39 (fun s => s.RIP = 0x114a39) (shrR64Effect 0x114a39 4 6 52) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.out 0x114a3d (addR64M64Effect 0x114a3d 6 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4] []) (.reg (.gpr 6))) #v[75, 4]
    (.letOp (n := 78) (.exec 0x114a3d (LoadPre 0x114a3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x114a3d + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x114a3d 6 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[75, 4]
    (.letOp (n := 79) (.out 0x114a42 (movR64R64Effect 0x114a42 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[77]
    (.letOp (n := 80) (.exec 0x114a42 (fun s => s.RIP = 0x114a42) (movR64R64Effect 0x114a42 7 6) (Reg.operands [.gpr 6] [])) #v[77]
    (.letOp (n := 81) (.out 0x114a45 (shrR64Effect 0x114a45 4 7 52) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[79]
    (.letOp (n := 82) (.exec 0x114a45 (fun s => s.RIP = 0x114a45) (shrR64Effect 0x114a45 4 7 52) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.out 0x114a49 (addR64R64Effect 0x114a49 7 12) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 12] []) (.reg (.gpr 7))) #v[81, 12]
    (.letOp (n := 84) (.exec 0x114a49 (fun s => s.RIP = 0x114a49) (addR64R64Effect 0x114a49 7 12) (Reg.operands [.gpr 7, .gpr 12] [])) #v[81, 12]
    (.letOp (n := 85) (.out 0x114a4c (movR64Imm64Effect 0x114a4c 9 0xffffffffffff) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 86) (.exec 0x114a4c (fun s => s.RIP = 0x114a4c) (movR64Imm64Effect 0x114a4c 9 0xffffffffffff) (Reg.operands [] [])) #v[]
    (.letOp (n := 87) (.out 0x114a56 (andR64R64Effect 0x114a56 7 9) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 9] []) (.reg (.gpr 7))) #v[83, 85]
    (.letOp (n := 88) (.exec 0x114a56 (fun s => s.RIP = 0x114a56) (andR64R64Effect 0x114a56 7 9) (Reg.operands [.gpr 7, .gpr 9] [])) #v[83, 85]
    (.letOp (n := 89) (.out 0x114a59 (xorR64R64Effect 0x114a59 14 13) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 13] []) (.reg (.gpr 14))) #v[55, 13]
    (.letOp (n := 90) (.exec 0x114a59 (fun s => s.RIP = 0x114a59) (xorR64R64Effect 0x114a59 14 13) (Reg.operands [.gpr 14, .gpr 13] [])) #v[55, 13]
    (.letOp (n := 91) (.out 0x114a5c (movzxR32R8Effect 0x114a5c 3 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 92) (.exec 0x114a5c (fun s => s.RIP = 0x114a5c) (movzxR32R8Effect 0x114a5c 3 0 0) (Reg.operands [.gpr 0] [])) #v[0]
    (b_l114a10_1))))))))))))))))))))))))))))))))))))))))

def bytes_l114a10 : List UInt8 :=
  [0x4C, 0x8B, 0x5C, 0x24, 0x10, 0x4D, 0x01, 0xDE, 0x4C, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x34, 0x4C,
    0x8B, 0x54, 0x24, 0x18, 0x4C, 0x01, 0xD1, 0x48, 0x89, 0xCA, 0x48, 0xC1, 0xEA, 0x34, 0x4C, 0x8B,
    0x44, 0x24, 0x20, 0x4C, 0x01, 0xC2, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x34, 0x48, 0x03, 0x74,
    0x24, 0x08, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x34, 0x4C, 0x01, 0xE7, 0x49, 0xB9, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x4C, 0x21, 0xCF, 0x4D, 0x31, 0xEE, 0x0F, 0xB6, 0xC0] ++ bytes_l114a10_1

theorem code_l114a10 : ∀ x ∈ codeRange 0x114a10 bytes_l114a10, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x14a10 79 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l114a10_1

@[cfg_block] def b_l11aa40_5 : Block Op Label signature Reg.count 226 :=
  .letOp (n := 226) (.exec 0x11abb6 (StorePre 0x11abb6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1a)) s (0x11abb6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abb6 5 7 (.sib 4 none 0 (.d8 0x1a))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[224, 53]
    (.letOp (n := 227) (.out 0x11abbb (shrR8Effect 0x11abbb 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[220]
    (.letOp (n := 228) (.exec 0x11abbb (fun s => s.RIP = 0x11abbb) (shrR8Effect 0x11abbb 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[220]
    (.letOp (n := 229) (.exec 0x11abbf (StorePre 0x11abbf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1b)) s (0x11abbf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abbf 5 6 (.sib 4 none 0 (.d8 0x1b))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[227, 53]
    (.letOp (n := 230) (.out 0x11abc4 (movR32R32Effect 0x11abc4 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 231) (.exec 0x11abc4 (fun s => s.RIP = 0x11abc4) (movR32R32Effect 0x11abc4 2 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 232) (.out 0x11abc6 (shrR32Effect 0x11abc6 3 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[230]
    (.letOp (n := 233) (.exec 0x11abc6 (fun s => s.RIP = 0x11abc6) (shrR32Effect 0x11abc6 3 6 8) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[230]
    (.letOp (n := 234) (.out 0x11abc9 (movR32R32Effect 0x11abc9 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[232]
    (.letOp (n := 235) (.exec 0x11abc9 (fun s => s.RIP = 0x11abc9) (movR32R32Effect 0x11abc9 2 7 6) (Reg.operands [.gpr 6] [])) #v[232]
    (.letOp (n := 236) (.out 0x11abcb (andR8Imm8Effect 0x11abcb 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[234]
    (.letOp (n := 237) (.exec 0x11abcb (fun s => s.RIP = 0x11abcb) (andR8Imm8Effect 0x11abcb 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[234]
    (.letOp (n := 238) (.exec 0x11abcf (StorePre 0x11abcf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1c)) s (0x11abcf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abcf 5 7 (.sib 4 none 0 (.d8 0x1c))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[236, 53]
    (.letOp (n := 239) (.out 0x11abd4 (shrR8Effect 0x11abd4 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[232]
    (.letOp (n := 240) (.exec 0x11abd4 (fun s => s.RIP = 0x11abd4) (shrR8Effect 0x11abd4 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[232]
    (.letOp (n := 241) (.exec 0x11abd8 (StorePre 0x11abd8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1d)) s (0x11abd8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abd8 5 6 (.sib 4 none 0 (.d8 0x1d))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[239, 53]
    (.letOp (n := 242) (.out 0x11abdd (movR32R32Effect 0x11abdd 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 243) (.exec 0x11abdd (fun s => s.RIP = 0x11abdd) (movR32R32Effect 0x11abdd 2 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 244) (.out 0x11abdf (andR8Imm8Effect 0x11abdf 4 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[242]
    (.letOp (n := 245) (.exec 0x11abdf (fun s => s.RIP = 0x11abdf) (andR8Imm8Effect 0x11abdf 4 6 0xf) (Reg.operands [.gpr 6] [])) #v[242]
    (.letOp (n := 246) (.exec 0x11abe3 (StorePre 0x11abe3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1e)) s (0x11abe3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11abe3 5 6 (.sib 4 none 0 (.d8 0x1e))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[244, 53]
    (.letOp (n := 247) (.out 0x11abe8 (shrR8Effect 0x11abe8 3 2 4) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[60]
    (.letOp (n := 248) (.exec 0x11abe8 (fun s => s.RIP = 0x11abe8) (shrR8Effect 0x11abe8 3 2 4) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[60]
    (.letOp (n := 249) (.exec 0x11abeb (StorePre 0x11abeb 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1f)) s (0x11abeb + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11abeb 4 2 (.sib 4 none 0 (.d8 0x1f))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[247, 53]
    (.letOp (n := 250) (.out 0x11abef (movR32Imm32Effect 0x11abef 5 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 251) (.exec 0x11abef (fun s => s.RIP = 0x11abef) (movR32Imm32Effect 0x11abef 5 2 0x2) (Reg.operands [] [])) #v[]
    (.letOp (n := 252) (.exec 0x11abf4 (fun s => s.RIP = 0x11abf4) (fun _ => nopEffect 0x11abf4 12) (Reg.operands [] [])) #v[]
    (.terminate (.br ⟨.l11ac00, RegMap.args [(0, 55), (1, 70), (2, 250), (3, 3), (4, 53), (5, 5), (6, 244), (7, 236), (8, 144), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 253⟩))))))))))))))))))))))))))))

def bytes_l11aa40_5 : List UInt8 :=
  [0x40, 0x88, 0x7C, 0x24, 0x1A, 0x40, 0xC0, 0xEE, 0x04, 0x40, 0x88, 0x74, 0x24, 0x1B, 0x89, 0xD6,
    0xC1, 0xEE, 0x08, 0x89, 0xF7, 0x40, 0x80, 0xE7, 0x0F, 0x40, 0x88, 0x7C, 0x24, 0x1C, 0x40, 0xC0,
    0xEE, 0x04, 0x40, 0x88, 0x74, 0x24, 0x1D, 0x89, 0xD6, 0x40, 0x80, 0xE6, 0x0F, 0x40, 0x88, 0x74,
    0x24, 0x1E, 0xC0, 0xEA, 0x04, 0x88, 0x54, 0x24, 0x1F, 0xBA, 0x02, 0x00, 0x00, 0x00, 0x66, 0x66,
    0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem code_l11aa40_5 : ∀ x ∈ codeRange 0x11abb6 bytes_l11aa40_5, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1abb6 74 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11aa40_4 : Block Op Label signature Reg.count 191 :=
  .letOp (n := 191) (.out 0x11ab6f (shrR8Effect 0x11ab6f 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[184]
    (.letOp (n := 192) (.exec 0x11ab6f (fun s => s.RIP = 0x11ab6f) (shrR8Effect 0x11ab6f 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[184]
    (.letOp (n := 193) (.exec 0x11ab73 (StorePre 0x11ab73 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x15)) s (0x11ab73 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab73 5 6 (.sib 4 none 0 (.d8 0x15))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[191, 53]
    (.letOp (n := 194) (.out 0x11ab78 (movR64R64Effect 0x11ab78 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 195) (.exec 0x11ab78 (fun s => s.RIP = 0x11ab78) (movR64R64Effect 0x11ab78 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 196) (.out 0x11ab7b (shrR64Effect 0x11ab7b 4 6 32) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[194]
    (.letOp (n := 197) (.exec 0x11ab7b (fun s => s.RIP = 0x11ab7b) (shrR64Effect 0x11ab7b 4 6 32) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[194]
    (.letOp (n := 198) (.out 0x11ab7f (movR32R32Effect 0x11ab7f 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[196]
    (.letOp (n := 199) (.exec 0x11ab7f (fun s => s.RIP = 0x11ab7f) (movR32R32Effect 0x11ab7f 2 7 6) (Reg.operands [.gpr 6] [])) #v[196]
    (.letOp (n := 200) (.out 0x11ab81 (andR8Imm8Effect 0x11ab81 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[198]
    (.letOp (n := 201) (.exec 0x11ab81 (fun s => s.RIP = 0x11ab81) (andR8Imm8Effect 0x11ab81 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[198]
    (.letOp (n := 202) (.exec 0x11ab85 (StorePre 0x11ab85 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x16)) s (0x11ab85 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab85 5 7 (.sib 4 none 0 (.d8 0x16))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[200, 53]
    (.letOp (n := 203) (.out 0x11ab8a (shrR8Effect 0x11ab8a 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[196]
    (.letOp (n := 204) (.exec 0x11ab8a (fun s => s.RIP = 0x11ab8a) (shrR8Effect 0x11ab8a 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[196]
    (.letOp (n := 205) (.exec 0x11ab8e (StorePre 0x11ab8e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x17)) s (0x11ab8e + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab8e 5 6 (.sib 4 none 0 (.d8 0x17))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[203, 53]
    (.letOp (n := 206) (.out 0x11ab93 (movR32R32Effect 0x11ab93 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 207) (.exec 0x11ab93 (fun s => s.RIP = 0x11ab93) (movR32R32Effect 0x11ab93 2 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 208) (.out 0x11ab95 (shrR32Effect 0x11ab95 3 6 24) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[206]
    (.letOp (n := 209) (.exec 0x11ab95 (fun s => s.RIP = 0x11ab95) (shrR32Effect 0x11ab95 3 6 24) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[206]
    (.letOp (n := 210) (.out 0x11ab98 (andR8Imm8Effect 0x11ab98 4 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[208]
    (.letOp (n := 211) (.exec 0x11ab98 (fun s => s.RIP = 0x11ab98) (andR8Imm8Effect 0x11ab98 4 6 0xf) (Reg.operands [.gpr 6] [])) #v[208]
    (.letOp (n := 212) (.exec 0x11ab9c (StorePre 0x11ab9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ab9c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab9c 5 6 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[210, 53]
    (.letOp (n := 213) (.out 0x11aba1 (movR32R32Effect 0x11aba1 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 214) (.exec 0x11aba1 (fun s => s.RIP = 0x11aba1) (movR32R32Effect 0x11aba1 2 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 215) (.out 0x11aba3 (shrR32Effect 0x11aba3 3 6 28) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[213]
    (.letOp (n := 216) (.exec 0x11aba3 (fun s => s.RIP = 0x11aba3) (shrR32Effect 0x11aba3 3 6 28) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[213]
    (.letOp (n := 217) (.exec 0x11aba6 (StorePre 0x11aba6 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x19)) s (0x11aba6 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aba6 5 6 (.sib 4 none 0 (.d8 0x19))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[215, 53]
    (.letOp (n := 218) (.out 0x11abab (movR32R32Effect 0x11abab 2 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 219) (.exec 0x11abab (fun s => s.RIP = 0x11abab) (movR32R32Effect 0x11abab 2 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 220) (.out 0x11abad (shrR32Effect 0x11abad 3 6 16) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[218]
    (.letOp (n := 221) (.exec 0x11abad (fun s => s.RIP = 0x11abad) (shrR32Effect 0x11abad 3 6 16) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[218]
    (.letOp (n := 222) (.out 0x11abb0 (movR32R32Effect 0x11abb0 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[220]
    (.letOp (n := 223) (.exec 0x11abb0 (fun s => s.RIP = 0x11abb0) (movR32R32Effect 0x11abb0 2 7 6) (Reg.operands [.gpr 6] [])) #v[220]
    (.letOp (n := 224) (.out 0x11abb2 (andR8Imm8Effect 0x11abb2 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[222]
    (.letOp (n := 225) (.exec 0x11abb2 (fun s => s.RIP = 0x11abb2) (andR8Imm8Effect 0x11abb2 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[222]
    (b_l11aa40_5)))))))))))))))))))))))))))))))))))

def bytes_l11aa40_4 : List UInt8 :=
  [0x40, 0xC0, 0xEE, 0x04, 0x40, 0x88, 0x74, 0x24, 0x15, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x20,
    0x89, 0xF7, 0x40, 0x80, 0xE7, 0x0F, 0x40, 0x88, 0x7C, 0x24, 0x16, 0x40, 0xC0, 0xEE, 0x04, 0x40,
    0x88, 0x74, 0x24, 0x17, 0x89, 0xD6, 0xC1, 0xEE, 0x18, 0x40, 0x80, 0xE6, 0x0F, 0x40, 0x88, 0x74,
    0x24, 0x18, 0x89, 0xD6, 0xC1, 0xEE, 0x1C, 0x40, 0x88, 0x74, 0x24, 0x19, 0x89, 0xD6, 0xC1, 0xEE,
    0x10, 0x89, 0xF7, 0x40, 0x80, 0xE7, 0x0F] ++ bytes_l11aa40_5

theorem code_l11aa40_4 : ∀ x ∈ codeRange 0x11ab6f bytes_l11aa40_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ab6f 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11aa40_5

@[cfg_block] def b_l11aa40_3 : Block Op Label signature Reg.count 157 :=
  .letOp (n := 157) (.exec 0x11ab21 (StorePre 0x11ab21 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xf)) s (0x11ab21 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab21 5 6 (.sib 4 none 0 (.d8 0xf))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[155, 53]
    (.letOp (n := 158) (.out 0x11ab26 (movR64R64Effect 0x11ab26 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 159) (.exec 0x11ab26 (fun s => s.RIP = 0x11ab26) (movR64R64Effect 0x11ab26 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 160) (.out 0x11ab29 (shrR64Effect 0x11ab29 4 6 56) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[158]
    (.letOp (n := 161) (.exec 0x11ab29 (fun s => s.RIP = 0x11ab29) (shrR64Effect 0x11ab29 4 6 56) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[158]
    (.letOp (n := 162) (.out 0x11ab2d (andR8Imm8Effect 0x11ab2d 4 6 0xf) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[160]
    (.letOp (n := 163) (.exec 0x11ab2d (fun s => s.RIP = 0x11ab2d) (andR8Imm8Effect 0x11ab2d 4 6 0xf) (Reg.operands [.gpr 6] [])) #v[160]
    (.letOp (n := 164) (.exec 0x11ab31 (StorePre 0x11ab31 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ab31 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab31 5 6 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[162, 53]
    (.letOp (n := 165) (.out 0x11ab36 (movR64R64Effect 0x11ab36 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 166) (.exec 0x11ab36 (fun s => s.RIP = 0x11ab36) (movR64R64Effect 0x11ab36 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 167) (.out 0x11ab39 (shrR64Effect 0x11ab39 4 6 60) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[165]
    (.letOp (n := 168) (.exec 0x11ab39 (fun s => s.RIP = 0x11ab39) (shrR64Effect 0x11ab39 4 6 60) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[165]
    (.letOp (n := 169) (.exec 0x11ab3d (StorePre 0x11ab3d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x11)) s (0x11ab3d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab3d 5 6 (.sib 4 none 0 (.d8 0x11))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[167, 53]
    (.letOp (n := 170) (.out 0x11ab42 (movR64R64Effect 0x11ab42 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 171) (.exec 0x11ab42 (fun s => s.RIP = 0x11ab42) (movR64R64Effect 0x11ab42 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 172) (.out 0x11ab45 (shrR64Effect 0x11ab45 4 6 48) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[170]
    (.letOp (n := 173) (.exec 0x11ab45 (fun s => s.RIP = 0x11ab45) (shrR64Effect 0x11ab45 4 6 48) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[170]
    (.letOp (n := 174) (.out 0x11ab49 (movR32R32Effect 0x11ab49 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[172]
    (.letOp (n := 175) (.exec 0x11ab49 (fun s => s.RIP = 0x11ab49) (movR32R32Effect 0x11ab49 2 7 6) (Reg.operands [.gpr 6] [])) #v[172]
    (.letOp (n := 176) (.out 0x11ab4b (andR8Imm8Effect 0x11ab4b 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[174]
    (.letOp (n := 177) (.exec 0x11ab4b (fun s => s.RIP = 0x11ab4b) (andR8Imm8Effect 0x11ab4b 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[174]
    (.letOp (n := 178) (.exec 0x11ab4f (StorePre 0x11ab4f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x12)) s (0x11ab4f + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab4f 5 7 (.sib 4 none 0 (.d8 0x12))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[176, 53]
    (.letOp (n := 179) (.out 0x11ab54 (shrR8Effect 0x11ab54 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[172]
    (.letOp (n := 180) (.exec 0x11ab54 (fun s => s.RIP = 0x11ab54) (shrR8Effect 0x11ab54 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[172]
    (.letOp (n := 181) (.exec 0x11ab58 (StorePre 0x11ab58 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x13)) s (0x11ab58 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab58 5 6 (.sib 4 none 0 (.d8 0x13))) (Reg.operands [.gpr 6, .gpr 4] [])) #v[179, 53]
    (.letOp (n := 182) (.out 0x11ab5d (movR64R64Effect 0x11ab5d 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 2] []) (.reg (.gpr 6))) #v[60]
    (.letOp (n := 183) (.exec 0x11ab5d (fun s => s.RIP = 0x11ab5d) (movR64R64Effect 0x11ab5d 6 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 184) (.out 0x11ab60 (shrR64Effect 0x11ab60 4 6 40) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[182]
    (.letOp (n := 185) (.exec 0x11ab60 (fun s => s.RIP = 0x11ab60) (shrR64Effect 0x11ab60 4 6 40) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[182]
    (.letOp (n := 186) (.out 0x11ab64 (movR32R32Effect 0x11ab64 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[184]
    (.letOp (n := 187) (.exec 0x11ab64 (fun s => s.RIP = 0x11ab64) (movR32R32Effect 0x11ab64 2 7 6) (Reg.operands [.gpr 6] [])) #v[184]
    (.letOp (n := 188) (.out 0x11ab66 (andR8Imm8Effect 0x11ab66 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[186]
    (.letOp (n := 189) (.exec 0x11ab66 (fun s => s.RIP = 0x11ab66) (andR8Imm8Effect 0x11ab66 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[186]
    (.letOp (n := 190) (.exec 0x11ab6a (StorePre 0x11ab6a 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x14)) s (0x11ab6a + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab6a 5 7 (.sib 4 none 0 (.d8 0x14))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[188, 53]
    (b_l11aa40_4))))))))))))))))))))))))))))))))))

def bytes_l11aa40_3 : List UInt8 :=
  [0x40, 0x88, 0x74, 0x24, 0x0F, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x38, 0x40, 0x80, 0xE6, 0x0F,
    0x40, 0x88, 0x74, 0x24, 0x10, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x3C, 0x40, 0x88, 0x74, 0x24,
    0x11, 0x48, 0x89, 0xD6, 0x48, 0xC1, 0xEE, 0x30, 0x89, 0xF7, 0x40, 0x80, 0xE7, 0x0F, 0x40, 0x88,
    0x7C, 0x24, 0x12, 0x40, 0xC0, 0xEE, 0x04, 0x40, 0x88, 0x74, 0x24, 0x13, 0x48, 0x89, 0xD6, 0x48,
    0xC1, 0xEE, 0x28, 0x89, 0xF7, 0x40, 0x80, 0xE7, 0x0F, 0x40, 0x88, 0x7C, 0x24, 0x14] ++ bytes_l11aa40_4

theorem code_l11aa40_3 : ∀ x ∈ codeRange 0x11ab21 bytes_l11aa40_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1ab21 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11aa40_4

@[cfg_block] def b_l11aa40_2 : Block Op Label signature Reg.count 123 :=
  .letOp (n := 123) (.out 0x11aad6 (shrR32Effect 0x11aad6 3 7 28) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[121]
    (.letOp (n := 124) (.exec 0x11aad6 (fun s => s.RIP = 0x11aad6) (shrR32Effect 0x11aad6 3 7 28) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[121]
    (.letOp (n := 125) (.exec 0x11aad9 (StorePre 0x11aad9 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x9)) s (0x11aad9 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aad9 5 7 (.sib 4 none 0 (.d8 0x9))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[123, 53]
    (.letOp (n := 126) (.out 0x11aade (movR32R32Effect 0x11aade 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 127) (.exec 0x11aade (fun s => s.RIP = 0x11aade) (movR32R32Effect 0x11aade 2 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 128) (.out 0x11aae0 (shrR32Effect 0x11aae0 3 7 16) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[126]
    (.letOp (n := 129) (.exec 0x11aae0 (fun s => s.RIP = 0x11aae0) (shrR32Effect 0x11aae0 3 7 16) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[126]
    (.letOp (n := 130) (.out 0x11aae3 (movR32R32Effect 0x11aae3 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[128]
    (.letOp (n := 131) (.exec 0x11aae3 (fun s => s.RIP = 0x11aae3) (movR32R32Effect 0x11aae3 3 8 7) (Reg.operands [.gpr 7] [])) #v[128]
    (.letOp (n := 132) (.out 0x11aae6 (andR8Imm8Effect 0x11aae6 4 8 0xf) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[130]
    (.letOp (n := 133) (.exec 0x11aae6 (fun s => s.RIP = 0x11aae6) (andR8Imm8Effect 0x11aae6 4 8 0xf) (Reg.operands [.gpr 8] [])) #v[130]
    (.letOp (n := 134) (.exec 0x11aaea (StorePre 0x11aaea 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xa)) s (0x11aaea + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaea 5 8 (.sib 4 none 0 (.d8 0xa))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[132, 53]
    (.letOp (n := 135) (.out 0x11aaef (shrR8Effect 0x11aaef 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[128]
    (.letOp (n := 136) (.exec 0x11aaef (fun s => s.RIP = 0x11aaef) (shrR8Effect 0x11aaef 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[128]
    (.letOp (n := 137) (.exec 0x11aaf3 (StorePre 0x11aaf3 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xb)) s (0x11aaf3 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaf3 5 7 (.sib 4 none 0 (.d8 0xb))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[135, 53]
    (.letOp (n := 138) (.out 0x11aaf8 (movR32R32Effect 0x11aaf8 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 139) (.exec 0x11aaf8 (fun s => s.RIP = 0x11aaf8) (movR32R32Effect 0x11aaf8 2 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 140) (.out 0x11aafa (shrR32Effect 0x11aafa 3 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[138]
    (.letOp (n := 141) (.exec 0x11aafa (fun s => s.RIP = 0x11aafa) (shrR32Effect 0x11aafa 3 7 8) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[138]
    (.letOp (n := 142) (.out 0x11aafd (movR32R32Effect 0x11aafd 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[140]
    (.letOp (n := 143) (.exec 0x11aafd (fun s => s.RIP = 0x11aafd) (movR32R32Effect 0x11aafd 3 8 7) (Reg.operands [.gpr 7] [])) #v[140]
    (.letOp (n := 144) (.out 0x11ab00 (andR8Imm8Effect 0x11ab00 4 8 0xf) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[142]
    (.letOp (n := 145) (.exec 0x11ab00 (fun s => s.RIP = 0x11ab00) (andR8Imm8Effect 0x11ab00 4 8 0xf) (Reg.operands [.gpr 8] [])) #v[142]
    (.letOp (n := 146) (.exec 0x11ab04 (StorePre 0x11ab04 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xc)) s (0x11ab04 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab04 5 8 (.sib 4 none 0 (.d8 0xc))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[144, 53]
    (.letOp (n := 147) (.out 0x11ab09 (shrR8Effect 0x11ab09 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[140]
    (.letOp (n := 148) (.exec 0x11ab09 (fun s => s.RIP = 0x11ab09) (shrR8Effect 0x11ab09 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[140]
    (.letOp (n := 149) (.exec 0x11ab0d (StorePre 0x11ab0d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xd)) s (0x11ab0d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab0d 5 7 (.sib 4 none 0 (.d8 0xd))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[147, 53]
    (.letOp (n := 150) (.out 0x11ab12 (movR32R32Effect 0x11ab12 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 151) (.exec 0x11ab12 (fun s => s.RIP = 0x11ab12) (movR32R32Effect 0x11ab12 2 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 152) (.out 0x11ab14 (andR8Imm8Effect 0x11ab14 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[150]
    (.letOp (n := 153) (.exec 0x11ab14 (fun s => s.RIP = 0x11ab14) (andR8Imm8Effect 0x11ab14 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[150]
    (.letOp (n := 154) (.exec 0x11ab18 (StorePre 0x11ab18 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0xe)) s (0x11ab18 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ab18 5 7 (.sib 4 none 0 (.d8 0xe))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[152, 53]
    (.letOp (n := 155) (.out 0x11ab1d (shrR8Effect 0x11ab1d 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[64]
    (.letOp (n := 156) (.exec 0x11ab1d (fun s => s.RIP = 0x11ab1d) (shrR8Effect 0x11ab1d 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[64]
    (b_l11aa40_3))))))))))))))))))))))))))))))))))

def bytes_l11aa40_2 : List UInt8 :=
  [0xC1, 0xEF, 0x1C, 0x40, 0x88, 0x7C, 0x24, 0x09, 0x89, 0xF7, 0xC1, 0xEF, 0x10, 0x41, 0x89, 0xF8,
    0x41, 0x80, 0xE0, 0x0F, 0x44, 0x88, 0x44, 0x24, 0x0A, 0x40, 0xC0, 0xEF, 0x04, 0x40, 0x88, 0x7C,
    0x24, 0x0B, 0x89, 0xF7, 0xC1, 0xEF, 0x08, 0x41, 0x89, 0xF8, 0x41, 0x80, 0xE0, 0x0F, 0x44, 0x88,
    0x44, 0x24, 0x0C, 0x40, 0xC0, 0xEF, 0x04, 0x40, 0x88, 0x7C, 0x24, 0x0D, 0x89, 0xF7, 0x40, 0x80,
    0xE7, 0x0F, 0x40, 0x88, 0x7C, 0x24, 0x0E, 0x40, 0xC0, 0xEE, 0x04] ++ bytes_l11aa40_3

theorem code_l11aa40_2 : ∀ x ∈ codeRange 0x11aad6 bytes_l11aa40_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1aad6 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11aa40_3

@[cfg_block] def b_l11aa40_1 : Block Op Label signature Reg.count 89 :=
  .letOp (n := 89) (.exec 0x11aa89 (StorePre 0x11aa89 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x3)) s (0x11aa89 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa89 5 7 (.sib 4 none 0 (.d8 0x3))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[87, 53]
    (.letOp (n := 90) (.out 0x11aa8e (movR64R64Effect 0x11aa8e 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 91) (.exec 0x11aa8e (fun s => s.RIP = 0x11aa8e) (movR64R64Effect 0x11aa8e 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 92) (.out 0x11aa91 (shrR64Effect 0x11aa91 4 7 40) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[90]
    (.letOp (n := 93) (.exec 0x11aa91 (fun s => s.RIP = 0x11aa91) (shrR64Effect 0x11aa91 4 7 40) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[90]
    (.letOp (n := 94) (.out 0x11aa95 (movR32R32Effect 0x11aa95 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[92]
    (.letOp (n := 95) (.exec 0x11aa95 (fun s => s.RIP = 0x11aa95) (movR32R32Effect 0x11aa95 3 8 7) (Reg.operands [.gpr 7] [])) #v[92]
    (.letOp (n := 96) (.out 0x11aa98 (andR8Imm8Effect 0x11aa98 4 8 0xf) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[94]
    (.letOp (n := 97) (.exec 0x11aa98 (fun s => s.RIP = 0x11aa98) (andR8Imm8Effect 0x11aa98 4 8 0xf) (Reg.operands [.gpr 8] [])) #v[94]
    (.letOp (n := 98) (.exec 0x11aa9c (StorePre 0x11aa9c 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x4)) s (0x11aa9c + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa9c 5 8 (.sib 4 none 0 (.d8 0x4))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[96, 53]
    (.letOp (n := 99) (.out 0x11aaa1 (shrR8Effect 0x11aaa1 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[92]
    (.letOp (n := 100) (.exec 0x11aaa1 (fun s => s.RIP = 0x11aaa1) (shrR8Effect 0x11aaa1 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[92]
    (.letOp (n := 101) (.exec 0x11aaa5 (StorePre 0x11aaa5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x5)) s (0x11aaa5 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aaa5 5 7 (.sib 4 none 0 (.d8 0x5))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[99, 53]
    (.letOp (n := 102) (.out 0x11aaaa (movR64R64Effect 0x11aaaa 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 103) (.exec 0x11aaaa (fun s => s.RIP = 0x11aaaa) (movR64R64Effect 0x11aaaa 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 104) (.out 0x11aaad (shrR64Effect 0x11aaad 4 7 32) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[102]
    (.letOp (n := 105) (.exec 0x11aaad (fun s => s.RIP = 0x11aaad) (shrR64Effect 0x11aaad 4 7 32) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[102]
    (.letOp (n := 106) (.out 0x11aab1 (movR32R32Effect 0x11aab1 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[104]
    (.letOp (n := 107) (.exec 0x11aab1 (fun s => s.RIP = 0x11aab1) (movR32R32Effect 0x11aab1 3 8 7) (Reg.operands [.gpr 7] [])) #v[104]
    (.letOp (n := 108) (.out 0x11aab4 (andR8Imm8Effect 0x11aab4 4 8 0xf) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[106]
    (.letOp (n := 109) (.exec 0x11aab4 (fun s => s.RIP = 0x11aab4) (andR8Imm8Effect 0x11aab4 4 8 0xf) (Reg.operands [.gpr 8] [])) #v[106]
    (.letOp (n := 110) (.exec 0x11aab8 (StorePre 0x11aab8 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x6)) s (0x11aab8 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aab8 5 8 (.sib 4 none 0 (.d8 0x6))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[108, 53]
    (.letOp (n := 111) (.out 0x11aabd (shrR8Effect 0x11aabd 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[104]
    (.letOp (n := 112) (.exec 0x11aabd (fun s => s.RIP = 0x11aabd) (shrR8Effect 0x11aabd 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[104]
    (.letOp (n := 113) (.exec 0x11aac1 (StorePre 0x11aac1 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x7)) s (0x11aac1 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aac1 5 7 (.sib 4 none 0 (.d8 0x7))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[111, 53]
    (.letOp (n := 114) (.out 0x11aac6 (movR32R32Effect 0x11aac6 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 115) (.exec 0x11aac6 (fun s => s.RIP = 0x11aac6) (movR32R32Effect 0x11aac6 2 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 116) (.out 0x11aac8 (shrR32Effect 0x11aac8 3 7 24) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[114]
    (.letOp (n := 117) (.exec 0x11aac8 (fun s => s.RIP = 0x11aac8) (shrR32Effect 0x11aac8 3 7 24) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[114]
    (.letOp (n := 118) (.out 0x11aacb (andR8Imm8Effect 0x11aacb 4 7 0xf) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[116]
    (.letOp (n := 119) (.exec 0x11aacb (fun s => s.RIP = 0x11aacb) (andR8Imm8Effect 0x11aacb 4 7 0xf) (Reg.operands [.gpr 7] [])) #v[116]
    (.letOp (n := 120) (.exec 0x11aacf (StorePre 0x11aacf 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11aacf + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aacf 5 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[118, 53]
    (.letOp (n := 121) (.out 0x11aad4 (movR32R32Effect 0x11aad4 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 122) (.exec 0x11aad4 (fun s => s.RIP = 0x11aad4) (movR32R32Effect 0x11aad4 2 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (b_l11aa40_2))))))))))))))))))))))))))))))))))

def bytes_l11aa40_1 : List UInt8 :=
  [0x40, 0x88, 0x7C, 0x24, 0x03, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x28, 0x41, 0x89, 0xF8, 0x41,
    0x80, 0xE0, 0x0F, 0x44, 0x88, 0x44, 0x24, 0x04, 0x40, 0xC0, 0xEF, 0x04, 0x40, 0x88, 0x7C, 0x24,
    0x05, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x20, 0x41, 0x89, 0xF8, 0x41, 0x80, 0xE0, 0x0F, 0x44,
    0x88, 0x44, 0x24, 0x06, 0x40, 0xC0, 0xEF, 0x04, 0x40, 0x88, 0x7C, 0x24, 0x07, 0x89, 0xF7, 0xC1,
    0xEF, 0x18, 0x40, 0x80, 0xE7, 0x0F, 0x40, 0x88, 0x7C, 0x24, 0x08, 0x89, 0xF7] ++ bytes_l11aa40_2

theorem code_l11aa40_1 : ∀ x ∈ codeRange 0x11aa89 bytes_l11aa40_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1aa89 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11aa40_2

@[cfg_block] def b_l11aa40 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11aa40 (subR64Imm8Effect 0x11aa40 4 0x21) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 54) (.exec 0x11aa40 (fun s => s.RIP = 0x11aa40) (subR64Imm8Effect 0x11aa40 4 0x21) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11aa44 (movR64R64Effect 0x11aa44 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[7]
    (.letOp (n := 56) (.exec 0x11aa44 (fun s => s.RIP = 0x11aa44) (movR64R64Effect 0x11aa44 0 7) (Reg.operands [.gpr 7] [])) #v[7]
    (.letOp (n := 57) (.exec 0x11aa47 (StorePre 0x11aa47 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11aa47 + BitVec.ofNat 64 5)) 1) (movM8Imm8Effect 0x11aa47 (.sib 4 none 0 (.d8 0x20)) 0x0) (Reg.operands [.gpr 4] [])) #v[53]
    (.letOp (n := 58) (.out 0x11aa4c (movR64M64Effect 0x11aa4c 2 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 6] []) (.reg (.gpr 2))) #v[6]
    (.letOp (n := 59) (.exec 0x11aa4c (LoadPre 0x11aa4c (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11aa4c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11aa4c 2 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 60) (.out 0x11aa50 (bswapR64Effect 0x11aa50 3 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[58]
    (.letOp (n := 61) (.exec 0x11aa50 (fun s => s.RIP = 0x11aa50) (bswapR64Effect 0x11aa50 3 2) (Reg.operands [.gpr 2] [])) #v[58]
    (.letOp (n := 62) (.out 0x11aa53 (movR64M64Effect 0x11aa53 6 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[6]
    (.letOp (n := 63) (.exec 0x11aa53 (LoadPre 0x11aa53 (fun s => AddrMode.addr (.base 6 .none) s (0x11aa53 + BitVec.ofNat 64 3)) 8) (movR64M64Effect 0x11aa53 6 (.base 6 .none)) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 64) (.out 0x11aa56 (bswapR64Effect 0x11aa56 3 6) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6] []) (.reg (.gpr 6))) #v[62]
    (.letOp (n := 65) (.exec 0x11aa56 (fun s => s.RIP = 0x11aa56) (bswapR64Effect 0x11aa56 3 6) (Reg.operands [.gpr 6] [])) #v[62]
    (.letOp (n := 66) (.out 0x11aa59 (movR64R64Effect 0x11aa59 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[64]
    (.letOp (n := 67) (.exec 0x11aa59 (fun s => s.RIP = 0x11aa59) (movR64R64Effect 0x11aa59 1 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 68) (.out 0x11aa5c (shrR64Effect 0x11aa5c 4 1 56) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 69) (.exec 0x11aa5c (fun s => s.RIP = 0x11aa5c) (shrR64Effect 0x11aa5c 4 1 56) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 70) (.out 0x11aa60 (andR8Imm8Effect 0x11aa60 3 1 0xf) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1] []) (.reg (.gpr 1))) #v[68]
    (.letOp (n := 71) (.exec 0x11aa60 (fun s => s.RIP = 0x11aa60) (andR8Imm8Effect 0x11aa60 3 1 0xf) (Reg.operands [.gpr 1] [])) #v[68]
    (.letOp (n := 72) (.exec 0x11aa63 (StorePre 0x11aa63 3 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11aa63 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11aa63 3 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 1, .gpr 4] [])) #v[70, 53]
    (.letOp (n := 73) (.out 0x11aa66 (movR64R64Effect 0x11aa66 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 74) (.exec 0x11aa66 (fun s => s.RIP = 0x11aa66) (movR64R64Effect 0x11aa66 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 75) (.out 0x11aa69 (shrR64Effect 0x11aa69 4 7 60) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[73]
    (.letOp (n := 76) (.exec 0x11aa69 (fun s => s.RIP = 0x11aa69) (shrR64Effect 0x11aa69 4 7 60) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[73]
    (.letOp (n := 77) (.exec 0x11aa6d (StorePre 0x11aa6d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x1)) s (0x11aa6d + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa6d 5 7 (.sib 4 none 0 (.d8 0x1))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[75, 53]
    (.letOp (n := 78) (.out 0x11aa72 (movR64R64Effect 0x11aa72 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[64]
    (.letOp (n := 79) (.exec 0x11aa72 (fun s => s.RIP = 0x11aa72) (movR64R64Effect 0x11aa72 7 6) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 80) (.out 0x11aa75 (shrR64Effect 0x11aa75 4 7 48) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[78]
    (.letOp (n := 81) (.exec 0x11aa75 (fun s => s.RIP = 0x11aa75) (shrR64Effect 0x11aa75 4 7 48) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[78]
    (.letOp (n := 82) (.out 0x11aa79 (movR32R32Effect 0x11aa79 3 8 7) (EffectPart.reads (.reg (.gpr 8)) [.gpr 7] []) (.reg (.gpr 8))) #v[80]
    (.letOp (n := 83) (.exec 0x11aa79 (fun s => s.RIP = 0x11aa79) (movR32R32Effect 0x11aa79 3 8 7) (Reg.operands [.gpr 7] [])) #v[80]
    (.letOp (n := 84) (.out 0x11aa7c (andR8Imm8Effect 0x11aa7c 4 8 0xf) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8] []) (.reg (.gpr 8))) #v[82]
    (.letOp (n := 85) (.exec 0x11aa7c (fun s => s.RIP = 0x11aa7c) (andR8Imm8Effect 0x11aa7c 4 8 0xf) (Reg.operands [.gpr 8] [])) #v[82]
    (.letOp (n := 86) (.exec 0x11aa80 (StorePre 0x11aa80 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x2)) s (0x11aa80 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11aa80 5 8 (.sib 4 none 0 (.d8 0x2))) (Reg.operands [.gpr 8, .gpr 4] [])) #v[84, 53]
    (.letOp (n := 87) (.out 0x11aa85 (shrR8Effect 0x11aa85 4 7 4) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[80]
    (.letOp (n := 88) (.exec 0x11aa85 (fun s => s.RIP = 0x11aa85) (shrR8Effect 0x11aa85 4 7 4) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[80]
    (b_l11aa40_1))))))))))))))))))))))))))))))))))))

def bytes_l11aa40 : List UInt8 :=
  [0x48, 0x83, 0xEC, 0x21, 0x48, 0x89, 0xF8, 0xC6, 0x44, 0x24, 0x20, 0x00, 0x48, 0x8B, 0x56, 0x08,
    0x48, 0x0F, 0xCA, 0x48, 0x8B, 0x36, 0x48, 0x0F, 0xCE, 0x48, 0x89, 0xF1, 0x48, 0xC1, 0xE9, 0x38,
    0x80, 0xE1, 0x0F, 0x88, 0x0C, 0x24, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x3C, 0x40, 0x88, 0x7C,
    0x24, 0x01, 0x48, 0x89, 0xF7, 0x48, 0xC1, 0xEF, 0x30, 0x41, 0x89, 0xF8, 0x41, 0x80, 0xE0, 0x0F,
    0x44, 0x88, 0x44, 0x24, 0x02, 0x40, 0xC0, 0xEF, 0x04] ++ bytes_l11aa40_1

theorem code_l11aa40 : ∀ x ∈ codeRange 0x11aa40 bytes_l11aa40, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1aa40 73 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11aa40_1

@[cfg_block] def b_l11ac00 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11ac00 (leaR32Effect 0x11ac00 3 6 (.base 1 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 1] []) (.reg (.gpr 6))) #v[1]
    (.letOp (n := 54) (.exec 0x11ac00 (fun s => s.RIP = 0x11ac00) (leaR32Effect 0x11ac00 3 6 (.base 1 (.d8 0x8))) (Reg.operands [.gpr 1] [])) #v[1]
    (.letOp (n := 55) (.out 0x11ac03 (movR32R32Effect 0x11ac03 2 7 6) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11ac03 (fun s => s.RIP = 0x11ac03) (movR32R32Effect 0x11ac03 2 7 6) (Reg.operands [.gpr 6] [])) #v[53]
    (.letOp (n := 57) (.out 0x11ac05 (andR8Imm8Effect 0x11ac05 4 7 0xf0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11ac05 (fun s => s.RIP = 0x11ac05) (andR8Imm8Effect 0x11ac05 4 7 0xf0) (Reg.operands [.gpr 7] [])) #v[55]
    (.letOp (n := 59) (.out 0x11ac09 (subR8R8Effect 0x11ac09 3 1 7) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 7] []) (.reg (.gpr 1))) #v[1, 57]
    (.letOp (n := 60) (.exec 0x11ac09 (fun s => s.RIP = 0x11ac09) (subR8R8Effect 0x11ac09 3 1 7) (Reg.operands [.gpr 1, .gpr 7] [])) #v[1, 57]
    (.letOp (n := 61) (.exec 0x11ac0c (StorePre 0x11ac0c 4 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xfe)) s (0x11ac0c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11ac0c 4 1 (.sib 4 (some 2) 0 (.d8 0xfe))) (Reg.operands [.gpr 1, .gpr 4, .gpr 2] [])) #v[59, 4, 2]
    (.letOp (n := 62) (.out 0x11ac10 (sarR8Effect 0x11ac10 4 6 4) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 6))) #v[53]
    (.letOp (n := 63) (.exec 0x11ac10 (fun s => s.RIP = 0x11ac10) (sarR8Effect 0x11ac10 4 6 4) (Reg.operands [.gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[53]
    (.letOp (n := 64) (.out 0x11ac14 (addR8M8Effect 0x11ac14 5 6 (.sib 4 (some 2) 0 (.d8 0xff))) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 4, .gpr 2] []) (.reg (.gpr 6))) #v[62, 4, 2]
    (.letOp (n := 65) (.exec 0x11ac14 (LoadPre 0x11ac14 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xff)) s (0x11ac14 + BitVec.ofNat 64 5)) 1) (addR8M8Effect 0x11ac14 5 6 (.sib 4 (some 2) 0 (.d8 0xff))) (Reg.operands [.gpr 6, .gpr 4, .gpr 2] [])) #v[62, 4, 2]
    (.letOp (n := 66) (.out 0x11ac19 (leaR32Effect 0x11ac19 3 1 (.base 6 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 6] []) (.reg (.gpr 1))) #v[64]
    (.letOp (n := 67) (.exec 0x11ac19 (fun s => s.RIP = 0x11ac19) (leaR32Effect 0x11ac19 3 1 (.base 6 (.d8 0x8))) (Reg.operands [.gpr 6] [])) #v[64]
    (.letOp (n := 68) (.out 0x11ac1c (movR32R32Effect 0x11ac1c 2 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 1] []) (.reg (.gpr 7))) #v[66]
    (.letOp (n := 69) (.exec 0x11ac1c (fun s => s.RIP = 0x11ac1c) (movR32R32Effect 0x11ac1c 2 7 1) (Reg.operands [.gpr 1] [])) #v[66]
    (.letOp (n := 70) (.out 0x11ac1e (andR8Imm8Effect 0x11ac1e 4 7 0xf0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 71) (.exec 0x11ac1e (fun s => s.RIP = 0x11ac1e) (andR8Imm8Effect 0x11ac1e 4 7 0xf0) (Reg.operands [.gpr 7] [])) #v[68]
    (.letOp (n := 72) (.out 0x11ac22 (subR8R8Effect 0x11ac22 3 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 7] []) (.reg (.gpr 6))) #v[64, 70]
    (.letOp (n := 73) (.exec 0x11ac22 (fun s => s.RIP = 0x11ac22) (subR8R8Effect 0x11ac22 3 6 7) (Reg.operands [.gpr 6, .gpr 7] [])) #v[64, 70]
    (.letOp (n := 74) (.exec 0x11ac25 (StorePre 0x11ac25 5 (fun s => AddrMode.addr (.sib 4 (some 2) 0 (.d8 0xff)) s (0x11ac25 + BitVec.ofNat 64 5)) 1) (movM8R8Effect 0x11ac25 5 6 (.sib 4 (some 2) 0 (.d8 0xff))) (Reg.operands [.gpr 6, .gpr 4, .gpr 2] [])) #v[72, 4, 2]
    (.letOp (n := 75) (.out 0x11ac2a (sarR8Effect 0x11ac2a 3 1 4) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[66]
    (.letOp (n := 76) (.exec 0x11ac2a (fun s => s.RIP = 0x11ac2a) (sarR8Effect 0x11ac2a 3 1 4) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[66]
    (.letOp (n := 77) (.out 0x11ac2d (addR8M8Effect 0x11ac2d 3 1 (.sib 4 (some 2) 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4, .gpr 2] []) (.reg (.gpr 1))) #v[75, 4, 2]
    (.letOp (n := 78) (.exec 0x11ac2d (LoadPre 0x11ac2d (fun s => AddrMode.addr (.sib 4 (some 2) 0 .none) s (0x11ac2d + BitVec.ofNat 64 3)) 1) (addR8M8Effect 0x11ac2d 3 1 (.sib 4 (some 2) 0 .none)) (Reg.operands [.gpr 1, .gpr 4, .gpr 2] [])) #v[75, 4, 2]
    (.letOp (n := 79) (.exec 0x11ac30 (StorePre 0x11ac30 3 (fun s => AddrMode.addr (.sib 4 (some 2) 0 .none) s (0x11ac30 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11ac30 3 1 (.sib 4 (some 2) 0 .none)) (Reg.operands [.gpr 1, .gpr 4, .gpr 2] [])) #v[77, 4, 2]
    (.letOp (n := 80) (.out 0x11ac33 (addR64Imm8Effect 0x11ac33 2 0x2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[2]
    (.letOp (n := 81) (.exec 0x11ac33 (fun s => s.RIP = 0x11ac33) (addR64Imm8Effect 0x11ac33 2 0x2) (Reg.operands [.gpr 2] [])) #v[2]
    (.letOp (n := 82) (.out 0x11ac37 (cmpR64Imm8Effect 0x11ac37 2 0x22) (EffectPart.reads (.flag .ZF) [.gpr 2] []) (.flag .ZF)) #v[80]
    (.letOp (n := 83) (.exec 0x11ac37 (fun s => s.RIP = 0x11ac37) (cmpR64Imm8Effect 0x11ac37 2 0x22) (Reg.operands [.gpr 2] [])) #v[80]
    (.letOp (n := 84) (.pure (condOp 5)) #v[82]
    (.terminate (.condBr (Fin.last 84) ⟨.l11ac00, RegMap.args [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩ ⟨.l11ac3d, RegMap.args [(0, 0), (1, 77), (2, 80), (3, 3), (4, 4), (5, 5), (6, 72), (7, 70), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (19, 82), (22, 22), (39, 39), (50, 50), (51, 51)] 85⟩)))))))))))))))))))))))))))))))))

def bytes_l11ac00 : List UInt8 :=
  [0x8D, 0x71, 0x08, 0x89, 0xF7, 0x40, 0x80, 0xE7, 0xF0, 0x40, 0x28, 0xF9, 0x88, 0x4C, 0x14, 0xFE,
    0x40, 0xC0, 0xFE, 0x04, 0x40, 0x02, 0x74, 0x14, 0xFF, 0x8D, 0x4E, 0x08, 0x89, 0xCF, 0x40, 0x80,
    0xE7, 0xF0, 0x40, 0x28, 0xFE, 0x40, 0x88, 0x74, 0x14, 0xFF, 0xC0, 0xF9, 0x04, 0x02, 0x0C, 0x14,
    0x88, 0x0C, 0x14, 0x48, 0x83, 0xC2, 0x02, 0x48, 0x83, 0xFA, 0x22, 0x75, 0xC3]

theorem code_l11ac00 : ∀ x ∈ codeRange 0x11ac00 bytes_l11ac00, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ac00 61 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11ac3d : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11ac3d (movzxR32M8Effect 0x11ac3d 5 1 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 54) (.exec 0x11ac3d (LoadPre 0x11ac3d (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11ac3d + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11ac3d 5 1 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11ac42 (StorePre 0x11ac42 3 (fun s => AddrMode.addr (.base 0 (.d8 0x20)) s (0x11ac42 + BitVec.ofNat 64 3)) 1) (movM8R8Effect 0x11ac42 3 1 (.base 0 (.d8 0x20))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[53, 0]
    (.letOp (n := 56) (.out 0x11ac45 (movR64M64Effect 0x11ac45 1 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 57) (.exec 0x11ac45 (LoadPre 0x11ac45 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11ac45 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac45 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 58) (.exec 0x11ac4a (StorePre 0x11ac4a 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11ac4a + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac4a 1 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[56, 0]
    (.letOp (n := 59) (.out 0x11ac4e (movR64M64Effect 0x11ac4e 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 60) (.exec 0x11ac4e (LoadPre 0x11ac4e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11ac4e + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac4e 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.exec 0x11ac53 (StorePre 0x11ac53 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11ac53 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac53 1 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 0] [])) #v[59, 0]
    (.letOp (n := 62) (.out 0x11ac57 (movR64M64Effect 0x11ac57 1 (.sib 4 none 0 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 63) (.exec 0x11ac57 (LoadPre 0x11ac57 (fun s => AddrMode.addr (.sib 4 none 0 .none) s (0x11ac57 + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11ac57 1 (.sib 4 none 0 .none)) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 64) (.out 0x11ac5b (movR64M64Effect 0x11ac5b 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 65) (.exec 0x11ac5b (LoadPre 0x11ac5b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11ac5b + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11ac5b 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 66) (.exec 0x11ac60 (StorePre 0x11ac60 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11ac60 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11ac60 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[64, 0]
    (.letOp (n := 67) (.exec 0x11ac64 (StorePre 0x11ac64 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11ac64 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11ac64 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[62, 0]
    (.letOp (n := 68) (.out 0x11ac67 (addR64Imm8Effect 0x11ac67 4 0x21) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 69) (.exec 0x11ac67 (fun s => s.RIP = 0x11ac67) (addR64Imm8Effect 0x11ac67 4 0x21) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 70) (.out 0x11ac6b (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[68]
    (.letOp (n := 71) (.out 0x11ac6b (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[68]
    (.letOp (n := 72) (.exec 0x11ac6b (RetPre 0x11ac6b) (retEffect) (Reg.operands [.gpr 4] [])) #v[68]
    (.terminate (.ret (RegMap.args [(0, 0), (1, 62), (2, 64), (3, 3), (4, 71), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 73) (some ⟨70, by decide⟩))))))))))))))))))))))

def bytes_l11ac3d : List UInt8 :=
  [0x0F, 0xB6, 0x4C, 0x24, 0x20, 0x88, 0x48, 0x20, 0x48, 0x8B, 0x4C, 0x24, 0x18, 0x48, 0x89, 0x48,
    0x18, 0x48, 0x8B, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x48, 0x10, 0x48, 0x8B, 0x0C, 0x24, 0x48, 0x8B,
    0x54, 0x24, 0x08, 0x48, 0x89, 0x50, 0x08, 0x48, 0x89, 0x08, 0x48, 0x83, 0xC4, 0x21, 0xC3]

theorem code_l11ac3d : ∀ x ∈ codeRange 0x11ac3d bytes_l11ac3d, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1ac3d 47 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b510 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11b510 (pushR64Effect 0x11b510 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 5] []) (.reg (.gpr 4))) #v[4, 5]
    (.letOp (n := 54) (.exec 0x11b510 (PushPre 0x11b510 1) (pushR64Effect 0x11b510 1 5) (Reg.operands [.gpr 4, .gpr 5] [])) #v[4, 5]
    (.letOp (n := 55) (.out 0x11b511 (pushR64Effect 0x11b511 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 15] []) (.reg (.gpr 4))) #v[53, 15]
    (.letOp (n := 56) (.exec 0x11b511 (PushPre 0x11b511 2) (pushR64Effect 0x11b511 2 15) (Reg.operands [.gpr 4, .gpr 15] [])) #v[53, 15]
    (.letOp (n := 57) (.out 0x11b513 (pushR64Effect 0x11b513 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 14] []) (.reg (.gpr 4))) #v[55, 14]
    (.letOp (n := 58) (.exec 0x11b513 (PushPre 0x11b513 2) (pushR64Effect 0x11b513 2 14) (Reg.operands [.gpr 4, .gpr 14] [])) #v[55, 14]
    (.letOp (n := 59) (.out 0x11b515 (pushR64Effect 0x11b515 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 13] []) (.reg (.gpr 4))) #v[57, 13]
    (.letOp (n := 60) (.exec 0x11b515 (PushPre 0x11b515 2) (pushR64Effect 0x11b515 2 13) (Reg.operands [.gpr 4, .gpr 13] [])) #v[57, 13]
    (.letOp (n := 61) (.out 0x11b517 (pushR64Effect 0x11b517 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 12] []) (.reg (.gpr 4))) #v[59, 12]
    (.letOp (n := 62) (.exec 0x11b517 (PushPre 0x11b517 2) (pushR64Effect 0x11b517 2 12) (Reg.operands [.gpr 4, .gpr 12] [])) #v[59, 12]
    (.letOp (n := 63) (.out 0x11b519 (pushR64Effect 0x11b519 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4, .gpr 3] []) (.reg (.gpr 4))) #v[61, 3]
    (.letOp (n := 64) (.exec 0x11b519 (PushPre 0x11b519 1) (pushR64Effect 0x11b519 1 3) (Reg.operands [.gpr 4, .gpr 3] [])) #v[61, 3]
    (.letOp (n := 65) (.out 0x11b51a (subR64Imm8Effect 0x11b51a 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[63]
    (.letOp (n := 66) (.exec 0x11b51a (fun s => s.RIP = 0x11b51a) (subR64Imm8Effect 0x11b51a 4 0x48) (Reg.operands [.gpr 4] [])) #v[63]
    (.letOp (n := 67) (.exec 0x11b51e (StorePre 0x11b51e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11b51e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b51e 7 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 65]
    (.letOp (n := 68) (.out 0x11b523 (movR64Imm64Effect 0x11b523 7 0xbaaedce6af48a03b) (EffectPart.reads (.reg (.gpr 7)) [] []) (.reg (.gpr 7))) #v[]
    (.letOp (n := 69) (.exec 0x11b523 (fun s => s.RIP = 0x11b523) (movR64Imm64Effect 0x11b523 7 0xbaaedce6af48a03b) (Reg.operands [] [])) #v[]
    (.letOp (n := 70) (.out 0x11b52d (movR64Imm64Effect 0x11b52d 9 0x402da1732fc9bebf) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 71) (.exec 0x11b52d (fun s => s.RIP = 0x11b52d) (movR64Imm64Effect 0x11b52d 9 0x402da1732fc9bebf) (Reg.operands [] [])) #v[]
    (.letOp (n := 72) (.out 0x11b537 (testR32R32Effect 0x11b537 2 2 2) (EffectPart.reads (.flag .ZF) [.gpr 2, .gpr 2] []) (.flag .ZF)) #v[2, 2]
    (.letOp (n := 73) (.exec 0x11b537 (fun s => s.RIP = 0x11b537) (testR32R32Effect 0x11b537 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 74) (.pure (condOp 4)) #v[72]
    (.terminate (.condBr (Fin.last 74) ⟨.l11b5a3, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 68), (9, 70), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩ ⟨.l11b53b, RegMap.args [(1, 1), (2, 2), (3, 3), (4, 65), (5, 5), (6, 6), (7, 68), (9, 70), (10, 10), (12, 12), (13, 13), (14, 14), (15, 15), (19, 72), (22, 22), (39, 39), (50, 50), (51, 51)] 75⟩)))))))))))))))))))))))

def bytes_l11b510 : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x83, 0xEC, 0x48, 0x48, 0x89,
    0x7C, 0x24, 0x40, 0x48, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC, 0xAE, 0xBA, 0x49, 0xB9, 0xBF,
    0xBE, 0xC9, 0x2F, 0x73, 0xA1, 0x2D, 0x40, 0x85, 0xD2, 0x74, 0x68]

theorem code_l11b510 : ∀ x ∈ codeRange 0x11b510 bytes_l11b510, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b510 43 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b53b_1 : Block Op Label signature Reg.count 85 :=
  .letOp (n := 85) (.out 0x11b59e (incR64Effect 0x11b59e 9) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 9))) #v[9]
    (.letOp (n := 86) (.exec 0x11b59e (fun s => s.RIP = 0x11b59e) (incR64Effect 0x11b59e 9) (Reg.operands [.gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[9]
    (.terminate (.br ⟨.l11b5ba, RegMap.args [(1, 81), (2, 73), (4, 4), (6, 6), (7, 61), (9, 85), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 87⟩)))

def bytes_l11b53b_1 : List UInt8 :=
  [0x49, 0xFF, 0xC1, 0xEB, 0x17]

theorem code_l11b53b_1 : ∀ x ∈ codeRange 0x11b59e bytes_l11b53b_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b59e 5 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b53b : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11b53b (StorePre 0x11b53b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b53b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b53b (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x11b544 (fun s => s.RIP = 0x11b544) (leaR64Effect 0x11b544 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11b549 (xorR32R32Effect 0x11b549 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[1, 1]
    (.letOp (n := 56) (.exec 0x11b549 (fun s => s.RIP = 0x11b549) (xorR32R32Effect 0x11b549 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[1, 1]
    (.letOp (n := 57) (.out 0x11b54b (subR64M64Effect 0x11b54b 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[55, 4]
    (.letOp (n := 58) (.exec 0x11b54b (LoadPre 0x11b54b (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b54b + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b54b 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[55, 4]
    (.letOp (n := 59) (.out 0x11b550 (sarR64Effect 0x11b550 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[57]
    (.letOp (n := 60) (.exec 0x11b550 (fun s => s.RIP = 0x11b550) (sarR64Effect 0x11b550 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[57]
    (.letOp (n := 61) (.out 0x11b554 (addR64R64Effect 0x11b554 7 1) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 1] []) (.reg (.gpr 7))) #v[7, 59]
    (.letOp (n := 62) (.exec 0x11b554 (fun s => s.RIP = 0x11b554) (addR64R64Effect 0x11b554 7 1) (Reg.operands [.gpr 7, .gpr 1] [])) #v[7, 59]
    (.letOp (n := 63) (.exec 0x11b557 (StorePre 0x11b557 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b557 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b557 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[61, 4]
    (.letOp (n := 64) (.exec 0x11b55c (StorePre 0x11b55c 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b55c + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b55c (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 65) (.out 0x11b565 (xorR32R32Effect 0x11b565 2 2 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 2] []) (.reg (.gpr 2))) #v[2, 2]
    (.letOp (n := 66) (.exec 0x11b565 (fun s => s.RIP = 0x11b565) (xorR32R32Effect 0x11b565 2 2 2) (Reg.operands [.gpr 2, .gpr 2] [])) #v[2, 2]
    (.letOp (n := 67) (.out 0x11b567 (subR64M64Effect 0x11b567 2 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 4] []) (.reg (.gpr 2))) #v[65, 4]
    (.letOp (n := 68) (.exec 0x11b567 (LoadPre 0x11b567 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b567 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b567 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[65, 4]
    (.letOp (n := 69) (.out 0x11b56c (xorR32R32Effect 0x11b56c 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[59, 59]
    (.letOp (n := 70) (.exec 0x11b56c (fun s => s.RIP = 0x11b56c) (xorR32R32Effect 0x11b56c 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[59, 59]
    (.letOp (n := 71) (.out 0x11b56e (sarR64Effect 0x11b56e 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[67]
    (.letOp (n := 72) (.exec 0x11b56e (fun s => s.RIP = 0x11b56e) (sarR64Effect 0x11b56e 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[67]
    (.letOp (n := 73) (.out 0x11b572 (addR64Imm8Effect 0x11b572 2 0xfe) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[71]
    (.letOp (n := 74) (.exec 0x11b572 (fun s => s.RIP = 0x11b572) (addR64Imm8Effect 0x11b572 2 0xfe) (Reg.operands [.gpr 2] [])) #v[71]
    (.letOp (n := 75) (.exec 0x11b576 (StorePre 0x11b576 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b576 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b576 2 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 76) (.exec 0x11b57b (StorePre 0x11b57b 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b57b + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b57b (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 77) (.out 0x11b584 (subR64M64Effect 0x11b584 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[69, 4]
    (.letOp (n := 78) (.exec 0x11b584 (LoadPre 0x11b584 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b584 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b584 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[69, 4]
    (.letOp (n := 79) (.out 0x11b589 (sarR64Effect 0x11b589 4 1 63) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[77]
    (.letOp (n := 80) (.exec 0x11b589 (fun s => s.RIP = 0x11b589) (sarR64Effect 0x11b589 4 1 63) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[77]
    (.letOp (n := 81) (.out 0x11b58d (decR64Effect 0x11b58d 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 1))) #v[79]
    (.letOp (n := 82) (.exec 0x11b58d (fun s => s.RIP = 0x11b58d) (decR64Effect 0x11b58d 1) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[79]
    (.letOp (n := 83) (.exec 0x11b590 (StorePre 0x11b590 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b590 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b590 1 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[81, 4]
    (.letOp (n := 84) (.exec 0x11b595 (StorePre 0x11b595 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b595 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b595 (.sib 4 none 0 (.d8 0x8)) 0x0) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11b53b_1))))))))))))))))))))))))))))))))

def bytes_l11b53b : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x31, 0xC9,
    0x48, 0x2B, 0x4C, 0x24, 0x08, 0x48, 0xC1, 0xF9, 0x3F, 0x48, 0x01, 0xCF, 0x48, 0x89, 0x7C, 0x24,
    0x28, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x31, 0xD2, 0x48, 0x2B, 0x54, 0x24,
    0x08, 0x31, 0xC9, 0x48, 0xC1, 0xFA, 0x3F, 0x48, 0x83, 0xC2, 0xFE, 0x48, 0x89, 0x54, 0x24, 0x30,
    0x48, 0xC7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0x2B, 0x4C, 0x24, 0x08, 0x48, 0xC1,
    0xF9, 0x3F, 0x48, 0xFF, 0xC9, 0x48, 0x89, 0x4C, 0x24, 0x18, 0x48, 0xC7, 0x44, 0x24, 0x08, 0x00,
    0x00, 0x00, 0x00] ++ bytes_l11b53b_1

theorem code_l11b53b : ∀ x ∈ codeRange 0x11b53b bytes_l11b53b, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b53b 99 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b53b_1

@[cfg_block] def b_l11b5a3 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11b5a3 (StorePre 0x11b5a3 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b5a3 + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b5a3 (.sib 4 none 0 (.d8 0x30)) 0xfffffffe) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 54) (.exec 0x11b5ac (StorePre 0x11b5ac 9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b5ac + BitVec.ofNat 64 9)) 8) (movM64Imm32Effect 0x11b5ac (.sib 4 none 0 (.d8 0x18)) 0xffffffff) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.exec 0x11b5b5 (StorePre 0x11b5b5 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b5b5 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b5b5 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[7, 4]
    (.terminate (.br ⟨.l11b5ba, RegMap.args [(4, 4), (6, 6), (7, 7), (9, 9), (10, 10), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 56⟩))))

def bytes_l11b5a3 : List UInt8 :=
  [0x48, 0xC7, 0x44, 0x24, 0x30, 0xFE, 0xFF, 0xFF, 0xFF, 0x48, 0xC7, 0x44, 0x24, 0x18, 0xFF, 0xFF,
    0xFF, 0xFF, 0x48, 0x89, 0x7C, 0x24, 0x28]

theorem code_l11b5a3 : ∀ x ∈ codeRange 0x11b5a3 bytes_l11b5a3, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b5a3 23 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b5ba_9 : Block Op Label signature Reg.count 451 :=
  .letOp (n := 451) (.out 0x11b82b (subR64R64Effect 0x11b82b 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[447, 449]
    (.letOp (n := 452) (.exec 0x11b82b (fun s => s.RIP = 0x11b82b) (subR64R64Effect 0x11b82b 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[447, 449]
    (.letOp (n := 453) (.out 0x11b82e (sarR64Effect 0x11b82e 4 5 63) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 5))) #v[445]
    (.letOp (n := 454) (.exec 0x11b82e (fun s => s.RIP = 0x11b82e) (sarR64Effect 0x11b82e 4 5 63) (Reg.operands [.gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[445]
    (.letOp (n := 455) (.out 0x11b832 (addR64R64Effect 0x11b832 5 2) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 2] []) (.reg (.gpr 5))) #v[453, 451]
    (.letOp (n := 456) (.exec 0x11b832 (fun s => s.RIP = 0x11b832) (addR64R64Effect 0x11b832 5 2) (Reg.operands [.gpr 5, .gpr 2] [])) #v[453, 451]
    (.letOp (n := 457) (.out 0x11b835 (movR64R64Effect 0x11b835 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[362]
    (.letOp (n := 458) (.exec 0x11b835 (fun s => s.RIP = 0x11b835) (movR64R64Effect 0x11b835 2 3) (Reg.operands [.gpr 3] [])) #v[362]
    (.letOp (n := 459) (.out 0x11b838 (notR64Effect 0x11b838 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[457]
    (.letOp (n := 460) (.exec 0x11b838 (fun s => s.RIP = 0x11b838) (notR64Effect 0x11b838 2) (Reg.operands [.gpr 2] [])) #v[457]
    (.letOp (n := 461) (.out 0x11b83b (movR64R64Effect 0x11b83b 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[449]
    (.letOp (n := 462) (.exec 0x11b83b (fun s => s.RIP = 0x11b83b) (movR64R64Effect 0x11b83b 6 7) (Reg.operands [.gpr 7] [])) #v[449]
    (.letOp (n := 463) (.out 0x11b83e (andR64R64Effect 0x11b83e 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[461, 459]
    (.letOp (n := 464) (.exec 0x11b83e (fun s => s.RIP = 0x11b83e) (andR64R64Effect 0x11b83e 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[461, 459]
    (.letOp (n := 465) (.out 0x11b841 (orR64R64Effect 0x11b841 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[459, 449]
    (.letOp (n := 466) (.exec 0x11b841 (fun s => s.RIP = 0x11b841) (orR64R64Effect 0x11b841 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[459, 449]
    (.letOp (n := 467) (.out 0x11b844 (andR64R64Effect 0x11b844 2 5) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 5] []) (.reg (.gpr 2))) #v[465, 455]
    (.letOp (n := 468) (.exec 0x11b844 (fun s => s.RIP = 0x11b844) (andR64R64Effect 0x11b844 2 5) (Reg.operands [.gpr 2, .gpr 5] [])) #v[465, 455]
    (.letOp (n := 469) (.out 0x11b847 (orR64R64Effect 0x11b847 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[467, 463]
    (.letOp (n := 470) (.exec 0x11b847 (fun s => s.RIP = 0x11b847) (orR64R64Effect 0x11b847 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[467, 463]
    (.letOp (n := 471) (.out 0x11b84a (shrR64Effect 0x11b84a 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[469]
    (.letOp (n := 472) (.exec 0x11b84a (fun s => s.RIP = 0x11b84a) (shrR64Effect 0x11b84a 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[469]
    (.letOp (n := 473) (.exec 0x11b84e (StorePre 0x11b84e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b84e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b84e 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[471, 4]
    (.letOp (n := 474) (.out 0x11b853 (xorR32R32Effect 0x11b853 3 13 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 13] []) (.reg (.gpr 13))) #v[234, 234]
    (.letOp (n := 475) (.exec 0x11b853 (fun s => s.RIP = 0x11b853) (xorR32R32Effect 0x11b853 3 13 13) (Reg.operands [.gpr 13, .gpr 13] [])) #v[234, 234]
    (.letOp (n := 476) (.out 0x11b856 (subR64M64Effect 0x11b856 13 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .gpr 4] []) (.reg (.gpr 13))) #v[474, 4]
    (.letOp (n := 477) (.exec 0x11b856 (LoadPre 0x11b856 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b856 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b856 13 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 13, .gpr 4] [])) #v[474, 4]
    (.letOp (n := 478) (.out 0x11b85b (movzxR32R8Effect 0x11b85b 4 7 8) (EffectPart.reads (.reg (.gpr 7)) [.gpr 8] []) (.reg (.gpr 7))) #v[365]
    (.letOp (n := 479) (.exec 0x11b85b (fun s => s.RIP = 0x11b85b) (movzxR32R8Effect 0x11b85b 4 7 8) (Reg.operands [.gpr 8] [])) #v[365]
    (.letOp (n := 480) (.out 0x11b85f (callEffect (fun _ => 0x127d50) 0x11b864) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 481) (.exec 0x11b85f (PushPre 0x11b85f 5) (callEffect (fun _ => 0x127d50) 0x11b864) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 482) (.const ⟨64, 0x11b864⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 356), (1, 378), (2, 471), (3, 362), (4, 480), (5, 455), (6, 463), (7, 478), (8, 365), (9, 275), (10, 327), (11, 261), (12, 393), (13, 476), (14, 424), (15, 359), (22, 22), (39, 39), (50, 50), (51, 51)] 483⟩ { target := .l11b864, kept := #v[], arity := rfl, guard := some (Fin.last 482) })))))))))))))))))))))))))))))))))

def bytes_l11b5ba_9 : List UInt8 :=
  [0x48, 0x29, 0xFA, 0x48, 0xC1, 0xFD, 0x3F, 0x48, 0x01, 0xD5, 0x48, 0x89, 0xDA, 0x48, 0xF7, 0xD2,
    0x48, 0x89, 0xFE, 0x48, 0x21, 0xD6, 0x48, 0x09, 0xFA, 0x48, 0x21, 0xEA, 0x48, 0x09, 0xF2, 0x48,
    0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x45, 0x31, 0xED, 0x4C, 0x2B, 0x6C, 0x24, 0x08,
    0x41, 0x0F, 0xB6, 0xF8, 0xE8, 0xEC, 0xC4, 0x00, 0x00]

theorem code_l11b5ba_9 : ∀ x ∈ codeRange 0x11b82b bytes_l11b5ba_9, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b82b 57 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b5ba_8 : Block Op Label signature Reg.count 412 :=
  .letOp (n := 412) (.out 0x11b7e4 (xorR32R32Effect 0x11b7e4 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[304, 304]
    (.letOp (n := 413) (.exec 0x11b7e4 (fun s => s.RIP = 0x11b7e4) (xorR32R32Effect 0x11b7e4 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[304, 304]
    (.letOp (n := 414) (.out 0x11b7e7 (subR64M64Effect 0x11b7e7 14 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 4] []) (.reg (.gpr 14))) #v[412, 4]
    (.letOp (n := 415) (.exec 0x11b7e7 (LoadPre 0x11b7e7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7e7 + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b7e7 14 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 14, .gpr 4] [])) #v[412, 4]
    (.letOp (n := 416) (.out 0x11b7ec (movR64R64Effect 0x11b7ec 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[359]
    (.letOp (n := 417) (.exec 0x11b7ec (fun s => s.RIP = 0x11b7ec) (movR64R64Effect 0x11b7ec 2 15) (Reg.operands [.gpr 15] [])) #v[359]
    (.letOp (n := 418) (.out 0x11b7ef (movR64M64Effect 0x11b7ef 7 (.sib 4 none 0 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 419) (.exec 0x11b7ef (LoadPre 0x11b7ef (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x30)) s (0x11b7ef + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b7ef 7 (.sib 4 none 0 (.d8 0x30))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 420) (.out 0x11b7f4 (subR64R64Effect 0x11b7f4 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[416, 418]
    (.letOp (n := 421) (.exec 0x11b7f4 (fun s => s.RIP = 0x11b7f4) (subR64R64Effect 0x11b7f4 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[416, 418]
    (.letOp (n := 422) (.out 0x11b7f7 (sarR64Effect 0x11b7f7 4 14 63) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 14))) #v[414]
    (.letOp (n := 423) (.exec 0x11b7f7 (fun s => s.RIP = 0x11b7f7) (sarR64Effect 0x11b7f7 4 14 63) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[414]
    (.letOp (n := 424) (.out 0x11b7fb (addR64R64Effect 0x11b7fb 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2] []) (.reg (.gpr 14))) #v[422, 420]
    (.letOp (n := 425) (.exec 0x11b7fb (fun s => s.RIP = 0x11b7fb) (addR64R64Effect 0x11b7fb 14 2) (Reg.operands [.gpr 14, .gpr 2] [])) #v[422, 420]
    (.letOp (n := 426) (.out 0x11b7fe (movR64R64Effect 0x11b7fe 2 15) (EffectPart.reads (.reg (.gpr 2)) [.gpr 15] []) (.reg (.gpr 2))) #v[359]
    (.letOp (n := 427) (.exec 0x11b7fe (fun s => s.RIP = 0x11b7fe) (movR64R64Effect 0x11b7fe 2 15) (Reg.operands [.gpr 15] [])) #v[359]
    (.letOp (n := 428) (.out 0x11b801 (notR64Effect 0x11b801 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[426]
    (.letOp (n := 429) (.exec 0x11b801 (fun s => s.RIP = 0x11b801) (notR64Effect 0x11b801 2) (Reg.operands [.gpr 2] [])) #v[426]
    (.letOp (n := 430) (.out 0x11b804 (movR64R64Effect 0x11b804 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[418]
    (.letOp (n := 431) (.exec 0x11b804 (fun s => s.RIP = 0x11b804) (movR64R64Effect 0x11b804 6 7) (Reg.operands [.gpr 7] [])) #v[418]
    (.letOp (n := 432) (.out 0x11b807 (andR64R64Effect 0x11b807 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[430, 428]
    (.letOp (n := 433) (.exec 0x11b807 (fun s => s.RIP = 0x11b807) (andR64R64Effect 0x11b807 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[430, 428]
    (.letOp (n := 434) (.out 0x11b80a (orR64R64Effect 0x11b80a 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[428, 418]
    (.letOp (n := 435) (.exec 0x11b80a (fun s => s.RIP = 0x11b80a) (orR64R64Effect 0x11b80a 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[428, 418]
    (.letOp (n := 436) (.out 0x11b80d (andR64R64Effect 0x11b80d 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[434, 424]
    (.letOp (n := 437) (.exec 0x11b80d (fun s => s.RIP = 0x11b80d) (andR64R64Effect 0x11b80d 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[434, 424]
    (.letOp (n := 438) (.out 0x11b810 (orR64R64Effect 0x11b810 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[436, 432]
    (.letOp (n := 439) (.exec 0x11b810 (fun s => s.RIP = 0x11b810) (orR64R64Effect 0x11b810 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[436, 432]
    (.letOp (n := 440) (.out 0x11b813 (shrR64Effect 0x11b813 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[438]
    (.letOp (n := 441) (.exec 0x11b813 (fun s => s.RIP = 0x11b813) (shrR64Effect 0x11b813 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[438]
    (.letOp (n := 442) (.exec 0x11b817 (StorePre 0x11b817 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b817 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b817 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[440, 4]
    (.letOp (n := 443) (.out 0x11b81c (xorR32R32Effect 0x11b81c 2 5 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 5] []) (.reg (.gpr 5))) #v[236, 236]
    (.letOp (n := 444) (.exec 0x11b81c (fun s => s.RIP = 0x11b81c) (xorR32R32Effect 0x11b81c 2 5 5) (Reg.operands [.gpr 5, .gpr 5] [])) #v[236, 236]
    (.letOp (n := 445) (.out 0x11b81e (subR64M64Effect 0x11b81e 5 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 5)) [.gpr 5, .gpr 4] []) (.reg (.gpr 5))) #v[443, 4]
    (.letOp (n := 446) (.exec 0x11b81e (LoadPre 0x11b81e (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b81e + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b81e 5 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 5, .gpr 4] [])) #v[443, 4]
    (.letOp (n := 447) (.out 0x11b823 (movR64R64Effect 0x11b823 2 3) (EffectPart.reads (.reg (.gpr 2)) [.gpr 3] []) (.reg (.gpr 2))) #v[362]
    (.letOp (n := 448) (.exec 0x11b823 (fun s => s.RIP = 0x11b823) (movR64R64Effect 0x11b823 2 3) (Reg.operands [.gpr 3] [])) #v[362]
    (.letOp (n := 449) (.out 0x11b826 (movR64M64Effect 0x11b826 7 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 450) (.exec 0x11b826 (LoadPre 0x11b826 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b826 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b826 7 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11b5ba_9)))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_8 : List UInt8 :=
  [0x45, 0x31, 0xF6, 0x4C, 0x2B, 0x74, 0x24, 0x08, 0x4C, 0x89, 0xFA, 0x48, 0x8B, 0x7C, 0x24, 0x30,
    0x48, 0x29, 0xFA, 0x49, 0xC1, 0xFE, 0x3F, 0x49, 0x01, 0xD6, 0x4C, 0x89, 0xFA, 0x48, 0xF7, 0xD2,
    0x48, 0x89, 0xFE, 0x48, 0x21, 0xD6, 0x48, 0x09, 0xFA, 0x4C, 0x21, 0xF2, 0x48, 0x09, 0xF2, 0x48,
    0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08, 0x31, 0xED, 0x48, 0x2B, 0x6C, 0x24, 0x08, 0x48,
    0x89, 0xDA, 0x48, 0x8B, 0x7C, 0x24, 0x18] ++ bytes_l11b5ba_9

theorem code_l11b5ba_8 : ∀ x ∈ codeRange 0x11b7e4 bytes_l11b5ba_8, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b7e4 71 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_9

@[cfg_block] def b_l11b5ba_7 : Block Op Label signature Reg.count 375 :=
  .letOp (n := 375) (.out 0x11b799 (shrR64Effect 0x11b799 4 7 63) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 7))) #v[373]
    (.letOp (n := 376) (.exec 0x11b799 (fun s => s.RIP = 0x11b799) (shrR64Effect 0x11b799 4 7 63) (Reg.operands [.gpr 7, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[373]
    (.letOp (n := 377) (.exec 0x11b79d (StorePre 0x11b79d 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b79d + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b79d 7 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[375, 4]
    (.letOp (n := 378) (.out 0x11b7a2 (leaR64Effect 0x11b7a2 1 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 379) (.exec 0x11b7a2 (fun s => s.RIP = 0x11b7a2) (leaR64Effect 0x11b7a2 1 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 380) (.out 0x11b7a7 (xorR32R32Effect 0x11b7a7 3 12 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 12] []) (.reg (.gpr 12))) #v[222, 222]
    (.letOp (n := 381) (.exec 0x11b7a7 (fun s => s.RIP = 0x11b7a7) (xorR32R32Effect 0x11b7a7 3 12 12) (Reg.operands [.gpr 12, .gpr 12] [])) #v[222, 222]
    (.letOp (n := 382) (.out 0x11b7aa (subR64M64Effect 0x11b7aa 12 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 4] []) (.reg (.gpr 12))) #v[380, 4]
    (.letOp (n := 383) (.exec 0x11b7aa (LoadPre 0x11b7aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7aa + BitVec.ofNat 64 5)) 8) (subR64M64Effect 0x11b7aa 12 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[380, 4]
    (.letOp (n := 384) (.exec 0x11b7af (StorePre 0x11b7af 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11b7af + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b7af 0 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[356, 4]
    (.letOp (n := 385) (.out 0x11b7b4 (movR64R64Effect 0x11b7b4 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[356]
    (.letOp (n := 386) (.exec 0x11b7b4 (fun s => s.RIP = 0x11b7b4) (movR64R64Effect 0x11b7b4 2 0) (Reg.operands [.gpr 0] [])) #v[356]
    (.letOp (n := 387) (.out 0x11b7b7 (movR64M64Effect 0x11b7b7 7 (.sib 4 none 0 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 4] []) (.reg (.gpr 7))) #v[4]
    (.letOp (n := 388) (.exec 0x11b7b7 (LoadPre 0x11b7b7 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x28)) s (0x11b7b7 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b7b7 7 (.sib 4 none 0 (.d8 0x28))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 389) (.out 0x11b7bc (subR64R64Effect 0x11b7bc 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[385, 387]
    (.letOp (n := 390) (.exec 0x11b7bc (fun s => s.RIP = 0x11b7bc) (subR64R64Effect 0x11b7bc 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[385, 387]
    (.letOp (n := 391) (.out 0x11b7bf (sarR64Effect 0x11b7bf 4 12 63) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 12))) #v[382]
    (.letOp (n := 392) (.exec 0x11b7bf (fun s => s.RIP = 0x11b7bf) (sarR64Effect 0x11b7bf 4 12 63) (Reg.operands [.gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[382]
    (.letOp (n := 393) (.out 0x11b7c3 (addR64R64Effect 0x11b7c3 12 2) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 2] []) (.reg (.gpr 12))) #v[391, 389]
    (.letOp (n := 394) (.exec 0x11b7c3 (fun s => s.RIP = 0x11b7c3) (addR64R64Effect 0x11b7c3 12 2) (Reg.operands [.gpr 12, .gpr 2] [])) #v[391, 389]
    (.letOp (n := 395) (.out 0x11b7c6 (movR64R64Effect 0x11b7c6 2 0) (EffectPart.reads (.reg (.gpr 2)) [.gpr 0] []) (.reg (.gpr 2))) #v[356]
    (.letOp (n := 396) (.exec 0x11b7c6 (fun s => s.RIP = 0x11b7c6) (movR64R64Effect 0x11b7c6 2 0) (Reg.operands [.gpr 0] [])) #v[356]
    (.letOp (n := 397) (.out 0x11b7c9 (notR64Effect 0x11b7c9 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2] []) (.reg (.gpr 2))) #v[395]
    (.letOp (n := 398) (.exec 0x11b7c9 (fun s => s.RIP = 0x11b7c9) (notR64Effect 0x11b7c9 2) (Reg.operands [.gpr 2] [])) #v[395]
    (.letOp (n := 399) (.out 0x11b7cc (movR64R64Effect 0x11b7cc 6 7) (EffectPart.reads (.reg (.gpr 6)) [.gpr 7] []) (.reg (.gpr 6))) #v[387]
    (.letOp (n := 400) (.exec 0x11b7cc (fun s => s.RIP = 0x11b7cc) (movR64R64Effect 0x11b7cc 6 7) (Reg.operands [.gpr 7] [])) #v[387]
    (.letOp (n := 401) (.out 0x11b7cf (andR64R64Effect 0x11b7cf 6 2) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 2] []) (.reg (.gpr 6))) #v[399, 397]
    (.letOp (n := 402) (.exec 0x11b7cf (fun s => s.RIP = 0x11b7cf) (andR64R64Effect 0x11b7cf 6 2) (Reg.operands [.gpr 6, .gpr 2] [])) #v[399, 397]
    (.letOp (n := 403) (.out 0x11b7d2 (orR64R64Effect 0x11b7d2 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[397, 387]
    (.letOp (n := 404) (.exec 0x11b7d2 (fun s => s.RIP = 0x11b7d2) (orR64R64Effect 0x11b7d2 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[397, 387]
    (.letOp (n := 405) (.out 0x11b7d5 (andR64R64Effect 0x11b7d5 2 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12] []) (.reg (.gpr 2))) #v[403, 393]
    (.letOp (n := 406) (.exec 0x11b7d5 (fun s => s.RIP = 0x11b7d5) (andR64R64Effect 0x11b7d5 2 12) (Reg.operands [.gpr 2, .gpr 12] [])) #v[403, 393]
    (.letOp (n := 407) (.out 0x11b7d8 (orR64R64Effect 0x11b7d8 2 6) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 6] []) (.reg (.gpr 2))) #v[405, 401]
    (.letOp (n := 408) (.exec 0x11b7d8 (fun s => s.RIP = 0x11b7d8) (orR64R64Effect 0x11b7d8 2 6) (Reg.operands [.gpr 2, .gpr 6] [])) #v[405, 401]
    (.letOp (n := 409) (.out 0x11b7db (shrR64Effect 0x11b7db 4 2 63) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 2))) #v[407]
    (.letOp (n := 410) (.exec 0x11b7db (fun s => s.RIP = 0x11b7db) (shrR64Effect 0x11b7db 4 2 63) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[407]
    (.letOp (n := 411) (.exec 0x11b7df (StorePre 0x11b7df 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b7df + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b7df 2 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[409, 4]
    (b_l11b5ba_8)))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_7 : List UInt8 :=
  [0x48, 0xC1, 0xEF, 0x3F, 0x48, 0x89, 0x7C, 0x24, 0x08, 0x48, 0x8D, 0x4C, 0x24, 0x08, 0x45, 0x31,
    0xE4, 0x4C, 0x2B, 0x64, 0x24, 0x08, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0xC2, 0x48, 0x8B,
    0x7C, 0x24, 0x28, 0x48, 0x29, 0xFA, 0x49, 0xC1, 0xFC, 0x3F, 0x49, 0x01, 0xD4, 0x48, 0x89, 0xC2,
    0x48, 0xF7, 0xD2, 0x48, 0x89, 0xFE, 0x48, 0x21, 0xD6, 0x48, 0x09, 0xFA, 0x4C, 0x21, 0xE2, 0x48,
    0x09, 0xF2, 0x48, 0xC1, 0xEA, 0x3F, 0x48, 0x89, 0x54, 0x24, 0x08] ++ bytes_l11b5ba_8

theorem code_l11b5ba_7 : ∀ x ∈ codeRange 0x11b799 bytes_l11b5ba_7, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b799 75 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_8

@[cfg_block] def b_l11b5ba_6 : Block Op Label signature Reg.count 329 :=
  .letOp (n := 329) (.out 0x11b755 (mulR64Effect 0x11b755 10) (EffectPart.reads (.reg (.gpr 0)) [.gpr 10, .gpr 0] []) (.reg (.gpr 0))) #v[327, 325]
    (.letOp (n := 330) (.out 0x11b755 (mulR64Effect 0x11b755 10) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 0] []) (.reg (.gpr 2))) #v[327, 325]
    (.letOp (n := 331) (.exec 0x11b755 (fun s => s.RIP = 0x11b755) (mulR64Effect 0x11b755 10) (Reg.operands [.gpr 10, .gpr 0] [])) #v[327, 325]
    (.letOp (n := 332) (.out 0x11b758 (movR64R64Effect 0x11b758 1 2) (EffectPart.reads (.reg (.gpr 1)) [.gpr 2] []) (.reg (.gpr 1))) #v[330]
    (.letOp (n := 333) (.exec 0x11b758 (fun s => s.RIP = 0x11b758) (movR64R64Effect 0x11b758 1 2) (Reg.operands [.gpr 2] [])) #v[330]
    (.letOp (n := 334) (.out 0x11b75b (movR64R64Effect 0x11b75b 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[329]
    (.letOp (n := 335) (.exec 0x11b75b (fun s => s.RIP = 0x11b75b) (movR64R64Effect 0x11b75b 7 0) (Reg.operands [.gpr 0] [])) #v[329]
    (.letOp (n := 336) (.out 0x11b75e (movR64R64Effect 0x11b75e 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[323]
    (.letOp (n := 337) (.exec 0x11b75e (fun s => s.RIP = 0x11b75e) (movR64R64Effect 0x11b75e 0 15) (Reg.operands [.gpr 15] [])) #v[323]
    (.letOp (n := 338) (.out 0x11b761 (mulR64Effect 0x11b761 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[275, 336]
    (.letOp (n := 339) (.out 0x11b761 (mulR64Effect 0x11b761 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[275, 336]
    (.letOp (n := 340) (.exec 0x11b761 (fun s => s.RIP = 0x11b761) (mulR64Effect 0x11b761 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[275, 336]
    (.letOp (n := 341) (.out 0x11b764 (addR64R64Effect 0x11b764 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 11] []) (.reg (.gpr 0))) #v[338, 261]
    (.letOp (n := 342) (.out 0x11b764 (addR64R64Effect 0x11b764 0 11) (EffectPart.reads (.flag .CF) [.gpr 0, .gpr 11] []) (.flag .CF)) #v[338, 261]
    (.letOp (n := 343) (.exec 0x11b764 (fun s => s.RIP = 0x11b764) (addR64R64Effect 0x11b764 0 11) (Reg.operands [.gpr 0, .gpr 11] [])) #v[338, 261]
    (.letOp (n := 344) (.out 0x11b767 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b767 2 0x0)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[339, 342]
    (.letOp (n := 345) (.exec 0x11b767 (fun s => s.RIP = 0x11b767) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b767 2 0x0)) (Reg.operands [.gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[339, 342]
    (.letOp (n := 346) (.out 0x11b76b (xorR32R32Effect 0x11b76b 2 3 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 3] []) (.reg (.gpr 3))) #v[100, 100]
    (.letOp (n := 347) (.exec 0x11b76b (fun s => s.RIP = 0x11b76b) (xorR32R32Effect 0x11b76b 2 3 3) (Reg.operands [.gpr 3, .gpr 3] [])) #v[100, 100]
    (.letOp (n := 348) (.out 0x11b76d (addR64R64Effect 0x11b76d 15 8) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 8] []) (.reg (.gpr 15))) #v[323, 292]
    (.letOp (n := 349) (.out 0x11b76d (addR64R64Effect 0x11b76d 15 8) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 8] []) (.flag .CF)) #v[323, 292]
    (.letOp (n := 350) (.exec 0x11b76d (fun s => s.RIP = 0x11b76d) (addR64R64Effect 0x11b76d 15 8) (Reg.operands [.gpr 15, .gpr 8] [])) #v[323, 292]
    (.letOp (n := 351) (.out 0x11b770 (atFlags (condHolds 2) (setccR8Effect 0x11b770 3 3)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[346, 349]
    (.letOp (n := 352) (.exec 0x11b770 (fun s => s.RIP = 0x11b770) (atFlags (condHolds 2) (setccR8Effect 0x11b770 3 3)) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[346, 349]
    (.letOp (n := 353) (.out 0x11b773 (addR64M64Effect 0x11b773 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 4] []) (.reg (.gpr 7))) #v[334, 4]
    (.letOp (n := 354) (.out 0x11b773 (addR64M64Effect 0x11b773 7 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 7, .gpr 4] []) (.flag .CF)) #v[334, 4]
    (.letOp (n := 355) (.exec 0x11b773 (LoadPre 0x11b773 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b773 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11b773 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[334, 4]
    (.letOp (n := 356) (.out 0x11b778 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b778 0 1)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[341, 332, 354]
    (.letOp (n := 357) (.out 0x11b778 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b778 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[341, 332, 354]
    (.letOp (n := 358) (.exec 0x11b778 (fun s => s.RIP = 0x11b778) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b778 0 1)) (Reg.operands [.gpr 0, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[341, 332, 354]
    (.letOp (n := 359) (.out 0x11b77b (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77b 15 2)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[348, 344, 357]
    (.letOp (n := 360) (.out 0x11b77b (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77b 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[348, 344, 357]
    (.letOp (n := 361) (.exec 0x11b77b (fun s => s.RIP = 0x11b77b) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77b 15 2)) (Reg.operands [.gpr 15, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[348, 344, 357]
    (.letOp (n := 362) (.out 0x11b77e (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77e 3 6)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 3))) #v[351, 320, 360]
    (.letOp (n := 363) (.out 0x11b77e (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77e 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[351, 320, 360]
    (.letOp (n := 364) (.exec 0x11b77e (fun s => s.RIP = 0x11b77e) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b77e 3 6)) (Reg.operands [.gpr 3, .gpr 6, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[351, 320, 360]
    (.letOp (n := 365) (.out 0x11b781 (atFlags (condHolds 2) (setccR8Effect 0x11b781 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[292, 363]
    (.letOp (n := 366) (.exec 0x11b781 (fun s => s.RIP = 0x11b781) (atFlags (condHolds 2) (setccR8Effect 0x11b781 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[292, 363]
    (.letOp (n := 367) (.exec 0x11b785 (StorePre 0x11b785 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b785 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b785 7 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 7, .gpr 4] [])) #v[353, 4]
    (.letOp (n := 368) (.out 0x11b78a (leaR64Effect 0x11b78a 2 (.sib 10 (some 7) 0 .none)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 10, .gpr 7] []) (.reg (.gpr 2))) #v[327, 353]
    (.letOp (n := 369) (.exec 0x11b78a (fun s => s.RIP = 0x11b78a) (leaR64Effect 0x11b78a 2 (.sib 10 (some 7) 0 .none)) (Reg.operands [.gpr 10, .gpr 7] [])) #v[327, 353]
    (.letOp (n := 370) (.exec 0x11b78e (StorePre 0x11b78e 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b78e + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b78e 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 2, .gpr 4] [])) #v[368, 4]
    (.letOp (n := 371) (.out 0x11b793 (notR64Effect 0x11b793 7) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7] []) (.reg (.gpr 7))) #v[353]
    (.letOp (n := 372) (.exec 0x11b793 (fun s => s.RIP = 0x11b793) (notR64Effect 0x11b793 7) (Reg.operands [.gpr 7] [])) #v[353]
    (.letOp (n := 373) (.out 0x11b796 (orR64R64Effect 0x11b796 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 7, .gpr 2] []) (.reg (.gpr 7))) #v[371, 368]
    (.letOp (n := 374) (.exec 0x11b796 (fun s => s.RIP = 0x11b796) (orR64R64Effect 0x11b796 7 2) (Reg.operands [.gpr 7, .gpr 2] [])) #v[371, 368]
    (b_l11b5ba_7))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_6 : List UInt8 :=
  [0x49, 0xF7, 0xE2, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xC7, 0x4C, 0x89, 0xF8, 0x49, 0xF7, 0xE1, 0x4C,
    0x01, 0xD8, 0x48, 0x83, 0xD2, 0x00, 0x31, 0xDB, 0x4D, 0x01, 0xC7, 0x0F, 0x92, 0xC3, 0x48, 0x03,
    0x7C, 0x24, 0x10, 0x48, 0x11, 0xC8, 0x49, 0x11, 0xD7, 0x48, 0x11, 0xF3, 0x41, 0x0F, 0x92, 0xC0,
    0x48, 0x89, 0x7C, 0x24, 0x10, 0x49, 0x8D, 0x14, 0x3A, 0x48, 0x89, 0x54, 0x24, 0x20, 0x48, 0xF7,
    0xD7, 0x48, 0x09, 0xD7] ++ bytes_l11b5ba_7

theorem code_l11b5ba_6 : ∀ x ∈ codeRange 0x11b755 bytes_l11b5ba_6, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b755 68 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_7

@[cfg_block] def b_l11b5ba_5 : Block Op Label signature Reg.count 283 :=
  .letOp (n := 283) (.out 0x11b714 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b714 2 1)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[278, 271, 281]
    (.letOp (n := 284) (.exec 0x11b714 (fun s => s.RIP = 0x11b714) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b714 2 1)) (Reg.operands [.gpr 2, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[278, 271, 281]
    (.letOp (n := 285) (.out 0x11b717 (xorR32R32Effect 0x11b717 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[271, 271]
    (.letOp (n := 286) (.exec 0x11b717 (fun s => s.RIP = 0x11b717) (xorR32R32Effect 0x11b717 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[271, 271]
    (.letOp (n := 287) (.out 0x11b719 (addR64R64Effect 0x11b719 8 0) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 0] []) (.reg (.gpr 8))) #v[280, 277]
    (.letOp (n := 288) (.out 0x11b719 (addR64R64Effect 0x11b719 8 0) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 0] []) (.flag .CF)) #v[280, 277]
    (.letOp (n := 289) (.exec 0x11b719 (fun s => s.RIP = 0x11b719) (addR64R64Effect 0x11b719 8 0) (Reg.operands [.gpr 8, .gpr 0] [])) #v[280, 277]
    (.letOp (n := 290) (.out 0x11b71c (atFlags (condHolds 2) (setccR8Effect 0x11b71c 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[285, 288]
    (.letOp (n := 291) (.exec 0x11b71c (fun s => s.RIP = 0x11b71c) (atFlags (condHolds 2) (setccR8Effect 0x11b71c 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[285, 288]
    (.letOp (n := 292) (.out 0x11b71f (addR64R64Effect 0x11b71f 8 15) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 15] []) (.reg (.gpr 8))) #v[287, 203]
    (.letOp (n := 293) (.out 0x11b71f (addR64R64Effect 0x11b71f 8 15) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 15] []) (.flag .CF)) #v[287, 203]
    (.letOp (n := 294) (.exec 0x11b71f (fun s => s.RIP = 0x11b71f) (addR64R64Effect 0x11b71f 8 15) (Reg.operands [.gpr 8, .gpr 15] [])) #v[287, 203]
    (.letOp (n := 295) (.out 0x11b722 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b722 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[290, 283, 293]
    (.letOp (n := 296) (.exec 0x11b722 (fun s => s.RIP = 0x11b722) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b722 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[290, 283, 293]
    (.letOp (n := 297) (.out 0x11b725 (xorR32R32Effect 0x11b725 2 0 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 0] []) (.reg (.gpr 0))) #v[277, 277]
    (.letOp (n := 298) (.exec 0x11b725 (fun s => s.RIP = 0x11b725) (xorR32R32Effect 0x11b725 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[277, 277]
    (.letOp (n := 299) (.out 0x11b727 (addR64R64Effect 0x11b727 1 6) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[295, 184]
    (.letOp (n := 300) (.out 0x11b727 (addR64R64Effect 0x11b727 1 6) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[295, 184]
    (.letOp (n := 301) (.exec 0x11b727 (fun s => s.RIP = 0x11b727) (addR64R64Effect 0x11b727 1 6) (Reg.operands [.gpr 1, .gpr 6] [])) #v[295, 184]
    (.letOp (n := 302) (.out 0x11b72a (atFlags (condHolds 2) (setccR8Effect 0x11b72a 3 0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[297, 300]
    (.letOp (n := 303) (.exec 0x11b72a (fun s => s.RIP = 0x11b72a) (atFlags (condHolds 2) (setccR8Effect 0x11b72a 3 0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[297, 300]
    (.letOp (n := 304) (.out 0x11b72d (addR64R64Effect 0x11b72d 14 7) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 7] []) (.reg (.gpr 14))) #v[206, 140]
    (.letOp (n := 305) (.out 0x11b72d (addR64R64Effect 0x11b72d 14 7) (EffectPart.reads (.flag .CF) [.gpr 14, .gpr 7] []) (.flag .CF)) #v[206, 140]
    (.letOp (n := 306) (.exec 0x11b72d (fun s => s.RIP = 0x11b72d) (addR64R64Effect 0x11b72d 14 7) (Reg.operands [.gpr 14, .gpr 7] [])) #v[206, 140]
    (.letOp (n := 307) (.out 0x11b730 (movR32Imm32Effect 0x11b730 5 6 0x0) (EffectPart.reads (.reg (.gpr 6)) [] []) (.reg (.gpr 6))) #v[]
    (.letOp (n := 308) (.exec 0x11b730 (fun s => s.RIP = 0x11b730) (movR32Imm32Effect 0x11b730 5 6 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 309) (.out 0x11b735 (atFlags (condHolds 2) (cmovR64R64Effect 0x11b735 4 6 9)) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 6))) #v[307, 275, 305]
    (.letOp (n := 310) (.exec 0x11b735 (fun s => s.RIP = 0x11b735) (atFlags (condHolds 2) (cmovR64R64Effect 0x11b735 4 6 9)) (Reg.operands [.gpr 6, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[307, 275, 305]
    (.letOp (n := 311) (.out 0x11b739 (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b739 0 0x0)) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 0))) #v[302, 305]
    (.letOp (n := 312) (.exec 0x11b739 (fun s => s.RIP = 0x11b739) (atFlags StatusFlags.CF (adcR64Imm8Effect 0x11b739 0 0x0)) (Reg.operands [.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[302, 305]
    (.letOp (n := 313) (.out 0x11b73d (xorR32R32Effect 0x11b73d 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[203, 203]
    (.letOp (n := 314) (.exec 0x11b73d (fun s => s.RIP = 0x11b73d) (xorR32R32Effect 0x11b73d 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[203, 203]
    (.letOp (n := 315) (.out 0x11b740 (addR64R64Effect 0x11b740 6 1) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 1] []) (.reg (.gpr 6))) #v[309, 299]
    (.letOp (n := 316) (.out 0x11b740 (addR64R64Effect 0x11b740 6 1) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 1] []) (.flag .CF)) #v[309, 299]
    (.letOp (n := 317) (.exec 0x11b740 (fun s => s.RIP = 0x11b740) (addR64R64Effect 0x11b740 6 1) (Reg.operands [.gpr 6, .gpr 1] [])) #v[309, 299]
    (.letOp (n := 318) (.out 0x11b743 (atFlags (condHolds 2) (setccR8Effect 0x11b743 4 15)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[313, 316]
    (.letOp (n := 319) (.exec 0x11b743 (fun s => s.RIP = 0x11b743) (atFlags (condHolds 2) (setccR8Effect 0x11b743 4 15)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[313, 316]
    (.letOp (n := 320) (.out 0x11b747 (addR64R64Effect 0x11b747 6 14) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 14] []) (.reg (.gpr 6))) #v[315, 304]
    (.letOp (n := 321) (.out 0x11b747 (addR64R64Effect 0x11b747 6 14) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 14] []) (.flag .CF)) #v[315, 304]
    (.letOp (n := 322) (.exec 0x11b747 (fun s => s.RIP = 0x11b747) (addR64R64Effect 0x11b747 6 14) (Reg.operands [.gpr 6, .gpr 14] [])) #v[315, 304]
    (.letOp (n := 323) (.out 0x11b74a (atFlags StatusFlags.CF (adcR64R64Effect 0x11b74a 15 0)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[318, 311, 321]
    (.letOp (n := 324) (.exec 0x11b74a (fun s => s.RIP = 0x11b74a) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b74a 15 0)) (Reg.operands [.gpr 15, .gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[318, 311, 321]
    (.letOp (n := 325) (.out 0x11b74d (movR64R64Effect 0x11b74d 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[323]
    (.letOp (n := 326) (.exec 0x11b74d (fun s => s.RIP = 0x11b74d) (movR64R64Effect 0x11b74d 0 15) (Reg.operands [.gpr 15] [])) #v[323]
    (.letOp (n := 327) (.out 0x11b750 (movR64M64Effect 0x11b750 10 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 4] []) (.reg (.gpr 10))) #v[4]
    (.letOp (n := 328) (.exec 0x11b750 (LoadPre 0x11b750 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b750 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b750 10 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11b5ba_6))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_5 : List UInt8 :=
  [0x48, 0x11, 0xCA, 0x31, 0xC9, 0x49, 0x01, 0xC0, 0x0F, 0x92, 0xC1, 0x4D, 0x01, 0xF8, 0x48, 0x11,
    0xD1, 0x31, 0xC0, 0x48, 0x01, 0xF1, 0x0F, 0x92, 0xC0, 0x49, 0x01, 0xFE, 0xBE, 0x00, 0x00, 0x00,
    0x00, 0x49, 0x0F, 0x42, 0xF1, 0x48, 0x83, 0xD0, 0x00, 0x45, 0x31, 0xFF, 0x48, 0x01, 0xCE, 0x41,
    0x0F, 0x92, 0xC7, 0x4C, 0x01, 0xF6, 0x49, 0x11, 0xC7, 0x4C, 0x89, 0xF8, 0x4C, 0x8B, 0x54, 0x24,
    0x20] ++ bytes_l11b5ba_6

theorem code_l11b5ba_5 : ∀ x ∈ codeRange 0x11b714 bytes_l11b5ba_5, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b714 65 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_6

@[cfg_block] def b_l11b5ba_4 : Block Op Label signature Reg.count 236 :=
  .letOp (n := 236) (.out 0x11b6c6 (movR64R64Effect 0x11b6c6 5 0) (EffectPart.reads (.reg (.gpr 5)) [.gpr 0] []) (.reg (.gpr 5))) #v[231]
    (.letOp (n := 237) (.exec 0x11b6c6 (fun s => s.RIP = 0x11b6c6) (movR64R64Effect 0x11b6c6 5 0) (Reg.operands [.gpr 0] [])) #v[231]
    (.letOp (n := 238) (.out 0x11b6c9 (movR64R64Effect 0x11b6c9 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[203]
    (.letOp (n := 239) (.exec 0x11b6c9 (fun s => s.RIP = 0x11b6c9) (movR64R64Effect 0x11b6c9 0 15) (Reg.operands [.gpr 15] [])) #v[203]
    (.letOp (n := 240) (.out 0x11b6cc (movR64Imm64Effect 0x11b6cc 2 0x4551231950b75fc4) (EffectPart.reads (.reg (.gpr 2)) [] []) (.reg (.gpr 2))) #v[]
    (.letOp (n := 241) (.exec 0x11b6cc (fun s => s.RIP = 0x11b6cc) (movR64Imm64Effect 0x11b6cc 2 0x4551231950b75fc4) (Reg.operands [] [])) #v[]
    (.letOp (n := 242) (.out 0x11b6d6 (mulR64Effect 0x11b6d6 2) (EffectPart.reads (.reg (.gpr 0)) [.gpr 2, .gpr 0] []) (.reg (.gpr 0))) #v[240, 238]
    (.letOp (n := 243) (.out 0x11b6d6 (mulR64Effect 0x11b6d6 2) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 0] []) (.reg (.gpr 2))) #v[240, 238]
    (.letOp (n := 244) (.exec 0x11b6d6 (fun s => s.RIP = 0x11b6d6) (mulR64Effect 0x11b6d6 2) (Reg.operands [.gpr 2, .gpr 0] [])) #v[240, 238]
    (.letOp (n := 245) (.out 0x11b6d9 (addR64M64Effect 0x11b6d9 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 4] []) (.reg (.gpr 1))) #v[216, 4]
    (.letOp (n := 246) (.out 0x11b6d9 (addR64M64Effect 0x11b6d9 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 4] []) (.flag .CF)) #v[216, 4]
    (.letOp (n := 247) (.exec 0x11b6d9 (LoadPre 0x11b6d9 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b6d9 + BitVec.ofNat 64 5)) 8) (addR64M64Effect 0x11b6d9 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[216, 4]
    (.letOp (n := 248) (.exec 0x11b6de (StorePre 0x11b6de 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b6de + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b6de 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[245, 4]
    (.letOp (n := 249) (.out 0x11b6e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e3 11 3)) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 11))) #v[218, 100, 246]
    (.letOp (n := 250) (.out 0x11b6e3 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e3 11 3)) (Reg.operands [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.flag .CF)) #v[218, 100, 246]
    (.letOp (n := 251) (.exec 0x11b6e3 (fun s => s.RIP = 0x11b6e3) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e3 11 3)) (Reg.operands [.gpr 11, .gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[218, 100, 246]
    (.letOp (n := 252) (.out 0x11b6e6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e6 2 13)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[243, 234, 250]
    (.letOp (n := 253) (.exec 0x11b6e6 (fun s => s.RIP = 0x11b6e6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6e6 2 13)) (Reg.operands [.gpr 2, .gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[243, 234, 250]
    (.letOp (n := 254) (.out 0x11b6e9 (xorR32R32Effect 0x11b6e9 3 8 8) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 8] []) (.reg (.gpr 8))) #v[210, 210]
    (.letOp (n := 255) (.exec 0x11b6e9 (fun s => s.RIP = 0x11b6e9) (xorR32R32Effect 0x11b6e9 3 8 8) (Reg.operands [.gpr 8, .gpr 8] [])) #v[210, 210]
    (.letOp (n := 256) (.out 0x11b6ec (addR64R64Effect 0x11b6ec 11 5) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 5] []) (.reg (.gpr 11))) #v[249, 236]
    (.letOp (n := 257) (.out 0x11b6ec (addR64R64Effect 0x11b6ec 11 5) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 5] []) (.flag .CF)) #v[249, 236]
    (.letOp (n := 258) (.exec 0x11b6ec (fun s => s.RIP = 0x11b6ec) (addR64R64Effect 0x11b6ec 11 5) (Reg.operands [.gpr 11, .gpr 5] [])) #v[249, 236]
    (.letOp (n := 259) (.out 0x11b6ef (atFlags (condHolds 2) (setccR8Effect 0x11b6ef 4 8)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[254, 257]
    (.letOp (n := 260) (.exec 0x11b6ef (fun s => s.RIP = 0x11b6ef) (atFlags (condHolds 2) (setccR8Effect 0x11b6ef 4 8)) (Reg.operands [.gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[254, 257]
    (.letOp (n := 261) (.out 0x11b6f3 (addR64R64Effect 0x11b6f3 11 0) (EffectPart.reads (.reg (.gpr 11)) [.gpr 11, .gpr 0] []) (.reg (.gpr 11))) #v[256, 242]
    (.letOp (n := 262) (.out 0x11b6f3 (addR64R64Effect 0x11b6f3 11 0) (EffectPart.reads (.flag .CF) [.gpr 11, .gpr 0] []) (.flag .CF)) #v[256, 242]
    (.letOp (n := 263) (.exec 0x11b6f3 (fun s => s.RIP = 0x11b6f3) (addR64R64Effect 0x11b6f3 11 0) (Reg.operands [.gpr 11, .gpr 0] [])) #v[256, 242]
    (.letOp (n := 264) (.out 0x11b6f6 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6f6 8 2)) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 8))) #v[259, 252, 262]
    (.letOp (n := 265) (.exec 0x11b6f6 (fun s => s.RIP = 0x11b6f6) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b6f6 8 2)) (Reg.operands [.gpr 8, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[259, 252, 262]
    (.letOp (n := 266) (.out 0x11b6f9 (xorR32R32Effect 0x11b6f9 2 1 1) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 1] []) (.reg (.gpr 1))) #v[245, 245]
    (.letOp (n := 267) (.exec 0x11b6f9 (fun s => s.RIP = 0x11b6f9) (xorR32R32Effect 0x11b6f9 2 1 1) (Reg.operands [.gpr 1, .gpr 1] [])) #v[245, 245]
    (.letOp (n := 268) (.out 0x11b6fb (addR64R64Effect 0x11b6fb 8 9) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 9] []) (.reg (.gpr 8))) #v[264, 144]
    (.letOp (n := 269) (.out 0x11b6fb (addR64R64Effect 0x11b6fb 8 9) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 9] []) (.flag .CF)) #v[264, 144]
    (.letOp (n := 270) (.exec 0x11b6fb (fun s => s.RIP = 0x11b6fb) (addR64R64Effect 0x11b6fb 8 9) (Reg.operands [.gpr 8, .gpr 9] [])) #v[264, 144]
    (.letOp (n := 271) (.out 0x11b6fe (atFlags (condHolds 2) (setccR8Effect 0x11b6fe 3 1)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 1))) #v[266, 269]
    (.letOp (n := 272) (.exec 0x11b6fe (fun s => s.RIP = 0x11b6fe) (atFlags (condHolds 2) (setccR8Effect 0x11b6fe 3 1)) (Reg.operands [.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[266, 269]
    (.letOp (n := 273) (.out 0x11b701 (movR64R64Effect 0x11b701 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[222]
    (.letOp (n := 274) (.exec 0x11b701 (fun s => s.RIP = 0x11b701) (movR64R64Effect 0x11b701 0 12) (Reg.operands [.gpr 12] [])) #v[222]
    (.letOp (n := 275) (.out 0x11b704 (movR64Imm64Effect 0x11b704 9 0x4551231950b75fc4) (EffectPart.reads (.reg (.gpr 9)) [] []) (.reg (.gpr 9))) #v[]
    (.letOp (n := 276) (.exec 0x11b704 (fun s => s.RIP = 0x11b704) (movR64Imm64Effect 0x11b704 9 0x4551231950b75fc4) (Reg.operands [] [])) #v[]
    (.letOp (n := 277) (.out 0x11b70e (mulR64Effect 0x11b70e 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[275, 273]
    (.letOp (n := 278) (.out 0x11b70e (mulR64Effect 0x11b70e 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[275, 273]
    (.letOp (n := 279) (.exec 0x11b70e (fun s => s.RIP = 0x11b70e) (mulR64Effect 0x11b70e 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[275, 273]
    (.letOp (n := 280) (.out 0x11b711 (addR64R64Effect 0x11b711 8 10) (EffectPart.reads (.reg (.gpr 8)) [.gpr 8, .gpr 10] []) (.reg (.gpr 8))) #v[268, 227]
    (.letOp (n := 281) (.out 0x11b711 (addR64R64Effect 0x11b711 8 10) (EffectPart.reads (.flag .CF) [.gpr 8, .gpr 10] []) (.flag .CF)) #v[268, 227]
    (.letOp (n := 282) (.exec 0x11b711 (fun s => s.RIP = 0x11b711) (addR64R64Effect 0x11b711 8 10) (Reg.operands [.gpr 8, .gpr 10] [])) #v[268, 227]
    (b_l11b5ba_5)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_4 : List UInt8 :=
  [0x48, 0x89, 0xC5, 0x4C, 0x89, 0xF8, 0x48, 0xBA, 0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45,
    0x48, 0xF7, 0xE2, 0x48, 0x03, 0x4C, 0x24, 0x10, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x49, 0x11, 0xDB,
    0x4C, 0x11, 0xEA, 0x45, 0x31, 0xC0, 0x49, 0x01, 0xEB, 0x41, 0x0F, 0x92, 0xC0, 0x49, 0x01, 0xC3,
    0x49, 0x11, 0xD0, 0x31, 0xC9, 0x4D, 0x01, 0xC8, 0x0F, 0x92, 0xC1, 0x4C, 0x89, 0xE0, 0x49, 0xB9,
    0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45, 0x49, 0xF7, 0xE1, 0x4D, 0x01, 0xD0] ++ bytes_l11b5ba_5

theorem code_l11b5ba_4 : ∀ x ∈ codeRange 0x11b6c6 bytes_l11b5ba_4, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b6c6 78 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_5

@[cfg_block] def b_l11b5ba_3 : Block Op Label signature Reg.count 191 :=
  .letOp (n := 191) (.out 0x11b683 (mulR64Effect 0x11b683 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[77, 189]
    (.letOp (n := 192) (.out 0x11b683 (mulR64Effect 0x11b683 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[77, 189]
    (.letOp (n := 193) (.exec 0x11b683 (fun s => s.RIP = 0x11b683) (mulR64Effect 0x11b683 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 189]
    (.letOp (n := 194) (.out 0x11b686 (movR64R64Effect 0x11b686 15 0) (EffectPart.reads (.reg (.gpr 15)) [.gpr 0] []) (.reg (.gpr 15))) #v[191]
    (.letOp (n := 195) (.exec 0x11b686 (fun s => s.RIP = 0x11b686) (movR64R64Effect 0x11b686 15 0) (Reg.operands [.gpr 0] [])) #v[191]
    (.letOp (n := 196) (.out 0x11b689 (xorR32R32Effect 0x11b689 3 14 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 14] []) (.reg (.gpr 14))) #v[161, 161]
    (.letOp (n := 197) (.exec 0x11b689 (fun s => s.RIP = 0x11b689) (xorR32R32Effect 0x11b689 3 14 14) (Reg.operands [.gpr 14, .gpr 14] [])) #v[161, 161]
    (.letOp (n := 198) (.out 0x11b68c (addR64R64Effect 0x11b68c 15 10) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 10] []) (.reg (.gpr 15))) #v[194, 187]
    (.letOp (n := 199) (.out 0x11b68c (addR64R64Effect 0x11b68c 15 10) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 10] []) (.flag .CF)) #v[194, 187]
    (.letOp (n := 200) (.exec 0x11b68c (fun s => s.RIP = 0x11b68c) (addR64R64Effect 0x11b68c 15 10) (Reg.operands [.gpr 15, .gpr 10] [])) #v[194, 187]
    (.letOp (n := 201) (.out 0x11b68f (atFlags (condHolds 2) (setccR8Effect 0x11b68f 4 14)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[196, 199]
    (.letOp (n := 202) (.exec 0x11b68f (fun s => s.RIP = 0x11b68f) (atFlags (condHolds 2) (setccR8Effect 0x11b68f 4 14)) (Reg.operands [.gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[196, 199]
    (.letOp (n := 203) (.out 0x11b693 (addR64R64Effect 0x11b693 15 11) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 11] []) (.reg (.gpr 15))) #v[198, 105]
    (.letOp (n := 204) (.out 0x11b693 (addR64R64Effect 0x11b693 15 11) (EffectPart.reads (.flag .CF) [.gpr 15, .gpr 11] []) (.flag .CF)) #v[198, 105]
    (.letOp (n := 205) (.exec 0x11b693 (fun s => s.RIP = 0x11b693) (addR64R64Effect 0x11b693 15 11) (Reg.operands [.gpr 15, .gpr 11] [])) #v[198, 105]
    (.letOp (n := 206) (.out 0x11b696 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b696 14 2)) (EffectPart.reads (.reg (.gpr 14)) [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 14))) #v[201, 192, 204]
    (.letOp (n := 207) (.exec 0x11b696 (fun s => s.RIP = 0x11b696) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b696 14 2)) (Reg.operands [.gpr 14, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[201, 192, 204]
    (.letOp (n := 208) (.out 0x11b699 (movR64R64Effect 0x11b699 0 15) (EffectPart.reads (.reg (.gpr 0)) [.gpr 15] []) (.reg (.gpr 0))) #v[203]
    (.letOp (n := 209) (.exec 0x11b699 (fun s => s.RIP = 0x11b699) (movR64R64Effect 0x11b699 0 15) (Reg.operands [.gpr 15] [])) #v[203]
    (.letOp (n := 210) (.out 0x11b69c (movR64R64Effect 0x11b69c 8 12) (EffectPart.reads (.reg (.gpr 8)) [.gpr 12] []) (.reg (.gpr 8))) #v[73]
    (.letOp (n := 211) (.exec 0x11b69c (fun s => s.RIP = 0x11b69c) (movR64R64Effect 0x11b69c 8 12) (Reg.operands [.gpr 12] [])) #v[73]
    (.letOp (n := 212) (.exec 0x11b69f (StorePre 0x11b69f 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b69f + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b69f 12 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 12, .gpr 4] [])) #v[73, 4]
    (.letOp (n := 213) (.out 0x11b6a4 (mulR64Effect 0x11b6a4 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[73, 208]
    (.letOp (n := 214) (.out 0x11b6a4 (mulR64Effect 0x11b6a4 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[73, 208]
    (.letOp (n := 215) (.exec 0x11b6a4 (fun s => s.RIP = 0x11b6a4) (mulR64Effect 0x11b6a4 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[73, 208]
    (.letOp (n := 216) (.out 0x11b6a7 (movR64R64Effect 0x11b6a7 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[213]
    (.letOp (n := 217) (.exec 0x11b6a7 (fun s => s.RIP = 0x11b6a7) (movR64R64Effect 0x11b6a7 1 0) (Reg.operands [.gpr 0] [])) #v[213]
    (.letOp (n := 218) (.out 0x11b6aa (movR64R64Effect 0x11b6aa 11 2) (EffectPart.reads (.reg (.gpr 11)) [.gpr 2] []) (.reg (.gpr 11))) #v[214]
    (.letOp (n := 219) (.exec 0x11b6aa (fun s => s.RIP = 0x11b6aa) (movR64R64Effect 0x11b6aa 11 2) (Reg.operands [.gpr 2] [])) #v[214]
    (.letOp (n := 220) (.out 0x11b6ad (movR64R64Effect 0x11b6ad 12 14) (EffectPart.reads (.reg (.gpr 12)) [.gpr 14] []) (.reg (.gpr 12))) #v[206]
    (.letOp (n := 221) (.exec 0x11b6ad (fun s => s.RIP = 0x11b6ad) (movR64R64Effect 0x11b6ad 12 14) (Reg.operands [.gpr 14] [])) #v[206]
    (.letOp (n := 222) (.out 0x11b6b0 (addR64R64Effect 0x11b6b0 12 7) (EffectPart.reads (.reg (.gpr 12)) [.gpr 12, .gpr 7] []) (.reg (.gpr 12))) #v[220, 140]
    (.letOp (n := 223) (.out 0x11b6b0 (addR64R64Effect 0x11b6b0 12 7) (EffectPart.reads (.flag .CF) [.gpr 12, .gpr 7] []) (.flag .CF)) #v[220, 140]
    (.letOp (n := 224) (.exec 0x11b6b0 (fun s => s.RIP = 0x11b6b0) (addR64R64Effect 0x11b6b0 12 7) (Reg.operands [.gpr 12, .gpr 7] [])) #v[220, 140]
    (.letOp (n := 225) (.out 0x11b6b3 (movR32Imm32Effect 0x11b6b3 6 10 0x0) (EffectPart.reads (.reg (.gpr 10)) [] []) (.reg (.gpr 10))) #v[]
    (.letOp (n := 226) (.exec 0x11b6b3 (fun s => s.RIP = 0x11b6b3) (movR32Imm32Effect 0x11b6b3 6 10 0x0) (Reg.operands [] [])) #v[]
    (.letOp (n := 227) (.out 0x11b6b9 (atFlags (condHolds 2) (cmovR64R64Effect 0x11b6b9 4 10 8)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[225, 210, 223]
    (.letOp (n := 228) (.exec 0x11b6b9 (fun s => s.RIP = 0x11b6b9) (atFlags (condHolds 2) (cmovR64R64Effect 0x11b6b9 4 10 8)) (Reg.operands [.gpr 10, .gpr 8, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[225, 210, 223]
    (.letOp (n := 229) (.out 0x11b6bd (movR64R64Effect 0x11b6bd 0 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12] []) (.reg (.gpr 0))) #v[222]
    (.letOp (n := 230) (.exec 0x11b6bd (fun s => s.RIP = 0x11b6bd) (movR64R64Effect 0x11b6bd 0 12) (Reg.operands [.gpr 12] [])) #v[222]
    (.letOp (n := 231) (.out 0x11b6c0 (mulR64Effect 0x11b6c0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8, .gpr 0] []) (.reg (.gpr 0))) #v[210, 229]
    (.letOp (n := 232) (.out 0x11b6c0 (mulR64Effect 0x11b6c0 8) (EffectPart.reads (.reg (.gpr 2)) [.gpr 8, .gpr 0] []) (.reg (.gpr 2))) #v[210, 229]
    (.letOp (n := 233) (.exec 0x11b6c0 (fun s => s.RIP = 0x11b6c0) (mulR64Effect 0x11b6c0 8) (Reg.operands [.gpr 8, .gpr 0] [])) #v[210, 229]
    (.letOp (n := 234) (.out 0x11b6c3 (movR64R64Effect 0x11b6c3 13 2) (EffectPart.reads (.reg (.gpr 13)) [.gpr 2] []) (.reg (.gpr 13))) #v[232]
    (.letOp (n := 235) (.exec 0x11b6c3 (fun s => s.RIP = 0x11b6c3) (movR64R64Effect 0x11b6c3 13 2) (Reg.operands [.gpr 2] [])) #v[232]
    (b_l11b5ba_4)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_3 : List UInt8 :=
  [0x49, 0xF7, 0xE5, 0x49, 0x89, 0xC7, 0x45, 0x31, 0xF6, 0x4D, 0x01, 0xD7, 0x41, 0x0F, 0x92, 0xC6,
    0x4D, 0x01, 0xDF, 0x49, 0x11, 0xD6, 0x4C, 0x89, 0xF8, 0x4D, 0x89, 0xE0, 0x4C, 0x89, 0x64, 0x24,
    0x20, 0x49, 0xF7, 0xE4, 0x48, 0x89, 0xC1, 0x49, 0x89, 0xD3, 0x4D, 0x89, 0xF4, 0x49, 0x01, 0xFC,
    0x41, 0xBA, 0x00, 0x00, 0x00, 0x00, 0x4D, 0x0F, 0x42, 0xD0, 0x4C, 0x89, 0xE0, 0x49, 0xF7, 0xE0,
    0x49, 0x89, 0xD5] ++ bytes_l11b5ba_4

theorem code_l11b5ba_3 : ∀ x ∈ codeRange 0x11b683 bytes_l11b5ba_3, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b683 67 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_4

@[cfg_block] def b_l11b5ba_2 : Block Op Label signature Reg.count 144 :=
  .letOp (n := 144) (.out 0x11b644 (addR64R64Effect 0x11b644 9 14) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 14] []) (.reg (.gpr 9))) #v[137, 53]
    (.letOp (n := 145) (.out 0x11b644 (addR64R64Effect 0x11b644 9 14) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 14] []) (.flag .CF)) #v[137, 53]
    (.letOp (n := 146) (.exec 0x11b644 (fun s => s.RIP = 0x11b644) (addR64R64Effect 0x11b644 9 14) (Reg.operands [.gpr 9, .gpr 14] [])) #v[137, 53]
    (.letOp (n := 147) (.out 0x11b647 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b647 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[142, 133, 145]
    (.letOp (n := 148) (.exec 0x11b647 (fun s => s.RIP = 0x11b647) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b647 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[142, 133, 145]
    (.letOp (n := 149) (.out 0x11b64a (xorR32R32Effect 0x11b64a 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[112, 112]
    (.letOp (n := 150) (.exec 0x11b64a (fun s => s.RIP = 0x11b64a) (xorR32R32Effect 0x11b64a 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[112, 112]
    (.letOp (n := 151) (.out 0x11b64d (addR64M64Effect 0x11b64d 10 (.base 6 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[147, 6]
    (.letOp (n := 152) (.out 0x11b64d (addR64M64Effect 0x11b64d 10 (.base 6 (.d8 0x18))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[147, 6]
    (.letOp (n := 153) (.exec 0x11b64d (LoadPre 0x11b64d (fun s => AddrMode.addr (.base 6 (.d8 0x18)) s (0x11b64d + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11b64d 10 (.base 6 (.d8 0x18))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[147, 6]
    (.letOp (n := 154) (.out 0x11b651 (atFlags (condHolds 2) (setccR8Effect 0x11b651 4 15)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[149, 152]
    (.letOp (n := 155) (.exec 0x11b651 (fun s => s.RIP = 0x11b651) (atFlags (condHolds 2) (setccR8Effect 0x11b651 4 15)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[149, 152]
    (.letOp (n := 156) (.out 0x11b655 (movR64R64Effect 0x11b655 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[140]
    (.letOp (n := 157) (.exec 0x11b655 (fun s => s.RIP = 0x11b655) (movR64R64Effect 0x11b655 0 7) (Reg.operands [.gpr 7] [])) #v[140]
    (.letOp (n := 158) (.out 0x11b658 (mulR64Effect 0x11b658 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[73, 156]
    (.letOp (n := 159) (.out 0x11b658 (mulR64Effect 0x11b658 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[73, 156]
    (.letOp (n := 160) (.exec 0x11b658 (fun s => s.RIP = 0x11b658) (mulR64Effect 0x11b658 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[73, 156]
    (.letOp (n := 161) (.out 0x11b65b (movR64R64Effect 0x11b65b 14 2) (EffectPart.reads (.reg (.gpr 14)) [.gpr 2] []) (.reg (.gpr 14))) #v[159]
    (.letOp (n := 162) (.exec 0x11b65b (fun s => s.RIP = 0x11b65b) (movR64R64Effect 0x11b65b 14 2) (Reg.operands [.gpr 2] [])) #v[159]
    (.letOp (n := 163) (.out 0x11b65e (movR64R64Effect 0x11b65e 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 0] []) (.reg (.gpr 6))) #v[158]
    (.letOp (n := 164) (.exec 0x11b65e (fun s => s.RIP = 0x11b65e) (movR64R64Effect 0x11b65e 6 0) (Reg.operands [.gpr 0] [])) #v[158]
    (.letOp (n := 165) (.out 0x11b661 (movR64R64Effect 0x11b661 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 166) (.exec 0x11b661 (fun s => s.RIP = 0x11b661) (movR64R64Effect 0x11b661 0 11) (Reg.operands [.gpr 11] [])) #v[105]
    (.letOp (n := 167) (.out 0x11b664 (mulR64Effect 0x11b664 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[77, 165]
    (.letOp (n := 168) (.out 0x11b664 (mulR64Effect 0x11b664 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[77, 165]
    (.letOp (n := 169) (.exec 0x11b664 (fun s => s.RIP = 0x11b664) (mulR64Effect 0x11b664 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 165]
    (.letOp (n := 170) (.out 0x11b667 (addR64R64Effect 0x11b667 2 14) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 14] []) (.reg (.gpr 2))) #v[168, 161]
    (.letOp (n := 171) (.exec 0x11b667 (fun s => s.RIP = 0x11b667) (addR64R64Effect 0x11b667 2 14) (Reg.operands [.gpr 2, .gpr 14] [])) #v[168, 161]
    (.letOp (n := 172) (.out 0x11b66a (addR64R64Effect 0x11b66a 6 10) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 10] []) (.reg (.gpr 6))) #v[163, 151]
    (.letOp (n := 173) (.out 0x11b66a (addR64R64Effect 0x11b66a 6 10) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 10] []) (.flag .CF)) #v[163, 151]
    (.letOp (n := 174) (.exec 0x11b66a (fun s => s.RIP = 0x11b66a) (addR64R64Effect 0x11b66a 6 10) (Reg.operands [.gpr 6, .gpr 10] [])) #v[163, 151]
    (.letOp (n := 175) (.out 0x11b66d (atFlags StatusFlags.CF (adcR64R64Effect 0x11b66d 2 15)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[170, 154, 173]
    (.letOp (n := 176) (.exec 0x11b66d (fun s => s.RIP = 0x11b66d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b66d 2 15)) (Reg.operands [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[170, 154, 173]
    (.letOp (n := 177) (.out 0x11b670 (xorR32R32Effect 0x11b670 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[151, 151]
    (.letOp (n := 178) (.exec 0x11b670 (fun s => s.RIP = 0x11b670) (xorR32R32Effect 0x11b670 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[151, 151]
    (.letOp (n := 179) (.out 0x11b673 (addR64R64Effect 0x11b673 6 0) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 0] []) (.reg (.gpr 6))) #v[172, 167]
    (.letOp (n := 180) (.out 0x11b673 (addR64R64Effect 0x11b673 6 0) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 0] []) (.flag .CF)) #v[172, 167]
    (.letOp (n := 181) (.exec 0x11b673 (fun s => s.RIP = 0x11b673) (addR64R64Effect 0x11b673 6 0) (Reg.operands [.gpr 6, .gpr 0] [])) #v[172, 167]
    (.letOp (n := 182) (.out 0x11b676 (atFlags (condHolds 2) (setccR8Effect 0x11b676 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[177, 180]
    (.letOp (n := 183) (.exec 0x11b676 (fun s => s.RIP = 0x11b676) (atFlags (condHolds 2) (setccR8Effect 0x11b676 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[177, 180]
    (.letOp (n := 184) (.out 0x11b67a (addR64R64Effect 0x11b67a 6 8) (EffectPart.reads (.reg (.gpr 6)) [.gpr 6, .gpr 8] []) (.reg (.gpr 6))) #v[179, 55]
    (.letOp (n := 185) (.out 0x11b67a (addR64R64Effect 0x11b67a 6 8) (EffectPart.reads (.flag .CF) [.gpr 6, .gpr 8] []) (.flag .CF)) #v[179, 55]
    (.letOp (n := 186) (.exec 0x11b67a (fun s => s.RIP = 0x11b67a) (addR64R64Effect 0x11b67a 6 8) (Reg.operands [.gpr 6, .gpr 8] [])) #v[179, 55]
    (.letOp (n := 187) (.out 0x11b67d (atFlags StatusFlags.CF (adcR64R64Effect 0x11b67d 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[182, 175, 185]
    (.letOp (n := 188) (.exec 0x11b67d (fun s => s.RIP = 0x11b67d) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b67d 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[182, 175, 185]
    (.letOp (n := 189) (.out 0x11b680 (movR64R64Effect 0x11b680 0 7) (EffectPart.reads (.reg (.gpr 0)) [.gpr 7] []) (.reg (.gpr 0))) #v[140]
    (.letOp (n := 190) (.exec 0x11b680 (fun s => s.RIP = 0x11b680) (movR64R64Effect 0x11b680 0 7) (Reg.operands [.gpr 7] [])) #v[140]
    (b_l11b5ba_3)))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_2 : List UInt8 :=
  [0x4D, 0x01, 0xF1, 0x49, 0x11, 0xD2, 0x45, 0x31, 0xFF, 0x4C, 0x03, 0x56, 0x18, 0x41, 0x0F, 0x92,
    0xC7, 0x48, 0x89, 0xF8, 0x49, 0xF7, 0xE4, 0x49, 0x89, 0xD6, 0x48, 0x89, 0xC6, 0x4C, 0x89, 0xD8,
    0x49, 0xF7, 0xE5, 0x4C, 0x01, 0xF2, 0x4C, 0x01, 0xD6, 0x4C, 0x11, 0xFA, 0x45, 0x31, 0xD2, 0x48,
    0x01, 0xC6, 0x41, 0x0F, 0x92, 0xC2, 0x4C, 0x01, 0xC6, 0x49, 0x11, 0xD2, 0x48, 0x89, 0xF8] ++ bytes_l11b5ba_3

theorem code_l11b5ba_2 : ∀ x ∈ codeRange 0x11b644 bytes_l11b5ba_2, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b644 63 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_3

@[cfg_block] def b_l11b5ba_1 : Block Op Label signature Reg.count 98 :=
  .letOp (n := 98) (.out 0x11b602 (atFlags (condHolds 2) (setccR8Effect 0x11b602 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[93, 96]
    (.letOp (n := 99) (.exec 0x11b602 (fun s => s.RIP = 0x11b602) (atFlags (condHolds 2) (setccR8Effect 0x11b602 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[93, 96]
    (.letOp (n := 100) (.out 0x11b606 (addR64R64Effect 0x11b606 3 0) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 0] []) (.reg (.gpr 3))) #v[95, 81]
    (.letOp (n := 101) (.out 0x11b606 (addR64R64Effect 0x11b606 3 0) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 0] []) (.flag .CF)) #v[95, 81]
    (.letOp (n := 102) (.exec 0x11b606 (fun s => s.RIP = 0x11b606) (addR64R64Effect 0x11b606 3 0) (Reg.operands [.gpr 3, .gpr 0] [])) #v[95, 81]
    (.letOp (n := 103) (.out 0x11b609 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b609 10 2)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[98, 91, 101]
    (.letOp (n := 104) (.exec 0x11b609 (fun s => s.RIP = 0x11b609) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b609 10 2)) (Reg.operands [.gpr 10, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[98, 91, 101]
    (.letOp (n := 105) (.out 0x11b60c (movR64M64Effect 0x11b60c 11 (.base 6 (.d8 0x30))) (EffectPart.reads (.reg (.gpr 11)) [.gpr 6] []) (.reg (.gpr 11))) #v[6]
    (.letOp (n := 106) (.exec 0x11b60c (LoadPre 0x11b60c (fun s => AddrMode.addr (.base 6 (.d8 0x30)) s (0x11b60c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b60c 11 (.base 6 (.d8 0x30))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 107) (.out 0x11b610 (xorR32R32Effect 0x11b610 3 15 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 15] []) (.reg (.gpr 15))) #v[15, 15]
    (.letOp (n := 108) (.exec 0x11b610 (fun s => s.RIP = 0x11b610) (xorR32R32Effect 0x11b610 3 15 15) (Reg.operands [.gpr 15, .gpr 15] [])) #v[15, 15]
    (.letOp (n := 109) (.out 0x11b613 (addR64M64Effect 0x11b613 10 (.base 6 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 6] []) (.reg (.gpr 10))) #v[103, 6]
    (.letOp (n := 110) (.out 0x11b613 (addR64M64Effect 0x11b613 10 (.base 6 (.d8 0x10))) (EffectPart.reads (.flag .CF) [.gpr 10, .gpr 6] []) (.flag .CF)) #v[103, 6]
    (.letOp (n := 111) (.exec 0x11b613 (LoadPre 0x11b613 (fun s => AddrMode.addr (.base 6 (.d8 0x10)) s (0x11b613 + BitVec.ofNat 64 4)) 8) (addR64M64Effect 0x11b613 10 (.base 6 (.d8 0x10))) (Reg.operands [.gpr 10, .gpr 6] [])) #v[103, 6]
    (.letOp (n := 112) (.out 0x11b617 (atFlags (condHolds 2) (setccR8Effect 0x11b617 4 15)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 15))) #v[107, 110]
    (.letOp (n := 113) (.exec 0x11b617 (fun s => s.RIP = 0x11b617) (atFlags (condHolds 2) (setccR8Effect 0x11b617 4 15)) (Reg.operands [.gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[107, 110]
    (.letOp (n := 114) (.out 0x11b61b (movR64R64Effect 0x11b61b 0 11) (EffectPart.reads (.reg (.gpr 0)) [.gpr 11] []) (.reg (.gpr 0))) #v[105]
    (.letOp (n := 115) (.exec 0x11b61b (fun s => s.RIP = 0x11b61b) (movR64R64Effect 0x11b61b 0 11) (Reg.operands [.gpr 11] [])) #v[105]
    (.letOp (n := 116) (.out 0x11b61e (mulR64Effect 0x11b61e 12) (EffectPart.reads (.reg (.gpr 0)) [.gpr 12, .gpr 0] []) (.reg (.gpr 0))) #v[73, 114]
    (.letOp (n := 117) (.out 0x11b61e (mulR64Effect 0x11b61e 12) (EffectPart.reads (.reg (.gpr 2)) [.gpr 12, .gpr 0] []) (.reg (.gpr 2))) #v[73, 114]
    (.letOp (n := 118) (.exec 0x11b61e (fun s => s.RIP = 0x11b61e) (mulR64Effect 0x11b61e 12) (Reg.operands [.gpr 12, .gpr 0] [])) #v[73, 114]
    (.letOp (n := 119) (.out 0x11b621 (movR64R64Effect 0x11b621 7 2) (EffectPart.reads (.reg (.gpr 7)) [.gpr 2] []) (.reg (.gpr 7))) #v[117]
    (.letOp (n := 120) (.exec 0x11b621 (fun s => s.RIP = 0x11b621) (movR64R64Effect 0x11b621 7 2) (Reg.operands [.gpr 2] [])) #v[117]
    (.letOp (n := 121) (.out 0x11b624 (movR64R64Effect 0x11b624 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 0] []) (.reg (.gpr 9))) #v[116]
    (.letOp (n := 122) (.exec 0x11b624 (fun s => s.RIP = 0x11b624) (movR64R64Effect 0x11b624 9 0) (Reg.operands [.gpr 0] [])) #v[116]
    (.letOp (n := 123) (.out 0x11b627 (movR64R64Effect 0x11b627 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 124) (.exec 0x11b627 (fun s => s.RIP = 0x11b627) (movR64R64Effect 0x11b627 0 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 125) (.out 0x11b62a (mulR64Effect 0x11b62a 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[77, 123]
    (.letOp (n := 126) (.out 0x11b62a (mulR64Effect 0x11b62a 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[77, 123]
    (.letOp (n := 127) (.exec 0x11b62a (fun s => s.RIP = 0x11b62a) (mulR64Effect 0x11b62a 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 123]
    (.letOp (n := 128) (.out 0x11b62d (addR64R64Effect 0x11b62d 2 7) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 7] []) (.reg (.gpr 2))) #v[126, 119]
    (.letOp (n := 129) (.exec 0x11b62d (fun s => s.RIP = 0x11b62d) (addR64R64Effect 0x11b62d 2 7) (Reg.operands [.gpr 2, .gpr 7] [])) #v[126, 119]
    (.letOp (n := 130) (.out 0x11b630 (addR64R64Effect 0x11b630 9 10) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 10] []) (.reg (.gpr 9))) #v[121, 109]
    (.letOp (n := 131) (.out 0x11b630 (addR64R64Effect 0x11b630 9 10) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 10] []) (.flag .CF)) #v[121, 109]
    (.letOp (n := 132) (.exec 0x11b630 (fun s => s.RIP = 0x11b630) (addR64R64Effect 0x11b630 9 10) (Reg.operands [.gpr 9, .gpr 10] [])) #v[121, 109]
    (.letOp (n := 133) (.out 0x11b633 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b633 2 15)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[128, 112, 131]
    (.letOp (n := 134) (.exec 0x11b633 (fun s => s.RIP = 0x11b633) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b633 2 15)) (Reg.operands [.gpr 2, .gpr 15, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[128, 112, 131]
    (.letOp (n := 135) (.out 0x11b636 (xorR32R32Effect 0x11b636 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[109, 109]
    (.letOp (n := 136) (.exec 0x11b636 (fun s => s.RIP = 0x11b636) (xorR32R32Effect 0x11b636 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[109, 109]
    (.letOp (n := 137) (.out 0x11b639 (addR64R64Effect 0x11b639 9 0) (EffectPart.reads (.reg (.gpr 9)) [.gpr 9, .gpr 0] []) (.reg (.gpr 9))) #v[130, 125]
    (.letOp (n := 138) (.out 0x11b639 (addR64R64Effect 0x11b639 9 0) (EffectPart.reads (.flag .CF) [.gpr 9, .gpr 0] []) (.flag .CF)) #v[130, 125]
    (.letOp (n := 139) (.exec 0x11b639 (fun s => s.RIP = 0x11b639) (addR64R64Effect 0x11b639 9 0) (Reg.operands [.gpr 9, .gpr 0] [])) #v[130, 125]
    (.letOp (n := 140) (.out 0x11b63c (movR64M64Effect 0x11b63c 7 (.base 6 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 7)) [.gpr 6] []) (.reg (.gpr 7))) #v[6]
    (.letOp (n := 141) (.exec 0x11b63c (LoadPre 0x11b63c (fun s => AddrMode.addr (.base 6 (.d8 0x38)) s (0x11b63c + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b63c 7 (.base 6 (.d8 0x38))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 142) (.out 0x11b640 (atFlags (condHolds 2) (setccR8Effect 0x11b640 4 10)) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 10))) #v[135, 138]
    (.letOp (n := 143) (.exec 0x11b640 (fun s => s.RIP = 0x11b640) (atFlags (condHolds 2) (setccR8Effect 0x11b640 4 10)) (Reg.operands [.gpr 10, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[135, 138]
    (b_l11b5ba_2))))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba_1 : List UInt8 :=
  [0x41, 0x0F, 0x92, 0xC2, 0x48, 0x01, 0xC3, 0x49, 0x11, 0xD2, 0x4C, 0x8B, 0x5E, 0x30, 0x45, 0x31,
    0xFF, 0x4C, 0x03, 0x56, 0x10, 0x41, 0x0F, 0x92, 0xC7, 0x4C, 0x89, 0xD8, 0x49, 0xF7, 0xE4, 0x48,
    0x89, 0xD7, 0x49, 0x89, 0xC1, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE5, 0x48, 0x01, 0xFA, 0x4D, 0x01,
    0xD1, 0x4C, 0x11, 0xFA, 0x45, 0x31, 0xD2, 0x49, 0x01, 0xC1, 0x48, 0x8B, 0x7E, 0x38, 0x41, 0x0F,
    0x92, 0xC2] ++ bytes_l11b5ba_2

theorem code_l11b5ba_1 : ∀ x ∈ codeRange 0x11b602 bytes_l11b5ba_1, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b602 66 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_2

@[cfg_block] def b_l11b5ba : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11b5ba (movR64M64Effect 0x11b5ba 14 (.base 6 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 14)) [.gpr 6] []) (.reg (.gpr 14))) #v[6]
    (.letOp (n := 54) (.exec 0x11b5ba (LoadPre 0x11b5ba (fun s => AddrMode.addr (.base 6 (.d8 0x20)) s (0x11b5ba + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b5ba 14 (.base 6 (.d8 0x20))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 55) (.out 0x11b5be (movR64M64Effect 0x11b5be 8 (.base 6 (.d8 0x28))) (EffectPart.reads (.reg (.gpr 8)) [.gpr 6] []) (.reg (.gpr 8))) #v[6]
    (.letOp (n := 56) (.exec 0x11b5be (LoadPre 0x11b5be (fun s => AddrMode.addr (.base 6 (.d8 0x28)) s (0x11b5be + BitVec.ofNat 64 4)) 8) (movR64M64Effect 0x11b5be 8 (.base 6 (.d8 0x28))) (Reg.operands [.gpr 6] [])) #v[6]
    (.letOp (n := 57) (.out 0x11b5c2 (movR64R64Effect 0x11b5c2 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 58) (.exec 0x11b5c2 (fun s => s.RIP = 0x11b5c2) (movR64R64Effect 0x11b5c2 0 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 59) (.out 0x11b5c5 (mulR64Effect 0x11b5c5 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 57]
    (.letOp (n := 60) (.out 0x11b5c5 (mulR64Effect 0x11b5c5 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 57]
    (.letOp (n := 61) (.exec 0x11b5c5 (fun s => s.RIP = 0x11b5c5) (mulR64Effect 0x11b5c5 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 57]
    (.letOp (n := 62) (.out 0x11b5c8 (movR64R64Effect 0x11b5c8 3 2) (EffectPart.reads (.reg (.gpr 3)) [.gpr 2] []) (.reg (.gpr 3))) #v[60]
    (.letOp (n := 63) (.exec 0x11b5c8 (fun s => s.RIP = 0x11b5c8) (movR64R64Effect 0x11b5c8 3 2) (Reg.operands [.gpr 2] [])) #v[60]
    (.letOp (n := 64) (.out 0x11b5cb (movR64R64Effect 0x11b5cb 1 0) (EffectPart.reads (.reg (.gpr 1)) [.gpr 0] []) (.reg (.gpr 1))) #v[59]
    (.letOp (n := 65) (.exec 0x11b5cb (fun s => s.RIP = 0x11b5cb) (movR64R64Effect 0x11b5cb 1 0) (Reg.operands [.gpr 0] [])) #v[59]
    (.letOp (n := 66) (.out 0x11b5ce (movR64R64Effect 0x11b5ce 0 8) (EffectPart.reads (.reg (.gpr 0)) [.gpr 8] []) (.reg (.gpr 0))) #v[55]
    (.letOp (n := 67) (.exec 0x11b5ce (fun s => s.RIP = 0x11b5ce) (movR64R64Effect 0x11b5ce 0 8) (Reg.operands [.gpr 8] [])) #v[55]
    (.letOp (n := 68) (.out 0x11b5d1 (mulR64Effect 0x11b5d1 9) (EffectPart.reads (.reg (.gpr 0)) [.gpr 9, .gpr 0] []) (.reg (.gpr 0))) #v[9, 66]
    (.letOp (n := 69) (.out 0x11b5d1 (mulR64Effect 0x11b5d1 9) (EffectPart.reads (.reg (.gpr 2)) [.gpr 9, .gpr 0] []) (.reg (.gpr 2))) #v[9, 66]
    (.letOp (n := 70) (.exec 0x11b5d1 (fun s => s.RIP = 0x11b5d1) (mulR64Effect 0x11b5d1 9) (Reg.operands [.gpr 9, .gpr 0] [])) #v[9, 66]
    (.letOp (n := 71) (.out 0x11b5d4 (movR64R64Effect 0x11b5d4 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[68]
    (.letOp (n := 72) (.exec 0x11b5d4 (fun s => s.RIP = 0x11b5d4) (movR64R64Effect 0x11b5d4 7 0) (Reg.operands [.gpr 0] [])) #v[68]
    (.letOp (n := 73) (.out 0x11b5d7 (movR64R64Effect 0x11b5d7 12 9) (EffectPart.reads (.reg (.gpr 12)) [.gpr 9] []) (.reg (.gpr 12))) #v[9]
    (.letOp (n := 74) (.exec 0x11b5d7 (fun s => s.RIP = 0x11b5d7) (movR64R64Effect 0x11b5d7 12 9) (Reg.operands [.gpr 9] [])) #v[9]
    (.letOp (n := 75) (.out 0x11b5da (movR64R64Effect 0x11b5da 9 2) (EffectPart.reads (.reg (.gpr 9)) [.gpr 2] []) (.reg (.gpr 9))) #v[69]
    (.letOp (n := 76) (.exec 0x11b5da (fun s => s.RIP = 0x11b5da) (movR64R64Effect 0x11b5da 9 2) (Reg.operands [.gpr 2] [])) #v[69]
    (.letOp (n := 77) (.out 0x11b5dd (movR64Imm64Effect 0x11b5dd 13 0x4551231950b75fc4) (EffectPart.reads (.reg (.gpr 13)) [] []) (.reg (.gpr 13))) #v[]
    (.letOp (n := 78) (.exec 0x11b5dd (fun s => s.RIP = 0x11b5dd) (movR64Imm64Effect 0x11b5dd 13 0x4551231950b75fc4) (Reg.operands [] [])) #v[]
    (.letOp (n := 79) (.out 0x11b5e7 (movR64R64Effect 0x11b5e7 0 14) (EffectPart.reads (.reg (.gpr 0)) [.gpr 14] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 80) (.exec 0x11b5e7 (fun s => s.RIP = 0x11b5e7) (movR64R64Effect 0x11b5e7 0 14) (Reg.operands [.gpr 14] [])) #v[53]
    (.letOp (n := 81) (.out 0x11b5ea (mulR64Effect 0x11b5ea 13) (EffectPart.reads (.reg (.gpr 0)) [.gpr 13, .gpr 0] []) (.reg (.gpr 0))) #v[77, 79]
    (.letOp (n := 82) (.out 0x11b5ea (mulR64Effect 0x11b5ea 13) (EffectPart.reads (.reg (.gpr 2)) [.gpr 13, .gpr 0] []) (.reg (.gpr 2))) #v[77, 79]
    (.letOp (n := 83) (.exec 0x11b5ea (fun s => s.RIP = 0x11b5ea) (mulR64Effect 0x11b5ea 13) (Reg.operands [.gpr 13, .gpr 0] [])) #v[77, 79]
    (.letOp (n := 84) (.out 0x11b5ed (addR64M64Effect 0x11b5ed 1 (.base 6 .none)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 6] []) (.reg (.gpr 1))) #v[64, 6]
    (.letOp (n := 85) (.out 0x11b5ed (addR64M64Effect 0x11b5ed 1 (.base 6 .none)) (EffectPart.reads (.flag .CF) [.gpr 1, .gpr 6] []) (.flag .CF)) #v[64, 6]
    (.letOp (n := 86) (.exec 0x11b5ed (LoadPre 0x11b5ed (fun s => AddrMode.addr (.base 6 .none) s (0x11b5ed + BitVec.ofNat 64 3)) 8) (addR64M64Effect 0x11b5ed 1 (.base 6 .none)) (Reg.operands [.gpr 1, .gpr 6] [])) #v[64, 6]
    (.letOp (n := 87) (.exec 0x11b5f0 (StorePre 0x11b5f0 5 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b5f0 + BitVec.ofNat 64 5)) 8) (movM64R64Effect 0x11b5f0 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 1, .gpr 4] [])) #v[84, 4]
    (.letOp (n := 88) (.out 0x11b5f5 (atFlags StatusFlags.CF (adcR64M64Effect 0x11b5f5 3 (.base 6 (.d8 0x8)))) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 6] [.CF]) (.reg (.gpr 3))) #v[62, 6, 85]
    (.letOp (n := 89) (.out 0x11b5f5 (atFlags StatusFlags.CF (adcR64M64Effect 0x11b5f5 3 (.base 6 (.d8 0x8)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 6] [.CF]) (.flag .CF)) #v[62, 6, 85]
    (.letOp (n := 90) (.exec 0x11b5f5 (LoadPre 0x11b5f5 (fun s => AddrMode.addr (.base 6 (.d8 0x8)) s (0x11b5f5 + BitVec.ofNat 64 4)) 8) (atFlags StatusFlags.CF (adcR64M64Effect 0x11b5f5 3 (.base 6 (.d8 0x8)))) (Reg.operands [.gpr 3, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF, .gpr 6] [.CF])) #v[62, 6, 85]
    (.letOp (n := 91) (.out 0x11b5f9 (atFlags StatusFlags.CF (adcR64R64Effect 0x11b5f9 2 9)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF]) (.reg (.gpr 2))) #v[82, 75, 89]
    (.letOp (n := 92) (.exec 0x11b5f9 (fun s => s.RIP = 0x11b5f9) (atFlags StatusFlags.CF (adcR64R64Effect 0x11b5f9 2 9)) (Reg.operands [.gpr 2, .gpr 9, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.CF])) #v[82, 75, 89]
    (.letOp (n := 93) (.out 0x11b5fc (xorR32R32Effect 0x11b5fc 3 10 10) (EffectPart.reads (.reg (.gpr 10)) [.gpr 10, .gpr 10] []) (.reg (.gpr 10))) #v[10, 10]
    (.letOp (n := 94) (.exec 0x11b5fc (fun s => s.RIP = 0x11b5fc) (xorR32R32Effect 0x11b5fc 3 10 10) (Reg.operands [.gpr 10, .gpr 10] [])) #v[10, 10]
    (.letOp (n := 95) (.out 0x11b5ff (addR64R64Effect 0x11b5ff 3 7) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 7] []) (.reg (.gpr 3))) #v[88, 71]
    (.letOp (n := 96) (.out 0x11b5ff (addR64R64Effect 0x11b5ff 3 7) (EffectPart.reads (.flag .CF) [.gpr 3, .gpr 7] []) (.flag .CF)) #v[88, 71]
    (.letOp (n := 97) (.exec 0x11b5ff (fun s => s.RIP = 0x11b5ff) (addR64R64Effect 0x11b5ff 3 7) (Reg.operands [.gpr 3, .gpr 7] [])) #v[88, 71]
    (b_l11b5ba_1)))))))))))))))))))))))))))))))))))))))))))))

def bytes_l11b5ba : List UInt8 :=
  [0x4C, 0x8B, 0x76, 0x20, 0x4C, 0x8B, 0x46, 0x28, 0x4C, 0x89, 0xF0, 0x49, 0xF7, 0xE1, 0x48, 0x89,
    0xD3, 0x48, 0x89, 0xC1, 0x4C, 0x89, 0xC0, 0x49, 0xF7, 0xE1, 0x48, 0x89, 0xC7, 0x4D, 0x89, 0xCC,
    0x49, 0x89, 0xD1, 0x49, 0xBD, 0xC4, 0x5F, 0xB7, 0x50, 0x19, 0x23, 0x51, 0x45, 0x4C, 0x89, 0xF0,
    0x49, 0xF7, 0xE5, 0x48, 0x03, 0x0E, 0x48, 0x89, 0x4C, 0x24, 0x10, 0x48, 0x13, 0x5E, 0x08, 0x4C,
    0x11, 0xCA, 0x45, 0x31, 0xD2, 0x48, 0x01, 0xFB] ++ bytes_l11b5ba_1

theorem code_l11b5ba : ∀ x ∈ codeRange 0x11b5ba bytes_l11b5ba, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b5ba 72 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b5ba_1

@[cfg_block] def b_l11b864 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11b864 (StorePre 0x11b864 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b864 + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11b864 4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.out 0x11b868 (shrR64Effect 0x11b868 4 13 63) (EffectPart.reads (.reg (.gpr 13)) [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] []) (.reg (.gpr 13))) #v[13]
    (.letOp (n := 55) (.exec 0x11b868 (fun s => s.RIP = 0x11b868) (shrR64Effect 0x11b868 4 13 63) (Reg.operands [.gpr 13, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [])) #v[13]
    (.letOp (n := 56) (.out 0x11b86c (movR32R32Effect 0x11b86c 3 7 13) (EffectPart.reads (.reg (.gpr 7)) [.gpr 13] []) (.reg (.gpr 7))) #v[54]
    (.letOp (n := 57) (.exec 0x11b86c (fun s => s.RIP = 0x11b86c) (movR32R32Effect 0x11b86c 3 7 13) (Reg.operands [.gpr 13] [])) #v[54]
    (.letOp (n := 58) (.out 0x11b86f (callEffect (fun _ => 0x127d50) 0x11b874) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 59) (.exec 0x11b86f (PushPre 0x11b86f 5) (callEffect (fun _ => 0x127d50) 0x11b874) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 60) (.const ⟨64, 0x11b874⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 0), (1, 1), (2, 2), (3, 3), (4, 58), (5, 5), (6, 6), (7, 56), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 54), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 61⟩ { target := .l11b874, kept := #v[], arity := rfl, guard := some (Fin.last 60) })))))))))

def bytes_l11b864 : List UInt8 :=
  [0x88, 0x44, 0x24, 0x18, 0x49, 0xC1, 0xED, 0x3F, 0x44, 0x89, 0xEF, 0xE8, 0xDC, 0xC4, 0x00, 0x00]

theorem code_l11b864 : ∀ x ∈ codeRange 0x11b864 bytes_l11b864, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b864 16 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b874 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11b874 (notR8Effect 0x11b874 2 0) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[0]
    (.letOp (n := 54) (.exec 0x11b874 (fun s => s.RIP = 0x11b874) (notR8Effect 0x11b874 2 0) (Reg.operands [.gpr 0] [])) #v[0]
    (.letOp (n := 55) (.out 0x11b876 (andAlImm8Effect 0x11b876 0x1) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0] []) (.reg (.gpr 0))) #v[53]
    (.letOp (n := 56) (.exec 0x11b876 (fun s => s.RIP = 0x11b876) (andAlImm8Effect 0x11b876 0x1) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x11b878 (movzxR32R8Effect 0x11b878 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[55]
    (.letOp (n := 58) (.exec 0x11b878 (fun s => s.RIP = 0x11b878) (movzxR32R8Effect 0x11b878 3 7 0) (Reg.operands [.gpr 0] [])) #v[55]
    (.letOp (n := 59) (.out 0x11b87b (callEffect (fun _ => 0x127d50) 0x11b880) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 60) (.exec 0x11b87b (PushPre 0x11b87b 5) (callEffect (fun _ => 0x127d50) 0x11b880) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.const ⟨64, 0x11b880⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 55), (1, 1), (2, 2), (3, 3), (4, 59), (5, 5), (6, 6), (7, 57), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 62⟩ { target := .l11b880, kept := #v[], arity := rfl, guard := some (Fin.last 61) }))))))))))

def bytes_l11b874 : List UInt8 :=
  [0xF6, 0xD0, 0x24, 0x01, 0x0F, 0xB6, 0xF8, 0xE8, 0xD0, 0xC4, 0x00, 0x00]

theorem code_l11b874 : ∀ x ∈ codeRange 0x11b874 bytes_l11b874, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b874 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b880 : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.out 0x11b880 (orR8M8Effect 0x11b880 4 0 (.sib 4 none 0 (.d8 0x18))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 0, .gpr 4] []) (.reg (.gpr 0))) #v[0, 4]
    (.letOp (n := 54) (.exec 0x11b880 (LoadPre 0x11b880 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x18)) s (0x11b880 + BitVec.ofNat 64 4)) 1) (orR8M8Effect 0x11b880 4 0 (.sib 4 none 0 (.d8 0x18))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 55) (.out 0x11b884 (movzxR32R8Effect 0x11b884 3 7 0) (EffectPart.reads (.reg (.gpr 7)) [.gpr 0] []) (.reg (.gpr 7))) #v[53]
    (.letOp (n := 56) (.exec 0x11b884 (fun s => s.RIP = 0x11b884) (movzxR32R8Effect 0x11b884 3 7 0) (Reg.operands [.gpr 0] [])) #v[53]
    (.letOp (n := 57) (.out 0x11b887 (callEffect (fun _ => 0x127d50) 0x11b88c) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 58) (.exec 0x11b887 (PushPre 0x11b887 5) (callEffect (fun _ => 0x127d50) 0x11b88c) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.const ⟨64, 0x11b88c⟩) #v[]
    (.terminate (.call ⟨.l127d50, RegMap.args [(0, 53), (1, 1), (2, 2), (3, 3), (4, 57), (5, 5), (6, 6), (7, 55), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 60⟩ { target := .l11b88c, kept := #v[], arity := rfl, guard := some (Fin.last 59) }))))))))

def bytes_l11b880 : List UInt8 :=
  [0x0A, 0x44, 0x24, 0x18, 0x0F, 0xB6, 0xF8, 0xE8, 0xC4, 0xC4, 0x00, 0x00]

theorem code_l11b880 : ∀ x ∈ codeRange 0x11b880 bytes_l11b880, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b880 12 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b88c_1 : Block Op Label signature Reg.count 87 :=
  .letOp (n := 87) (.out 0x11b8d9 (popR64Effect 0x11b8d9 1 3) (EffectPart.reads (.reg (.gpr 3)) [.gpr 4] []) (.reg (.gpr 3))) #v[85]
    (.letOp (n := 88) (.out 0x11b8d9 (popR64Effect 0x11b8d9 1 3) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[85]
    (.letOp (n := 89) (.exec 0x11b8d9 (PopPre 0x11b8d9) (popR64Effect 0x11b8d9 1 3) (Reg.operands [.gpr 4] [])) #v[85]
    (.letOp (n := 90) (.out 0x11b8da (popR64Effect 0x11b8da 2 12) (EffectPart.reads (.reg (.gpr 12)) [.gpr 4] []) (.reg (.gpr 12))) #v[88]
    (.letOp (n := 91) (.out 0x11b8da (popR64Effect 0x11b8da 2 12) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[88]
    (.letOp (n := 92) (.exec 0x11b8da (PopPre 0x11b8da) (popR64Effect 0x11b8da 2 12) (Reg.operands [.gpr 4] [])) #v[88]
    (.letOp (n := 93) (.out 0x11b8dc (popR64Effect 0x11b8dc 2 13) (EffectPart.reads (.reg (.gpr 13)) [.gpr 4] []) (.reg (.gpr 13))) #v[91]
    (.letOp (n := 94) (.out 0x11b8dc (popR64Effect 0x11b8dc 2 13) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[91]
    (.letOp (n := 95) (.exec 0x11b8dc (PopPre 0x11b8dc) (popR64Effect 0x11b8dc 2 13) (Reg.operands [.gpr 4] [])) #v[91]
    (.letOp (n := 96) (.out 0x11b8de (popR64Effect 0x11b8de 2 14) (EffectPart.reads (.reg (.gpr 14)) [.gpr 4] []) (.reg (.gpr 14))) #v[94]
    (.letOp (n := 97) (.out 0x11b8de (popR64Effect 0x11b8de 2 14) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[94]
    (.letOp (n := 98) (.exec 0x11b8de (PopPre 0x11b8de) (popR64Effect 0x11b8de 2 14) (Reg.operands [.gpr 4] [])) #v[94]
    (.letOp (n := 99) (.out 0x11b8e0 (popR64Effect 0x11b8e0 2 15) (EffectPart.reads (.reg (.gpr 15)) [.gpr 4] []) (.reg (.gpr 15))) #v[97]
    (.letOp (n := 100) (.out 0x11b8e0 (popR64Effect 0x11b8e0 2 15) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[97]
    (.letOp (n := 101) (.exec 0x11b8e0 (PopPre 0x11b8e0) (popR64Effect 0x11b8e0 2 15) (Reg.operands [.gpr 4] [])) #v[97]
    (.letOp (n := 102) (.out 0x11b8e2 (popR64Effect 0x11b8e2 1 5) (EffectPart.reads (.reg (.gpr 5)) [.gpr 4] []) (.reg (.gpr 5))) #v[100]
    (.letOp (n := 103) (.out 0x11b8e2 (popR64Effect 0x11b8e2 1 5) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[100]
    (.letOp (n := 104) (.exec 0x11b8e2 (PopPre 0x11b8e2) (popR64Effect 0x11b8e2 1 5) (Reg.operands [.gpr 4] [])) #v[100]
    (.letOp (n := 105) (.out 0x11b8e3 (retEffect) (EffectPart.reads (.target) [.gpr 4] []) (.target)) #v[103]
    (.letOp (n := 106) (.out 0x11b8e3 (retEffect) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[103]
    (.letOp (n := 107) (.exec 0x11b8e3 (RetPre 0x11b8e3) (retEffect) (Reg.operands [.gpr 4] [])) #v[103]
    (.terminate (.ret (RegMap.args [(0, 79), (1, 63), (2, 69), (3, 87), (4, 106), (5, 102), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 90), (13, 93), (14, 96), (15, 99), (22, 22), (39, 39), (50, 50), (51, 51)] 108) (some ⟨105, by decide⟩)))))))))))))))))))))))

def bytes_l11b88c_1 : List UInt8 :=
  [0x5B, 0x41, 0x5C, 0x41, 0x5D, 0x41, 0x5E, 0x41, 0x5F, 0x5D, 0xC3]

theorem code_l11b88c_1 : ∀ x ∈ codeRange 0x11b8d9 bytes_l11b88c_1, x ∈ fnCode :=
  codeRange_sub_section (s := textSection) (.head _) 0x1b8d9 11 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl

@[cfg_block] def b_l11b88c : Block Op Label signature Reg.count 53 :=
  .letOp (n := 53) (.exec 0x11b88c (StorePre 0x11b88c 4 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b88c + BitVec.ofNat 64 4)) 1) (movM8R8Effect 0x11b88c 4 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 0, .gpr 4] [])) #v[0, 4]
    (.letOp (n := 54) (.exec 0x11b890 (fun s => s.RIP = 0x11b890) (leaR64Effect 0x11b890 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 55) (.out 0x11b895 (movzxR32M8Effect 0x11b895 5 0 (.sib 4 none 0 (.d8 0x8))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 56) (.exec 0x11b895 (LoadPre 0x11b895 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x8)) s (0x11b895 + BitVec.ofNat 64 5)) 1) (movzxR32M8Effect 0x11b895 5 0 (.sib 4 none 0 (.d8 0x8))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 57) (.out 0x11b89a (movR64M64Effect 0x11b89a 1 (.sib 4 none 0 (.d8 0x10))) (EffectPart.reads (.reg (.gpr 1)) [.gpr 4] []) (.reg (.gpr 1))) #v[4]
    (.letOp (n := 58) (.exec 0x11b89a (LoadPre 0x11b89a (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x10)) s (0x11b89a + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b89a 1 (.sib 4 none 0 (.d8 0x10))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 59) (.out 0x11b89f (movR64M64Effect 0x11b89f 2 (.sib 4 none 0 (.d8 0x20))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 60) (.exec 0x11b89f (LoadPre 0x11b89f (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x20)) s (0x11b89f + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b89f 2 (.sib 4 none 0 (.d8 0x20))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 61) (.out 0x11b8a4 (testR8R8Effect 0x11b8a4 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 62) (.exec 0x11b8a4 (fun s => s.RIP = 0x11b8a4) (testR8R8Effect 0x11b8a4 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 63) (.out 0x11b8a6 (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8a6 4 1 2)) (EffectPart.reads (.reg (.gpr 1)) [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 1))) #v[57, 59, 61]
    (.letOp (n := 64) (.exec 0x11b8a6 (fun s => s.RIP = 0x11b8a6) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8a6 4 1 2)) (Reg.operands [.gpr 1, .gpr 2, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[57, 59, 61]
    (.letOp (n := 65) (.out 0x11b8aa (movR64M64Effect 0x11b8aa 2 (.sib 4 none 0 (.d8 0x38))) (EffectPart.reads (.reg (.gpr 2)) [.gpr 4] []) (.reg (.gpr 2))) #v[4]
    (.letOp (n := 66) (.exec 0x11b8aa (LoadPre 0x11b8aa (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x38)) s (0x11b8aa + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b8aa 2 (.sib 4 none 0 (.d8 0x38))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 67) (.out 0x11b8af (testR8R8Effect 0x11b8af 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 68) (.exec 0x11b8af (fun s => s.RIP = 0x11b8af) (testR8R8Effect 0x11b8af 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 69) (.out 0x11b8b1 (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b1 4 2 12)) (EffectPart.reads (.reg (.gpr 2)) [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 2))) #v[65, 12, 67]
    (.letOp (n := 70) (.exec 0x11b8b1 (fun s => s.RIP = 0x11b8b1) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b1 4 2 12)) (Reg.operands [.gpr 2, .gpr 12, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[65, 12, 67]
    (.letOp (n := 71) (.out 0x11b8b5 (testR8R8Effect 0x11b8b5 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 72) (.exec 0x11b8b5 (fun s => s.RIP = 0x11b8b5) (testR8R8Effect 0x11b8b5 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 73) (.out 0x11b8b7 (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b7 4 15 14)) (EffectPart.reads (.reg (.gpr 15)) [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 15))) #v[15, 14, 71]
    (.letOp (n := 74) (.exec 0x11b8b7 (fun s => s.RIP = 0x11b8b7) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8b7 4 15 14)) (Reg.operands [.gpr 15, .gpr 14, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[15, 14, 71]
    (.letOp (n := 75) (.out 0x11b8bb (testR8R8Effect 0x11b8bb 2 0 0) (EffectPart.reads (.flag .ZF) [.gpr 0, .gpr 0] []) (.flag .ZF)) #v[55, 55]
    (.letOp (n := 76) (.exec 0x11b8bb (fun s => s.RIP = 0x11b8bb) (testR8R8Effect 0x11b8bb 2 0 0) (Reg.operands [.gpr 0, .gpr 0] [])) #v[55, 55]
    (.letOp (n := 77) (.out 0x11b8bd (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8bd 4 3 5)) (EffectPart.reads (.reg (.gpr 3)) [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF]) (.reg (.gpr 3))) #v[3, 5, 75]
    (.letOp (n := 78) (.exec 0x11b8bd (fun s => s.RIP = 0x11b8bd) (atFlags (condHolds 5) (cmovR64R64Effect 0x11b8bd 4 3 5)) (Reg.operands [.gpr 3, .gpr 5, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] [.ZF])) #v[3, 5, 75]
    (.letOp (n := 79) (.out 0x11b8c1 (movR64M64Effect 0x11b8c1 0 (.sib 4 none 0 (.d8 0x40))) (EffectPart.reads (.reg (.gpr 0)) [.gpr 4] []) (.reg (.gpr 0))) #v[4]
    (.letOp (n := 80) (.exec 0x11b8c1 (LoadPre 0x11b8c1 (fun s => AddrMode.addr (.sib 4 none 0 (.d8 0x40)) s (0x11b8c1 + BitVec.ofNat 64 5)) 8) (movR64M64Effect 0x11b8c1 0 (.sib 4 none 0 (.d8 0x40))) (Reg.operands [.gpr 4] [])) #v[4]
    (.letOp (n := 81) (.exec 0x11b8c6 (StorePre 0x11b8c6 3 (fun s => AddrMode.addr (.base 0 .none) s (0x11b8c6 + BitVec.ofNat 64 3)) 8) (movM64R64Effect 0x11b8c6 1 (.base 0 .none)) (Reg.operands [.gpr 1, .gpr 0] [])) #v[63, 79]
    (.letOp (n := 82) (.exec 0x11b8c9 (StorePre 0x11b8c9 4 (fun s => AddrMode.addr (.base 0 (.d8 0x8)) s (0x11b8c9 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8c9 2 (.base 0 (.d8 0x8))) (Reg.operands [.gpr 2, .gpr 0] [])) #v[69, 79]
    (.letOp (n := 83) (.exec 0x11b8cd (StorePre 0x11b8cd 4 (fun s => AddrMode.addr (.base 0 (.d8 0x10)) s (0x11b8cd + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8cd 15 (.base 0 (.d8 0x10))) (Reg.operands [.gpr 15, .gpr 0] [])) #v[73, 79]
    (.letOp (n := 84) (.exec 0x11b8d1 (StorePre 0x11b8d1 4 (fun s => AddrMode.addr (.base 0 (.d8 0x18)) s (0x11b8d1 + BitVec.ofNat 64 4)) 8) (movM64R64Effect 0x11b8d1 3 (.base 0 (.d8 0x18))) (Reg.operands [.gpr 3, .gpr 0] [])) #v[77, 79]
    (.letOp (n := 85) (.out 0x11b8d5 (addR64Imm8Effect 0x11b8d5 4 0x48) (EffectPart.reads (.reg (.gpr 4)) [.gpr 4] []) (.reg (.gpr 4))) #v[4]
    (.letOp (n := 86) (.exec 0x11b8d5 (fun s => s.RIP = 0x11b8d5) (addR64Imm8Effect 0x11b8d5 4 0x48) (Reg.operands [.gpr 4] [])) #v[4]
    (b_l11b88c_1))))))))))))))))))))))))))))))))))

def bytes_l11b88c : List UInt8 :=
  [0x88, 0x44, 0x24, 0x08, 0x48, 0x8D, 0x44, 0x24, 0x08, 0x0F, 0xB6, 0x44, 0x24, 0x08, 0x48, 0x8B,
    0x4C, 0x24, 0x10, 0x48, 0x8B, 0x54, 0x24, 0x20, 0x84, 0xC0, 0x48, 0x0F, 0x45, 0xCA, 0x48, 0x8B,
    0x54, 0x24, 0x38, 0x84, 0xC0, 0x49, 0x0F, 0x45, 0xD4, 0x84, 0xC0, 0x4D, 0x0F, 0x45, 0xFE, 0x84,
    0xC0, 0x48, 0x0F, 0x45, 0xDD, 0x48, 0x8B, 0x44, 0x24, 0x40, 0x48, 0x89, 0x08, 0x48, 0x89, 0x50,
    0x08, 0x4C, 0x89, 0x78, 0x10, 0x48, 0x89, 0x58, 0x18, 0x48, 0x83, 0xC4, 0x48] ++ bytes_l11b88c_1

theorem code_l11b88c : ∀ x ∈ codeRange 0x11b88c bytes_l11b88c, x ∈ fnCode :=
  codeRange_sub_section_append (s := textSection) (.head _) 0x1b88c 77 (by decide +kernel)
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl) rfl rfl code_l11b88c_1

end K256.Proofs.Generate.LIR
